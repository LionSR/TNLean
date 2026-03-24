#!/usr/bin/env python3
"""
Blueprint ↔ Lean code synchronisation checker.

Parses the blueprint .tex files for \lean{DeclName} and \leanok annotations,
then greps the Lean source tree for matching declarations.  Reports:

  1. Blueprint references whose Lean declaration cannot be found.
  2. \leanok tags on items whose declaration is missing from the Lean source.
  3. lean_decls entries that don't appear in any .tex file (stale entries).
  4. \lean{} refs that are not listed in lean_decls (missing entries).
  5. Summary statistics (formalization progress per chapter).

Exit code 0  → everything in sync.
Exit code 1  → mismatches found (details on stdout / in report file).
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path


# ---------------------------------------------------------------------------
# Helpers
# ---------------------------------------------------------------------------

_LEAN_DECL_RE = re.compile(
    r"^\s*(?:@\[.*?\]\s*)?(?:noncomputable\s+)?(?:protected\s+)?(?:private\s+)?(?:def|theorem|lemma|abbrev|instance|class|structure|inductive)\s+([\w.]+)",
    re.MULTILINE,
)

_NAMESPACE_OPEN_RE = re.compile(r"^\s*namespace\s+([\w.]+)", re.MULTILINE)
_NAMESPACE_CLOSE_RE = re.compile(r"^\s*end\s+([\w.]+)", re.MULTILINE)

_TEX_LEAN_RE = re.compile(r"\\lean\{([^}]+)\}")
_TEX_LEANOK_RE = re.compile(r"\\leanok")
_TEX_ENV_BEGIN_RE = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
    r"(?:\[.*?\])?"
    r"(?:\\label\{([^}]+)\})?"
)
_TEX_ENV_END_RE = re.compile(
    r"\\end\{(definition|theorem|lemma|proposition|corollary|remark|example)\}"
)
_TEX_PROOF_BEGIN_RE = re.compile(r"\\begin\{proof\}")
_TEX_PROOF_END_RE = re.compile(r"\\end\{proof\}")


# ---------------------------------------------------------------------------
# Data structures
# ---------------------------------------------------------------------------

@dataclass
class BlueprintEntry:
    """A single blueprint environment that references a Lean declaration."""
    file: str
    line: int
    env_type: str          # definition, theorem, lemma, …
    label: str | None
    lean_decl: str         # the \lean{X} name
    has_leanok: bool       # whether \leanok appears on the statement
    proof_has_leanok: bool  # whether the proof block has \leanok


@dataclass
class LeanDecl:
    """A Lean declaration found in the source tree."""
    file: str
    line: int
    fqn: str  # fully-qualified name including namespace


@dataclass
class SyncReport:
    """Aggregated sync report."""
    blueprint_entries: list[BlueprintEntry] = field(default_factory=list)
    lean_decls: dict[str, LeanDecl] = field(default_factory=dict)
    # Problems
    missing_in_lean: list[BlueprintEntry] = field(default_factory=list)
    leanok_but_missing: list[BlueprintEntry] = field(default_factory=list)
    stale_lean_decls: list[str] = field(default_factory=list)
    missing_from_lean_decls_file: list[str] = field(default_factory=list)

    @property
    def ok(self) -> bool:
        return not (
            self.missing_in_lean
            or self.leanok_but_missing
            or self.stale_lean_decls
            or self.missing_from_lean_decls_file
        )


# ---------------------------------------------------------------------------
# Parse Lean source tree
# ---------------------------------------------------------------------------

def collect_lean_decls(lean_root: Path) -> dict[str, LeanDecl]:
    """Walk all .lean files and return {fqn: LeanDecl}."""
    decls: dict[str, LeanDecl] = {}

    for lean_file in sorted(lean_root.rglob("*.lean")):
        text = lean_file.read_text(errors="replace")
        lines = text.splitlines()

        # Track namespace stack
        ns_stack: list[str] = []

        for i, line in enumerate(lines, 1):
            # Namespace open
            m = _NAMESPACE_OPEN_RE.match(line)
            if m:
                ns_stack.append(m.group(1))
                continue

            # Namespace close
            m = _NAMESPACE_CLOSE_RE.match(line)
            if m:
                closed = m.group(1)
                # Pop matching namespace(s)
                if ns_stack and ns_stack[-1] == closed:
                    ns_stack.pop()
                elif ns_stack:
                    # Try to find it further up
                    for j in range(len(ns_stack) - 1, -1, -1):
                        if ns_stack[j] == closed:
                            ns_stack = ns_stack[:j]
                            break
                continue

            # Declaration
            m = _LEAN_DECL_RE.match(line)
            if m:
                short_name = m.group(1)
                # If the short name already contains dots, it's already qualified
                if "." in short_name:
                    fqn = short_name
                else:
                    prefix = ".".join(ns_stack) + "." if ns_stack else ""
                    fqn = prefix + short_name
                rel = str(lean_file.relative_to(lean_root.parent))
                decls[fqn] = LeanDecl(file=rel, line=i, fqn=fqn)

    return decls


# ---------------------------------------------------------------------------
# Parse blueprint .tex files
# ---------------------------------------------------------------------------

def collect_blueprint_entries(blueprint_src: Path) -> list[BlueprintEntry]:
    """Parse all chapter .tex files for \\lean{} and \\leanok."""
    entries: list[BlueprintEntry] = []
    chapter_dir = blueprint_src / "chapter"
    if not chapter_dir.exists():
        return entries

    for tex_file in sorted(chapter_dir.glob("*.tex")):
        text = tex_file.read_text(errors="replace")
        lines = text.splitlines()

        # State machine: track current environment
        env_stack: list[dict] = []
        in_proof = False
        current_proof: dict | None = None
        last_env: dict | None = None  # last closed environment

        for i, line in enumerate(lines, 1):
            # Check for environment begin
            m = _TEX_ENV_BEGIN_RE.search(line)
            if m:
                env = {
                    "type": m.group(1),
                    "label": m.group(2),
                    "file": str(tex_file.relative_to(blueprint_src.parent)),
                    "line": i,
                    "lean_decls": [],
                    "has_leanok": bool(_TEX_LEANOK_RE.search(line)),
                }
                env_stack.append(env)
                # Check rest of line for \lean{} and \leanok
                for lm in _TEX_LEAN_RE.finditer(line):
                    for decl in lm.group(1).split(","):
                        decl = decl.strip()
                        if decl:
                            env["lean_decls"].append(decl)
                continue

            # Check for environment end
            m = _TEX_ENV_END_RE.search(line)
            if m and env_stack:
                env = env_stack.pop()
                env_entry_start = len(entries)
                for decl in env["lean_decls"]:
                    entries.append(BlueprintEntry(
                        file=env["file"],
                        line=env["line"],
                        env_type=env["type"],
                        label=env["label"],
                        lean_decl=decl,
                        has_leanok=env["has_leanok"],
                        proof_has_leanok=False,
                    ))
                env["_entry_start"] = env_entry_start
                env["_entry_end"] = len(entries)
                last_env = env
                continue

            # Proof begin
            m = _TEX_PROOF_BEGIN_RE.search(line)
            if m:
                in_proof = True
                current_proof = {
                    "has_leanok": bool(_TEX_LEANOK_RE.search(line)),
                }
                continue

            # Proof end
            m = _TEX_PROOF_END_RE.search(line)
            if m and in_proof:
                # Attach proof leanok to all entries from the preceding environment
                if current_proof and current_proof["has_leanok"] and last_env:
                    for idx in range(last_env["_entry_start"], last_env["_entry_end"]):
                        e = entries[idx]
                        entries[idx] = BlueprintEntry(
                            file=e.file,
                            line=e.line,
                            env_type=e.env_type,
                            label=e.label,
                            lean_decl=e.lean_decl,
                            has_leanok=e.has_leanok,
                            proof_has_leanok=True,
                        )
                in_proof = False
                current_proof = None
                continue

            # Inside an environment: collect \lean{} and \leanok
            if env_stack:
                for lm in _TEX_LEAN_RE.finditer(line):
                    for decl in lm.group(1).split(","):
                        decl = decl.strip()
                        if decl:
                            env_stack[-1]["lean_decls"].append(decl)
                if _TEX_LEANOK_RE.search(line):
                    env_stack[-1]["has_leanok"] = True

    return entries


# ---------------------------------------------------------------------------
# Read lean_decls file
# ---------------------------------------------------------------------------

def read_lean_decls_file(path: Path) -> set[str]:
    if not path.exists():
        return set()
    return {line.strip() for line in path.read_text().splitlines() if line.strip()}


# ---------------------------------------------------------------------------
# Run sync check
# ---------------------------------------------------------------------------

def run_sync(
    root: Path,
    *,
    report_file: Path | None = None,
    update_lean_decls: bool = False,
) -> SyncReport:
    lean_root = root / "TNLean"
    blueprint_src = root / "blueprint" / "src"
    lean_decls_path = root / "blueprint" / "lean_decls"

    report = SyncReport()

    # 1. Collect Lean declarations
    print("Scanning Lean source tree …")
    report.lean_decls = collect_lean_decls(lean_root)
    print(f"  Found {len(report.lean_decls)} declarations in Lean source")

    # 2. Collect blueprint entries
    print("Scanning blueprint .tex files …")
    report.blueprint_entries = collect_blueprint_entries(blueprint_src)
    print(f"  Found {len(report.blueprint_entries)} \\lean{{}} references in blueprint")

    # 3. Cross-reference
    blueprint_decl_names: set[str] = set()
    for entry in report.blueprint_entries:
        blueprint_decl_names.add(entry.lean_decl)
        if entry.lean_decl not in report.lean_decls:
            report.missing_in_lean.append(entry)
            if entry.has_leanok:
                report.leanok_but_missing.append(entry)

    # 4. Check lean_decls file
    existing_lean_decls = read_lean_decls_file(lean_decls_path)
    for name in sorted(existing_lean_decls - blueprint_decl_names):
        report.stale_lean_decls.append(name)
    for name in sorted(blueprint_decl_names - existing_lean_decls):
        report.missing_from_lean_decls_file.append(name)

    # 5. Optionally update lean_decls
    if update_lean_decls:
        sorted_decls = sorted(blueprint_decl_names)
        lean_decls_path.write_text("\n".join(sorted_decls) + "\n")
        print(f"  Updated {lean_decls_path} with {len(sorted_decls)} entries")

    # 6. Print report
    _print_report(report, root)

    # 7. Write JSON report
    if report_file:
        _write_json_report(report, report_file, root)

    return report


def _chapter_stats(report: SyncReport) -> dict[str, dict]:
    """Per-chapter formalization progress."""
    stats: dict[str, dict] = {}
    for entry in report.blueprint_entries:
        chapter = entry.file
        if chapter not in stats:
            stats[chapter] = {
                "total": 0,
                "formalized": 0,
                "proof_formalized": 0,
                "missing_lean": 0,
            }
        s = stats[chapter]
        s["total"] += 1
        found = entry.lean_decl in report.lean_decls
        if entry.has_leanok and found:
            s["formalized"] += 1
        if entry.proof_has_leanok and found:
            s["proof_formalized"] += 1
        if not found:
            s["missing_lean"] += 1
    return stats


def _print_report(report: SyncReport, root: Path) -> None:
    print()
    print("=" * 70)
    print("  BLUEPRINT ↔ LEAN SYNC REPORT")
    print("=" * 70)

    # Per-chapter stats
    stats = _chapter_stats(report)
    print()
    print("Per-chapter formalization progress:")
    print(f"  {'Chapter':<50} {'Done':>5} / {'Total':>5}  {'%':>6}")
    print("  " + "-" * 68)
    total_done = 0
    total_all = 0
    for chapter in sorted(stats):
        s = stats[chapter]
        pct = 100 * s["formalized"] / s["total"] if s["total"] else 0
        short = chapter.replace("src/chapter/", "")
        print(f"  {short:<50} {s['formalized']:>5} / {s['total']:>5}  {pct:>5.1f}%")
        total_done += s["formalized"]
        total_all += s["total"]
    pct = 100 * total_done / total_all if total_all else 0
    print("  " + "-" * 68)
    print(f"  {'TOTAL':<50} {total_done:>5} / {total_all:>5}  {pct:>5.1f}%")

    # Missing in Lean
    if report.missing_in_lean:
        print()
        print(f"Blueprint refs with NO matching Lean declaration ({len(report.missing_in_lean)}):")
        seen: set[str] = set()
        for entry in report.missing_in_lean:
            if entry.lean_decl not in seen:
                seen.add(entry.lean_decl)
                ok_tag = " [has \\leanok!]" if entry.has_leanok else ""
                print(f"  ✗ {entry.lean_decl}{ok_tag}")
                print(f"    {entry.file}:{entry.line} ({entry.env_type})")

    # leanok but missing
    if report.leanok_but_missing:
        print()
        print(f"WARNING: \\leanok on items whose Lean decl is MISSING ({len(report.leanok_but_missing)}):")
        seen2: set[str] = set()
        for entry in report.leanok_but_missing:
            if entry.lean_decl not in seen2:
                seen2.add(entry.lean_decl)
                print(f"  ⚠ {entry.lean_decl}  ({entry.file}:{entry.line})")

    # Stale lean_decls
    if report.stale_lean_decls:
        print()
        print(f"Stale entries in lean_decls (not in any .tex) ({len(report.stale_lean_decls)}):")
        for name in report.stale_lean_decls:
            print(f"  − {name}")

    # Missing from lean_decls
    if report.missing_from_lean_decls_file:
        print()
        print(f"Blueprint refs missing from lean_decls file ({len(report.missing_from_lean_decls_file)}):")
        for name in report.missing_from_lean_decls_file:
            print(f"  + {name}")

    # Summary
    print()
    if report.ok:
        print("✓ Blueprint and Lean code are in sync.")
    else:
        problems = (
            len(report.missing_in_lean)
            + len(report.stale_lean_decls)
            + len(report.missing_from_lean_decls_file)
        )
        print(f"✗ Found {problems} sync issue(s). See details above.")
    print()


def _write_json_report(report: SyncReport, path: Path, root: Path) -> None:
    data = {
        "sync_ok": report.ok,
        "total_blueprint_refs": len(report.blueprint_entries),
        "total_lean_decls": len(report.lean_decls),
        "missing_in_lean": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line, "has_leanok": e.has_leanok}
            for e in report.missing_in_lean
        ],
        "leanok_but_missing": [
            {"decl": e.lean_decl, "file": e.file, "line": e.line}
            for e in report.leanok_but_missing
        ],
        "stale_lean_decls": report.stale_lean_decls,
        "missing_from_lean_decls_file": report.missing_from_lean_decls_file,
        "chapter_stats": _chapter_stats(report),
    }
    path.write_text(json.dumps(data, indent=2) + "\n")
    print(f"JSON report written to {path}")


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def main() -> None:
    parser = argparse.ArgumentParser(
        description="Check synchronisation between blueprint .tex and Lean source."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path(__file__).resolve().parent.parent,
        help="Repository root (default: auto-detected)",
    )
    parser.add_argument(
        "--report",
        type=Path,
        default=None,
        help="Write JSON report to this file",
    )
    parser.add_argument(
        "--update-lean-decls",
        action="store_true",
        help="Rewrite blueprint/lean_decls from current .tex refs",
    )
    parser.add_argument(
        "--ci",
        action="store_true",
        help="Exit with code 1 on mismatches (for CI)",
    )
    args = parser.parse_args()

    report = run_sync(
        args.root,
        report_file=args.report,
        update_lean_decls=args.update_lean_decls,
    )

    if args.ci and not report.ok:
        sys.exit(1)


if __name__ == "__main__":
    main()
