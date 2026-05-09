#!/usr/bin/env python3
"""Generate Shields.io endpoint JSON for Lean repository badges.

Badges
------
* sorries — count of sorry in tracked .lean files.
* axioms — count of axiom declarations in tracked .lean files.
* lean / mathlib — toolchain versions.
* blueprint_no_leanok — unique blueprint declarations that have a
  \lean{...} reference but **no** \leanok marker anywhere (neither
  statement-level nor proof-level).  A declaration is counted when every
  blueprint entry that references it lacks \leanok.  This is the count
  of declarations whose Lean statement has not been matched to the blueprint
  yet.
* blueprint_not_ready — unique blueprint declarations that are **not
  fully formalized** in Lean according to the convention in
  docs/blueprint_style_guide.md:

  * for theorem-/lemma-/proposition-/corollary-scoped declarations: both
    statement-level **and** proof-level \leanok must be present;
  * for definition-only declarations: statement-level \leanok must
    be present (definitions have no proof block);
  * remark-/example-only declarations are excluded from the denominator
    because they are not expected to carry a proof.

  This badge shows the count of declarations that still need proof work or
  (for definitions) statement matching.
"""

from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tomllib
from collections import defaultdict
from pathlib import Path


SORRY_RE = re.compile(r"\bsorry\b")
AXIOM_RE = re.compile(
    r"(?m)^\s*"
    r"(?:@\[[^\]\n]*(?:\n\s*[^\]\n]*)*\]\s*)*"
    r"(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"axiom\s+[A-Za-z_]"
)


def tracked_lean_files(repo_root: Path) -> list[Path]:
    output = subprocess.check_output(
        ["git", "ls-files", "*.lean"], cwd=repo_root, text=True
    )
    return [
        repo_root / line
        for line in output.splitlines()
        if line
        and "TNLean/Archive/" not in line
        and not line.startswith("scripts/")
    ]


def strip_comments_and_strings(source: str) -> str:
    result: list[str] = []
    i = 0
    block_depth = 0
    in_string = False

    while i < len(source):
        char = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""

        if in_string:
            if char == "\\" and nxt:
                i += 2
                continue
            if char == '"':
                in_string = False
            result.append("\n" if char == "\n" else " ")
            i += 1
            continue

        if block_depth > 0:
            if char == "/" and nxt == "-":
                block_depth += 1
                i += 2
                continue
            if char == "-" and nxt == "/":
                block_depth -= 1
                i += 2
                continue
            result.append("\n" if char == "\n" else " ")
            i += 1
            continue

        if char == "-" and nxt == "-":
            while i < len(source) and source[i] != "\n":
                result.append(" ")
                i += 1
            continue

        if char == "/" and nxt == "-":
            block_depth = 1
            i += 2
            continue

        if char == '"':
            in_string = True
            result.append(" ")
            i += 1
            continue

        result.append(char)
        i += 1

    return "".join(result)


def badge(label: str, message: str, color: str) -> dict[str, str | int]:
    return {
        "schemaVersion": 1,
        "label": label,
        "message": message,
        "color": color,
    }


def count_pattern(files: list[Path], pattern: re.Pattern[str]) -> int:
    count = 0
    for path in files:
        source = path.read_text(encoding="utf-8")
        count += len(pattern.findall(strip_comments_and_strings(source)))
    return count


def count_color(count: int, *, warn: int, danger: int) -> str:
    if count == 0:
        return "brightgreen"
    if count < warn:
        return "yellow"
    if count < danger:
        return "orange"
    return "red"


def lean_version(repo_root: Path) -> str:
    toolchain = (repo_root / "lean-toolchain").read_text(encoding="utf-8").strip()
    return toolchain.rsplit(":", maxsplit=1)[-1]


def mathlib_version(repo_root: Path) -> str:
    lakefile = tomllib.loads((repo_root / "lakefile.toml").read_text(encoding="utf-8"))
    for requirement in lakefile.get("require", []):
        if requirement.get("name") == "mathlib":
            return str(requirement.get("rev", "unknown"))
    return "unknown"


# ---------------------------------------------------------------------------
# Blueprint badge helpers
# ---------------------------------------------------------------------------

# Environment types that are expected to carry a proof in the blueprint.
_PROOF_BEARING_ENV_TYPES: frozenset[str] = frozenset(
    {"theorem", "lemma", "proposition", "corollary"}
)

# Environment types that are ignored in the "not ready" denominator because
# they are auxiliary annotations, not formalization targets.
_SKIP_ENV_TYPES: frozenset[str] = frozenset({"remark", "example"})


def _blueprint_badge_counts(
    entries: list,
) -> tuple[int, int]:
    """Return (no_leanok_count, not_ready_count) for **unique declarations**.

    The caller must pass a list of objects with attributes lean_decl,
    has_leanok, proof_has_leanok, and env_type (a protocol — see source for the expected attributes).

    no_leanok_count
       Number of unique lean_decl values that have **no** \leanok
       marker anywhere — neither has_leanok nor proof_has_leanok on
       any entry that references the declaration.

    not_ready_count
       Number of unique lean_decl values that are **not fully
       formalized** by the following rules:

       * Proof-bearing declarations (theorem, lemma, proposition,
         corollary) require **both** statement-level and proof-level
         \leanok.
       * Definition-only declarations require statement-level \leanok
         (they cannot carry a proof).
       * Remark-/example-only declarations are excluded from the denominator.

       Declarations that mix proof-bearing and non-proof-bearing environment
       types are treated as proof-bearing.
    """
    # Group entries by declaration name.
    decl_entries: dict[str, list] = defaultdict(list)
    for entry in entries:
        decl_entries[entry.lean_decl].append(entry)

    no_leanok = 0
    not_ready = 0

    for decl, elist in decl_entries.items():
        has_stmt = any(e.has_leanok for e in elist)
        has_proof = any(e.proof_has_leanok for e in elist)
        env_types = {e.env_type for e in elist}

        # --- no-leanok: no marker at all ---
        if not has_stmt and not has_proof:
            no_leanok += 1

        # --- not-ready: not fully formalized ---
        is_proof_bearing = bool(env_types & _PROOF_BEARING_ENV_TYPES)
        is_skip_only = env_types <= _SKIP_ENV_TYPES
        if is_skip_only:
            # Remark/example-only: not a formalization target.
            continue
        if is_proof_bearing:
            if not (has_stmt and has_proof):
                not_ready += 1
        else:
            # Definition-only (or other non-proof-bearing): needs statement-level.
            if not has_stmt:
                not_ready += 1

    return no_leanok, not_ready


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=Path("badges"))
    parser.add_argument(
        "--blueprint-src",
        type=Path,
        default=None,
        help=(
            "Path to blueprint/src directory.  When provided, also emit "
            "blueprint_no_leanok.json and blueprint_not_ready.json badges "
            "by parsing \lean{} and \leanok annotations in the chapter "
            ".tex files."
        ),
    )
    args = parser.parse_args()

    repo_root = Path(__file__).resolve().parents[1]
    lean_files = tracked_lean_files(repo_root)

    sorry_count = count_pattern(lean_files, SORRY_RE)
    axiom_count = count_pattern(lean_files, AXIOM_RE)

    badge_records = {
        "sorries.json": badge(
            "sorries", str(sorry_count), count_color(sorry_count, warn=10, danger=50)
        ),
        "axioms.json": badge(
            "axioms", str(axiom_count), "brightgreen" if axiom_count == 0 else "red"
        ),
        "lean.json": badge("Lean", lean_version(repo_root), "blue"),
        "mathlib.json": badge("Mathlib", mathlib_version(repo_root), "blue"),
    }

    # --- Blueprint badges ---
    if args.blueprint_src is not None:
        blueprint_src = args.blueprint_src
        if not blueprint_src.is_absolute():
            blueprint_src = repo_root / blueprint_src

        # Import the blueprint parser (lazy, so the script still works without
        # the blueprint source tree checked out).
        sys.path.insert(0, str(repo_root / "scripts"))
        from blueprint_lean_sync import collect_blueprint_entries  # noqa: E402

        entries = collect_blueprint_entries(blueprint_src)
        no_leanok_count, not_ready_count = _blueprint_badge_counts(entries)

        badge_records["blueprint_no_leanok.json"] = badge(
            r"blueprint: no \leanok",
            str(no_leanok_count),
            count_color(no_leanok_count, warn=100, danger=300),
        )
        badge_records["blueprint_not_ready.json"] = badge(
            "blueprint: not ready",
            str(not_ready_count),
            count_color(not_ready_count, warn=100, danger=300),
        )

    # --- Write badges ---
    args.output_dir.mkdir(parents=True, exist_ok=True)
    for filename, payload in badge_records.items():
        path = args.output_dir / filename
        path.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
        print(f"Wrote {path}: {payload['message']}")


if __name__ == "__main__":
    main()
