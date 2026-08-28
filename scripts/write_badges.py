#!/usr/bin/env python3
"""Write Shields.io endpoint JSON files for the project homepage.

Usage:
  write_badges.py [OUTPUT_DIR]

  OUTPUT_DIR  Directory to write badge JSON files into.
              Defaults to <repo-root>/home_page/badges.
"""

from __future__ import annotations

import json
import re
import sys
from collections import defaultdict
from pathlib import Path

from badge_utils import axioms_color, count_color, sorries_color


ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / "TNLean"
BLUEPRINT_SRC = ROOT / "blueprint" / "src"

_PROOF_BEARING_ENV_TYPES: frozenset[str] = frozenset(
    {"theorem", "lemma", "proposition", "corollary"}
)
_SKIP_ENV_TYPES: frozenset[str] = frozenset({"remark", "example"})


def strip_lean_comments_and_strings(text: str) -> str:
    """Remove Lean comments and strings while preserving token separation."""
    out: list[str] = []
    i = 0
    n = len(text)
    block_depth = 0
    in_string = False

    while i < n:
        ch = text[i]
        nxt = text[i + 1] if i + 1 < n else ""

        if block_depth:
            if ch == "/" and nxt == "-":
                block_depth += 1
                out.append("  ")
                i += 2
            elif ch == "-" and nxt == "/":
                block_depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if in_string:
            if ch == "\\" and nxt:
                out.append("  ")
                i += 2
            else:
                if ch == '"':
                    in_string = False
                out.append("\n" if ch == "\n" else " ")
                i += 1
            continue

        if ch == "-" and nxt == "-":
            while i < n and text[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if ch == "/" and nxt == "-":
            block_depth = 1
            out.append("  ")
            i += 2
            continue
        if ch == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue

        out.append(ch)
        i += 1

    return "".join(out)


def lean_files() -> list[Path]:
    return [
        path
        for path in LEAN_ROOT.rglob("*.lean")
        if "Archive" not in path.relative_to(LEAN_ROOT).parts
    ]


def count_token(token: str) -> int:
    pattern = re.compile(rf"(?<![A-Za-z0-9_']){re.escape(token)}(?![A-Za-z0-9_'])")
    total = 0
    for path in lean_files():
        total += len(pattern.findall(strip_lean_comments_and_strings(path.read_text())))
    return total


def lean_version() -> str:
    raw = (ROOT / "lean-toolchain").read_text().strip()
    return raw.rsplit(":", 1)[-1] if ":" in raw else raw


def mathlib_version() -> str:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest.get("packages", []):
        if package.get("name") == "mathlib":
            return package.get("inputRev") or package.get("rev", "")[:7]
    return "unknown"


def write_badge(name: str, label: str, message: str, color: str, badge_dir: Path) -> None:
    badge_dir.mkdir(parents=True, exist_ok=True)
    payload = {"schemaVersion": 1, "label": label, "message": message, "color": color}
    (badge_dir / f"{name}.json").write_text(json.dumps(payload, indent=2) + "\n")


def blueprint_badge_counts() -> tuple[int, int]:
    """Return (no_leanok_count, not_ready_count) for unique blueprint declarations."""
    sys.path.insert(0, str(ROOT / "scripts"))
    from blueprint_lean_sync import collect_blueprint_entries

    entries = collect_blueprint_entries(BLUEPRINT_SRC)
    decl_entries: dict[str, list] = defaultdict(list)
    for entry in entries:
        decl_entries[entry.lean_decl].append(entry)

    no_leanok = 0
    not_ready = 0
    for elist in decl_entries.values():
        has_stmt = any(e.has_leanok for e in elist)
        has_proof = any(e.proof_has_leanok for e in elist)
        env_types = {e.env_type for e in elist}
        if not has_stmt and not has_proof:
            no_leanok += 1
        if env_types <= _SKIP_ENV_TYPES:
            continue
        is_proof_bearing = bool(env_types & _PROOF_BEARING_ENV_TYPES)
        if is_proof_bearing:
            if not (has_stmt and has_proof):
                not_ready += 1
        elif not has_stmt:
            not_ready += 1
    return no_leanok, not_ready


def badge_count_colors(sorries: int, axioms: int) -> dict[str, str]:
    """Return colors for the count badges emitted by this generator."""
    return {"sorries": sorries_color(sorries), "axioms": axioms_color(axioms)}


def main() -> None:
    badge_dir = Path(sys.argv[1]) if len(sys.argv) > 1 else ROOT / "home_page" / "badges"
    sorries = count_token("sorry")
    axioms = count_token("axiom")
    colors = badge_count_colors(sorries, axioms)
    write_badge("sorries", "sorries", str(sorries), colors["sorries"], badge_dir)
    write_badge("axioms", "axioms", str(axioms), colors["axioms"], badge_dir)
    write_badge("lean", "Lean", lean_version(), "blue", badge_dir)
    write_badge("mathlib", "Mathlib", mathlib_version(), "blue", badge_dir)
    no_leanok, not_ready = blueprint_badge_counts()
    write_badge(
        "blueprint_no_leanok",
        r"blueprint: no \leanok",
        str(no_leanok),
        count_color(no_leanok, warning_at=100, danger_at=300),
        badge_dir,
    )
    write_badge(
        "blueprint_not_ready",
        "blueprint: not ready",
        str(not_ready),
        count_color(not_ready, warning_at=100, danger_at=300),
        badge_dir,
    )


if __name__ == "__main__":
    main()
