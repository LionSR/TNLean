#!/usr/bin/env python3
"""Write Shields.io endpoint JSON files for the project homepage."""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
BADGE_DIR = ROOT / "home_page" / "badges"
LEAN_ROOT = ROOT / "TNLean"


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


def write_badge(name: str, label: str, message: str, color: str) -> None:
    BADGE_DIR.mkdir(parents=True, exist_ok=True)
    payload = {"schemaVersion": 1, "label": label, "message": message, "color": color}
    (BADGE_DIR / f"{name}.json").write_text(json.dumps(payload, indent=2) + "\n")


def count_color(count: int, *, warning_at: int = 1) -> str:
    if count == 0:
        return "brightgreen"
    if count <= warning_at:
        return "yellow"
    return "orange"


def main() -> None:
    sorries = count_token("sorry")
    axioms = count_token("axiom")
    write_badge("sorries", "sorries", str(sorries), count_color(sorries, warning_at=10))
    write_badge("axioms", "axioms", str(axioms), count_color(axioms, warning_at=0))
    write_badge("lean", "Lean", lean_version(), "blue")
    write_badge("mathlib", "Mathlib", mathlib_version(), "blue")


if __name__ == "__main__":
    main()
