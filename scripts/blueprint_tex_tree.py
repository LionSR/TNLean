#!/usr/bin/env python3
"""Read blueprint TeX sources with their ``\\input`` wrappers expanded.

Chapters may ``\\input`` other chapter files and shared diagrams from
``blueprint/src/figures/``.  Source-linked diagram tests must see the ink
wherever it lives, so they read the expanded tree rather than the raw file.
Targets resolve against ``blueprint/src`` (the blueprint's ``TEXINPUTS``
root), with ``.tex`` appended when the target has no extension.
"""

from __future__ import annotations

import re
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
SOURCE_ROOT = REPO / "blueprint" / "src"

# The literal form only: macro wrappers (such as tnleanfigures' \tnfigure)
# are deliberately not expanded, because chapters must use the literal form.
INPUT_RE = re.compile(r"\\input\{([^}]+)\}")


def input_path(target: str, src_root: Path = SOURCE_ROOT) -> Path:
    """Return the file that ``\\input{target}`` names under ``src_root``."""
    if not target.endswith(".tex"):
        target += ".tex"
    return src_root / target


def read_tex_tree(path: Path, src_root: Path = SOURCE_ROOT) -> str:
    """Read ``path`` after recursively expanding every ``\\input{...}``.

    Each ``\\input{target}`` is replaced by the expanded text of
    ``input_path(target, src_root)``.  A missing target raises
    ``FileNotFoundError`` and an input cycle raises ``ValueError``.
    """
    return _expand(Path(path), Path(src_root), ())


def _expand(path: Path, src_root: Path, stack: tuple[Path, ...]) -> str:
    key = path.resolve()
    if key in stack:
        chain = " -> ".join(str(item) for item in (*stack, key))
        raise ValueError(f"\\input cycle: {chain}")
    source = path.read_text(encoding="utf-8")

    def expand(match: re.Match[str]) -> str:
        return _expand(input_path(match.group(1), src_root), src_root, (*stack, key))

    return INPUT_RE.sub(expand, source)
