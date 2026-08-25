#!/usr/bin/env python3
"""Locate the pinned tenkz companion checkout.

Resolution order: ``TENKZ_ROOT``, then ``.deps/tenkz`` after
``scripts/fetch_tenkz.py``.
"""

from __future__ import annotations

import os
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]


class TenkzMissing(FileNotFoundError):
    """The companion package is not checked out."""


def tenkz_root() -> Path:
    """Return the tenkz repository root (contains ``tex/tenkz/tenkz.sty``)."""
    env = os.environ.get("TENKZ_ROOT")
    if env:
        root = Path(env).expanduser().resolve()
        if (root / "tex/tenkz/tenkz.sty").is_file():
            return root
        raise TenkzMissing(f"TENKZ_ROOT={root} has no tex/tenkz/tenkz.sty")
    deps = REPO / ".deps" / "tenkz"
    if (deps / "tex/tenkz/tenkz.sty").is_file():
        return deps
    raise TenkzMissing(
        "tenkz is not checked out; run python3 scripts/fetch_tenkz.py"
    )


def tenkz_tex() -> Path:
    """Return the directory that belongs on TEXINPUTS."""
    return tenkz_root() / "tex" / "tenkz"


def ensure_pythonpath() -> Path:
    """Put tenkz's ``scripts/`` on ``sys.path`` and return that directory."""
    scripts = tenkz_root() / "scripts"
    path = str(scripts)
    if path not in sys.path:
        sys.path.insert(0, path)
    return scripts
