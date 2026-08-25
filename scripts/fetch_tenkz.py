#!/usr/bin/env python3
"""Clone or update the tenkz companion pinned by ``tenkz.toml``."""

from __future__ import annotations

import argparse
import subprocess
import sys
import tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CONFIG = REPO / "tenkz.toml"
DEST = REPO / ".deps" / "tenkz"


def load_pin() -> tuple[str, str]:
    data = tomllib.loads(CONFIG.read_text(encoding="utf-8"))
    tenkz = data.get("tenkz")
    if not isinstance(tenkz, dict):
        raise SystemExit("tenkz.toml is missing a [tenkz] table")
    git = tenkz.get("git")
    rev = tenkz.get("rev")
    if not isinstance(git, str) or not git:
        raise SystemExit("tenkz.toml [tenkz].git must be a nonempty string")
    if not isinstance(rev, str) or not rev:
        raise SystemExit("tenkz.toml [tenkz].rev must be a nonempty string")
    return git, rev


def git(args: list[str], *, cwd: Path | None = None) -> str:
    result = subprocess.run(
        ["git", *args],
        cwd=cwd,
        check=False,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode:
        detail = result.stderr.strip() or result.stdout.strip()
        raise SystemExit(f"git {' '.join(args)} failed: {detail}")
    return result.stdout.strip()


def fetch(git_url: str, rev: str) -> Path:
    DEST.parent.mkdir(parents=True, exist_ok=True)
    if not (DEST / ".git").is_dir():
        if DEST.exists():
            raise SystemExit(f"{DEST} exists and is not a git checkout")
        git(["clone", "--filter=blob:none", git_url, str(DEST)])
    else:
        git(["remote", "set-url", "origin", git_url], cwd=DEST)
        git(["fetch", "--tags", "origin"], cwd=DEST)
    git(["fetch", "--depth=1", "origin", rev], cwd=DEST)
    git(["checkout", "--detach", "FETCH_HEAD"], cwd=DEST)
    wanted = git(["rev-parse", "FETCH_HEAD^{commit}"], cwd=DEST)
    have = git(["rev-parse", "HEAD"], cwd=DEST)
    if wanted != have:
        raise SystemExit(f"tenkz HEAD {have} does not match pin {rev} ({wanted})")
    sty = DEST / "tex" / "tenkz" / "tenkz.sty"
    if not sty.is_file():
        raise SystemExit(f"checked out tenkz at {have} but {sty} is missing")
    print(f"tenkz {have} at {DEST}")
    return DEST


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    git_url, rev = load_pin()
    fetch(git_url, rev)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
