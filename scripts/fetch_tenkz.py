#!/usr/bin/env python3
"""Clone or update the tenkz companion pinned by ``tenkz.toml``."""

from __future__ import annotations

import argparse
import shutil
import subprocess
import sys
import tomllib
from pathlib import Path

REPO = Path(__file__).resolve().parents[1]
CONFIG = REPO / "tenkz.toml"
DEST = REPO / ".deps" / "tenkz"


def load_pin() -> tuple[str, str, str]:
    data = tomllib.loads(CONFIG.read_text(encoding="utf-8"))
    tenkz = data.get("tenkz")
    if not isinstance(tenkz, dict):
        raise SystemExit("tenkz.toml is missing a [tenkz] table")
    git = tenkz.get("git")
    rev = tenkz.get("rev")
    sha = tenkz.get("sha")
    if not isinstance(git, str) or not git:
        raise SystemExit("tenkz.toml [tenkz].git must be a nonempty string")
    if not isinstance(rev, str) or not rev:
        raise SystemExit("tenkz.toml [tenkz].rev must be a nonempty string")
    if not isinstance(sha, str) or len(sha) != 40:
        raise SystemExit("tenkz.toml [tenkz].sha must be a 40-character commit SHA")
    try:
        int(sha, 16)
    except ValueError:
        raise SystemExit("tenkz.toml [tenkz].sha must be hexadecimal") from None
    return git, rev, sha


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


def fetch(git_url: str, rev: str, sha: str) -> Path:
    DEST.parent.mkdir(parents=True, exist_ok=True)
    if not (DEST / ".git").is_dir():
        if DEST.exists():
            raise SystemExit(f"{DEST} exists and is not a git checkout")
        try:
            git(["clone", "--filter=blob:none", git_url, str(DEST)])
        except SystemExit:
            shutil.rmtree(DEST, ignore_errors=True)
            raise
    else:
        git(["remote", "set-url", "origin", git_url], cwd=DEST)
        git(["fetch", "--tags", "origin"], cwd=DEST)
    git(["fetch", "--depth=1", "origin", rev], cwd=DEST)
    resolved = git(["rev-parse", "FETCH_HEAD^{commit}"], cwd=DEST)
    if resolved != sha:
        raise SystemExit(f"tenkz pin {rev} resolved to {resolved}, expected {sha}")
    git(["checkout", "--detach", sha], cwd=DEST)
    have = git(["rev-parse", "HEAD"], cwd=DEST)
    if have != sha:
        raise SystemExit(f"tenkz HEAD {have} does not match immutable pin {sha}")
    sty = DEST / "tex" / "tenkz" / "tenkz.sty"
    if not sty.is_file():
        raise SystemExit(f"checked out tenkz at {have} but {sty} is missing")
    print(f"tenkz {have} at {DEST}")
    return DEST


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.parse_args()
    git_url, rev, sha = load_pin()
    fetch(git_url, rev, sha)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
