#!/usr/bin/env python3
"""Exercise the print build's string-pool budget without rendering the volume."""

from __future__ import annotations

import os
import re
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LATEXMKRC = ROOT / "blueprint/src/latexmkrc"


def compile_fixture(
    work: Path, source: str, env: dict[str, str]
) -> subprocess.CompletedProcess[str]:
    work.mkdir()
    (work / "capacity.tex").write_text(source, encoding="utf-8")
    return subprocess.run(
        ["latexmk", "-norc", "-r", str(LATEXMKRC),
         "-interaction=nonstopmode", "-halt-on-error", "capacity.tex"],
        cwd=work, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=120,
    )


def main() -> None:
    # XeTeX retains generated control-sequence names in its string pool. A
    # short loop reproduces the cumulative pressure of the full volume's
    # TikZ/Tenkz pictures, exceeding TeX Live's 6,250,000-character default.
    prefix = "tnleanBlueprintStringPoolRegression" * 8
    source = rf"""\documentclass{{article}}
\begin{{document}}
\newcount\poolindex
\loop
  \expandafter\def\csname {prefix}\the\poolindex\endcsname{{}}
  \advance\poolindex by 1
\ifnum\poolindex<28000
\repeat
Blueprint PDF capacity regression.
\end{{document}}
"""
    env = os.environ.copy()
    env.pop("pool_size", None)
    with tempfile.TemporaryDirectory(prefix="blueprint-pdf-capacity-") as tmp:
        work = Path(tmp) / "configured"
        run = compile_fixture(work, source, env)
        if run.returncode:
            raise AssertionError(run.stdout)
        log = (work / "capacity.log").read_text(encoding="utf-8")
        usage = re.search(r"(\d+) string characters out of (\d+)", log)
        assert usage, "XeTeX did not report its string-pool usage"
        used, capacity = map(int, usage.groups())
        assert used > 6_250_000, (used, capacity)
        assert capacity > used, (used, capacity)
        assert (work / "capacity.pdf").stat().st_size > 1000

        # Reproduce the original failure at the stock budget. This also
        # proves that the rc preserves an explicit caller override.
        env["pool_size"] = "6250000"
        baseline = compile_fixture(Path(tmp) / "stock", source, env)
        assert baseline.returncode != 0, "The stock pool unexpectedly sufficed"
        assert "TeX capacity exceeded" in baseline.stdout, baseline.stdout
        assert "pool size=" in baseline.stdout, baseline.stdout
    print(f"Blueprint PDF capacity passed: {used:,}/{capacity:,} string characters")


if __name__ == "__main__":
    main()
