#!/usr/bin/env python3
"""Exercise the print build's string-pool and node-memory budgets."""

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
    env.pop("main_memory", None)
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

        # Unlike pool_size, main_memory is fixed in the dumped XeTeX format.
        # A large zero-width rule list exceeds the stock node array without
        # depending on the size or content of the full blueprint.
        nodes = r"""\documentclass{article}
\begin{document}
\newcount\nodeindex
\setbox0=\hbox{\loop
  \vrule width0pt height1pt depth0pt
  \advance\nodeindex by1
\ifnum\nodeindex<1200000
\repeat}
\setbox0=\hbox{}
Blueprint PDF node-memory regression.
\end{document}
"""
        env.pop("pool_size")
        node_work = Path(tmp) / "nodes"
        enlarged = compile_fixture(node_work, nodes, env)
        assert enlarged.returncode == 0, enlarged.stdout
        node_log = (node_work / "capacity.log").read_text(encoding="utf-8")
        node_usage = re.search(r"(\d+) words of memory out of (\d+)", node_log)
        assert node_usage, "XeTeX did not report its node-memory usage"
        node_used, node_capacity = map(int, node_usage.groups())
        assert node_used > 5_000_000, (node_used, node_capacity)
        assert node_capacity == 20_000_000, (node_used, node_capacity)
        assert (node_work / "capacity.pdf").stat().st_size > 1000

        # An explicitly smaller budget must reach the format-generation
        # subprocess and reproduce the production error, not silently reuse
        # a larger persistent user/system format or success marker.
        env["main_memory"] = "5000000"
        stock_nodes = compile_fixture(Path(tmp) / "stock-nodes", nodes, env)
        assert stock_nodes.returncode != 0, "The stock node array unexpectedly sufficed"
        assert "TeX capacity exceeded" in stock_nodes.stdout, stock_nodes.stdout
        assert "main memory size=5000000" in stock_nodes.stdout, stock_nodes.stdout
    print(f"Blueprint PDF capacity passed: {used:,}/{capacity:,} string characters")
    print(f"Blueprint PDF capacity passed: {node_used:,}/{node_capacity:,} memory words")


if __name__ == "__main__":
    main()
