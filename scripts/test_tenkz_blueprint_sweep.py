#!/usr/bin/env python3
"""Focused regressions for the blueprint sweep's unit selection.

The sweep decides what one audited compile is.  Getting that wrong is not a
wrong answer but a missing question: a display split into panels leaves every
equation unchecked, and a nested picture cut at its inner `\\end` compiles a
fragment.
"""

import sys
import tempfile
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

from tenkz_blueprint_sweep import scan_units


SOURCES = {
    "display.tex": (
        "\\begin{tenkzequation}\n"
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n"
        "$ = $\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkzequation}\n"
    ),
    "scope.tex": (
        "\\begin{tenkzeq}[check={signature}]\n"
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n=\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end{tenkzeq}\n"
    ),
    "nested.tex": (
        "\\begin{tenkz}\\tngroup{\\begin{tenkz}\\tn{I}\\end{tenkz}}\\end{tenkz}\n"
    ),
    "commented.tex": (
        "% \\begin{tenkz}\\tn{dead}\\end{tenkz}\n"
        "\\begin{tenkz}\\tn{live}\\end{tenkz}\n"
    ),
    "spaced.tex": (
        "\\begin {tenkzequation}\n"
        "\\begin{tenkz}\\tn{A}\\end{tenkz}\n"
        "$ = $\n"
        "\\begin{tenkz}\\tn{B}\\end{tenkz}\n"
        "\\end {tenkzequation}\n"
    ),
    "prose_row.tex": (
        "\\begin{tenkzequation}\n$a = b$\n\\end{tenkzequation}\n"
    ),
}


def main() -> int:
    with tempfile.TemporaryDirectory(prefix="tenkz_sweep_units_") as tmp:
        root = Path(tmp)
        for name, text in SOURCES.items():
            (root / name).write_text(text, encoding="utf-8")
        units = {unit.path.name: unit for unit in scan_units(root)}
        names = [unit.path.name for unit in scan_units(root)]

    # A display is one unit holding both its panels, not two units.
    assert names.count("display.tex") == 1, names
    assert units["display.tex"].display
    assert units["display.tex"].source.count("\\begin{tenkz}") == 2

    # A `tenkzeq` display keeps its environment: the scope is what the hard
    # rules read, and dropping it would drop the check records with it.
    assert units["scope.tex"].source.startswith("\\begin{tenkzeq}")
    assert "check={signature}" in units["scope.tex"].source

    # A presentational row contributes its body, whose macro a standalone
    # compile does not have.
    assert not units["display.tex"].source.startswith("\\begin{tenkzequation}")

    # A nested picture belongs to its parent's unit, and the parent is not cut
    # short at the inner `\end`.
    assert names.count("nested.tex") == 1, names
    assert units["nested.tex"].source.count("\\begin{tenkz}") == 2
    assert units["nested.tex"].source.endswith("\\end{tenkz}")

    # A commented-out picture draws nothing and owns no unit.
    assert names.count("commented.tex") == 1, names
    assert "dead" not in units["commented.tex"].source

    # A row with no picture writes no event stream.
    assert "prose_row.tex" not in units, names

    # TeX reads the space after a control word as part of it, so a spaced
    # wrapper opens the same environment and keeps its panels together.
    assert names.count("spaced.tex") == 1, names
    assert units["spaced.tex"].display
    assert units["spaced.tex"].source.count("\\begin{tenkz}") == 2

    print(f"tenkz-blueprint-sweep-units: {len(names)} unit(s) over "
          f"{len(SOURCES)} source(s) selected as expected")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
