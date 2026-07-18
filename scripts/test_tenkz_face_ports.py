#!/usr/bin/env python3
"""Regression checks for asymmetric tenkz face ports.

The test compiles small pictures and reads their `.tnlog` contraction
records.  It guards the two failures from issue 4249: inventing a second open
port on the centred face, and dropping the second contraction on the declared
two-port face.  It also fixes the compatibility meaning of `legs at=`, the
virtual arity of default and sparse splitting endpoints, and exact-slot
resolution for ordinary tall glyphs and physical contractions.
"""

from __future__ import annotations

import os
import shutil
import subprocess
import tempfile
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

SOURCE = r"""
\documentclass{article}
\usepackage{tenkz}
\pagestyle{empty}
\begin{document}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at=center, down at={1,2}]{U^\dagger} & \\
  \tn{A} & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at={1,2}, down at=center]{U} & \\
  \tn[wide=2]{A} &
\end{tenkz}
\begin{tenkz}[physical=up, tensor style=box]
  \tn[pill, wide=2, legs at={1,2}]{U} &
\end{tenkz}
\begin{tenkz}[rows={ket:fused:nopair, wire:west none}]
  \tn[box]{B} & \tndots & \tn[box]{B} &
  \tnfuse[span=2, west at=center, east at={1,2}]{V}\\
  & & &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=3, up at=center, down at={1,2,3}]{W} & & \\
  \tn{A} & \tn{A} & \tn{A}
\end{tenkz}
\begin{tenkz}[physical=up, tensor style=box]
  \tn[pill, wide=2, legs at={1,2}, up at=center]{U} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}]
  \tnfuse[span=2]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V}\\
  &\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V} & \tn{A}\\
  & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, west at=center, east at={1,2}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, west at=center, east at={1,2}]{X} & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={op:none, ket}, tensor style=box]
  \tn[pill, wide=2, up at=center, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at={1}, down at=center]{L} &
\end{tenkz}
\end{document}
"""


def events_by_picture(lines: list[str]) -> dict[int, list[str]]:
    pictures: dict[int, list[str]] = {}
    current = 0
    for line in lines:
        if line.startswith("picture|"):
            current = int(dict(field.split("=", 1) for field in line.split("|")[1:])["id"])
            pictures[current] = []
        elif current:
            pictures[current].append(line)
    return pictures


def require(lines: list[str], expected: str, message: str) -> None:
    if expected not in lines:
        raise AssertionError(f"{message}: missing {expected!r}")


def forbid(lines: list[str], forbidden: str, message: str) -> None:
    if forbidden in lines:
        raise AssertionError(f"{message}: found {forbidden!r}")


def paired_ports(lines: list[str]) -> list[tuple[str, str]]:
    result: list[tuple[str, str]] = []
    for line in lines:
        if not line.startswith("pairleg|"):
            continue
        attrs = dict(field.split("=", 1) for field in line.split("|")[1:])
        result.append((attrs["upper-port"], attrs["column"]))
    return sorted(result)


def main() -> int:
    engine = shutil.which("xelatex")
    if engine is None:
        print("FAIL: xelatex is required")
        return 1
    with tempfile.TemporaryDirectory(prefix="tenkz_face_ports_") as tmp:
        work = Path(tmp)
        tex = work / "face-ports.tex"
        tex.write_text(SOURCE, encoding="utf-8")
        env = os.environ.copy()
        env["TEXINPUTS"] = f"{ROOT / 'tex/tenkz'}//:" + env.get("TEXINPUTS", "")
        run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=work,
            env=env,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if run.returncode:
            print(run.stdout)
            print("FAIL: face-port fixture did not compile")
            return 1
        pictures = events_by_picture(
            (work / "face-ports.tnlog").read_text(encoding="utf-8").splitlines()
        )

    inverse = pictures[1]
    require(
        inverse,
        "boundary|picture=1|virtual-west=1|virtual-east=1|physical-up=1|physical-down=0",
        "centred upper face acquired a spurious port",
    )
    if paired_ports(inverse) != [("1", "1"), ("2", "2")]:
        raise AssertionError("two-port lower face did not contract ports 1 and 2 distinctly")

    forward = pictures[2]
    if paired_ports(forward) != [("center", "1")]:
        raise AssertionError("centred lower face did not emit one contraction")

    legacy = pictures[3]
    require(legacy, "faceports|picture=3|cell=1-1|face=up|arity=2|at=1,2",
            "legacy upper-face arity changed")
    require(legacy, "faceports|picture=3|cell=1-1|face=down|arity=2|at=1,2",
            "legacy lower-face arity changed")

    zipper = pictures[4]
    require(zipper, "faceports|picture=4|cell=1-4|face=west|arity=1|at=center",
            "zipper fused-face arity changed")
    require(zipper, "faceports|picture=4|cell=1-4|face=east|arity=2|at=1,2",
            "zipper split-face arity changed")
    require(
        zipper,
        "boundary|picture=4|virtual-west=1|virtual-east=2|physical-up=2|physical-down=0",
        "zipper boundary signature changed",
    )
    arity_three = pictures[5]
    require(arity_three,
            "faceports|picture=5|cell=1-1|face=down|arity=3|at=1,2,3",
            "three-port face arity changed")
    if paired_ports(arity_three) != [("1", "1"), ("2", "2"), ("3", "3")]:
        raise AssertionError("three-port face did not contract ports 1, 2, and 3 distinctly")
    override = pictures[6]
    require(override, "faceports|picture=6|cell=1-1|face=up|arity=1|at=center",
            "explicit face did not override legacy alias")
    require(override, "faceports|picture=6|cell=1-1|face=down|arity=2|at=1,2",
            "legacy alias stopped supplying the other face")
    default_fuse = pictures[7]
    require(default_fuse, "faceports|picture=7|cell=1-1|face=west|arity=1|at=center",
            "bare fuse did not emit its centred face")
    require(default_fuse, "faceports|picture=7|cell=1-1|face=east|arity=2|at=rows",
            "bare fuse did not emit its separate span face")
    require(
        default_fuse,
        "boundary|picture=7|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "bare fuse boundary disagrees with its two face events",
    )
    sparse = pictures[8]
    require(sparse, "faceports|picture=8|cell=1-1|face=east|arity=2|at=1,3",
            "sparse face event lost its declared slots")
    require(
        sparse,
        "boundary|picture=8|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "sparse boundary did not count exactly its declared row slots",
    )
    sparse_pairing = pictures[9]
    require(sparse_pairing,
            "bond|picture=9|row=1|from=1|to=2|dir=none|role=none|species=none",
            "sparse face did not contract declared row slot 1")
    require(sparse_pairing,
            "bond|picture=9|row=3|from=1|to=2|dir=none|role=none|species=none",
            "sparse face did not contract declared row slot 3")
    forbid(sparse_pairing,
           "bond|picture=9|row=2|from=1|to=2|dir=none|role=none|species=none",
           "sparse face contracted undeclared row slot 2")
    tall = pictures[10]
    require(tall, "faceports|picture=10|cell=1-1|face=west|arity=1|at=center",
            "tall glyph lost its centred west face")
    require(tall, "faceports|picture=10|cell=1-1|face=east|arity=2|at=1,2",
            "tall glyph lost its separate east face")
    require(
        tall,
        "boundary|picture=10|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "tall glyph boundary disagrees with its declared faces",
    )
    tall_pairing = pictures[11]
    require(tall_pairing,
            "bond|picture=11|row=1|from=1|to=2|dir=none|role=none|species=none",
            "tall glyph did not contract east slot 1")
    require(tall_pairing,
            "bond|picture=11|row=2|from=1|to=2|dir=none|role=none|species=none",
            "tall glyph did not contract east slot 2")
    lower_sparse = pictures[12]
    if paired_ports(lower_sparse) != [("1", "1")]:
        raise AssertionError("wide contraction ignored the lower face's exact slots")
    print("PASS: physical faces, compatibility aliases, and virtual face arity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
