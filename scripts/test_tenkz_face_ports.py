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
\begin{tenkz}[physical=updown, trace=physical, tensor style=box]
  \tn[pill, wide=2, up at={1,2}, down at=center]{T} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnfuse[span=2, combined=west, west at={1,2}]{V}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, physical=updown, up at=center, down at={1,2}]{B}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[down at=center]{U} & \\
  \tn[pill, wide=2, up at={1,2}, down at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, physical=up]{B}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, box, east at=center]{X} & \tn{A}\\
  & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire, wire}]
  \tnfuse[span=3, west at=center, east at={1,3}]{V} & & \tn{A}\\
  & & \tn{A}\\
  & & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{K} & \\
  \tn[pill, wide=2, up at={1,2}]{B} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1}, down={$i$}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, up={$j$,$k$}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,1)}, tensor style=box]
  \tn[down at=center, down={$i$}]{U} & \\
  \tn[pill, wide=2, up at={1,2}, up={$j$,$k$}]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire}, tensor style=box]
  \tn[west at=center, east at=center]{X}
\end{tenkz}
\begin{tenkz}[rows={ket, bra}, trace={(physical,1)}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{K} & \\
  \tn[pill, wide=2, up at={1,2}]{B} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, open={(1,2)}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at={1}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tnskip & \tn{L}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={2}]{U} & \\
  \tnskip & \tn{L}
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tnskip & \tn{U}\\
  \tn[pill, wide=2, up at={1,2}]{L} &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn[pill, wide=2, down at={1,2}]{U} & \\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  & \tnfuse[span=2, west at=center, east at={1,2}]{V}\\
  \tn{A} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnX[wires=2, west at=center, east at=center]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={op, ket}, tensor style=box]
  \tn{U_1} & \tn{U_2}\\
  \tn[pill, wide=2, up at=center]{L} &
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tnfuse[span=2, west at={1,2}, east at=center]{V} & & \tn{A}\\
  & & \tn{A}
\end{tenkz}
\begin{tenkz}[rows={wire, wire}]
  \tn[wires=2, west at={1,2}, east at={3}]{X}\\
  &
\end{tenkz}
\begin{tenkz}[rows={ket, wire}, tensor style=box]
  \tn[no legs, up at=center, down at=center]{A}\\
  \tnX[up at=center, down at=center]{X}
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
    require(
        sparse_pairing,
        "boundary|picture=9|virtual-west=2|virtual-east=3|physical-up=0|physical-down=0",
        "neighboring port opposite an omitted sparse slot disappeared",
    )
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
    require(
        lower_sparse,
        "boundary|picture=12|virtual-west=1|virtual-east=1|physical-up=1|physical-down=1",
        "unmatched upper port disappeared from the boundary signature",
    )
    asymmetric_trace = pictures[13]
    require(asymmetric_trace,
            "warning|code=phtrace-face-ports|cell=1-1",
            "asymmetric physical trace was not rejected")
    forbid(asymmetric_trace,
           "phtrace|picture=13|row=1|col=1",
           "asymmetric physical trace emitted a centre-only loop")
    require(
        asymmetric_trace,
        "boundary|picture=13|virtual-west=1|virtual-east=1|physical-up=2|physical-down=1",
        "rejected physical trace did not leave its declared faces open",
    )
    compatibility_conflict = pictures[14]
    require(compatibility_conflict,
            "faceports|picture=14|cell=1-1|face=west|arity=2|at=1,2",
            "explicit split face did not override combined=")
    require(compatibility_conflict,
            "faceports|picture=14|cell=1-1|face=east|arity=2|at=rows",
            "opposite implicit split face acquired the wrong arity")
    require(
        compatibility_conflict,
        "boundary|picture=14|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "combined= conflict left a hidden centred stub",
    )
    brick_faces = pictures[15]
    require(brick_faces,
            "faceports|picture=15|cell=1-1|face=up|arity=1|at=center",
            "tall brick lost its centred physical face")
    require(brick_faces,
            "faceports|picture=15|cell=1-1|face=down|arity=2|at=1,2",
            "tall brick lost its split physical face")
    require(
        brick_faces,
        "boundary|picture=15|virtual-west=2|virtual-east=2|physical-up=1|physical-down=2",
        "tall brick physical signature disagrees with its declared faces",
    )
    lower_surplus = pictures[16]
    require(
        lower_surplus,
        "boundary|picture=16|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "surplus lower-face port disappeared from the boundary signature",
    )
    default_brick = pictures[17]
    require(
        default_brick,
        "faceports|picture=17|cell=1-1|face=up|arity=2|at=rows",
        "default tall-brick face record disagrees with its two drawn ports",
    )
    require(
        default_brick,
        "boundary|picture=17|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "face-port support changed the default tall-brick arity",
    )
    default_virtual = pictures[18]
    require(default_virtual,
            "faceports|picture=18|cell=1-1|face=west|arity=2|at=rows",
            "default tall glyph did not record its west split face")
    require(default_virtual,
            "faceports|picture=18|cell=1-1|face=east|arity=2|at=rows",
            "default tall glyph did not record its east split face")
    centred_virtual = pictures[19]
    require(centred_virtual,
            "bond|picture=19|row=1|from=1|to=2|dir=none|role=none|species=none",
            "centred virtual face did not meet row 1")
    require(centred_virtual,
            "bond|picture=19|row=2|from=1|to=2|dir=none|role=none|species=none",
            "centred virtual face did not meet every row of its span")
    hole = pictures[20]
    forbid(hole,
           "bond|picture=20|row=2|from=1|to=2|dir=none|role=none|species=none",
           "sparse virtual face acquired a port in its omitted row")
    pair_trace = pictures[21]
    require(pair_trace,
            "warning|code=pair-trace-face-ports|cell=1-1",
            "multi-port pair trace was not rejected")
    forbid(pair_trace,
           "pairtrace|picture=21|row=1|col=1",
           "multi-port pair trace emitted a misleading centre loop")
    if paired_ports(pair_trace) != [("1", "1"), ("2", "2")]:
        raise AssertionError("rejected pair trace did not retain both ordinary contractions")
    opened_wide = pictures[22]
    require(
        opened_wide,
        "boundary|picture=22|virtual-west=2|virtual-east=2|physical-up=3|physical-down=1",
        "opened wide interface omitted a surplus lower-face port",
    )
    opened_plain = pictures[23]
    require(
        opened_plain,
        "boundary|picture=23|virtual-west=2|virtual-east=2|physical-up=3|physical-down=1",
        "opened centred interface omitted a surplus lower-face port",
    )
    single_wire = pictures[24]
    require(single_wire,
            "faceports|picture=24|cell=1-1|face=west|arity=1|at=center",
            "single-wire centred west face was not recorded")
    require(single_wire,
            "faceports|picture=24|cell=1-1|face=east|arity=1|at=center",
            "single-wire centred east face was not recorded")
    forbid(single_wire,
           "warning|code=combined-wires|cell=1-1",
           "single-wire centred face was mistaken for combined=")
    physical_pair_trace = pictures[25]
    require(physical_pair_trace,
            "warning|code=pair-trace-face-ports|cell=1-1",
            "multi-port physical-column trace was not rejected")
    forbid(physical_pair_trace,
           "pairtrace|picture=25|row=1|col=1",
           "multi-port physical-column trace emitted a centre loop")
    if paired_ports(physical_pair_trace) != [("1", "1"), ("2", "2")]:
        raise AssertionError(
            "rejected physical-column trace did not retain ordinary contractions"
        )
    sparse_open = pictures[26]
    require(
        sparse_open,
        "boundary|picture=26|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "opened sparse lower face changed its exact-slot signature",
    )
    partial_skip = pictures[27]
    require(
        partial_skip,
        "boundary|picture=27|virtual-west=2|virtual-east=2|physical-up=1|physical-down=1",
        "one skipped column counted the whole upper face",
    )
    sparse_skip = pictures[28]
    require(
        sparse_skip,
        "boundary|picture=28|virtual-west=2|virtual-east=2|physical-up=1|physical-down=0",
        "a skipped column invented an absent sparse upper port",
    )
    lower_partial_skip = pictures[29]
    require(
        lower_partial_skip,
        "boundary|picture=29|virtual-west=2|virtual-east=2|physical-up=2|physical-down=0",
        "one skipped column counted the whole lower face",
    )
    upper_split_lower_center = pictures[30]
    if paired_ports(upper_split_lower_center) != [("1", "1")]:
        raise AssertionError("a centred lower face consumed multiple upper indices")
    require(
        upper_split_lower_center,
        "boundary|picture=30|virtual-west=2|virtual-east=2|physical-up=1|physical-down=1",
        "an unmatched upper port disappeared beside a centred lower face",
    )
    continuation_center = pictures[31]
    require(
        continuation_center,
        "bond|picture=31|row=2|from=1|to=2|dir=none|role=none|species=none",
        "continuation-row bond did not meet the centred fusion face",
    )
    require(
        continuation_center,
        "boundary|picture=31|virtual-west=1|virtual-east=2|physical-up=0|physical-down=0",
        "contracted centred fusion face was still counted as open",
    )
    two_centred_faces = pictures[32]
    require(
        two_centred_faces,
        "faceports|picture=32|cell=1-1|face=west|arity=1|at=center",
        "tall glyph lost its centred west face",
    )
    require(
        two_centred_faces,
        "faceports|picture=32|cell=1-1|face=east|arity=1|at=center",
        "tall glyph lost its independent centred east face",
    )
    require(
        two_centred_faces,
        "boundary|picture=32|virtual-west=1|virtual-east=1|physical-up=0|physical-down=0",
        "two centred virtual faces did not contribute independently",
    )
    separate_upper_cells = pictures[33]
    if paired_ports(separate_upper_cells) != [("center", "1")]:
        raise AssertionError("separate upper glyphs consumed one centred lower index twice")
    require(
        separate_upper_cells,
        "boundary|picture=33|virtual-west=2|virtual-east=2|physical-up=2|physical-down=1",
        "the surplus upper index beside a centred lower face disappeared",
    )
    distant_center = pictures[34]
    require(
        distant_center,
        "bond|picture=34|row=1|from=1|to=3|dir=none|role=none|species=none",
        "centred fusion face did not meet its distant row-1 neighbour",
    )
    require(
        distant_center,
        "boundary|picture=34|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "a distant bond left the centred fusion face counted as open",
    )
    invalid_slot = pictures[35]
    require(
        invalid_slot,
        "faceports|picture=35|cell=1-1|face=east|arity=0|at=none",
        "out-of-span virtual slot was not normalized away",
    )
    require(
        invalid_slot,
        "boundary|picture=35|virtual-west=2|virtual-east=0|physical-up=0|physical-down=0",
        "out-of-span virtual slot survived in the boundary signature",
    )
    suppressed_physical = pictures[36]
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=1-1|face=up|arity=1|at=center",
        "no-legs tensor emitted a physical upper face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=1-1|face=down|arity=1|at=center",
        "no-legs tensor emitted a physical lower face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=2-1|face=up|arity=1|at=center",
        "on-wire matrix emitted a physical upper face",
    )
    forbid(
        suppressed_physical,
        "faceports|picture=36|cell=2-1|face=down|arity=1|at=center",
        "on-wire matrix emitted a physical lower face",
    )
    require(
        suppressed_physical,
        "boundary|picture=36|virtual-west=2|virtual-east=2|physical-up=0|physical-down=0",
        "suppressed physical faces survived in the boundary signature",
    )
    print("PASS: physical faces, compatibility aliases, and virtual face arity")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
