#!/usr/bin/env python3
"""Check the PEPS assembly diagrams: dyadic routing, hole encoder, ket column.

The source checks recompute the anchors, the routed link, the fold, the
square samples and the closed input legs from the stated coordinates and
reject mutated sources. Use --source-only when TeX is unavailable; the default
also renders every picture through the production path and runs the tenkz
audit on its event stream.
"""

from __future__ import annotations

import argparse
from collections import Counter
from pathlib import Path
import re
import sys
import tempfile

from blueprint_tex_tree import read_tex_tree

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ROOT / "blueprint/src/chapter"
ROUTING = CHAPTERS / "ch24_peps_dyadic_routing.tex"
FRAMES = CHAPTERS / "ch24_peps_encoded_frames.tex"
KET = CHAPTERS / "ch24_peps_ket_column.tex"
# The displays live in shared figure files that the entries input; every check reads
# the expanded chapter, so it still asserts that the ink sits in its entry.
FIGURES = {
    ROUTING: ["figures/peps_dyadic_hv_routing"],
    FRAMES: ["figures/peps_frame_hole_encoder_a", "figures/peps_frame_hole_encoder_b"],
    KET: ["figures/peps_ket_column_square_fix_input"],
}

N, L = 8, 5
# Open indices promised by each picture's adjacent ink-to-index comment,
# in the order returned by check_sources().
BOUNDARIES = [Counter(), Counter(), Counter({"phys:w": 2, "phys:e": 1}),
              Counter({"phys:n": 9, "phys:s": 9}), Counter({"phys:n": 9})]


def entry(source: str, label: str) -> str:
    start = source.index(r"\label{" + label + "}")
    return source[start:source.index(r"\end{definition}", start)]


def units(text: str) -> list[str]:
    return re.findall(r"\\begin\{tenkz\}.*?\\end\{tenkz\}", text, re.S)


def anchor(j: int, r: int) -> int:
    return 2 ** j * r + 2 ** (j - 1) if j >= 1 else r


def fold(x: int) -> int:
    return x if x <= L - 1 else 2 * (L - 1) - x


def cell(x: int, y: int) -> tuple[int, int]:
    """Cell (row, column) of the padded point (x, y); y grows downward."""
    return (y + 1, x + 1)


def atoms(unit: str) -> dict[tuple[int, int], tuple[str, str]]:
    found = {}
    for options, body in re.findall(r"\\tn\[([^]]*)\]\{([^}]*)\}", unit, re.S):
        at = re.search(r"at=\((\d+),(\d+)\)", options)
        if not at:
            continue
        key = (int(at[1]), int(at[2]))
        assert key not in found, key
        skin = re.search(r"skin=(\w+)", options)
        species = re.search(r"species=([\w-]+)", options)
        found[key] = ((skin[1] if skin else "") + "/" + (species[1] if species else ""), body)
    return found


def check_routing(text: str) -> str:
    block = entry(text, "def:peps_dyadic_hv_routing")
    [unit] = units(block)
    assert "rows={ket,ket,ket,ket,ket,ket,ket,ket}, cols=8" in unit
    expected = {}
    for j, look in ((3, "box/"), (2, "ring/"), (1, "/scale-one")):
        coords = sorted({anchor(j, r) for r in range(N // 2 ** j)})
        assert all(0 <= a < N for a in coords)
        for x in coords:
            for y in coords:
                expected[cell(x, y)] = look
    found = atoms(unit)
    assert {k: v[0] for k, v in found.items()} == expected, "anchor scales"
    p, q = (anchor(2, 0), anchor(2, 0)), (anchor(1, 3), anchor(1, 2))
    assert found[cell(*p)][1] == "P" and found[cell(*q)][1] == "Q"
    corner = cell(q[0], p[1])  # horizontal on the row of P, then vertical
    wire = re.search(r"\\tnwire\[([^]]*)\]\{(\w+)\}\{(\w+)\}", unit, re.S)
    assert wire and wire[2] == "P" and wire[3] == "Q", "link orientation"
    # The link is a solid route; P and Q name its ends (no mid-wire arrowhead).
    assert "route=orth" in wire[1] and "stroke" not in wire[1]
    assert f"via={{({corner[0]},{corner[1]})}}" in wire[1], "horizontal-then-vertical corner"
    folded = cell(fold(q[0]), fold(q[1]))
    # f(Q) is a route ring on the folded cell, reached by a dashed fold string from Q.
    assert (f"\\tnmark[form=enclosure, species=route]{{({folded[0]},{folded[1]})}}{{}}"
            in unit), "fold of Q"
    fold_wire = re.search(r"\\tnwire\[([^]]*)\]\s*\{Q\}\{([^}]*)\}", unit, re.S)
    assert fold_wire and "stroke=dashed" in fold_wire[1], "dashed fold string"
    assert fold_wire[2] == f"0.5 e of ({folded[0]},{folded[1]})", "fold string ends at f(Q)"
    assert unit.count("{$f(Q)$}") == 1, "f(Q) named once"
    square = re.search(r"\\tnmark\[form=enclosure, species=(\w+)[^]]*\]\s*"
                       + re.escape(f"{{(1,1) .. ({L},{L})}}{{$L\\times L$}}"), unit)
    assert square, "genuine square"
    assert square[1] == "neutral", "the genuine square is context, not the selected set"
    # Separation of the drawn link fits c=3 times either block side.
    assert max(abs(q[0] - p[0]), abs(q[1] - p[1])) <= 3 * min(4, 2)
    return unit


def check_frames(text: str) -> list[str]:
    block = entry(text, "def:peps_frame_hole_encoder")
    found = units(block)
    assert len(found) == 2
    grid, encoder = found
    # Unit grid, centre c at cell (4,4), h = 3/2, r_j = 2: samples are the
    # sites within sup-distance h, r_j, 2h of the centre.
    h, rj, size, centre = 1.5, 2, 7, 4

    def sample(radius: float) -> str:
        cells = [k for k in range(1, size + 1) if abs(k - centre) <= radius]
        return f"{{({cells[0]},{cells[0]}) .. ({cells[-1]},{cells[-1]})}}"

    assert f"cols={size}" in grid and grid.count("ket") == size
    assert h <= rj <= 2 * h
    marks = re.findall(r"\\tnmark\[form=enclosure, species=(\w+)[^]]*\](\{[^}]*\})", grid)
    assert marks == [("selected", sample(h)), ("secondary", sample(rj)),
                     ("complement", sample(2 * h))], marks
    for label in ("$Q^-$", "$D_j$", "$Q^+$"):
        assert grid.count(label) == 1, label
    assert r"{(4,4)}{$c$}" in grid
    # Encoder, read right to left: one input on the east face, the tag above
    # the raw output on the west face. Each port is carried one pitch out by an
    # invisible end vertex whose outward port names the space.
    ports = re.search(r"ports=\{([^{}]*)\}\]\{K_\{c,h\}\}", encoder)
    assert ports, "encoder ports"
    faces = sorted(re.findall(r"(\d+@\d):physical", ports[1]))
    assert faces == ["0@2", "180@1", "180@2"], faces
    ends = {}
    for options in re.findall(r"\\tn\[([^]]*)\]\{\}", encoder):
        name = re.search(r"name=(\w+)", options)
        named = re.search(r"(\d+)(?:@\d)?:physical:\$(\\mathcal (?:H_\\Lambda|J_\{c,h\}))\$",
                          options)
        if name and named:
            ends[name[1]] = (named[1], named[2])
    legs = []
    for a, b in re.findall(r"\\tnwire\{(\w+\.[\d@]+)\}\{(\w+\.[\d@]+)\}", encoder):
        for mine, other in ((a, b), (b, a)):
            if mine.startswith("encK."):
                face = mine.split(".")[1]
                outward, space = ends[other.split(".")[0]]
                assert outward == face.split("@")[0], ("space name on the open side", face)
                legs.append((face, space))
    assert sorted(legs) == [("0@2", r"\mathcal H_\Lambda"), ("180@1", r"\mathcal J_{c,h}"),
                            ("180@2", r"\mathcal H_\Lambda")], legs
    return found


def check_ket(text: str) -> list[str]:
    block = entry(text, "def:peps_ket_column_square_fix_input")
    left, right = units(block)
    assert "rows={op,op,op}, cols=3, frame=plane" in left
    assert "physical=updown" in left and "bonds=none" not in left
    assert "rows={op,op,op}, cols=3," in right
    assert "frame={plane, basis={op at (0,0), ket at (1,-2)}}, bonds=none" in right
    assert "physical=" not in right, "physical contractions must be explicit"
    inputs = re.findall(r"at=\((\d),(\d),2\), skin=dot, species=input", right)
    assert sorted(inputs) == [(str(r), str(c)) for r in (1, 2, 3) for c in (1, 2, 3)], inputs
    # Only the input dot of the middle site of the right column is named |z_v>.
    assert not re.search(r"skin=dot, species=input[^]]*\]\{[^}]", right), "unlabelled dots"
    labels = re.findall(r"\\tnmark\[form=label, label pos=e\]\{\((\d),(\d),2\)\}"
                        r"\{\$\\ket\{z_v\}\$\}", right)
    assert labels == [("2", "3")], ("middle site of the right column", labels)
    assert right.count("z_v") == 1, "z_v named once"
    wires = re.findall(r"\\tnwire\{([^}]*)\}\{([^}]*)\}", right)
    assert len(re.findall(r"\\tnwire\b", right)) == len(wires), "every wire must be checked"
    expected = []
    for r in (1, 2, 3):
        for c in (1, 2, 3):
            site = f"({r},{c},1)"
            expected += [(site, f"({r},{c},2)"), (site, "open up")]
            if c < 3:
                expected.append((site, f"({r},{c + 1},1)"))
            if r < 3:
                expected.append((site, f"({r + 1},{c},1)"))
    assert Counter(tuple(sorted(w)) for w in wires) == Counter(tuple(sorted(w)) for w in expected), (
        "input contractions, outputs and original virtual grid")
    assert r"\tn[" not in left
    return [left, right]


def check_sources() -> list[str]:
    for chapter, figures in FIGURES.items():
        raw = chapter.read_text()
        for figure in figures:
            assert f"\\input{{{figure}}}" in raw, (chapter.name, figure)
    routing, frames, ket = read_tex_tree(ROUTING), read_tex_tree(FRAMES), read_tex_tree(KET)
    found = [check_routing(routing)] + check_frames(frames) + check_ket(ket)
    for source in (routing, frames, ket):
        for line in source.splitlines():
            assert not re.search(r"\\(?:draw|fill|node)\b|tikzpicture", line), line
    return found


def check_mutations() -> None:
    cases = [
        (ROUTING, check_routing, "via={(3,8)}", "via={(6,3)}"),
        (ROUTING, check_routing, "species=route]{(4,2)}{}", "species=route]{(4,8)}{}"),
        (ROUTING, check_routing, "{Q}{0.5 e of (4,2)}", "{Q}{0.5 e of (4,8)}"),
        (ROUTING, check_routing, "species=neutral, tint", "species=selected, tint"),
        (ROUTING, check_routing, r"\tn[at=(2,6), species=scale-one, size=l]{}", r"\tn[at=(2,6), skin=ring, size=l]{}"),
        (ROUTING, check_routing, "{(1,1) .. (5,5)}", "{(1,1) .. (6,6)}"),
        (FRAMES, check_frames, "{(2,2) .. (6,6)}{}", "{(3,3) .. (5,5)}{}"),
        (FRAMES, check_frames, "{encTag.0}{encK.180@1}", "{encTag.0}{encK.0@1}"),
        (FRAMES, check_frames, "{encTag.0}{encK.180@1}", "{encTag.0}{encK.180@2}"),
        (FRAMES, check_frames, r"\tnwire{encTag.0}{encK.180@1}" "\n"
         r"        \tnwire{encOut.0}{encK.180@2}",
         r"\tnwire{encTag.0}{encK.180@2}" "\n"
         r"        \tnwire{encOut.0}{encK.180@1}"),
        (KET, check_ket, "at=(3,3,2), skin=dot", "at=(3,3,1), skin=dot"),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,1,2)}", r"\tnwire{(1,1,1)}{open down}"),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,1,2)}", ""),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,1,2)}", r"\tnwire{(1,1,1)}{(1,2,2)}"),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,2,1)}", r"\tnwire{(1,1,1)}{(1,3,1)}"),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,2,1)}", r"\tnwire{(1,1,2)}{(1,2,1)}"),
        (KET, check_ket, r"\tnwire{(1,1,1)}{(1,2,1)}",
         r"\tnwire{(1,1,1)}{(1,2,1)}" "\n"
         r"        \tnwire[name=extra]{(1,1,1)}{open up}"),
    ]
    for path, check, old, new in cases:
        # Mutate the expanded text, i.e. the figure's ink as the entry sees it.
        text = read_tex_tree(path)
        assert old in text, old
        try:
            check(text.replace(old, new, 1))
        except (AssertionError, ValueError):
            continue
        raise AssertionError(("mutation accepted", old, new))
    ket = read_tex_tree(KET)
    labelled = r"label pos=e]{(2,3,2)}{$\ket{z_v}$}"
    assert labelled in ket
    moved = ket.replace(labelled, labelled.replace("(2,3,2)", "(2,2,2)"), 1)
    try:
        check_ket(moved)
    except AssertionError:
        pass
    else:
        raise AssertionError("moving z_v to the middle column was accepted")
    for signatures, expected in (
        ([], BOUNDARIES[0]),
        (["", ""], BOUNDARIES[0]),
        (["open:e"], BOUNDARIES[0]),
        (["phys:e, phys:e, phys:n"], BOUNDARIES[2]),
        ([", ".join(["phys:n"] * 9 + ["phys:s"] * 9)], BOUNDARIES[4]),
    ):
        try:
            check_boundary(signatures, expected)
        except AssertionError:
            continue
        raise AssertionError(("boundary mutation accepted", signatures, expected))


def check_boundary(signatures: list[str], expected: Counter[str]) -> None:
    assert len(signatures) == 1, ("one boundary event required", signatures)
    actual = Counter(s.strip() for s in signatures[0].split(",") if s.strip())
    assert actual == expected, ("open-index multiset", actual, expected)


def check_render(found: list[str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
    assert len(found) == len(BOUNDARIES), "one boundary specification per picture"
    for index, unit in enumerate(found):
        svg, _ = tenkz_pic.render_unit(unit, output)
        assert svg is not None and svg.is_file(), "production SVG rendering unavailable"
        assert "<path" in svg.read_text(), "SVG without ink"
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, "complete event stream required"
        source = output / f"peps-assembly-{index}.tex"
        source.write_text(unit + "\n")
        audit = Audit(log, source)
        audit.run()
        hard = [f for f in audit.findings if f.severity == "HARD"]
        assert not hard, hard
        signatures = [e.attrs["signature"] for e in audit.events()
                      if e.kind == "kernel-boundary"]
        check_boundary(signatures, BOUNDARIES[index])
        print(f"PASS: picture {index + 1}, audited SVG {svg}")
    # Exercise the boundary check on real production event streams as well.
    for name, unit, expected in (
        ("routing-extra-port", found[0].replace("skin=box", "skin=box, ports={0:virtual}", 1),
         BOUNDARIES[0]),
        ("ket-open-input", found[4].replace(r"\tnwire{(1,1,1)}{(1,1,2)}",
                                           r"\tnwire{(1,1,1)}{open down}", 1), BOUNDARIES[4]),
    ):
        log = tenkz_pic.unit_event_log(unit, output)
        assert log is not None, (name, "production mutation event stream required")
        signatures = re.findall(r"^kernel-boundary\|signature=(.*)$", log.read_text(), re.M)
        assert len(signatures) == 1, (name, "one production boundary event required", signatures)
        try:
            check_boundary(signatures, expected)
        except AssertionError:
            print(f"PASS: rejected rendered boundary mutation {name}")
        else:
            raise AssertionError(("rendered boundary mutation accepted", name))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    found = check_sources()
    check_mutations()
    print("PASS: anchors, routed link, fold, square samples, encoder legs, "
          "input contractions and label position, eighteen rejected source mutations, "
          "five rejected boundary mutations")
    if args.source_only:
        print("NOT RUN: SVG rendering and event-stream audit (--source-only)")
    elif args.output_dir:
        out = args.output_dir.resolve()
        out.mkdir(parents=True, exist_ok=True)
        check_render(found, out)
    else:
        with tempfile.TemporaryDirectory(prefix="tenkz_peps_assembly_") as tmp:
            check_render(found, Path(tmp).resolve())
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
