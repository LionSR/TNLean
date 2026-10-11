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
from pathlib import Path
import re
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = ROOT / "blueprint/src/chapter"
ROUTING = CHAPTERS / "ch24_peps_dyadic_routing.tex"
FRAMES = CHAPTERS / "ch24_peps_encoded_frames.tex"
KET = CHAPTERS / "ch24_peps_ket_column.tex"

N, L = 8, 5


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
    assert "route=orth" in wire[1] and "dir=to" in wire[1]
    assert f"via={{({corner[0]},{corner[1]})}}" in wire[1], "horizontal-then-vertical corner"
    folded = cell(fold(q[0]), fold(q[1]))
    assert f"{{({folded[0]},{folded[1]})}}{{$f(Q)$}}" in unit, "fold of Q"
    assert f"{{(1,1) .. ({L},{L})}}{{$L\\times L$}}" in unit, "genuine square"
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
    ports = re.search(r"ports=\{([^}]*(?:\}[^}]*)*?)\}\]\{K_\{c,h\}\}", encoder, re.S)
    assert ports, "encoder ports"
    legs = re.findall(r"(\d+)@\d:physical:\$(\\mathcal [HJ])", ports[1])
    assert sorted(legs) == [("0", r"\mathcal H"), ("0", r"\mathcal J"), ("180", r"\mathcal H")], legs
    return found


def check_ket(text: str) -> list[str]:
    block = entry(text, "def:peps_ket_column_square_fix_input")
    left, right = units(block)
    for unit in (left, right):
        assert "rows={op,op,op}, cols=3, frame=plane" in unit
        assert "physical=updown" in unit
        assert "bonds=none" not in unit, "bonds must be unchanged"
    legs = re.findall(r"at=on leg-s-(\d)-(\d) 1, skin=dot, species=input", right)
    assert sorted(legs) == [(str(r), str(c)) for r in (1, 2, 3) for c in (1, 2, 3)], legs
    assert "leg-n-" not in right, "output legs stay open"
    assert r"\tn[" not in left
    return [left, right]


def check_sources() -> list[str]:
    routing, frames, ket = ROUTING.read_text(), FRAMES.read_text(), KET.read_text()
    found = [check_routing(routing)] + check_frames(frames) + check_ket(ket)
    for source in (routing, frames, ket):
        for line in source.splitlines():
            assert not re.search(r"\\(?:draw|fill|node)\b|tikzpicture", line), line
    return found


def check_mutations() -> None:
    cases = [
        (ROUTING, check_routing, "via={(3,8)}", "via={(6,3)}"),
        (ROUTING, check_routing, "{(4,2)}{$f(Q)$}", "{(4,8)}{$f(Q)$}"),
        (ROUTING, check_routing, r"\tn[at=(2,6), species=scale-one]{}", r"\tn[at=(2,6), skin=ring]{}"),
        (ROUTING, check_routing, "{(1,1) .. (5,5)}", "{(1,1) .. (6,6)}"),
        (FRAMES, check_frames, "{(2,2) .. (6,6)}{}", "{(3,3) .. (5,5)}{}"),
        (FRAMES, check_frames, r"0@1:physical:$\mathcal J", r"180@1:physical:$\mathcal J"),
        (KET, check_ket, "at=on leg-s-3-3 1", "at=on leg-n-3-3 1"),
    ]
    for path, check, old, new in cases:
        text = path.read_text()
        assert old in text, old
        try:
            check(text.replace(old, new, 1))
        except (AssertionError, ValueError):
            continue
        raise AssertionError(("mutation accepted", old, new))


def check_render(found: list[str], output: Path) -> None:
    from tenkz_paths import ensure_pythonpath

    ensure_pythonpath()
    from tenkz_audit import Audit

    sys.path.insert(0, str(ROOT / "blueprint/src/Packages"))
    import tenkz_pic

    tenkz_pic._CACHE_DIR = output / "cache"
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
        print(f"PASS: picture {index + 1}, audited SVG {svg}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-only", action="store_true")
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    found = check_sources()
    check_mutations()
    print("PASS: anchors, routed link, fold, square samples, encoder legs, "
          "closed input legs, seven rejected mutations")
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
