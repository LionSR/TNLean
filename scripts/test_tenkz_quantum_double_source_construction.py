#!/usr/bin/env python3
"""Regress Section 7's checkerboard, controlled loops and two distinct blockings.

The source oracle is Papers/1001.3807/paper_v3.tex, Section 7, and its figs6
artwork. Check geometric supports and typed graph incidences, then exercise
noncommuting S3 and exhaustive binary fixtures. The fixtures are regressions,
not general proofs. --no-render needs only Python's standard library.
Otherwise render seven equation units (eight pictures) separately and combine
with the three local-term pictures using the actual blueprint print preamble,
checking boundary events and Audit.
"""
from __future__ import annotations

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import itertools
import os
from pathlib import Path
import re
import subprocess
import tempfile

from tenkz_paths import ensure_pythonpath, tenkz_tex

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "blueprint/src"
CONSTRUCTION = SOURCE / "chapter/ch24_peps_quantum_double_source_construction.tex"
CHECKERBOARD = SOURCE / "chapter/ch24_peps_kitaev_checkerboard_blocking.tex"
DIRECTIONS = {"n": (-1, 0), "e": (0, 1), "s": (1, 0), "w": (0, -1),
              "ne": (-1, 1), "nw": (-1, -1), "se": (1, 1), "sw": (1, -1)}
CORNERS = ("NW", "NE", "SE", "SW")


def uncomment(text):
    return re.sub(r"(?<!\\)%[^\n]*", "", text)


def compact(text):
    return re.sub(r"\s+", "", uncomment(text))


def group(text, start, left="{", right="}"):
    while text[start].isspace():
        start += 1
    assert text[start] == left, f"expected {left}: {text[start:start+60]}"
    level = 1
    end = start + 1
    while level:
        assert end < len(text), "unterminated TeX group"
        if text[end] == left:
            level += 1
        elif text[end] == right:
            level -= 1
        end += 1
    return text[start + 1:end - 1], end


def split_options(text):
    parts, depth, start = [], 0, 0
    for i, char in enumerate(text):
        if char in "{([":
            depth += 1
        elif char in "})]":
            depth -= 1
        elif char == "," and depth == 0:
            parts.append(text[start:i].strip())
            start = i + 1
    assert depth == 0
    parts.append(text[start:].strip())
    return parts


def commands(text, command, nargs):
    text = uncomment(text)
    for found in re.finditer(r"\\" + command + r"(?![A-Za-z])", text):
        pos = found.end()
        while text[pos].isspace():
            pos += 1
        options = {}
        if text[pos] == "[":
            raw, pos = group(text, pos, "[", "]")
            for item in split_options(raw):
                key, _, value = item.partition("=")
                assert key not in options, f"duplicate option {key}"
                options[key.strip()] = value.strip()
        args = []
        for _ in range(nargs):
            arg, pos = group(text, pos)
            args.append(arg.strip())
        yield options, args


@dataclass
class Atom:
    glyph: str
    ports: dict
    at: str
    skin: str


@dataclass
class Picture:
    atoms: dict
    wires: dict
    marks: list

    def endpoints(self):
        used = set()
        for options, first, second in self.wires.values():
            for endpoint in (first, second):
                match = re.fullmatch(r"(\w+)\.(\d+)", endpoint)
                if match:
                    name, angle = match[1], int(match[2])
                    assert name in self.atoms and angle in self.atoms[name].ports
                    assert (name, angle) not in used, f"port reused: {endpoint}"
                    used.add((name, angle))
            if "." in first and "." in second and not " of " in second:
                n1, a1 = first.split(".")
                n2, a2 = second.split(".")
                assert self.atoms[n1].ports[int(a1)][0] == self.atoms[n2].ports[int(a2)][0]
        return used

    def boundary(self):
        used = self.endpoints()
        result = Counter(port[0] for name, atom in self.atoms.items()
                         for angle, port in atom.ports.items() if (name, angle) not in used)
        for _, first, second in self.wires.values():
            if second.startswith("open "):
                name, angle = first.split(".")
                result[self.atoms[name].ports[int(angle)][0]] += 1
        return result

    def signature(self):
        used = self.endpoints()
        bearings = {0: "e", 90: "n", 180: "w", 270: "s"}
        entries = [("phys" if kind == "physical" else "open") + ":" +
                   bearings.get(angle, str(angle))
                   for name, atom in self.atoms.items() for angle, (kind, _) in atom.ports.items()
                   if (name, angle) not in used]
        for opts, first, second in self.wires.values():
            if second.startswith("open "):
                name, angle = first.split(".")
                kind = self.atoms[name].ports[int(angle)][0]
                entries.append(("phys" if kind == "physical" else "open") + ":" +
                               second.removeprefix("open ") + ":" + opts["dir"])
        return ", ".join(sorted(entries))


def parse_picture(text):
    text = uncomment(text)
    atoms, wires = {}, {}
    for opts, (glyph,) in commands(text, "tn", 1):
        name = opts["name"]
        assert name not in atoms
        ports = {}
        if "ports" in opts:
            for raw in split_options(opts["ports"][1:-1]):
                angle, kind, *label = raw.split(":", 2)
                assert int(angle) not in ports and kind in ("physical", "virtual")
                ports[int(angle)] = (kind, label[0] if label else "")
        atoms[name] = Atom(glyph, ports, opts["at"], opts.get("skin", ""))
    for opts, (first, second) in commands(text, "tnwire", 2):
        name = opts["name"]
        assert name not in wires
        wires[name] = (opts, first, second)
    return Picture(atoms, wires, list(commands(text, "tnmark", 2)))


def equations(source):
    return re.findall(r"\\begin\{tenkzequation\}(.*?)\\end\{tenkzequation\}", source, re.S)


def pictures(source):
    return [parse_picture(body) for body in re.findall(
        r"\\begin\{tenkz\}.*?\](.*?)\\end\{tenkz\}", source, re.S)]


def coordinate(raw, positions):
    match = re.fullmatch(r"\((\d+),\s*(\d+)\)", raw)
    if match:
        return (int(match[1]), int(match[2]))
    match = re.fullmatch(r"([\d.]+) ([nesw]+) of (\w+)", raw)
    assert match, f"unrecognized placement {raw}"
    dr, dc = DIRECTIONS[match[2]]
    r, c = positions[match[3]]
    return (r + float(match[1]) * dr, c + float(match[1]) * dc)


def positions(picture):
    result = {}
    for name, atom in picture.atoms.items():
        result[name] = coordinate(atom.at, result)
    return result


def support(center, points):
    r, c = center
    return {name for name, (x, y) in points.items() if abs(x-r) == abs(y-c) == 1}


def check_lattice(original, blocked):
    for prefix, pic in (("cb", original), ("bk", blocked)):
        expected = {f"{prefix}{r}{c}": (2*r+1, 2*c+1)
                    for r in range(4) for c in range(4)}
        assert positions(pic) == expected, "physical 4 by 4 grid changed"
        assert all(a.skin == "dot" and not a.glyph and not a.ports for a in pic.atoms.values())
        assert pic.boundary() == Counter(), "incidence rails must not create tensor indices"
        rails = {(a, b) for opts, a, b in pic.wires.values() if opts.get("stroke") == "dotted"}
        expected_rails = {(f"{prefix}{r}{c}", f"{prefix}{r}{c+1}")
                          for r in range(4) for c in range(3)} | {
                          (f"{prefix}{r}{c}", f"{prefix}{r+1}{c}")
                          for r in range(3) for c in range(4)}
        assert rails == expected_rails
        assert len(pic.wires) == 40, "24 adjacency rails and 16 spin arrows required"
        for r, c in itertools.product(range(4), repeat=2):
            opts, start, end = pic.wires[f"{prefix}Arrow{r}{c}"]
            assert opts.get("kind") == "string" and opts.get("dir") == "to"
            assert start == f"{prefix}{r}{c}"
            direction = (("sw", "nw"), ("se", "ne"))[r % 2][c % 2]
            dr, dc = DIRECTIONS[direction]
            if prefix == "bk":
                dr, dc = -dr, -dc
            a, b = coordinate(end, expected)
            x, y = expected[start]
            assert abs(a-x-0.7*dr) < 1e-9 and abs(b-y-0.7*dc) < 1e-9, \
                "spin arrow direction changed"
    labels = {coordinate(where, {}): label for opts, (where, label) in original.marks
              if opts.get("form") == "label"}
    assert labels == {(2*r+2, 2*c+2): "A" if (r+c) % 2 == 0 else "B"
                      for r in range(3) for c in range(3)}, "A/B checkerboard changed"
    centers = {"NW": (2, 2), "NE": (2, 6), "SE": (6, 6), "SW": (6, 2)}
    pts = positions(blocked)
    blocks = {}
    for opts, (where, label) in blocked.marks:
        if opts.get("form") == "enclosure":
            corner = opts["name"].removeprefix("block")
            assert where.startswith("{") and where.endswith("}"), "explicit node enclosure required"
            selected = set(split_options(where[1:-1]))
            assert selected == support(centers[corner], pts), "wrong spin in A block"
            blocks[corner] = selected
    assert set(blocks) == set(CORNERS)
    assert set.union(*blocks.values()) == set(pts)
    assert sum(map(len, blocks.values())) == 16, "A blocks overlap"
    expected_labels = {center: f"K_{{{corner}}}:A" for corner, center in centers.items()}
    expected_labels.update({(4, 4): r"A_\square", (2, 4): "B_h", (6, 4): "B_h",
                            (4, 2): "B_v", (4, 6): "B_v"})
    actual_labels = {coordinate(where, {}): label for opts, (where, label) in blocked.marks
                     if opts.get("form") == "label"}
    assert actual_labels == expected_labels, "blocked hole or bond placement changed"
    hole = support((4, 4), pts)
    assert hole == {"bk11", "bk12", "bk22", "bk21"}
    assert all(len(hole & block) == 1 for block in blocks.values())
    # Derive the physical coordinates from positions inside each selected block.
    spin_names = {}
    for corner, (r, c) in centers.items():
        for dr, dc, spin in ((-1, 1, "a"), (1, 1, "b"), (1, -1, "c"), (-1, -1, "d")):
            name = next(n for n, point in pts.items() if point == (r+dr, c+dc))
            spin_names[name] = (corner, spin)
    assert {spin_names[n] for n in support((2, 4), pts)} == {
        ("NW", "a"), ("NW", "b"), ("NE", "c"), ("NE", "d")}
    assert {spin_names[n] for n in support((4, 2), pts)} == {
        ("NW", "b"), ("NW", "c"), ("SW", "a"), ("SW", "d")}
    # The stack represents bk11, southeast of the NW A block. Its NE B
    # color r is acted on by L; the SW B color s is acted on by R. The
    # opposite original cb11 arrow swaps those actions before inversion.
    def arrow_action(pic, site, center):
        pts = positions(pic)
        _, start, end = pic.wires[site[:2] + "Arrow11"]
        assert start == site
        row, col = pts[site]
        arrow_row, arrow_col = coordinate(end, pts)
        toward = (arrow_row-row)*(center[0]-row) + (arrow_col-col)*(center[1]-col)
        assert toward != 0
        return "R" if toward > 0 else "L"
    assert arrow_action(blocked, "bk11", (2, 4)) == "L"
    assert arrow_action(blocked, "bk11", (4, 2)) == "R"
    assert arrow_action(original, "cb11", (2, 4)) == "R"
    assert arrow_action(original, "cb11", (4, 2)) == "L"
    # Counterclockwise around the hole, starting at its northwest corner.
    assert [spin_names[next(n for n, point in pts.items() if point == xy)]
            for xy in ((3, 3), (5, 3), (5, 5), (3, 5))] == [
                ("NW", "b"), ("SW", "a"), ("SE", "d"), ("NE", "c")]


def port(kind, label=""):
    return (kind, f"${label}$" if label else "")


def check_ports(pic, name, glyph, virtual, physical):
    expected = {angle: port("virtual", label) for angle, label in virtual.items()}
    expected.update({angle: port("physical", label) for angle, label in physical.items()})
    assert pic.atoms[name].glyph == glyph and pic.atoms[name].ports == expected, \
        f"wrong tensor or typed port: {name}"


def check_wires(pic, expected, directed=False):
    assert {name: (a, b) for name, (_, a, b) in pic.wires.items()} == expected
    assert all(opts.get("dir", "none") == (
        directed[name] if isinstance(directed, dict) else "to" if directed else "none")
               for name, (opts, _, _) in pic.wires.items())
    pic.endpoints()


def check_tensor_graphs(pics):
    _, _, loop, stack, tensor, source, block, zero = pics
    for picture, prefix in ((loop, "loop"), (block, "blockT")):
        pts = positions(picture)
        rows = sorted({r for r, _ in pts.values()})
        cols = sorted({c for _, c in pts.values()})
        assert len(rows) == len(cols) == 2
        assert [pts[prefix + corner] for corner in CORNERS] == [
            (rows[0], cols[0]), (rows[0], cols[1]), (rows[1], cols[1]), (rows[1], cols[0])], \
            "tensor assigned to the wrong geometric corner"
    stack_pts = positions(stack)
    assert stack_pts["stackL"][0] < stack_pts["stackR"][0] < stack_pts["stackOne"][0]
    assert len({c for _, c in stack_pts.values()}) == 1
    assert set(loop.atoms) == {"loop" + corner for corner in CORNERS}
    for corner, virt, phys in (
        ("NW", (0, 270), {90: "o_1", 180: "i_1"}),
        ("NE", (180, 270), {90: "o_2", 0: "i_2"}),
        ("SE", (90, 180), {0: "o_3", 270: "i_3"}),
        ("SW", (0, 90), {180: "o_4", 270: "i_4"}),
    ):
        check_ports(loop, "loop" + corner, "P", dict.fromkeys(virt, ""), phys)
    check_wires(loop, {"loopN": ("loopNW.0", "loopNE.180"),
                       "loopE": ("loopNE.270", "loopSE.90"),
                       "loopS": ("loopSE.180", "loopSW.0"),
                       "loopW": ("loopSW.90", "loopNW.270")}, True)
    assert [args for _, args in loop.marks] == [["on loopN 0.5", "$s$"]]
    # Equality of the two virtual legs at each P gives one connected control component.
    neighbors = {n: set() for n in loop.atoms}
    for _, first, second in loop.wires.values():
        a, b = first.split(".")[0], second.split(".")[0]
        neighbors[a].add(b)
        neighbors[b].add(a)
    reached, todo = set(), ["loopNW"]
    while todo:
        name = todo.pop()
        if name not in reached:
            reached.add(name)
            todo.extend(neighbors[name] - reached)
    assert reached == set(loop.atoms) and all(len(v) == 2 for v in neighbors.values())
    assert loop.boundary() == Counter(physical=8)
    assert set(stack.atoms) == {"stackL", "stackR", "stackOne"}
    check_ports(stack, "stackL", "P^L", {135: "", 45: ""}, {90: "rs^{-1}", 270: ""})
    check_ports(stack, "stackR", "P^R", {225: "", 315: ""}, {90: "", 270: ""})
    check_ports(stack, "stackOne", r"\ket1", {}, {90: ""})
    stack_wires = {"stackMiddle": ("stackR.90", "stackL.270"),
                   "stackInput": ("stackOne.90", "stackR.270"),
                   "stackLIn": ("stackL.135", "open nw"),
                   "stackLOut": ("stackL.45", "open ne"),
                   "stackRIn": ("stackR.225", "open sw"),
                   "stackROut": ("stackR.315", "open se")}
    check_wires(stack, stack_wires, {n: "from" if n in ("stackLIn", "stackRIn") else "to"
                                    for n in stack_wires})
    assert {where: label for _, (where, label) in stack.marks} == {
        "on stackLIn 0.5": "$r$", "on stackLOut 0.5": "$r$",
        "on stackRIn 0.5": "$s$", "on stackROut 0.5": "$s$"}
    assert set(tensor.atoms) == {"stackT"}
    check_ports(tensor, "stackT", "T", dict.fromkeys((90, 0, 270, 180), ""), {135: "rs^{-1}"})
    check_wires(tensor, {"stackTNorth": ("stackT.90", "open n"),
                         "stackTEast": ("stackT.0", "open e"),
                         "stackTSouth": ("stackT.270", "open s"),
                         "stackTWest": ("stackT.180", "open w")},
                {"stackTNorth": "from", "stackTEast": "to", "stackTSouth": "to", "stackTWest": "from"})
    assert {where: label for _, (where, label) in tensor.marks} == {
        "on stackTNorth 0.5": "$r$", "on stackTEast 0.5": "$r$",
        "on stackTSouth 0.5": "$s$", "on stackTWest 0.5": "$s$"}
    assert stack.boundary() == tensor.boundary() == Counter(virtual=4, physical=1)
    assert set(source.atoms) == {"sourceK", "sourceLN", "sourceLE", "sourceLS", "sourceLW"}
    assert not zero.wires
    source_wires = {"sourceK" + direction: (f"sourceK.{angle}", "open " + direction)
                    for direction, angle in (("n", 90), ("e", 0), ("s", 270), ("w", 180))}
    source_wires.update({f"sourceL{side}{direction}": (f"sourceL{side}.{angle}", "open " + direction)
                         for side, direction, angle in (("N", "n", 90), ("E", "e", 0),
                                                        ("S", "s", 270), ("W", "w", 180))})
    check_wires(source, source_wires, {name: "to" if name in ("sourceKe", "sourceKs") else "from"
                                      for name in source_wires})
    check_ports(source, "sourceK", "K", dict.fromkeys((90, 0, 270, 180), ""), {135: r"\mathcal H_K"})
    for side, angle, physical_angle in (("N", 90, 0), ("E", 0, 90), ("S", 270, 0), ("W", 180, 270)):
        check_ports(source, "sourceL" + side, "L_" + side, {angle: ""},
                    {physical_angle: rf"\mathcal H_{{L_{side}}}"})
        check_ports(zero, "zero" + side, r"\bra0", {angle: "a_" + side}, {})
    assert set(zero.atoms) == {"zeroK", "zeroN", "zeroE", "zeroS", "zeroW"}
    check_ports(zero, "zeroK", "K", {90: "p", 0: "q", 270: "r", 180: "s"}, {135: r"\sigma"})
    assert source.boundary() == Counter(virtual=8, physical=5)
    assert zero.boundary() == Counter(virtual=8, physical=1)
    assert set(block.atoms) == {"blockT" + corner for corner in CORNERS}
    for corner, glyph, virtual, physical in (
        ("NW", "T_0", {90: "N_0", 0: "", 270: "", 180: "W_1"}, {135: r"\sigma_3"}),
        ("NE", "T_1", {90: "N_1", 0: "E_0", 270: "", 180: ""}, {45: r"\sigma_0"}),
        ("SE", "T_0", {90: "", 0: "E_1", 270: "S_0", 180: ""}, {315: r"\sigma_1"}),
        ("SW", "T_1", {90: "", 0: "", 270: "S_1", 180: "W_0"}, {225: r"\sigma_2"}),
    ):
        check_ports(block, "blockT" + corner, glyph, virtual, physical)
    check_wires(block, {"blockX0": ("blockTNW.0", "blockTNE.180"),
                        "blockX1": ("blockTNE.270", "blockTSE.90"),
                        "blockX2": ("blockTSE.180", "blockTSW.0"),
                        "blockX3": ("blockTSW.90", "blockTNW.270")})
    assert {where: label for _, (where, label) in block.marks if where.startswith("on ")} == {
        f"on blockX{i} 0.5": f"$x_{i}$" for i in range(4)}
    assert block.boundary() == Counter(virtual=8, physical=4)


def words(text):
    tokens = re.findall(r"([a-z])(?:\^\{(-1)\})?", text)
    assert "".join(name + ("^{-1}" if inverse else "") for name, inverse in tokens) == text
    return tuple((name, bool(inverse)) for name, inverse in tokens)


def check_formulas(source, checkerboard):
    src, binary = compact(source), compact(checkerboard)
    expected = [r"L_u\ketg=\ket{ug}", r"R_u\ketg=\ket{gu^{-1}}",
                r"J\ketg=\ket{g^{-1}}", "JL_uJ=R_u", "JR_uJ=L_u", "abcd=1",
                r"\sigma_{NW,b}\sigma_{SW,a}\sigma_{SE,d}\sigma_{NE,c}=1",
                r"\Pi_B=|G|^{-1}\sum_{u\inG}V_u", r"\Pi_B=|G|^{-1}\sum_uV_u",
                r"h_B=I-\Pi_B", r"h_A=\tfrac12(I-Z^{\otimes4})",
                r"h_B=\tfrac12(I-X^{\otimes4})", r"\Pi_B=\tfrac12(I+X^{\otimes4})",
                r"P=\sum_{s,k}U_s\ket{k}_{\rmout}\bra{k}_{\rmin}\otimes\ket{s}_v\bra{s}_v",
                r"\operatorname{Loop}(P)&=\sum_{s\inG}U_s^{NW}\otimesU_s^{NE}\otimesU_s^{SE}\otimesU_s^{SW}=|G|\Pi_B",
                r"L_rR_s=R_sL_r", r"\mathsfB\mathsfC=\mathsfKE^\dagger",
                r"\ket{a,b}\mapsto\ket{a,a+b}", r"\ket{a,b}\mapsto\ket{a,b^{-1}a}"]
    for formula in expected:
        assert formula in src, f"missing or changed source formula: {formula}"
    assert r"\lean{" not in src and r"\leanok" not in src, "source picture adds a formalization claim"
    assert "southeastspinofablockedAplaquette" in src
    assert "thissamespinis$sr^{-1}$;applying$J$gives$rs^{-1}$" in src
    original = re.search(r"are\$\(([^()]*)\)\$", src)
    clockwise = re.search(r"\(a,b,c,d\)=\(([^()]*)\)", src)
    assert original and clockwise
    original_words = tuple(words(word) for word in original[1].split(","))
    clockwise_words = tuple(words(word) for word in clockwise[1].split(","))
    actions = {}
    for axis in ("h", "v"):
        match = re.search(r"V_u\^" + axis + r"&:\(a,b,c,d;e,f,g,h\)\\longmapsto\(([^()]*)\)", src)
        assert match, f"missing {axis} bond action"
        actions[axis] = tuple(words(word) for word in match[1].replace(";", ",").split(","))
        assert len(actions[axis]) == 8
    # Pairing data is parsed from the displayed T formulas, then evaluated below.
    pairings = {}
    for orientation in (0, 1):
        match = re.search(r"T_" + str(orientation) + r"\(t,r,d,l;k\)&=([^&]*?)(?:,&|\.)", binary)
        assert match, "elementary T formula missing"
        deltas = re.findall(r"\\delta_\{([a-z]),([a-z](?:\+[a-z])?)\}", match[1])
        assert len(deltas) == 3
        pairings[orientation] = deltas
    assert pairings == {0: [("t", "r"), ("d", "l"), ("k", "t+d")],
                        1: [("t", "l"), ("d", "r"), ("k", "t+d")]}
    for formula in (r"T_0(N_0,x_0,x_3,W_1;\sigma_3)", r"T_1(N_1,E_0,x_1,x_0;\sigma_0)",
                    r"T_0(x_1,E_1,S_0,x_2;\sigma_1)", r"T_1(x_3,x_2,S_1,W_0;\sigma_2)",
                    r"E\ket{p,q,r,s}=\ket{(p,0),(q,0),(r,0),(s,0)}",
                    r"\mathsfB\mathsfC=\mathsfKE^\dagger"):
        assert formula in binary, f"coefficient identity changed: {formula}"
    return original_words, clockwise_words, actions, pairings


def check_source(source, checkerboard):
    assert len(equations(source)) == 5 and len(equations(checkerboard)) == 2
    pics = pictures(source + checkerboard)
    assert len(pics) == 8
    check_lattice(*pics[:2])
    check_tensor_graphs(pics)
    data = check_formulas(source, checkerboard)
    return pics, data


def check_s3(data):
    original, clockwise, actions, _ = data
    group_elements = tuple(itertools.permutations(range(3)))
    one = (0, 1, 2)
    mul = lambda p, q: tuple(p[q[i]] for i in range(3))
    inv = lambda p: tuple(p.index(i) for i in range(3))

    def product(values):
        result = one
        for value in values:
            result = mul(result, value)
        return result

    def evaluate(word, values):
        return product(inv(values[n]) if negative else values[n] for n, negative in word)

    def spins(colors):
        values = dict(zip("pqrs", colors))
        return tuple(evaluate(word, values) for word in clockwise)

    def apply(axis, u, pair):
        values = dict(zip("abcdefgh", pair[0] + pair[1])) | {"u": u}
        result = tuple(evaluate(word, values) for word in actions[axis])
        return (result[:4], result[4:])

    assert any(mul(a, b) != mul(b, a) for a in group_elements for b in group_elements)
    wrong_order_detected = False
    for colors in itertools.product(group_elements, repeat=4):
        values = dict(zip("pqrs", colors))
        a = spins(colors)
        assert tuple(inv(evaluate(word, values)) for word in original) == a
        assert product(a) == one
        wrong_order_detected |= product((a[1], a[0], a[2], a[3])) != one
    assert wrong_order_detected, "S3 fixture must distinguish noncommuting order"
    for u, g in itertools.product(group_elements, repeat=2):
        assert inv(mul(u, inv(g))) == mul(g, inv(u))  # J L_u J = R_u
        assert inv(mul(inv(g), inv(u))) == mul(u, g)  # J R_u J = L_u
        for r in group_elements:
            assert mul(r, mul(g, inv(u))) == mul(mul(r, g), inv(u))
            assert mul(r, inv(u)) == mul(r, mul(one, inv(u)))
    # The general-group RG pair map is a permutation; order is significant.
    pair_images = {(a, mul(inv(b), a)) for a, b in itertools.product(group_elements, repeat=2)}
    assert len(pair_images) == len(group_elements)**2
    for a, b in itertools.product(group_elements, repeat=2):
        assert mul(a, inv(mul(inv(b), a))) == b
    # Explicit closed P-loop: equality on four virtual bonds leaves exactly
    # one control sum. Use alternating L/R actions of the original B plaquette.
    seed = tuple(group_elements[i] for i in (1, 2, 4, 5))
    def loop_output(controls):
        return tuple(mul(u, k) if i % 2 == 0 else mul(k, inv(u))
                     for i, (u, k) in enumerate(zip(controls, seed)))
    closed_loop = Counter(loop_output(control) for control in itertools.product(group_elements, repeat=4)
                          if all(control[i] == control[(i+1) % 4] for i in range(4)))
    single_sum = Counter(loop_output((u,)*4) for u in group_elements)
    assert closed_loop == single_sum and sum(closed_loop.values()) == len(group_elements)
    assert Counter(loop_output(control) for control in itertools.product(group_elements, repeat=4)) != single_sum
    # Explicit two-P physical contraction. The two virtual copies at each
    # P must agree; the intermediate physical index is the only free sum.
    for r_in, r_out, s_in, s_out in itertools.product(group_elements, repeat=4):
        output = Counter()
        for middle in group_elements:
            if s_in == s_out and middle == mul(one, inv(s_in)) and r_in == r_out:
                output[mul(r_in, middle)] += 1
        expected = Counter({mul(r_in, inv(s_in)): 1}) if r_in == r_out and s_in == s_out else Counter()
        assert output == expected
        assert inv(mul(s_in, inv(r_in))) == mul(r_in, inv(s_in))
    # Nontrivial exterior labels; all colors and acting group elements occur.
    for shift, step in itertools.product(range(6), repeat=2):
        p, q, r, s, t, v, w = [group_elements[(shift+i*step) % 6] for i in range(7)]
        for axis in ("h", "v"):
            make = (lambda x: (spins((p, x, r, s)), spins((t, v, w, x)))) if axis == "h" else (
                lambda x: (spins((p, q, x, s)), spins((x, t, v, w))))
            contraction = Counter(make(x) for x in group_elements)
            for u, x in itertools.product(group_elements, repeat=2):
                assert apply(axis, u, make(x)) == make(mul(u, x)), f"wrong {axis} shared-color action"
                for v0 in group_elements:
                    assert apply(axis, u, apply(axis, v0, make(x))) == apply(axis, mul(u, v0), make(x))
            for u in group_elements:
                assert Counter({apply(axis, u, pair): n for pair, n in contraction.items()}) == contraction
    for x, y, z, w in itertools.product(group_elements, repeat=4):
        nw, ne = spins((one, x, y, one)), spins((one, one, w, x))
        se, sw = spins((w, one, one, z)), spins((y, z, one, one))
        assert product((nw[1], sw[0], se[3], ne[2])) == one
    # Sparse exact averaging on an ambient basis vector, not just flat K outputs.
    seed = ((group_elements[1], group_elements[2], one, group_elements[4]),
            (one, group_elements[3], group_elements[5], group_elements[1]))
    for axis in ("h", "v"):
        def average(vector, scale):
            result = Counter()
            for pair, coefficient in vector.items():
                for u in group_elements:
                    result[apply(axis, u, pair)] += coefficient * scale
            return result
        projected = average({seed: Fraction(1)}, Fraction(1, 6))
        assert average(projected, Fraction(1, 6)) == projected
        unnormalized = average({seed: Fraction(1)}, Fraction(1))
        assert average(unnormalized, Fraction(1)) != unnormalized


def check_binary(picture, pairings):
    """Evaluate the drawn four-tensor graph, including all 4096 boundary/spin cases."""
    ports = {}
    for name, atom in picture.atoms.items():
        ports[name] = {angle: label.strip("$") for angle, (_, label) in atom.ports.items()}
    for i, (_, first, second) in enumerate(picture.wires.values()):
        for endpoint in (first, second):
            name, angle = endpoint.split(".")
            ports[name][int(angle)] = f"x_{i}"

    def elementary(orientation, indices):
        values = dict(zip("trdlk", indices))
        return all(values[left] == sum(values[v] for v in right.split("+")) % 2
                   for left, right in pairings[orientation])

    boundary_names = tuple(f"{side}_{i}" for side in "NESW" for i in range(2))
    for boundary in itertools.product((0, 1), repeat=8):
        values = dict(zip(boundary_names, boundary))
        actual = Counter()
        for internal in itertools.product((0, 1), repeat=4):
            env = values | {f"x_{i}": x for i, x in enumerate(internal)}
            spins, valid = {}, True
            for name, atom in picture.atoms.items():
                leg = [env[ports[name][a]] for a in (90, 0, 270, 180)]
                k = leg[0] ^ leg[2]
                valid &= elementary(int(atom.glyph[-1]), leg + [k])
                physical_label = next(label for angle, label in ports[name].items()
                                      if atom.ports[angle][0] == "physical")
                spins[int(physical_label[-1])] = k
            if valid:
                actual[tuple(spins[i] for i in range(4))] += 1
        colors = boundary[::2]
        expected_spin = tuple(colors[i] ^ colors[(i+1) % 4] for i in range(4))
        expected = Counter({expected_spin: 1}) if boundary[::2] == boundary[1::2] else Counter()
        assert actual == expected, "drawn checkerboard fails the coefficient identity"
        # C is involutive and BC vanishes exactly when any residual bit is one.
        transformed = tuple(x for a, b in zip(boundary[::2], boundary[1::2]) for x in (a, a ^ b))
        assert tuple(x for a, b in zip(transformed[::2], transformed[1::2]) for x in (a, a ^ b)) == boundary
        assert (transformed[::2] == transformed[1::2]) == (not any(boundary[1::2]))
    # Direct basis checks of C (X tensor X) C = X tensor I and
    # C (Z tensor Z) C = I tensor Z, with C = C inverse.
    for a, b in itertools.product((0, 1), repeat=2):
        first, second = a, a ^ b
        assert (first ^ 1, (first ^ 1) ^ (second ^ 1)) == (a ^ 1, b)
        assert (-1)**(first + second) == (-1)**b
    # Exact binary Pauli projectors and the one-control P loop (not four sums).
    for basis in itertools.product((0, 1), repeat=4):
        flip = tuple(1-x for x in basis)
        projector = {basis: Fraction(1, 2), flip: Fraction(1, 2)}
        square = Counter()
        loop = Counter(tuple(x ^ s for x in basis) for s in (0, 1))
        for state, weight in projector.items():
            square[state] += weight / 2
            square[tuple(1-x for x in state)] += weight / 2
        assert square == projector and loop == Counter({state: 2*v for state, v in projector.items()})
        a_penalty = Fraction(1 - (-1)**sum(basis), 2)
        assert a_penalty in (0, 1) and a_penalty**2 == a_penalty


def check_mutations(source, checkerboard):
    cases = [
        ("source arrow reversal", 0, "0.7 sw of cb00", "0.7 ne of cb00"),
        ("blocked arrow not inverted", 0, "0.7 ne of bk00", "0.7 sw of bk00"),
        ("A/B swap", 0, "{(2,2)}{A}", "{(2,2)}{B}"),
        ("wrong A support node", 0, "{bk00,bk01,bk10,bk11}", "{bk00,bk01,bk10,bk12}"),
        ("hole at wrong corner", 0, r"{(4,4)}{A_\square}", r"{(4,6)}{A_\square}"),
        ("wrong bond orientation", 0, "{(2,4)}{B_h}", "{(2,4)}{B_v}"),
        ("noncommutative multiplication order", 0, "au^{-1},ub", "u^{-1}a,ub"),
        ("vertical multiplication order", 0, "bu^{-1},uc", "u^{-1}b,uc"),
        ("hole product order", 0, r"\sigma_{NW,b}\sigma_{SW,a}", r"\sigma_{SW,a}\sigma_{NW,b}"),
        ("inversion L/R confusion", 0, "JL_uJ=R_u", "JL_uJ=L_u"),
        ("group-average normalization", 0, r"|G|^{-1}\sum_{u\in G}V_u", r"\sum_{u\in G}V_u"),
        ("Pauli normalization", 0, r"h_A=\tfrac12", "h_A="),
        ("independent P controls", 0, r"\ket{s}_v\bra{s}_v", r"\ket{s}_v\bra{t}_v"),
        ("wrong P loop port", 0, "{loopNE.180}", "{loopNE.0}"),
        ("wrong P stack port", 0, "{stackL.270}", "{stackL.135}"),
        ("wrong stack T pairing", 0, "{on stackTEast 0.5}{$r$}", "{on stackTEast 0.5}{$s$}"),
        ("wrong open T direction", 0, "name=stackTNorth,dir=from", "name=stackTNorth,dir=to"),
        ("wrong L virtual direction", 0, "name=sourceLNn,dir=from", "name=sourceLNn,dir=to"),
        ("stack anchored to wrong spin", 0, "southeast spin of a blocked", "northwest spin of a blocked"),
        ("physical L erased", 0, r"0:physical:$\mathcal H_{L_N}$", r"0:virtual:$\mathcal H_{L_N}$"),
        ("zero covector given physical output", 1, "90:virtual:$a_N$", "90:physical:$a_N$"),
        ("checkerboard T orientation", 1, r"135:physical:$\sigma_3$}]{T_0}", r"135:physical:$\sigma_3$}]{T_1}"),
        ("checkerboard internal corner", 1, "{blockTSE.90}", "{blockTSE.0}"),
        ("checkerboard geometric corner", 1, "at=3 s of blockTNW", "at=3 n of blockTNW"),
        ("binary orientation equation", 1, r"\delta_{t,l}\delta_{d,r}", r"\delta_{t,r}\delta_{d,l}"),
    ]
    for name, which, old, new in cases:
        changed = [source, checkerboard]
        assert old in changed[which], f"mutation anchor absent: {name}"
        changed[which] = changed[which].replace(old, new, 1)
        try:
            pics, data = check_source(*changed)
            # Formula mutations must fail the actual nonabelian interpretation too.
            if "multiplication order" in name:
                check_s3(data)
        except (AssertionError, KeyError, ValueError):
            continue
        raise AssertionError(f"incorrect semantic mutation accepted: {name}")
    return len(cases)


def render(work, source, checkerboard, pics, *, only_combined=False):
    ensure_pythonpath()
    from tenkz_audit import Audit

    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:{SOURCE}//:" + env.get("TEXINPUTS", "")
    preamble = (SOURCE / "print.tex").read_text().split(r"\providecommand", 1)[0]
    cases, at = [], 0
    for i, body in enumerate(equations(source) + equations(checkerboard)):
        count = len(pictures(body))
        unit = r"\begin{tenkzequation}" + body + r"\end{tenkzequation}"
        cases.append((f"qd-source-equation-{i+1}", unit, [p.signature() for p in pics[at:at+count]]))
        at += count
    # Include the real referenced definition, not a fake label or a suppressed warning.
    chapter = (SOURCE / "chapter/ch24_peps_examples.tex").read_text()
    definition = next(block for block in re.findall(r"\\begin\{definition\}.*?\\end\{definition\}", chapter, re.S)
                      if r"\label{def:peps_quantum_double_dual}" in block)
    # Omit only this context definition's invisible dependency annotation:
    # its G-injectivity definition lies outside the source-construction packet.
    definition = re.sub(r"\\uses\{[^}]*\}", "", definition)
    local = (SOURCE / "chapter/ch24_peps_quantum_double_local_terms.tex").read_text()
    local_pics = pictures(local)
    assert len(local_pics) == 3
    combined_pics = pics[:6] + local_pics + pics[6:]
    cases.append(("qd-source-combined", r"\chapter{Quantum-double source construction}" +
                  definition + source + local + checkerboard, [p.signature() for p in combined_pics]))
    bibliography = r"""
\begin{thebibliography}{3}
\bibitem{Schuch2010PEPS} N. Schuch, J. I. Cirac and D. P\'erez-Garc\'ia.
PEPS as ground states: degeneracy and topology. arXiv:1001.3807v3.
\bibitem{Cirac2021Matrix} J. I. Cirac, D. P\'erez-Garc\'ia, N. Schuch and F. Verstraete.
Matrix product states and projected entangled pair states: concepts, symmetries, and theorems.
Rev. Mod. Phys. 93, 045003 (2021).
\bibitem{gap:rmp_peps_quantum_double_g_isometry} The TNLean contributors.
Quantum-Double PEPS: Normalization, Representations and Scope. Paper-gap note (2026).
\url{https://sirui-lu.com/TNLean/paper-gaps/rmp_peps_quantum_double_g_isometry.pdf}.
\end{thebibliography}
\end{document}
"""
    for stem, body, signatures in cases:
        if only_combined and stem != "qd-source-combined":
            continue
        tex = work / f"{stem}.tex"
        tex.write_text(preamble + "\n\\begin{document}\n" + body + bibliography)
        for _ in range(2):
            run = subprocess.run(["xelatex", "-halt-on-error", "-interaction=nonstopmode", tex.name],
                                 cwd=work, env=env, capture_output=True, text=True, timeout=120)
            assert run.returncode == 0, f"{stem}: {run.stdout[-5000:]}"
        assert "Overfull" not in run.stdout, f"{stem}: overfull box"
        assert "undefined" not in run.stdout, f"{stem}: unresolved reference"
        log = work / f"{stem}.tnlog"
        events = log.read_text()
        actual = re.findall(r"^kernel-boundary\|signature=(.*)$", events, re.M)
        assert actual == signatures, f"{stem}: boundary mismatch {actual} != {signatures}"
        audit = Audit(log, tex)
        audit.parse_log()
        audit.link_tex()
        for check in ("check_empty_pictures", "check_dialects", "check_kernel_crossings",
                      "check_kernel_checks", "check_bbox_coverage", "check_label_overlaps",
                      "check_equation_groups", "check_equation_boundaries"):
            getattr(audit, check)()
        assert not audit.findings, [(f.severity, f.rule, f.msg) for f in audit.findings]
        subprocess.run(["pdftoppm", "-png", "-scale-to", "1200", f"{stem}.pdf", stem],
                       cwd=work, check=True, capture_output=True, timeout=120)
        print(f"PASS: {stem}: {len(signatures)} boundary signatures; no audit findings", flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--no-render", action="store_true")
    args = parser.parse_args()
    source, checkerboard = CONSTRUCTION.read_text(), CHECKERBOARD.read_text()
    pics, data = check_source(source, checkerboard)
    check_s3(data)
    check_binary(pics[6], data[3])
    rejected = check_mutations(source, checkerboard)
    print(f"PASS: grid/arrow/support/typed-graph semantics; {rejected} negative mutations; "
          "S3 inversion, ordered holonomy, horizontal/vertical shared-color actions and averaging; "
          "exhaustive Z2 boundary contraction/CNOT and Pauli fixtures (not proofs)", flush=True)
    if not args.no_render:
        if args.output_dir:
            args.output_dir.mkdir(parents=True, exist_ok=True)
            render(args.output_dir.resolve(), source, checkerboard, pics)
        else:
            with tempfile.TemporaryDirectory(prefix="qd-source-construction-") as tmp:
                render(Path(tmp), source, checkerboard, pics)


if __name__ == "__main__":
    main()
