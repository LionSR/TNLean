#!/usr/bin/env python3
"""Check actual mixed-normality diagrams and exact, mutation-sensitive coefficients.

Default: native production-wrapper/signature audits and rational fixtures.
--web-root checks real strict web output; --browser additionally requires the
existing desktop/mobile MathJax gate. Browser failures are never skipped.
Finite fixtures are regression evidence, not substitutes for Lean proofs.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import tempfile
from fractions import Fraction as Q
from html.parser import HTMLParser
from itertools import product
from pathlib import Path

from tenkz_paths import ensure_pythonpath, tenkz_tex

ensure_pythonpath()
from tenkz_audit import Audit  # noqa: E402
from test_tenkz_mixed_action import add, endpoint, ident, scale, zeros  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_mixed_normality.tex"
WIRES = {
    "RECOVERY": [("va.0", "wb.180"), ("wb.0", "rect.180"),
                 ("rect.0", "vc.180"), ("vc.0", "wd.180")],
    "SANDWICH": [("left.0", "cross.180"), ("cross.0", "right.180")],
}
EXPECTED = [("open:e, open:w", 5, 6), ("open:e, open:w", 1, 2),
            ("open:e, open:w", 3, 4), ("open:e, open:w", 1, 2)]
OPEN_LABELS = [["i", "j"], ["i", "j"]]


def bodies(source: str | None = None) -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8") if source is None else source
    assert r"\begin{tikzpicture}" not in source
    result = []
    for name, expected in WIRES.items():
        begin, end = [f"% TENKZ-MIXED-NORMALITY-{name}-{edge}"
                      for edge in ("BEGIN", "END")]
        assert source.count(begin) == source.count(end) == 1
        body = source.split(begin, 1)[1].split(end, 1)[0]
        assert body.count(r"\begin{tenkzequation}") == 1
        assert body.count(r"\begin{tenkz}") == 2
        assert re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body) == expected
        assert r"\dagger" not in body and r"\overline" not in body
        result.append(body)
    tokens = [r"{V_{0,\nu}}", r"{W_{0,\mu}}", r"{X}",
              r"{V_{1,\mu}}", r"{W_{1,\nu}}"]
    positions = [result[0].index(token) for token in tokens]
    assert positions == sorted(positions)
    assert r"$\displaystyle\sum_{\mu=0}^{m-1}$" in result[0]
    assert r"$=C_{uv}$" in result[1]
    for token in (r"{E_{au}}", r"{C}", r"{E_{vb}}", r"{E_{ab}}"):
        assert result[1].count(token) == 1, token
    for block in result:
        assert block.count(r"180:virtual:$i$") == 2
        assert block.count(r"0:virtual:$j$") == 2
    return result


def source_mutations() -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8")
    changes = {
        "recovery_endpoint": (r"{V_{1,\mu}}", r"{V_{0,\mu}}"),
        "recovery_multiplicity": (r"{W_{1,\nu}}", r"{W_{1,\mu}}"),
        "recovery_wire": (r"\tnwire{rect.0}{vc.180}", r"\tnwire{rect.0}{wd.180}"),
        "open_index": (r"180:virtual:$i$", r"180:virtual:$j$"),
        "sandwich_coefficient": (r"$=C_{uv}$", r"$=$"),
        "sandwich_index": (r"{E_{vb}}", r"{E_{ub}}"),
        "invented_adjoint": (r"{V_{1,\mu}}", r"{V_{1,\mu}^{\dagger}}"),
    }
    for name, (old, new) in changes.items():
        assert old in source
        try:
            bodies(source.replace(old, new, 1))
        except (AssertionError, ValueError):
            continue
        raise AssertionError(f"source mutation escaped: {name}")
    return list(changes)


def native_check(output: Path) -> dict[str, object]:
    engine = shutil.which("xelatex")
    assert engine, "xelatex is required"
    macros = (ROOT / "blueprint/src/macros/print.tex").read_text(encoding="utf-8")
    wrapper = re.search(r"\\newenvironment\{tenkzequation\}[^\n]+", macros)
    assert wrapper, "production print wrapper missing"
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    results = {}
    for mode in ("wrapper", "signature"):
        body = "\n".join(bodies())
        if mode == "signature":
            body = body.replace(r"\begin{tenkzequation}", r"\begin{tenkzeq}[check={signature}]")
            body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
            # Check complete mathematical ink in wrapper mode. Native equality
            # mode omits coefficient text so it compares the same open legs.
            body = body.replace(r"$\displaystyle\sum_{\mu=0}^{m-1}$", "")
            body = body.replace(r"$=C_{uv}$", "=")
            body = body.replace("$=$", "=")
        source = ("\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
                  "\\usepackage{tenkz}\n\\pagestyle{empty}\n" + wrapper.group(0)
                  + "\n\\begin{document}\n" + body + "\n\\end{document}\n")
        tex = output / f"mixed-normality-{mode}.tex"
        tex.write_text(source, encoding="utf-8")
        run = subprocess.run([engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
                             cwd=output, env=env, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, check=False)
        (output / f"{mode}-stdout.log").write_text(run.stdout, encoding="utf-8")
        assert run.returncode == 0, run.stdout[-8000:]
        audit = Audit(tex.with_suffix(".tnlog"), tex)
        audit.run()
        hard = [str(f) for f in audit.findings if f.severity == "HARD"]
        assert not hard, hard
        panels, atoms, wires, labels = [], [], [], []
        for event in audit.events():
            if event.kind == "atom":
                atoms.append(event)
            elif event.kind == "wire":
                wires.append(event)
            elif event.kind == "kernel-boundary":
                panels.append((event.attrs["signature"], len(atoms), len(wires)))
                labels.append([w.attrs.get("port-label") for w in wires
                               if w.attrs.get("origin") == "port-open"])
                assert not any(w.attrs.get("origin") in {"grid", "trace"} for w in wires)
                atoms, wires = [], []
        assert panels == EXPECTED, panels
        for group, expected in enumerate(OPEN_LABELS):
            for actual in labels[2*group:2*group+2]:
                assert sorted(actual) == sorted(expected), (group, actual)
        results[mode] = {"panels": panels, "open_labels": labels,
                         "hard": hard, "findings": [str(f) for f in audit.findings]}
    return results


def mul(a, b):
    assert a and b and len(a[0]) == len(b), (len(a), len(a[0]), len(b))
    assert all(len(row) == len(a[0]) for row in a)
    assert all(len(row) == len(b[0]) for row in b)
    sparse_b = [[(j, y) for j, y in enumerate(row) if y] for row in b]
    result = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in sparse_b[k]:
                    result[i][j] += x*y
    return result


def unit(n, k, i, j):
    result = zeros(n, k)
    result[i][j] = Q(1)
    return result


def trans(a):
    return [list(row) for row in zip(*a)]


def recover(v, b, w):
    return mul(mul(v, b), w)


def coefficients() -> dict[str, object]:
    count = 0
    mutations = {key: False for key in (
        "drop_multiplicity", "permute_multiplicity", "replace_analysis_by_adjoint",
        "state_first_flattening", "swap_physical_row_input", "wrong_coefficient")}
    dimensions = [(2, 3, 3, 4, 2), (3, 2, 2, 3, 1), (1, 2, 3, 4, 2)]
    for d0, d1, c0, c1, m in dimensions:
        data = [endpoint(d0, c0, m, 0), endpoint(d1, c1, m, 1)]
        # Mix the state coordinates too, so row/input exchanges cannot hide
        # behind diagonal state maps. Paired inverse gauges preserve retracts.
        for p, d in enumerate((d0, d1)):
            h = [[Q(i+2) if j in (i, i+1) else Q(0) for j in range(d)]
                 for i in range(d)]
            hinv = [[Q((-1)**(j-i), j+2) if j >= i else Q(0)
                     for j in range(d)] for i in range(d)]
            assert mul(hinv, h) == ident(d)
            state, tensor, v, w = data[p]
            v, w = [mul(hinv, x) for x in v], [mul(x, h) for x in w]
            data[p] = state, tensor, v, w
            for mu, nu in product(range(m), repeat=2):
                assert mul(v[mu], w[nu]) == (ident(d) if mu == nu else zeros(d))
        for p, q in ((0, 1), (1, 0)):
            dp, dq = (d0, d1)[p], (d0, d1)[q]
            cp, cq = (c0, c1)[p], (c0, c1)[q]
            vp, wp, vq, wq = data[p][2], data[p][3], data[q][2], data[q][3]
            xs = [unit(dp, dq, r, s) for r, s in product(range(dp), range(dq))]
            xs.append([[Q(2*r-3*s+2, r+s+2) for s in range(dq)] for r in range(dp)])
            for x in xs:
                b = add(*(mul(mul(wp[mu], x), vq[mu]) for mu in range(m)))
                assert any(any(row) for row in b)
                for nu in range(m):
                    assert recover(vp[nu], b, wq[nu]) == x
                    count += 1
                    bad = {
                        "drop_multiplicity": mul(mul(wp[0], x), vq[0]),
                        "permute_multiplicity": add(*(mul(mul(wp[mu], x), vq[(mu+1) % m])
                                                     for mu in range(m))),
                        "replace_analysis_by_adjoint": add(*(mul(mul(wp[mu], x), trans(wq[mu]))
                                                              for mu in range(m))),
                        "wrong_coefficient": scale(Q(2), b),
                    }
                    for name, wrong in bad.items():
                        mutations[name] |= recover(vp[nu], wrong, wq[nu]) != x
            for r, s, k, l, a, b in product(range(dp), range(dq), range(dp),
                                           range(dq), range(cp), range(cq)):
                expected = sum((wp[mu][a*dp+k][r]*vq[mu][s][b*dq+l]
                                for mu in range(m)), Q(0))
                x = unit(dp, dq, r, s)
                contraction = add(*(mul(mul(wp[mu], x), vq[mu]) for mu in range(m)))
                assert contraction[a*dp+k][b*dq+l] == expected
                count += 1
                wrong_flat = sum((wp[mu][k*cp+a][r]*vq[mu][s][l*cq+b]
                                  for mu in range(m)), Q(0))
                mutations["state_first_flattening"] |= wrong_flat != expected
                wrong_physical = sum((wp[mu][a*dp+r][k]*vq[mu][s][b*dq+l]
                                      for mu in range(m)), Q(0))
                mutations["swap_physical_row_input"] |= wrong_physical != expected
    assert all(mutations.values()), mutations
    return {"dimensions_D0_D1_chi0_chi1_m": dimensions,
            "exact_equalities": count, "rejected_mutations": list(mutations)}


def row_basis(matrices):
    """An exact row-echelon basis of a matrix span, retaining matrix shape."""
    basis = {}
    n, k = len(matrices[0]), len(matrices[0][0])
    for matrix in matrices:
        row = [x for line in matrix for x in line]
        for pivot, old in sorted(basis.items()):
            c = row[pivot]
            if c:
                row = [x-c*y for x, y in zip(row, old)]
        pivot = next((i for i, x in enumerate(row) if x), None)
        if pivot is not None:
            c = row[pivot]
            basis[pivot] = [x/c for x in row]
    return [[row[i*k:(i+1)*k] for i in range(n)] for row in basis.values()]


def three_letter_span() -> dict[str, object]:
    # Independent state and operator dimensions, with non-adjoint rectangular
    # maps. The endpoint operator letters are supplied matrix units; no state
    # tensor or exact-action reconstruction is assumed in the core theorem.
    dims, chis, m = (2, 3), (3, 4), 2
    n = sum(chis)
    maps = []
    for d, chi in zip(dims, chis):
        gauge = [[Q(a+2) if b in (a, a+1) else Q(0)
                  for b in range(chi)] for a in range(chi)]
        inv = [[Q((-1)**(b-a), b+2) if b >= a else Q(0)
                for b in range(chi)] for a in range(chi)]
        assert mul(inv, gauge) == ident(chi)
        w = [[[gauge[a][mu]*(k == r) for r in range(d)]
              for a in range(chi) for k in range(d)] for mu in range(m)]
        v = [[[inv[mu][a]*(s == l) for a in range(chi) for l in range(d)]
              for s in range(d)] for mu in range(m)]
        for mu, nu in product(range(m), repeat=2):
            assert mul(v[mu], w[nu]) == (ident(d) if mu == nu else zeros(d))
        assert v[0] != trans(w[0])
        maps.append((v, w))
    states = [(p, i) for p in range(2) for i in range(dims[p])]
    bonds = [(p, a) for p in range(2) for a in range(chis[p])]
    letters = []
    crossed = {}
    for (p, r), (q, s), (t, k), (z, l) in product(states, repeat=4):
        letter = zeros(n)
        if p == t and q == z:
            if p == q:
                # The first chi_p^2 physical pairs enumerate every matrix unit.
                index = ((r*dims[p]+s)*dims[p]+k)*dims[p]+l
                if index < chis[p]**2:
                    a, b = divmod(index, chis[p])
                    offset = 0 if p == 0 else chis[0]
                    letter[offset+a][offset+b] = Q(1)
            else:
                for ai, (pa, a) in enumerate(bonds):
                    for bi, (qb, b) in enumerate(bonds):
                        if pa == p and qb == q:
                            letter[ai][bi] = sum((maps[p][1][mu][a*dims[p]+k][r]
                                                  * maps[q][0][mu][s][b*dims[q]+l]
                                                  for mu in range(m)), Q(0))
                if any(any(row) for row in letter):
                    crossed[p, q] = letter
        letters.append(letter)
    one = row_basis(letters)
    two = row_basis([mul(a, b) for a, b in product(one, repeat=2)])
    three = row_basis([mul(a, b) for a in two for b in one])
    ranks = [len(one), len(two), len(three)]
    assert ranks == [27, 45, 49], ranks
    certificate_count = 0
    missing_scalar_rejected = False
    for ai, (p, a) in enumerate(bonds):
        for bi, (q, b) in enumerate(bonds):
            target = unit(n, n, ai, bi)
            if p == q:
                assert target in letters and unit(n, n, bi, bi) in letters
                actual = mul(mul(target, unit(n, n, bi, bi)), unit(n, n, bi, bi))
            else:
                c = crossed[p, q]
                u, v = next((i, j) for i, j in product(range(n), repeat=2)
                            if c[i][j] and c[i][j] != 1)
                assert c in letters
                assert unit(n, n, ai, u) in letters and unit(n, n, v, bi) in letters
                raw = mul(mul(unit(n, n, ai, u), c), unit(n, n, v, bi))
                assert raw == scale(c[u][v], target)
                actual = scale(1/c[u][v], raw)
                missing_scalar_rejected |= raw != target
            assert actual == target
            certificate_count += 1
    assert missing_scalar_rejected
    # Positivity is essential: empty cross contractions keep every word diagonal.
    no_cross = [x for x in letters if all(not x[i][j]
                 for i, j in product(range(n), repeat=2) if bonds[i][0] != bonds[j][0])]
    zero_one = row_basis(no_cross)
    zero_three = row_basis([mul(mul(a, b), c) for a in zero_one
                           for b in zero_one for c in zero_one])
    assert len(zero_three) == sum(c*c for c in chis) == 25
    return {"D": dims, "chi": chis, "multiplicity": m,
            "actual_physical_letter_count": len(letters),
            "exact_word_span_ranks_1_2_3": ranks,
            "matrix_unit_three_letter_certificates": certificate_count,
            "missing_scalar_rejected": missing_scalar_rejected,
            "zero_multiplicity_three_letter_rank": len(zero_three),
            "scope": "isolated core assumptions; no exact-action or categorical claim"}


def web_check(root: Path, browser: bool) -> dict[str, object]:
    matches = [p for p in root.glob("*.html")
               if 'id="sec:mpo_mixed_normality"' in p.read_text(encoding="utf-8")]
    assert len(matches) == 1, matches
    path = matches[0]
    source = path.read_text(encoding="utf-8")
    # On an integrated page isolate this subsection up to the following one.
    start = source.index('id="sec:mpo_mixed_normality"')
    following = re.search(r'<h[12]\b[^>]*\bid="', source[start + 1:])
    end = start + 1 + following.start() if following else len(source)
    relevant = source[start:end]
    assert relevant.count('class="tenkz-equation"') == 2
    assert relevant.count('class="tenkz-pic ') == 4
    class TextAndPictures(HTMLParser):
        def __init__(self):
            super().__init__()
            self.text, self.images = [], []

        def handle_data(self, data):
            self.text.append(data)

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            if tag == "img" and "tenkz-pic" in attrs.get("class", "").split():
                self.images.append(attrs["src"])

    visible = TextAndPictures()
    visible.feed(relevant)
    assert not any(token in "".join(visible.text)
                   for token in (r"\tnwire", r"\begin{tenkz}"))
    assert "??" not in "".join(visible.text), "unresolved generated reference"
    declarations = [name.strip() for group in re.findall(
        r"\\lean\{([^}]+)\}", CHAPTER.read_text(encoding="utf-8"), re.S)
                    for name in group.split(",")]
    assert len(declarations) == 4
    for declaration in declarations:
        assert relevant.count(f'#doc/{declaration}"') == 1, declaration
    assert len(visible.images) == 4
    for image in visible.images:
        assert (root / image).is_file(), image
    class ParagraphStructure(HTMLParser):
        def __init__(self):
            super().__init__()
            self.in_paragraph = False

        def handle_starttag(self, tag, attrs):
            if tag == "p":
                assert not self.in_paragraph, "nested generated paragraph"
                self.in_paragraph = True
            if tag == "div" and "tenkz-equation" in dict(attrs).get("class", "").split():
                assert not self.in_paragraph, "equation wrapper inside a paragraph"

        def handle_endtag(self, tag):
            if tag == "p":
                assert self.in_paragraph, "unopened generated paragraph"
                self.in_paragraph = False

    parser = ParagraphStructure()
    parser.feed(source)
    parser.close()
    assert not parser.in_paragraph
    result = {"page": path.name, "wrappers": 2, "pictures": 4, "browser": False}
    if browser:
        from playwright.sync_api import sync_playwright
        from test_tenkz_equation_web import serve, _assert_chapter_picture_layout
        with serve(root) as url, sync_playwright() as playwright:
            chromium = playwright.chromium.launch()
            page = chromium.new_page()
            for width in (1440, 360):
                page.set_viewport_size({"width": width, "height": 1000})
                page.goto(f"{url}/{path.name}", wait_until="domcontentloaded", timeout=300_000)
                page.wait_for_function("() => window.MathJax && window.MathJax.startup")
                page.wait_for_function("async () => { await MathJax.startup.promise; return true; }",
                                       timeout=300_000)
                page.evaluate("showmore_update(2)")
                page.wait_for_function("() => [...document.querySelectorAll('.tenkz-pic')]"
                                       ".every(i => i.complete && i.naturalWidth > 0)")
                _assert_chapter_picture_layout(page, path.name)
            chromium.close()
        result["browser"] = True
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--web-root", type=Path)
    parser.add_argument("--browser", action="store_true")
    args = parser.parse_args()
    if args.browser and not args.web_root:
        parser.error("--browser requires --web-root")
    with tempfile.TemporaryDirectory(prefix="tenkz_mixed_normality_") as tmp:
        output = args.output_dir or Path(tmp)
        output.mkdir(parents=True, exist_ok=True)
        results = {"source_mutations": source_mutations(), "coefficients": coefficients(),
                   "three_letter_span": three_letter_span(), "native": native_check(output)}
        if args.web_root:
            results["web"] = web_check(args.web_root.resolve(), args.browser)
        (output / "validation.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
