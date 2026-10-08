#!/usr/bin/env python3
"""Check mixed-action diagrams, their real wrapper, and exact coefficient identities.

The default check runs native Tenkz audits and rational arithmetic fixtures.
Add --web-root to inspect the actual strict web output, and --browser to run
its desktop/mobile MathJax layout gate. Browser failures are never skipped.
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

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_mixed_action.tex"
EXPECTED = [
    ("open:e, open:w, phys:n, phys:n, phys:s, phys:s", 1, 6),
    ("open:e, open:w, phys:n, phys:n, phys:s, phys:s", 2, 7),
    ("open:e, open:e, open:w, open:w, phys:n", 2, 6),
    ("open:e, open:e, open:w, open:w, phys:n", 3, 7),
]
WIRES = {
    "CROSS": [("syn.0", "ana.180")],
    "LOCAL": [("op.270", "state.90"), ("left.0", "middle.180"),
              ("middle.0", "right.180")],
}


def bodies() -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8")
    assert r"\begin{tikzpicture}" not in source
    result = []
    for name, expected in WIRES.items():
        begin = f"% TENKZ-MIXED-ACTION-{name}-BEGIN"
        end = f"% TENKZ-MIXED-ACTION-{name}-END"
        assert source.count(begin) == source.count(end) == 1
        body = source.split(begin, 1)[1].split(end, 1)[0]
        assert body.count(r"\begin{tenkzequation}") == 1
        assert body.count(r"\begin{tenkz}") == 2
        assert re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body) == expected
        assert r"\dagger" not in body and r"\overline" not in body
        result.append(body)
    assert r"{W_p}" in result[0] and r"{V_q}" in result[0]
    assert r"90:physical:$r$, 270:physical:$k$" in result[0]
    assert r"90:physical:$s$, 270:physical:$l$" in result[0]
    assert r"$=\displaystyle\sum_{\mu=0}^{m-1}$" in result[1]
    assert r"180@1:virtual:$\alpha$, 180@2:virtual:$i$" in result[1]
    assert r"0@1:virtual:$\beta$" in result[1]
    assert r"0@2:virtual:$j$" in result[1]
    return result


def native_check(output: Path) -> dict[str, object]:
    engine = shutil.which("xelatex")
    assert engine, "xelatex is required"
    # Compile the production wrapper verbatim; a separate pass additionally
    # tests Tenkz's hard equation-signature comparison, not a replacement pass.
    macros = (ROOT / "blueprint/src/macros/print.tex").read_text(encoding="utf-8")
    wrapper = re.search(r"\\newenvironment\{tenkzequation\}[^\n]+", macros)
    assert wrapper, "the production print wrapper is missing"
    env = os.environ.copy()
    env["TEXINPUTS"] = f"{tenkz_tex()}//:" + env.get("TEXINPUTS", "")
    results = {}
    for mode in ("wrapper", "signature"):
        body = "\n".join(bodies())
        if mode == "signature":
            body = body.replace(r"\begin{tenkzequation}",
                                r"\begin{tenkzeq}[check={signature}]")
            body = body.replace(r"\end{tenkzequation}", r"\end{tenkzeq}")
            body = body.replace("$=$", "=")
            # A multiplicity sum does not alter the external signature. Its
            # full ink is tested above in the verbatim production wrapper;
            # here omit it so its lower-limit '=' is not read as a relation.
            body = body.replace(r"$=\displaystyle\sum_{\mu=0}^{m-1}$",
                                "=")
        source = (
            "\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
            "\\usepackage{tenkz}\n\\pagestyle{empty}\n"
            + wrapper.group(0) + "\n\\begin{document}\n"
            + body + "\n\\end{document}\n"
        )
        tex = output / f"mixed-action-{mode}.tex"
        tex.write_text(source, encoding="utf-8")
        run = subprocess.run(
            [engine, "-interaction=nonstopmode", "-halt-on-error", tex.name],
            cwd=output, env=env, text=True, stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT, check=False,
        )
        (output / f"{mode}-stdout.log").write_text(run.stdout, encoding="utf-8")
        assert run.returncode == 0, run.stdout[-8000:]
        audit = Audit(tex.with_suffix(".tnlog"), tex)
        audit.run()
        hard = [str(f) for f in audit.findings if f.severity == "HARD"]
        assert not hard, hard
        panels, atoms, wires = [], [], []
        labels = []
        for event in audit.events():
            if event.kind == "atom":
                atoms.append(event)
            elif event.kind == "wire":
                wires.append(event)
            elif event.kind == "kernel-boundary":
                panels.append((event.attrs["signature"], len(atoms), len(wires)))
                labels.append([w.attrs.get("port-label") for w in wires
                               if w.attrs.get("origin") == "port-open"])
                assert not any(w.attrs.get("origin") in {"grid", "trace"}
                               for w in wires)
                atoms, wires = [], []
        assert panels == EXPECTED, panels
        assert sorted(labels[0]) == sorted(labels[1]) == sorted(
            [r"\alpha", r"\beta", "r", "s", "k", "l"]
        ), labels[:2]
        assert sorted(labels[2]) == sorted(labels[3]) == sorted(
            [r"\alpha", r"\beta", "i", "j", r"\rho"]
        ), labels[2:]
        results[mode] = {"panels": panels, "open_labels": labels, "hard": hard}
    return results


def zeros(n: int, k: int | None = None) -> list[list[Q]]:
    return [[Q(0) for _ in range(n if k is None else k)] for _ in range(n)]


def ident(n: int) -> list[list[Q]]:
    return [[Q(i == j) for j in range(n)] for i in range(n)]


def mul(a: list[list[Q]], b: list[list[Q]]) -> list[list[Q]]:
    return [[sum((x * y for x, y in zip(row, col) if x and y), Q(0))
             for col in zip(*b)] for row in a]


def add(*matrices: list[list[Q]]) -> list[list[Q]]:
    return [[sum(xs, Q(0)) for xs in zip(*rows)] for rows in zip(*matrices)]


def scale(c: Q, a: list[list[Q]]) -> list[list[Q]]:
    return [[c * x for x in row] for row in a]


def kron(a: list[list[Q]], b: list[list[Q]]) -> list[list[Q]]:
    return [[x * y for x in ar for y in br] for ar in a for br in b]


def trace(a: list[list[Q]]) -> Q:
    return sum((row[i] for i, row in enumerate(a)), Q(0))


def endpoint(d: int, chi: int, m: int, sector: int):
    # Invertible, nonunitary upper triangular MPO-bond gauge U=diag(t)(I+J).
    # Its explicit inverse uses the nilpotency of the superdiagonal shift J.
    u = [[Q((a + 2) if b in (a, a + 1) else 0)
          for b in range(chi)] for a in range(chi)]
    inv = [[Q((-1) ** (b - a), b + 2) if b >= a else Q(0)
            for b in range(chi)] for a in range(chi)]
    assert mul(inv, u) == ident(chi)
    w, v = [], []
    for mu in range(m):
        g = [Q((mu + 2) * (i + 2) + sector) for i in range(d)]
        w.append([[u[a][mu] * g[i] * (i == r) for r in range(d)]
                  for a in range(chi) for i in range(d)])
        v.append([[inv[mu][a] / g[r] * (r == i)
                   for a in range(chi) for i in range(d)] for r in range(d)])
    # Some letters deliberately vanish: no injectivity or nonzero state premise.
    letters = []
    for r, s in product(range(d), repeat=2):
        a = zeros(d)
        a[r][s] = Q(0 if r != s else (sector + 1) * (r + 1))
        letters.append(a)
    tensor = {}
    for r, s, k, l in product(range(d), repeat=4):
        tensor[r, s, k, l] = [[sum((w[mu][alpha*d+k][r]
                                                   * v[mu][s][beta*d+l]
                                                   for mu in range(m)), Q(0))
                              for beta in range(chi)] for alpha in range(chi)]
    # Diagonal endpoint tensors are supplied data, checked independently.
    for r, s in product(range(d), repeat=2):
        acted = add(zeros(chi*d), *(kron(tensor[r, s, k, l], letters[k*d+l])
                                    for k, l in product(range(d), repeat=2)))
        assert acted == add(zeros(chi*d), *(mul(mul(w[mu], letters[r*d+s]), v[mu])
                                          for mu in range(m)))
    for mu, nu in product(range(m), repeat=2):
        assert mul(v[mu], w[nu]) == (ident(d) if mu == nu else zeros(d))
    if m:
        assert v[0] != [list(row) for row in zip(*w[0])], "fixture must be non-adjoint"
    return letters, tensor, v, w


def coefficients() -> dict[str, object]:
    checks = 0
    gammas = [Q(-1), Q(0), Q(1, 3), Q(1), Q(2)]
    for m in (0, 1, 2, 3):
        dims = (1, 2)
        chis = (m + 1, m + 2)
        data = [endpoint(dims[p], chis[p], m, p) for p in range(2)]
        state = [(p, i) for p in range(2) for i in range(dims[p])]
        bond = [(p, a) for p in range(2) for a in range(chis[p])]
        d, chi = len(state), len(bond)
        v, w = [], []
        for mu in range(m):
            v.append([[data[p][2][mu][r][a*dims[p]+i] if p == q == t else Q(0)
                       for q, a in bond for t, i in state] for p, r in state])
            w.append([[data[p][3][mu][a*dims[p]+i][r] if p == q == t else Q(0)
                       for t, r in state] for p, a in bond for q, i in state])
        for mu, nu in product(range(m), repeat=2):
            assert mul(v[mu], w[nu]) == (ident(d) if mu == nu else zeros(d))
        # Unmatched sectors make ambient completeness false even at m>0.
        projection = add(zeros(chi*d), *(mul(wi, vi) for wi, vi in zip(w, v)))
        assert projection != ident(chi*d)
        base = []
        tensor = {}
        for ri, si in product(range(d), repeat=2):
            p, r = state[ri]
            q, s = state[si]
            a = zeros(d)
            if p == q:
                offset = 0 if p == 0 else dims[0]
                for i, j in product(range(dims[p]), repeat=2):
                    a[offset+i][offset+j] = data[p][0][r*dims[p]+s][i][j]
            else:
                a[ri][si] = Q(1)
            base.append(a)
            for ki, li in product(range(d), repeat=2):
                pk, k = state[ki]
                ql, l = state[li]
                t = zeros(chi)
                for ai, bi in product(range(chi), repeat=2):
                    pa, alpha = bond[ai]
                    qb, beta = bond[bi]
                    if p == pk == pa and q == ql == qb:
                        t[ai][bi] = (data[p][1][r,s,k,l][alpha][beta] if p == q
                            else sum((data[p][3][mu][alpha*dims[p]+k][r]
                                      * data[q][2][mu][s][beta*dims[q]+l]
                                      for mu in range(m)), Q(0)))
                tensor[ri*d+si, ki*d+li] = t
        x = [[Q(2*i-j+1) for j in range(chi)] for i in range(chi)]
        y = [[Q(i+3*j-1) for j in range(d)] for i in range(d)]
        xy = kron(x, y)
        z = add(zeros(d), *(mul(mul(vi, xy), wi) for vi, wi in zip(v, w)))
        for gamma in gammas:
            h = [[(Q(1)-gamma if state[i][0] == 0 else gamma) * (i == j)
                  for j in range(d)] for i in range(d)]
            lifted = kron(ident(chi), h)
            actual = [mul(a, h) for a in base]
            acted = []
            for vi in v:
                assert mul(vi, lifted) == mul(h, vi)
            for rs in range(d*d):
                # This uses the independent fixed T and the weighted input;
                # it is not simply a restatement of the reconstructed RHS.
                lhs = add(zeros(chi*d), *(kron(tensor[rs, kl], actual[kl])
                                        for kl in range(d*d)))
                rhs = add(zeros(chi*d), *(mul(mul(wi, actual[rs]), vi)
                                        for vi, wi in zip(v, w)))
                assert lhs == rhs, (m, gamma, rs)
                acted.append(lhs)
                checks += 1
            # Exhaust every physical word through length two. Boundary matrices
            # are non-diagonal and fixed before both length and gamma vary.
            for length in (1, 2):
                for word in product(range(d*d), repeat=length):
                    ab, bb = ident(d), ident(chi*d)
                    for rs in word:
                        ab, bb = mul(ab, actual[rs]), mul(bb, acted[rs])
                    assert trace(mul(xy, bb)) == trace(mul(z, ab))
                    assert trace(bb) == m * trace(ab)
                    checks += 2
        assert trace(ident(chi*d)) != m * trace(ident(d)), "empty-word counterexample"
    return {"exact_checks": checks, "multiplicities": [0, 1, 2, 3],
            "parameters": [str(g) for g in gammas],
            "non_adjoint": True, "ambient_complete": False,
            "lengths": [1, 2], "length_zero_counterexample": True}


def web_check(root: Path, browser: bool) -> dict[str, object]:
    matches = [p for p in root.glob("*.html")
               if 'id="sec:mpo_mixed_action"' in p.read_text(encoding="utf-8")]
    assert len(matches) == 1, matches
    path = matches[0]
    source = path.read_text(encoding="utf-8")
    # On an integrated page isolate this subsection up to the following one.
    start = source.index('id="sec:mpo_mixed_action"')
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
    with tempfile.TemporaryDirectory(prefix="tenkz_mixed_action_") as tmp:
        output = args.output_dir or Path(tmp)
        output.mkdir(parents=True, exist_ok=True)
        results = {"coefficients": coefficients(), "native": native_check(output)}
        if args.web_root:
            results["web"] = web_check(args.web_root.resolve(), args.browser)
        (output / "validation.json").write_text(json.dumps(results, indent=2) + "\n")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
