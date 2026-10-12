#!/usr/bin/env python3
"""Check actual mixed-fusion diagrams and exact, mutation-sensitive coefficients.

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
from test_tenkz_mixed_action import add, ident, kron, scale, trace, zeros  # noqa: E402

ROOT = Path(__file__).resolve().parents[1]
CHAPTER = ROOT / "blueprint/src/chapter/ch30_mpo_mixed_fusion.tex"
WIRES = {
    "CROSS": [("seqs.0", "rect.180"), ("rect.0", "seqh.180"),
              ("fuss.0", "rectf.180"), ("rectf.0", "fush.180")],
    "LOCAL": [("opa.270", "opb.90"), ("fsyn.0", "target.180"),
              ("target.0", "fana.180")],
    "BOUNDARY": [("bana.0@1", "bx.180"), ("bana.0@2", "by.180"),
                 ("bx.0", "bsyn.180@1"), ("by.0", "bsyn.180@2")],
}
EXPECTED = [
    ("open:e, open:e, open:e, open:w, open:w, open:w", 3, 8),
    ("open:e, open:e, open:e, open:w, open:w, open:w", 3, 8),
    ("open:e, open:e, open:w, open:w, phys:n, phys:s", 2, 7),
    ("open:e, open:e, open:w, open:w, phys:n, phys:s", 3, 8),
    ("open:e, open:w", 1, 2), ("open:e, open:w", 4, 6),
]
OPEN_LABELS = [
    [r"\alpha", r"\gamma", "k", r"\beta", r"\delta", "l"],
    [r"\alpha", r"\gamma", r"\beta", r"\delta", r"\rho", r"\sigma"],
    [r"\xi", r"\eta"],
]


def bodies(source: str | None = None) -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8") if source is None else source
    assert r"\begin{tikzpicture}" not in source
    result = []
    for name, expected in WIRES.items():
        begin, end = [f"% TENKZ-MIXED-FUSION-{name}-{edge}" for edge in ("BEGIN", "END")]
        assert source.count(begin) == source.count(end) == 1
        body = source.split(begin, 1)[1].split(end, 1)[0]
        assert body.count(r"\begin{tenkzequation}") == 1
        assert body.count(r"\begin{tenkz}") == 2
        assert re.findall(r"\\tnwire\{([^}]+)\}\{([^}]+)\}", body) == expected
        assert r"\dagger" not in body and r"\overline" not in body
        result.append(body)
    for token in (r"{S_{0,i}}", r"{H_{1,i}}", r"{R_{0,q}}", r"{Q_{1,q}}",
                  r"180@3:virtual:$k$", r"0@3:virtual:$l$"):
        assert result[0].count(token) == (2 if "virtual:" in token else 1), token
    assert r"$=\displaystyle\sum_{c,\mu}$" in result[1]
    assert result[1].index(r"{\widetilde W_{ab;c\mu}}") < result[1].index(r"{T_c}")
    assert result[1].index(r"{T_c}") < result[1].index(r"{\widetilde V_{ab;c\mu}}")
    assert result[2].index(r"{\widetilde V_{ab;c\mu}}") < result[2].index(r"{X}")
    assert result[2].index(r"{Y}") < result[2].index(r"{\widetilde W_{ab;c\mu}}")
    return result


def source_mutations() -> list[str]:
    source = CHAPTER.read_text(encoding="utf-8")
    changes = {
        "cross_endpoint_orientation": (r"{H_{1,i}}", r"{H_{0,i}}"),
        "third_open_leg": (r"180@3:virtual:$k$", r"180@3:virtual:$l$"),
        "physical_contraction": (r"\tnwire{opa.270}{opb.90}", r"\tnwire{opa.90}{opb.90}"),
        "boundary_factor_order": (r"\tnwire{bana.0@1}{bx.180}",
                                  r"\tnwire{bana.0@1}{by.180}"),
        "invented_adjoint": (r"{H_{1,i}}", r"{H_{1,i}^{\dagger}}"),
    }
    for name, (old, new) in changes.items():
        assert old in source
        try:
            bodies(source.replace(old, new, 1))
        except AssertionError:
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
            body = body.replace(r"$\displaystyle\sum_{i\in P_{ab}}$", "")
            body = body.replace(r"$=\displaystyle\sum_{q\in Q_{ab}}$", "=")
            body = body.replace(r"$=\displaystyle\sum_{c,\mu}$", "=")
            body = body.replace("$=$", "=")
        source = ("\\documentclass{article}\n\\usepackage{amsmath,amssymb}\n"
                  "\\usepackage{tenkz}\n\\pagestyle{empty}\n" + wrapper.group(0)
                  + "\n\\begin{document}\n" + body + "\n\\end{document}\n")
        tex = output / f"mixed-fusion-{mode}.tex"
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


def trace_pair(a, b):
    assert len(a[0]) == len(b) and len(b[0]) == len(a)
    return sum((x*b[j][i] for i, row in enumerate(a) for j, x in enumerate(row)
                if x and b[j][i]), Q(0))


def trans(a):
    return [list(row) for row in zip(*a)]


def sandwich(w, a, v):
    return mul(mul(w, a), v)


def gauge(n):
    u = [[Q(i + 2) if j in (i, i+1) else Q(0) for j in range(n)] for i in range(n)]
    ui = [[Q((-1)**(j-i), j+2) if j >= i else Q(0) for j in range(n)] for i in range(n)]
    assert mul(u, ui) == mul(ui, u) == ident(n)
    return u, ui


def endpoint(m, chi, d, reverse=False):
    """Two-label C2 action, each simple operator repeated m times and padded.

    T_a[r,s;k,l] = P G_a[k,r] G_a^-1[s,l]; A[r,s] is a matrix
    unit, hence injective. The padded bond gauge is genuinely nonunitary.
    N_ab^c=m for c=a+b mod 2 and zero otherwise. Reverse changes valid
    fusion maps without changing endpoint tensors, and changes actual L.
    """
    u, ui = gauge(chi)
    g = ident(d) if d == 1 else [[Q(1), Q(2)], [Q(0), Q(-1)]]
    assert mul(g, g) == ident(d)
    gs = [ident(d), g]
    active = [[Q(i == j and i < m) for j in range(chi)] for i in range(chi)]
    p = sandwich(u, active, ui)
    va, wa = [], []
    for a in range(2):
        wa.append([[[u[alpha][i] * gs[a][k][r] for r in range(d)]
                    for alpha in range(chi) for k in range(d)] for i in range(m)])
        va.append([[[ui[i][beta] * gs[a][s][l] for beta in range(chi) for l in range(d)]
                    for s in range(d)] for i in range(m)])
    unused = [(i, j) for i, j in product(range(chi), repeat=2) if i >= m or j >= m]
    vf, wf = [], []
    for mu in range(m):
        e = zeros(chi*chi, chi)
        for k in range(m):
            i, j = (k, mu) if reverse else (mu, k)
            e[i*chi+j][k] = Q(1)
        for k in range(m, chi):
            i, j = unused[mu*(chi-m)+k-m]
            e[i*chi+j][k] = Q(1)
        wf.append(sandwich(kron(u, u), e, ui))
        vf.append(sandwich(u, trans(e), kron(ui, ui)))
    letters = [[scale(gs[a][k][r] * gs[a][s][l], p)
                for r, s, k, l in product(range(d), repeat=4)] for a in range(2)]
    for a, i, j in product(range(2), range(m), range(m)):
        assert mul(va[a][i], wa[a][j]) == (ident(d) if i == j else zeros(d))
    for i, j in product(range(m), repeat=2):
        assert mul(vf[i], wf[j]) == (ident(chi) if i == j else zeros(chi))
    # Endpoint fusion is checked from the independently defined letters.
    for a, b, r, s, k, l in product(range(2), range(2), *([range(d)]*4)):
        c = (a+b) % 2
        lhs = add(zeros(chi*chi), *(kron(letters[a][((r*d+s)*d+t)*d+v],
                                               letters[b][((t*d+v)*d+k)*d+l])
                                  for t, v in product(range(d), repeat=2)))
        rhs = add(zeros(chi*chi), *(sandwich(w, letters[c][((r*d+s)*d+k)*d+l], v)
                                   for v, w in zip(vf, wf)))
        assert lhs == rhs, ("endpoint fusion", m, chi, a, b, r, s, k, l)
    # Check exact endpoint action on every matrix-unit letter as well.
    for a, r, s in product(range(2), range(d), range(d)):
        base = zeros(d)
        base[r][s] = Q(1)
        lhs = zeros(chi*d)
        for k, l in product(range(d), repeat=2):
            unit = zeros(d)
            unit[k][l] = Q(1)
            lhs = add(lhs, kron(letters[a][((r*d+s)*d+k)*d+l], unit))
        assert lhs == add(zeros(chi*d), *(sandwich(w, base, v)
                                          for v, w in zip(va[a], wa[a])))
    if m:
        assert vf[0] != trans(wf[0]) and va[0][0] != trans(wa[0][0])
    return {"chi": chi, "d": d, "va": va, "wa": wa, "vf": vf, "wf": wf,
            "letters": letters}


def mixed_maps(v0, v1, w0, w1, dims, cdims, ddims=None):
    # No equality of the outgoing dimensions is used by this constructor.
    ddims = cdims if ddims is None else ddims
    aa = [(p, i) for p in range(2) for i in range(dims[p][0])]
    bb = [(p, i) for p in range(2) for i in range(dims[p][1])]
    cc = [(p, i) for p in range(2) for i in range(cdims[p])]
    dd = [(p, i) for p in range(2) for i in range(ddims[p])]
    ab = list(product(aa, bb))
    v = [[(v0 if p == 0 else v1)[r][i*dims[p][1]+j] if p == q == t else Q(0)
          for (q, i), (t, j) in ab] for p, r in cc]
    w = [[(w0 if p == 0 else w1)[i*dims[p][1]+j][r] if p == q == t else Q(0)
          for p, r in dd] for (q, i), (t, j) in ab]
    return v, w, ab, cc, dd


def arbitrary_rectangles():
    dims, cdims, ddims = [(2, 3), (3, 2)], [2, 1], [1, 3]
    def matrix(n, k, shift):
        return [[Q((i+1)*(j+2)+shift, i+j+1) for j in range(k)] for i in range(n)]
    v0, v1 = [matrix(cdims[p], dims[p][0]*dims[p][1], 2+p) for p in range(2)]
    w0, w1 = [matrix(dims[p][0]*dims[p][1], ddims[p], 5+p) for p in range(2)]
    v, w, ab, cc, dd = mixed_maps(v0, v1, w0, w1, dims, cdims, ddims)
    vp = [mul(v0, w0), mul(v1, w1)]
    expected = [[vp[p][i][j] if p == q else Q(0) for q, j in dd] for p, i in cc]
    assert mul(v, w) == expected
    # Sandwich permits a second independent pair of output dimensions.
    middle = matrix(sum(ddims), sum(cdims), 11)
    actual = sandwich(w, middle, v)
    for row, ((p, i), (q, j)) in enumerate(ab):
        for col, ((t, k), (z, l)) in enumerate(ab):
            if p != q or t != z:
                expected_entry = Q(0)
            else:
                wp, vt = (w0, w1)[p], (v0, v1)[t]
                expected_entry = sum((wp[i*dims[p][1]+j][u]
                    * middle[sum(ddims[:p])+u][sum(cdims[:t])+h]
                    * vt[h][k*dims[t][1]+l]
                    for u in range(ddims[p]) for h in range(cdims[t])), Q(0))
            assert actual[row][col] == expected_entry
    unmatched = next(i for i, (a, b) in enumerate(ab) if a[0] != b[0])
    bad = [row[:] for row in w]
    bad[unmatched][0] = Q(1)
    assert sandwich(bad, middle, v) != actual, "unmatched-sector mutation escaped"
    return {"incoming": dims, "analysis_outgoing": cdims, "synthesis_outgoing": ddims,
            "entries": len(ab)**2, "unmatched_mutation_rejected": True}



def scalar_transport():
    """An independent rectangular sandwich with non-symmetric shared L.

    This checks the finite-sum transport algebra, not endpoint hypotheses.
    The endpoint fixtures below separately construct actual raw L matrices.
    """
    ell = [[Q(2), Q(3)], [Q(1), Q(2)]]
    ss = [[[Q((i+1)*(j+2)+t) for j in range(2)] for i in range(3)] for t in (1, 4)]
    qq = [[[Q((i+2)*(j+1)-t) for j in range(4)] for i in range(3)] for t in (2, 5)]
    xx = [[Q(1), Q(-2), Q(3)], [Q(4), Q(1), Q(-1)]]
    hh = [add(*(scale(ell[i][q], qq[q]) for q in range(2))) for i in range(2)]
    rr = [add(*(scale(ell[i][q], ss[i]) for i in range(2))) for q in range(2)]
    lhs = add(*(sandwich(ss[i], xx, hh[i]) for i in range(2)))
    rhs = add(*(sandwich(rr[q], xx, qq[q]) for q in range(2)))
    assert lhs == rhs
    wrong = [add(*(scale(ell[q][i], ss[i]) for i in range(2))) for q in range(2)]
    assert lhs != add(*(sandwich(wrong[q], xx, qq[q]) for q in range(2))), \
        "transposed L coefficients escaped"
    return {"shared_l": [[str(x) for x in row] for row in ell],
            "rectangular_x": [2, 3], "boundary_shape": [3, 4],
            "transposed_l_mutation_rejected": True}


def actual_trees(e, a, b, m):
    chi, d = e["chi"], e["d"]
    s, h, rr, qq = [], [], [], []
    for i, j in product(range(m), repeat=2):
        s.append([[sum((e["wa"][b][j][gamma*d+k][t] * e["wa"][a][i][alpha*d+t][r]
                        for t in range(d)), Q(0)) for r in range(d)]
                  for alpha, gamma, k in product(range(chi), range(chi), range(d))])
        h.append([[sum((e["va"][a][i][r][beta*d+t] * e["va"][b][j][t][delta*d+l]
                        for t in range(d)), Q(0))
                   for beta, delta, l in product(range(chi), range(chi), range(d))]
                  for r in range(d)])
    c = (a+b) % 2
    for k, mu in product(range(m), repeat=2):
        rr.append(mul(kron(e["wf"][mu], ident(d)), e["wa"][c][k]))
        qq.append(mul(e["va"][c][k], kron(e["vf"][mu], ident(d))))
    ll = [[trace(mul(hi, rq))/d for rq in rr] for hi in h]
    for i in range(m*m):
        assert add(zeros(d, chi*chi*d), *(scale(ll[i][q], qq[q]) for q in range(m*m))) == h[i]
    for q in range(m*m):
        assert add(zeros(chi*chi*d, d), *(scale(ll[i][q], s[i]) for i in range(m*m))) == rr[q]
    return s, h, rr, qq, ll


def mixed_letters(data, a, m):
    states = [(p, i) for p in range(2) for i in range(data[p]["d"])]
    bonds = [(p, i) for p in range(2) for i in range(data[p]["chi"])]
    letters = []
    for (p, r), (q, s), (t, k), (u, l) in product(states, repeat=4):
        letter = zeros(len(bonds))
        if p == t and q == u:
            for ai, (pa, alpha) in enumerate(bonds):
                for bi, (qb, beta) in enumerate(bonds):
                    if p != pa or q != qb:
                        continue
                    if p == q:
                        d = data[p]["d"]
                        letter[ai][bi] = data[p]["letters"][a][((r*d+s)*d+k)*d+l][alpha][beta]
                    else:
                        letter[ai][bi] = sum((data[p]["wa"][a][i][alpha*data[p]["d"]+k][r]
                              * data[q]["va"][a][i][s][beta*data[q]["d"]+l]
                              for i in range(m)), Q(0))
        letters.append(letter)
    return letters, states, bonds


def coefficients():
    counts = {"local_letters": 0, "crossed_trees": 0, "boundary_words": 0,
              "periodic_words": 0}
    rejected = ["unmatched_sector"]
    for m in (0, 1, 2):
        data = [endpoint(m, m+1, 1), endpoint(m, m+2, 2)]
        chis = [e["chi"] for e in data]
        chi = sum(chis)
        ts = [mixed_letters(data, a, m)[0] for a in range(2)]
        physical = (1+2)**2
        dims = [(chis[p], chis[p]) for p in range(2)]
        vs, ws = [], []
        for mu in range(m):
            v, w, ab, _, _ = mixed_maps(data[0]["vf"][mu], data[1]["vf"][mu],
                                       data[0]["wf"][mu], data[1]["wf"][mu], dims, chis)
            vs.append(v)
            ws.append(w)
        for i, j in product(range(m), repeat=2):
            assert mul(vs[i], ws[j]) == (ident(chi) if i == j else zeros(chi))
        assert add(zeros(chi*chi), *(mul(w, v) for v, w in zip(vs, ws))) != ident(chi*chi)
        x = [[Q(2*i-j+1, i+j+1) for j in range(chi)] for i in range(chi)]
        y = [[Q(i+3*j-1, i+j+2) for j in range(chi)] for i in range(chi)]
        xy = kron(x, y)
        zs = [sandwich(v, xy, w) for v, w in zip(vs, ws)]
        # Every output boundary is fixed before label pair and word length vary.
        for a, b in product(range(2), repeat=2):
            c = (a+b) % 2
            tree0, tree1 = [actual_trees(e, a, b, m) for e in data]
            assert tree0[4] == tree1[4]
            rect = [[Q(2), Q(-3)]]
            lhs = add(zeros(chis[0]**2, 2*chis[1]**2),
                      *(sandwich(s, rect, h) for s, h in zip(tree0[0], tree1[1])))
            rhs = add(zeros(chis[0]**2, 2*chis[1]**2),
                      *(sandwich(s, rect, h) for s, h in zip(tree0[2], tree1[3])))
            assert lhs == rhs
            counts["crossed_trees"] += 1
            stacked = []
            for rho, sigma in product(range(physical), repeat=2):
                actual = add(zeros(chi*chi), *(kron(ts[a][rho*physical+tau],
                                                           ts[b][tau*physical+sigma])
                                              for tau in range(physical)))
                predicted = add(zeros(chi*chi), *(sandwich(w, ts[c][rho*physical+sigma], v)
                                                 for v, w in zip(vs, ws)))
                assert actual == predicted, (m, a, b, rho, sigma)
                stacked.append(actual)
                counts["local_letters"] += 1
            # Exhaust length-one coefficients; sample both vanishing and
            # nonvanishing words through length three, including cross sectors.
            live = [i for i, t in enumerate(ts[c]) if any(any(row) for row in t)]
            chosen = list(dict.fromkeys([0, physical**2-1] + live[::max(1, len(live)//5)]))
            words = [(i,) for i in range(physical**2)]
            words += list(product(chosen, repeat=2))
            words += [(i, j, i) for i, j in zip(chosen, reversed(chosen))]
            for word in words:
                bb, tt = ident(chi*chi), ident(chi)
                for index in word:
                    bb, tt = mul(bb, stacked[index]), mul(tt, ts[c][index])
                assert trace_pair(xy, bb) == sum((trace_pair(z, tt) for z in zs), Q(0))
                assert trace(bb) == m * trace(tt)
                counts["boundary_words"] += 1
                counts["periodic_words"] += 1
            if m == 2 and a == b == 1:
                changed = [[row[:] for row in t] for t in ts[c]]
                nonzero = next(i for i, t in enumerate(changed) if any(any(row) for row in t))
                changed[nonzero] = scale(Q(2), changed[nonzero])
                bad = add(zeros(chi*chi), *(sandwich(w, changed[nonzero], v)
                                          for v, w in zip(vs, ws)))
                assert bad != stacked[nonzero], "coefficient mutation escaped"
                assert any(sandwich(v, kron(y, x), w) != z for v, w, z in zip(vs, ws, zs)), \
                    "boundary tensor-factor reversal escaped"
                assert trace(stacked[nonzero]) != (m+1)*trace(ts[c][nonzero]), \
                    "periodic multiplicity mutation escaped"
                rejected += ["reconstruction_coefficient", "boundary_tensor_factor_order",
                             "periodic_multiplicity"]
        assert trace(ident(chi*chi)) != m*trace(ident(chi)), "length-zero counterexample missing"
    # A valid change of one endpoint's fusion basis must not be mistaken for
    # equality of actual raw L. Its fusion/action identities still pass.
    m = 2
    normal, changed = endpoint(m, 3, 1), endpoint(m, 4, 2, reverse=True)
    t0, t1 = actual_trees(normal, 1, 1, m), actual_trees(changed, 1, 1, m)
    assert t0[4] != t1[4]
    x = [[Q(2), Q(-3)]]
    lhs = add(zeros(9, 32), *(sandwich(s, x, h) for s, h in zip(t0[0], t1[1])))
    rhs = add(zeros(9, 32), *(sandwich(s, x, h) for s, h in zip(t0[2], t1[3])))
    assert lhs != rhs, "unaligned actual-L mutation escaped"
    rejected.append("unaligned_actual_l")
    return {"counts": counts, "multiplicities": [0, 1, 2], "labels": [0, 1],
            "fusion": "N_ab^c=m when c=a+b mod 2, otherwise zero", "state_dimensions": [1, 2],
            "operator_dimensions": "m+1 and m+2", "non_adjoint": True,
            "ambient_complete": False, "positive_lengths": [1, 2, 3],
            "length_one": "all physical coefficients", "longer_words": "deterministic samples",
            "length_zero_counterexamples": True, "rejected_mutations": rejected,
            "rectangular_maps": arbitrary_rectangles(), "scalar_transport": scalar_transport()}


def web_check(root: Path, browser: bool):
    matches = [p for p in root.glob("*.html")
               if 'id="sec:mpo_mixed_fusion"' in p.read_text(encoding="utf-8")]
    assert len(matches) == 1, matches
    path = matches[0]
    source = path.read_text(encoding="utf-8")
    start = source.index('id="sec:mpo_mixed_fusion"')
    following = re.search(r'<h[123]\b[^>]*\bid="', source[start+1:])
    end = start+1+following.start() if following else len(source)
    relevant = source[start:end]
    assert relevant.count('class="tenkz-equation"') == 3
    assert relevant.count('class="tenkz-pic ') == 6

    class InspectHTML(HTMLParser):
        def __init__(self):
            super().__init__()
            self.text, self.images = [], []
            self.paragraph = False

        def handle_data(self, data):
            self.text.append(data)

        def handle_starttag(self, tag, attrs):
            attrs = dict(attrs)
            if tag == "p":
                assert not self.paragraph, "nested generated paragraph"
                self.paragraph = True
            if tag == "div" and "tenkz-equation" in attrs.get("class", "").split():
                assert not self.paragraph, "equation wrapper inside paragraph"
            if tag == "img" and "tenkz-pic" in attrs.get("class", "").split():
                self.images.append(attrs["src"])

        def handle_endtag(self, tag):
            if tag == "p":
                assert self.paragraph, "unopened generated paragraph"
                self.paragraph = False

    visible = InspectHTML()
    visible.feed(source)
    visible.close()
    assert not visible.paragraph
    assert not any(token in "".join(visible.text) for token in (r"\tnwire", r"\begin{tenkz}"))
    for image in visible.images:
        assert (root / image).is_file(), image
    result = {"page": path.name, "wrappers": 3, "pictures": 6, "browser": False}
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--web-root", type=Path)
    parser.add_argument("--browser", action="store_true")
    args = parser.parse_args()
    if args.browser and not args.web_root:
        parser.error("--browser requires --web-root")
    with tempfile.TemporaryDirectory(prefix="tenkz_mixed_fusion_") as tmp:
        output = args.output_dir or Path(tmp)
        output.mkdir(parents=True, exist_ok=True)
        results = {"source_mutations": source_mutations(), "native": native_check(output),
                   "coefficients": coefficients()}
        if args.web_root:
            results["web"] = web_check(args.web_root.resolve(), args.browser)
        (output / "validation.json").write_text(json.dumps(results, indent=2)+"\n")
    print(json.dumps(results, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
