#!/usr/bin/env python3
"""Exact check of the unitary counterexample in
docs/paper-gaps/glm23_mixed_path_parent_commutation.tex.

GLM23 (arXiv:2203.12563v3), Section 5, connects two injective MPS by the
interpolating tensor A(gamma) and the common operator T_g. Here the group is
Z2, both endpoints carry the same unitary on-site representation
u = diag(1, -1, -1, 1), the two endpoint tensors are different, and the L data
agree. The script checks, in exact rational arithmetic:

* the endpoint covariance sum_l u_kl A_p^l = Y_p A_p^k Y_p^{-1};
* the exact action T_g A(gamma) = W A(gamma) V of the common operator;
* that the two-site boundary range {O^2_X} of T_g is not closed under the
  adjoint (all data are real, so the adjoint is the transpose);
* that the canonical parent h_gamma does not commute with the periodic
  two-site operator O^2_1, and that the periodic three-site Hamiltonian does
  not commute with the periodic three-site operator, at gamma = 1/2;
* the control: with the Hermitian gauge Y_0 = sz the range is adjoint closed
  and h_gamma commutes with every O^2_X;
* the canonical-gauge instance A_0 = (1, sx, J, sz) / 2 and
  A_1 = (1, 2 sx, 2 J, 4 sz) / 5: both tensors satisfy
  sum_i A^i* A^i = sum_i A^i A^i* = 1, the action gauges are unitary, the
  range is adjoint closed and h_gamma commutes with every O^2_X.

Only the Python standard library is used; no rank is estimated numerically.
"""
from collections import defaultdict
from fractions import Fraction as F
from itertools import product


def zeros(n, m):
    return [[F(0)] * m for _ in range(n)]


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mat(rows):
    return [[F(x) for x in r] for r in rows]


def mul(a, b):
    out = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in enumerate(b[k]):
                    if y:
                        out[i][j] += x * y
    return out


def sub(a, b):
    return [[x - y for x, y in zip(r, s)] for r, s in zip(a, b)]


def transpose(a):
    return [list(r) for r in zip(*a)]


def trace(a):
    return sum(a[i][i] for i in range(len(a)))


def inverse(a):
    n = len(a)
    m = [list(r) + e for r, e in zip(a, eye(n))]
    for c in range(n):
        p = next(r for r in range(c, n) if m[r][c] != 0)
        m[c], m[p] = m[p], m[c]
        m[c] = [x / m[c][c] for x in m[c]]
        for r in range(n):
            if r != c and m[r][c] != 0:
                f = m[r][c]
                m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return [r[n:] for r in m]


def echelon(vectors):
    rows, pivots = [], []
    for v in vectors:
        v = reduce(rows, pivots, v)
        nz = next((i for i, x in enumerate(v) if x != 0), None)
        if nz is None:
            continue
        v = [x / v[nz] for x in v]
        rows = [[x - r[nz] * y for x, y in zip(r, v)] for r in rows]
        rows.append(v)
        pivots.append(nz)
    return rows, pivots


def reduce(rows, pivots, v):
    v = list(v)
    for p, r in zip(pivots, rows):
        if v[p] != 0:
            f = v[p]
            v = [x - f * y for x, y in zip(v, r)]
    return v


ONE = mat([[1, 0], [0, 1]])
SX = mat([[0, 1], [1, 0]])
J = mat([[0, 1], [-1, 0]])
SZ = mat([[1, 0], [0, -1]])
U = [F(1), F(-1), F(-1), F(1)]
D0 = D1 = 2
D = D0 + D1
LETTERS = [(r, s) for r in range(D) for s in range(D)]
INDEX = {p: k for k, p in enumerate(LETTERS)}
N1 = len(LETTERS)


def sector(r):
    return 0 if r < D0 else 1


def local(r):
    return r if r < D0 else r - D0


def scale(c, a):
    return [[c * x for x in r] for r in a]


def build(gauge, c0=F(1), w1=(1, 2, 1, 1), c1=F(1)):
    """Endpoint data, common operator letters and the mixed tensor."""
    gi = inverse(gauge)
    a0 = [scale(c0, mul(mul(gauge, x), gi)) for x in (ONE, SX, J, SZ)]
    a1 = [scale(c1 * w, x) for w, x in zip(w1, (ONE, SX, J, SZ))]
    y0, y1 = mul(mul(gauge, SZ), gi), SZ
    for a, y in ((a0, y0), (a1, y1)):
        assert mul(y, y) == eye(2)
        for k in range(4):
            lhs = [[U[k] * x for x in r] for r in a[k]]
            assert lhs == mul(mul(y, a[k]), inverse(y)), "endpoint covariance"
    w0, v0, w1, v1 = y0, inverse(y0), y1, inverse(y1)
    # The L entry (1/D) tr(V V) of the pair (g, g); fusion maps are trivial.
    assert trace(mul(v0, v0)) / 2 == trace(mul(v1, v1)) / 2 == 1

    def letter(p, q):
        (r, s), (k, l) = p, q
        m = zeros(2, 2)
        a, b = sector(r), sector(s)
        if (a, b) != (sector(k), sector(l)):
            return m
        r, s, k, l = local(r), local(s), local(k), local(l)
        if a == b:
            m[a][a] = U[2 * r + s] if (r, s) == (k, l) else F(0)
        elif a == 0:
            m[0][1] = w0[k][r] * v1[s][l]
        else:
            m[1][0] = w1[k][r] * v0[s][l]
        return m

    mpo = {(p, q): letter(p, q) for p in LETTERS for q in LETTERS}

    def base(r, s):
        m = zeros(D, D)
        a, b = sector(r), sector(s)
        if a == b:
            src = (a0 if a == 0 else a1)[2 * local(r) + local(s)]
            off = 0 if a == 0 else D0
            for i in range(2):
                for j in range(2):
                    m[off + i][off + j] = src[i][j]
        else:
            m[r][s] = F(1)
        return m

    def tensor(gam):
        wg = [[(1 - gam if i < D0 else gam) if i == j else F(0) for j in range(D)]
              for i in range(D)]
        return [mul(base(*p), wg) for p in LETTERS]

    synth, anal = zeros(2 * D, D), zeros(D, 2 * D)
    for k, r in product(range(D), repeat=2):
        if sector(k) == sector(r):
            al = sector(k)
            wp, vp = (w0, v0) if al == 0 else (w1, v1)
            synth[al * D + k][r] = wp[local(k)][local(r)]
            anal[r][al * D + k] = vp[local(r)][local(k)]
    assert mul(anal, synth) == eye(D)
    return mpo, tensor, synth, anal, y0


def kron(a, b):
    return [[x * y for x in ra for y in rb] for ra in a for rb in b]


def boundary_operator(mpo, x):
    out = zeros(N1 * N1, N1 * N1)
    live = [(p, q) for (p, q), m in mpo.items() if any(any(r) for r in m)]
    for (p1, q1), (p2, q2) in product(live, live):
        v = trace(mul(x, mul(mpo[(p1, q1)], mpo[(p2, q2)])))
        if v:
            out[INDEX[p1] * N1 + INDEX[p2]][INDEX[q1] * N1 + INDEX[q2]] = v
    return out


def parent(a):
    """h = 1 - projection onto {sum_ij tr(A^i A^j X)|ij>}."""
    basis = []
    for i, j in product(range(D), repeat=2):
        x = zeros(D, D)
        x[i][j] = F(1)
        basis.append([trace(mul(mul(a[p], a[q]), x)) for p in range(N1) for q in range(N1)])
    gram = [[sum(x * y for x, y in zip(v, w)) for w in basis] for v in basis]
    proj = mul(mul(transpose(basis), inverse(gram)), basis)
    return sub(eye(N1 * N1), proj)


def unit(a, b):
    m = zeros(2, 2)
    m[a][b] = F(1)
    return m


def three_site_commutator_entry(mpo, h, out_cfg, in_cfg):
    """<out|[H_3, O_3]|in> for the periodic Hamiltonian and operator."""
    live = [(p, q) for (p, q), m in mpo.items() if any(any(r) for r in m)]
    o3 = defaultdict(F)
    for t in product(live, repeat=3):
        v = trace(mul(mul(mpo[t[0]], mpo[t[1]]), mpo[t[2]]))
        if v:
            o3[(tuple(INDEX[p] for p, _ in t), tuple(INDEX[q] for _, q in t))] += v

    def ham(cfg):
        out = defaultdict(F)
        for s in range(3):
            col = cfg[s] * N1 + cfg[(s + 1) % 3]
            for i in range(N1 * N1):
                if h[i][col]:
                    new = list(cfg)
                    new[s], new[(s + 1) % 3] = divmod(i, N1)
                    out[tuple(new)] += h[i][col]
        return out

    def op(vec):
        out = defaultdict(F)
        for (x, y), v in o3.items():
            if y in vec:
                out[x] += v * vec[y]
        return out

    def ham_vec(vec):
        out = defaultdict(F)
        for y, c in vec.items():
            for x, v in ham(y).items():
                out[x] += c * v
        return out

    e = {in_cfg: F(1)}
    return ham_vec(op(e)).get(out_cfg, F(0)) - op(ham_vec(e)).get(out_cfg, F(0))


def run(gauge, expect_closed, **kw):
    mpo, tensor, synth, anal, y0 = build(gauge, **kw)
    gam = F(1, 3)
    a = tensor(gam)
    for p in LETTERS:
        lhs = zeros(2 * D, 2 * D)
        for q in LETTERS:
            k = kron(mpo[(p, q)], a[INDEX[q]])
            lhs = [[x + y for x, y in zip(r, s)] for r, s in zip(lhs, k)]
        assert lhs == mul(mul(synth, a[INDEX[p]]), anal), "exact action"
    ops = {(i, j): boundary_operator(mpo, unit(i, j)) for i in range(2) for j in range(2)}
    rows, pivots = echelon([[x for r in o for x in r] for o in ops.values()])
    assert len(rows) == 4
    closed = all(not any(reduce(rows, pivots, [x for r in transpose(o) for x in r]))
                 for o in ops.values())
    assert closed == expect_closed
    for gam in (F(1, 2), F(1, 3)):
        h = parent(tensor(gam))
        periodic = [[x + y for x, y in zip(r, s)] for r, s in zip(ops[(0, 0)], ops[(1, 1)])]
        comm = sub(mul(h, periodic), mul(periodic, h))
        assert any(any(r) for r in comm) == (not expect_closed)
    print(f"Y0 = {[[str(x) for x in r] for r in y0]}: boundary range adjoint closed = {closed}")
    return mpo, tensor, ops


def main():
    mpo, tensor, ops = run(mat([[1, 1], [0, 1]]), expect_closed=False)
    o = ops[(0, 0)]
    sigma = INDEX[(1, 2)] * N1 + INDEX[(2, 0)]
    tau = INDEX[(0, 2)] * N1 + INDEX[(2, 0)]
    diag = INDEX[(0, 0)] * N1 + INDEX[(0, 0)]
    assert (o[sigma][tau], o[tau][sigma], o[diag][diag]) == (F(-2), F(0), F(1))
    cfg_out = (INDEX[(0, 0)], INDEX[(0, 0)], INDEX[(1, 1)])
    cfg_in = (INDEX[(0, 0)], INDEX[(0, 0)], INDEX[(0, 1)])
    value = three_site_commutator_entry(mpo, parent(tensor(F(1, 2))), cfg_out, cfg_in)
    assert value == F(-4, 75)
    print(f"<e1e1,e1e1,e2e2|[H_3,O_3]|e1e1,e1e1,e1e2> at gamma = 1/2: {value}")
    run(ONE, expect_closed=True)
    # Canonical gauge: both tensors are left and right canonical with identity
    # fixed points, and the action gauge sz is unitary at both endpoints.
    c0, w1, c1 = F(1, 2), (1, 2, 2, 4), F(1, 5)
    a0 = [scale(c0, x) for x in (ONE, SX, J, SZ)]
    a1 = [scale(c1 * w, x) for w, x in zip(w1, (ONE, SX, J, SZ))]
    for a in (a0, a1):
        left = right = zeros(2, 2)
        for x in a:
            left = [[p + q for p, q in zip(r, t)] for r, t in zip(left, mul(transpose(x), x))]
            right = [[p + q for p, q in zip(r, t)] for r, t in zip(right, mul(x, transpose(x)))]
        assert left == right == eye(2), "canonical form"
    assert mul(SZ, transpose(SZ)) == eye(2), "unitary action gauge"
    print("canonical gauge:", end=" ")
    run(ONE, expect_closed=True, c0=c0, w1=w1, c1=c1)
    print("all checks passed")


if __name__ == "__main__":
    main()
