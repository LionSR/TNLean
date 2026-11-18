#!/usr/bin/env python3
"""Exact check of the Z3 instance in
docs/paper-gaps/glm23_mixed_path_parent_commutation.tex, paragraph
"Unitary groups".

GLM23 (arXiv:2203.12563v3), Section 5, connects two injective MPS by the
interpolating tensor A(gamma) and the common operators T_g, one for each group
element g. Here G = Z3 = {e, g, g^2} acts at both endpoints by the same
unitary on-site representation, on the tensors

    A_0 = (E11, E12, E21, E22),    A_1 = (E11, 2 E12, E21, E22),

with letters ordered (1,1), (1,2), (2,1), (2,2). The action gauge of g^n is
Y^n with Y = diag(1, w), w a primitive cube root of unity, which is unitary,
and u_{g^n} = diag(1, w^-n, w^n, 1). The script checks, in exact arithmetic
over Q(w):

* the endpoint covariance sum_l u_kl A_p^l = Y_p A_p^k Y_p^{-1} for every
  label, and the exact action T_g A(gamma) = W A(gamma) V of every common
  operator;
* per-label failure: u_g^2 = diag(1, w, w^2, 1) is not scalar, and the
  adjoint of O^2_{T_g, E_00} does not lie in the two-site boundary range of
  T_g; two diagonal entries in the sector a = b = c = 0 suffice;
* union closure: (O^2_{T_g, X})^* = O^2_{T_{g^-1}, X-bar} for every label and
  every boundary X, so the union of the ranges over the three labels is closed
  under the adjoint;
* commutation: the canonical parent h_gamma commutes with O^2_{T_g, X} for
  every label and every X at gamma = 1/2 and gamma = 1/3.

Only the Python standard library is used; no rank is estimated numerically.
"""
from fractions import Fraction as F
from itertools import product


class Q3:
    """The element a + b w of Q(w), with w^2 = -1 - w."""

    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a, self.b = F(a), F(b)

    @staticmethod
    def of(x):
        return x if isinstance(x, Q3) else Q3(x)

    def __add__(self, o):
        o = Q3.of(o)
        return Q3(self.a + o.a, self.b + o.b)

    __radd__ = __add__

    def __neg__(self):
        return Q3(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-Q3.of(o))

    def __rsub__(self, o):
        return Q3.of(o) - self

    def __mul__(self, o):
        o = Q3.of(o)
        bd = self.b * o.b
        return Q3(self.a * o.a - bd, self.a * o.b + self.b * o.a - bd)

    __rmul__ = __mul__

    def conj(self):
        return Q3(self.a - self.b, -self.b)

    def inv(self):
        n = self.a * self.a - self.a * self.b + self.b * self.b
        c = self.conj()
        return Q3(c.a / n, c.b / n)

    def __truediv__(self, o):
        return self * Q3.of(o).inv()

    def __eq__(self, o):
        o = Q3.of(o)
        return self.a == o.a and self.b == o.b

    def __hash__(self):
        return hash((self.a, self.b))

    def __bool__(self):
        return self.a != 0 or self.b != 0

    def __repr__(self):
        return f"{self.a} + {self.b} w"


W = Q3(0, 1)
ZERO, ONE = Q3(0), Q3(1)


def wpow(n):
    return [ONE, W, W * W][n % 3]


def zeros(n, m):
    return [[ZERO] * m for _ in range(n)]


def eye(n):
    return [[ONE if i == j else ZERO for j in range(n)] for i in range(n)]


def mul(a, b):
    out = zeros(len(a), len(b[0]))
    cols = [[(j, y) for j, y in enumerate(r) if y] for r in b]
    for i, row in enumerate(a):
        acc = out[i]
        for k, x in enumerate(row):
            if x:
                for j, y in cols[k]:
                    acc[j] = acc[j] + x * y
    return out


def sub(a, b):
    return [[x - y for x, y in zip(r, s)] for r, s in zip(a, b)]


def adjoint(a):
    return [[x.conj() for x in r] for r in zip(*a)]


def trace(a):
    return sum((a[i][i] for i in range(len(a))), ZERO)


def inverse(a):
    n = len(a)
    m = [list(r) + e for r, e in zip(a, eye(n))]
    for c in range(n):
        p = next(r for r in range(c, n) if m[r][c])
        m[c], m[p] = m[p], m[c]
        pinv = m[c][c].inv()
        m[c] = [x * pinv for x in m[c]]
        for r in range(n):
            if r != c and m[r][c]:
                f = m[r][c]
                m[r] = [x - f * y for x, y in zip(m[r], m[c])]
    return [r[n:] for r in m]


def is_zero(a):
    return not any(any(r) for r in a)


def in_span(vectors, v):
    """Exact membership of v in the span of vectors, by Gaussian elimination."""
    rows, pivots = [], []
    for u in vectors:
        u = list(u)
        for p, r in zip(pivots, rows):
            if u[p]:
                f = u[p]
                u = [x - f * y for x, y in zip(u, r)]
        nz = next((i for i, x in enumerate(u) if x), None)
        if nz is None:
            continue
        inv = u[nz].inv()
        u = [x * inv for x in u]
        rows.append(u)
        pivots.append(nz)
    v = list(v)
    for p, r in zip(pivots, rows):
        if v[p]:
            f = v[p]
            v = [x - f * y for x, y in zip(v, r)]
    return not any(v)


def unit(n, i, j):
    m = zeros(n, n)
    m[i][j] = ONE
    return m


def scale(c, a):
    return [[c * x for x in r] for r in a]


D0 = D1 = 2
D = D0 + D1
LETTERS = [(r, s) for r in range(D) for s in range(D)]
INDEX = {p: k for k, p in enumerate(LETTERS)}
N1 = len(LETTERS)
WEIGHTS = ([1, 1, 1, 1], [1, 2, 1, 1])
ENDPOINTS = [[scale(Q3(c), unit(2, r, s)) for c, (r, s) in
              zip(w, product(range(2), repeat=2))] for w in WEIGHTS]
Y = [[ONE, ZERO], [ZERO, W]]


def sector(r):
    return 0 if r < D0 else 1


def local(r):
    return r if r < D0 else r - D0


def gauge(n):
    y = eye(2)
    for _ in range(n % 3):
        y = mul(y, Y)
    return y


def onsite(n):
    """u_{g^n} on the letters (r, s): the phase w^(n (r - s))."""
    return [wpow(n * (r - s)) for r, s in product(range(2), repeat=2)]


def common_operator(n):
    """The letters of T_{g^n}, its synthesis and analysis maps."""
    y = gauge(n)
    yi = inverse(y)
    assert mul(adjoint(y), y) == eye(2), "unitary action gauge"
    u = onsite(n)
    for a in ENDPOINTS:
        for k in range(4):
            assert scale(u[k], a[k]) == mul(mul(y, a[k]), yi), "endpoint covariance"
    w0 = w1 = y
    v0 = v1 = yi

    def letter(p, q):
        (r, s), (k, l) = p, q
        m = zeros(2, 2)
        a, b = sector(r), sector(s)
        if (a, b) != (sector(k), sector(l)):
            return m
        r, s, k, l = local(r), local(s), local(k), local(l)
        if a == b:
            m[a][a] = u[2 * r + s] if (r, s) == (k, l) else ZERO
        elif a == 0:
            m[0][1] = w0[k][r] * v1[s][l]
        else:
            m[1][0] = w1[k][r] * v0[s][l]
        return m

    mpo = {(p, q): letter(p, q) for p in LETTERS for q in LETTERS}
    synth, anal = zeros(2 * D, D), zeros(D, 2 * D)
    for k, r in product(range(D), repeat=2):
        if sector(k) == sector(r):
            al = sector(k)
            wp, vp = (w0, v0) if al == 0 else (w1, v1)
            synth[al * D + k][r] = wp[local(k)][local(r)]
            anal[r][al * D + k] = vp[local(r)][local(k)]
    assert mul(anal, synth) == eye(D)
    return mpo, synth, anal


def mixed_tensor(gam):
    def base(r, s):
        m = zeros(D, D)
        a, b = sector(r), sector(s)
        if a == b:
            src = ENDPOINTS[a][2 * local(r) + local(s)]
            off = 0 if a == 0 else D0
            for i in range(2):
                for j in range(2):
                    m[off + i][off + j] = src[i][j]
        else:
            m[r][s] = ONE
        return m

    wg = [[Q3(1 - gam if i < D0 else gam) if i == j else ZERO for j in range(D)]
          for i in range(D)]
    return [mul(base(*p), wg) for p in LETTERS]


def kron(a, b):
    return [[x * y for x in ra for y in rb] for ra in a for rb in b]


def boundary_operator(mpo, x):
    out = zeros(N1 * N1, N1 * N1)
    live = [(p, q) for (p, q), m in mpo.items() if not is_zero(m)]
    for (p1, q1), (p2, q2) in product(live, live):
        v = trace(mul(x, mul(mpo[(p1, q1)], mpo[(p2, q2)])))
        if v:
            out[INDEX[p1] * N1 + INDEX[p2]][INDEX[q1] * N1 + INDEX[q2]] = v
    return out


def parent(a):
    """h = 1 - orthogonal projection onto {sum_ij tr(A^i A^j X)|ij>}."""
    basis = []
    for i, j in product(range(D), repeat=2):
        x = unit(D, i, j)
        basis.append([trace(mul(mul(a[p], a[q]), x)) for p in range(N1) for q in range(N1)])
    gram = [[sum((x.conj() * y for x, y in zip(v, w)), ZERO) for v in basis] for w in basis]
    cols = [list(c) for c in zip(*basis)]
    proj = mul(mul(cols, inverse(gram)), [[x.conj() for x in v] for v in basis])
    return sub(eye(N1 * N1), proj)


def flat(o):
    return [x for r in o for x in r]


def main():
    ops = {}
    for n in range(3):
        mpo, synth, anal = common_operator(n)
        a = mixed_tensor(F(1, 3))
        for p in LETTERS:
            lhs = zeros(2 * D, 2 * D)
            for q in LETTERS:
                k = kron(mpo[(p, q)], a[INDEX[q]])
                lhs = [[x + y for x, y in zip(r, s)] for r, s in zip(lhs, k)]
            assert lhs == mul(mul(synth, a[INDEX[p]]), anal), "exact action"
        ops[n] = {(i, j): boundary_operator(mpo, unit(2, i, j))
                  for i in range(2) for j in range(2)}
    print("covariance and exact action hold for e, g, g^2")

    # Per-label failure for the label g.
    u = onsite(1)
    u2 = [x * x for x in u]
    assert len(set(u2)) > 1, "u_g^2 is not scalar"
    print("u_g =", u, "; u_g^2 =", u2)
    o = ops[1][(0, 0)]
    star = adjoint(o)
    rng = [flat(m) for m in ops[1].values()]
    assert not in_span(rng, flat(star)), "per-label closure must fail"
    e11e11 = INDEX[(0, 0)] * N1 + INDEX[(0, 0)]
    e12e11 = INDEX[(0, 1)] * N1 + INDEX[(0, 0)]
    assert o[e11e11][e11e11] == ONE and o[e12e11][e12e11] == W * W
    assert star[e11e11][e11e11] == ONE and star[e12e11][e12e11] == W
    print("<E11E11|O_{g,E00}|E11E11> = 1, <E12E11|O_{g,E00}|E12E11> = w^2,")
    print("but the same entries of its adjoint are 1 and w: not in the range of T_g")

    # Union closure: the adjoint of O_{g^n, X} is O_{g^-n, X-bar}.
    for n, (i, j) in product(range(3), product(range(2), repeat=2)):
        assert adjoint(ops[n][(i, j)]) == ops[(-n) % 3][(i, j)], "union closure"
    print("(O^2_{T_g^n, E_ij})^* = O^2_{T_g^-n, E_ij} for all n, i, j: union closed")

    # Commutation of the canonical parent with every boundary operator.
    for gam in (F(1, 2), F(1, 3)):
        h = parent(mixed_tensor(gam))
        for n, (i, j) in product(range(3), product(range(2), repeat=2)):
            o = ops[n][(i, j)]
            assert is_zero(sub(mul(h, o), mul(o, h))), "commutation"
        print(f"[h_gamma, O^2_(T_g^n, E_ij)] = 0 for all n, i, j at gamma = {gam}")
    print("all checks passed")


if __name__ == "__main__":
    main()
