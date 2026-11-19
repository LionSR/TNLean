#!/usr/bin/env python3
"""Exact check of the counterexample in
docs/paper-gaps/glm23_mixed_operator_one_site_injectivity.tex.

GLM23 (arXiv:2203.12563v3), Section 5, lines 1687--1689, asserts that the
common operator T_a of the interpolating path is injective. Here the fusion
category is Rep(A4). For p = 0, 1 the endpoint has a label set S_p of four
elements of A4, the state tensor A_p consists of the 16 matrix units on
C^4, and for every irreducible representation rho_a the action maps are

    W_{p,mu}[(alpha, k), r] = delta_{kr} rho_a(g_r)^{-1}[alpha, mu],
    V_{p,mu}[s, (beta, l)]  = delta_{sl} rho_a(g_s)[mu, beta],

so that the endpoint operator is diagonal with letters rho_a(g_r^{-1} g_s).
The script checks, in exact rational arithmetic, for the three-dimensional
irreducible representation rho:

* rho is a representation of A4;
* biorthogonality V_{p,mu} W_{p,nu} = delta_{mu nu} 1;
* the exact action identity, in the index convention of the formal
  development, with A_p the matrix units;
* one-site injectivity of both endpoint operators (letter span of rank 9);
* the letter span of the mixed operator has rank 34 < 36, each crossed corner
  having rank 8 < 9;
* the same failure for every regauging of the second endpoint's action maps
  by rho(z), z in A4, which leaves the endpoint operator unchanged;
* an explicit integer matrix M with zero row and column sums whose matrix
  coefficient q -> sum_j M[q(j), j] of rho vanishes on S_0^{-1} S_1.

The one-dimensional representations give bond-one operators whose letters are
nonzero scalars, so they are injective without computation.

Only the Python standard library is used; no rank is estimated numerically.
"""
from fractions import Fraction as F
from math import gcd
from itertools import permutations, product


def zeros(n, m):
    return [[F(0)] * m for _ in range(n)]


def eye(n):
    return [[F(int(i == j)) for j in range(n)] for i in range(n)]


def mul(a, b):
    out = zeros(len(a), len(b[0]))
    for i, row in enumerate(a):
        for k, x in enumerate(row):
            if x:
                for j, y in enumerate(b[k]):
                    if y:
                        out[i][j] += x * y
    return out


def rank(vectors):
    """Rank of a list of rational vectors by exact Gaussian elimination."""
    rows = [list(v) for v in vectors]
    r = 0
    ncol = len(rows[0]) if rows else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        p = rows[r][c]
        rows[r] = [x / p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return r


def kernel(rows, ncol):
    """A basis of the right kernel of the matrix with the given rows."""
    rows = [list(v) for v in rows]
    pivots = []
    r = 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        p = rows[r][c]
        rows[r] = [x / p for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c] != 0:
                f = rows[i][c]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        pivots.append(c)
        r += 1
    free = [c for c in range(ncol) if c not in pivots]
    basis = []
    for fc in free:
        v = [F(0)] * ncol
        v[fc] = F(1)
        for i, pc in enumerate(pivots):
            v[pc] = -rows[i][fc]
        basis.append(v)
    return basis


# The group A4 as even permutations of {0, 1, 2, 3}; (p q)(i) = p(q(i)).
def sign(p):
    s = 1
    for i in range(4):
        for j in range(i + 1, 4):
            if p[i] > p[j]:
                s = -s
    return s


A4 = [p for p in permutations(range(4)) if sign(p) == 1]
E = (0, 1, 2, 3)


def compose(p, q):
    return tuple(p[q[i]] for i in range(4))


def inv(p):
    r = [0] * 4
    for i, x in enumerate(p):
        r[x] = i
    return tuple(r)


def perm_matrix(p):
    m = zeros(4, 4)
    for j in range(4):
        m[p[j]][j] = F(1)
    return m


def rho(p):
    """The standard representation on the sum-zero subspace of Q^4, in the
    basis f_i = e_i - e_3 (i = 0, 1, 2), with f_3 = 0: p f_i = f_{p(i)} -
    f_{p(3)}."""
    m = zeros(3, 3)
    for i in range(3):
        if p[i] < 3:
            m[p[i]][i] += 1
        if p[3] < 3:
            m[p[3]][i] -= 1
    return m


for g in A4:
    for h in A4:
        assert rho(compose(g, h)) == mul(rho(g), rho(h))
assert rho(E) == eye(3)

RHO = {g: rho(g) for g in A4}
RHO_INV = {g: rho(inv(g)) for g in A4}
for g in A4:
    assert mul(RHO[g], RHO_INV[g]) == eye(3)

# (123), (01)(23), (02)(13), (032) in the map notation i -> p[i].
C123 = (0, 2, 3, 1)
X = (1, 0, 3, 2)
Y = (2, 3, 0, 1)
C032 = (3, 1, 0, 2)
S = [[E, C123, X, Y], [E, C123, X, C032]]
for labels in S:
    assert all(g in A4 for g in labels) and len(set(labels)) == 4

D, CHI, M = 4, 3, 3


def action_maps(labels, gauge):
    """W_mu (CHI*D x D) and V_mu (D x CHI*D) of one endpoint; acted index
    (alpha, k) is flattened as alpha * D + k, as finProdFinEquiv does.
    The gauge z replaces rho(g)^{-1} by rho(g)^{-1} rho(z) and rho(g) by
    rho(z)^{-1} rho(g)."""
    Ws, Vs = [], []
    for mu in range(M):
        w = zeros(CHI * D, D)
        v = zeros(D, CHI * D)
        for r, g in enumerate(labels):
            left = mul(RHO_INV[g], RHO[gauge])
            right = mul(RHO_INV[gauge], RHO[g])
            for a in range(CHI):
                w[a * D + r][r] = left[a][mu]
                v[r][a * D + r] = right[mu][a]
        Ws.append(w)
        Vs.append(v)
    return Ws, Vs


def endpoint_operator(Ws, Vs):
    """T^{(r,s),(k,l)}_{alpha beta} = sum_mu W_mu[(alpha,k), r] V_mu[s, (beta,l)]."""
    T = {}
    for r, s, k, l in product(range(D), repeat=4):
        T[(r, s, k, l)] = [[sum(Ws[mu][a * D + k][r] * Vs[mu][s][b * D + l]
                                for mu in range(M))
                            for b in range(CHI)] for a in range(CHI)]
    return T


def matrix_unit(n, i, j):
    m = zeros(n, n)
    m[i][j] = F(1)
    return m


data = [action_maps(labels, E) for labels in S]
ops = [endpoint_operator(*d) for d in data]

for (Ws, Vs), T in zip(data, ops):
    # Biorthogonality.
    for mu in range(M):
        for nu in range(M):
            prod_ = mul(Vs[mu], Ws[nu])
            assert prod_ == (eye(D) if mu == nu else zeros(D, D))
    # Exact action: sum_{k,l} T^{(r,s),(k,l)}_{ab} A^{(k,l)}_{ij}
    #   = sum_mu (W_mu A^{(r,s)} V_mu)_{(a,i),(b,j)} with A^{(k,l)} = E_{kl}.
    for r, s in product(range(D), repeat=2):
        rhs = zeros(CHI * D, CHI * D)
        for mu in range(M):
            t = mul(mul(Ws[mu], matrix_unit(D, r, s)), Vs[mu])
            rhs = [[x + y for x, y in zip(ra, rb)] for ra, rb in zip(rhs, t)]
        for a, b, i, j in product(range(CHI), range(CHI), range(D), range(D)):
            lhs = T[(r, s, i, j)][a][b]
            assert lhs == rhs[a * D + i][b * D + j]
    # One-site injectivity of the endpoint operator.
    letters = [sum(T[key], []) for key in T]
    assert rank(letters) == CHI * CHI, "endpoint operator is not injective"

print("endpoint operators: biorthogonal exact actions, both injective (rank 9)")


def crossed_letters(Wp, Vq):
    """Letters of the crossed corner p -> q:
    sum_mu W_{p,mu}[(alpha,k), r] V_{q,mu}[s, (beta,l)]."""
    out = []
    for r, s, k, l in product(range(D), repeat=4):
        out.append([sum(Wp[mu][a * D + k][r] * Vq[mu][s][b * D + l]
                        for mu in range(M))
                    for a in range(CHI) for b in range(CHI)])
    return out


def mixed_rank(d0, d1):
    """Rank of the span of all letters of the mixed operator of bond
    dimension CHI + CHI, built sector by sector as mixedEndpointMPOLetter."""
    (W0, V0), (W1, V1) = d0, d1
    T0, T1 = endpoint_operator(W0, V0), endpoint_operator(W1, V1)
    n = 2 * CHI
    letters = []
    for p, q in product(range(2), repeat=2):
        for r, s, k, l in product(range(D), repeat=4):
            m = [[F(0)] * n for _ in range(n)]
            for a, b in product(range(CHI), repeat=2):
                if p == q:
                    val = (T0 if p == 0 else T1)[(r, s, k, l)][a][b]
                else:
                    Wp = W0 if p == 0 else W1
                    Vq = V1 if q == 1 else V0
                    val = sum(Wp[mu][a * D + k][r] * Vq[mu][s][b * D + l]
                              for mu in range(M))
                m[p * CHI + a][q * CHI + b] = val
            letters.append(sum(m, []))
    return rank(letters)


(W0, V0), (W1, V1) = data
assert rank(crossed_letters(W0, V1)) == 8
assert rank(crossed_letters(W1, V0)) == 8
assert mixed_rank(data[0], data[1]) == 34
print("mixed operator: letter span of rank 34 < 36; crossed corners of rank 8")

# Every regauging of the second endpoint by rho(z) fails as well.
for z in A4:
    Wz, Vz = action_maps(S[1], z)
    for mu in range(M):
        for nu in range(M):
            assert mul(Vz[mu], Wz[nu]) == (eye(D) if mu == nu else zeros(D, D))
    assert endpoint_operator(Wz, Vz) == ops[1]
    assert rank(crossed_letters(W0, Vz)) == 8
    assert rank(crossed_letters(Wz, V0)) == 8
print("all 12 regaugings by rho(z): same endpoint operator, crossed rank 8")

# An explicit vanishing matrix coefficient. The set Q = S_0^{-1} S_1.
Q = sorted({compose(inv(g), h) for g in S[0] for h in S[1]})
assert len(Q) == 10
# Unknown integer matrix M (16 entries) with zero row and column sums and
# sum_j M[q(j), j] = 0 for q in Q.
eqs = []
for i in range(4):
    eqs.append([F(int(a == i)) for a in range(4) for _ in range(4)])
    eqs.append([F(int(b == i)) for _ in range(4) for b in range(4)])
for q in Q:
    eqs.append([F(int(a == q[b])) for a in range(4) for b in range(4)])
ker = kernel(eqs, 16)
assert len(ker) == 1
Mc = ker[0]
den = 1
for x in Mc:
    den = den * x.denominator // gcd(den, x.denominator)
Mint = [[int(Mc[4 * a + b] * den) for b in range(4)] for a in range(4)]
if Mint[0][2] < 0:
    Mint = [[-x for x in row] for row in Mint]
print("vanishing coefficient matrix M =", Mint)
assert Mint == [[0, 0, 1, -1], [1, -1, 0, 0], [-1, 1, 0, 0], [0, 0, -1, 1]]
coeff = {q: sum(Mint[q[j]][j] for j in range(4)) for q in A4}
assert all(coeff[q] == 0 for q in Q)
# The two remaining elements are (012) and (023).
assert coeff[(1, 2, 0, 3)] == 4 and coeff[(2, 1, 3, 0)] == -4
# Cardinalities quoted in the note.
assert len({compose(inv(g), h) for g in S[0] for h in S[0]}) == 10
assert len({compose(inv(g), h) for g in S[1] for h in S[1]}) == 11
# Zero row and column sums put this coefficient in the rho-isotypic part, so
# it is a nonzero linear functional on End(C^3) vanishing on rho(Q).
print("coefficient values off Q:",
      {"".join(map(str, q)): coeff[q] for q in A4 if q not in Q})
print("all checks passed")
