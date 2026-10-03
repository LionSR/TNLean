#!/usr/bin/env python3
"""Verify the recursive rank-two phase decomposition on exact small examples.

The circuit proof is in docs/audits/2026-10-02_mpu_diagonal_circuits.tex.
This script enumerates small coefficient tables only for verification; it does
not assert that enumeration is an efficient way to construct the circuit.
"""
from itertools import product
from sympy import I, Matrix, Rational, cancel, conjugate


TRANSPOSED_BRANCHES = 0


def simplify(z):
    return cancel(z)


def cuts(values, n):
    return [Matrix(1 << k, 1 << (n-k), values).rank() for k in range(n+1)]


def decompose(values, n):
    global TRANSPOSED_BRANCHES
    assert all(simplify(z * conjugate(z)) == 1 for z in values)
    assert max(cuts(values, n)) <= 2
    if n <= 1:
        return values, 1, n, 0
    k = n // 2
    rows = [values[j:j+(1 << (n-k))] for j in range(0, len(values), 1 << (n-k))]
    normalized = [tuple(simplify(z / row[0]) for z in row) for row in rows]
    row_types = list(dict.fromkeys(normalized))
    transposed = False
    if len(row_types) > 2:
        rows = list(map(list, zip(*rows)))
        normalized = [tuple(simplify(z / row[0]) for z in row) for row in rows]
        row_types = list(dict.fromkeys(normalized))
        transposed = True
        TRANSPOSED_BRANCHES += 1
        assert len(row_types) <= 2
    left_n, right_n = (n-k, k) if transposed else (k, n-k)
    labels = [row_types.index(row) for row in normalized]
    if len(row_types) == 2:
        # Recover the selector from two restrictions, not from a row lookup.
        j = next(j for j in range(len(row_types[0])) if row_types[0][j] != row_types[1][j])
        alpha, beta = row_types[0][j], row_types[1][j]
        selector = [simplify((row[j] * conjugate(row[0]) - alpha) / (beta-alpha))
                    for row in rows]
        assert selector == labels
        assert max(cuts(selector, left_n)) <= 5
        for cut in range(left_n + 1):
            residuals = set(tuple(selector[j:j+(1 << (left_n-cut))])
                            for j in range(0, len(selector), 1 << (left_n-cut)))
            assert len(residuals) <= 32
    g, nodes, cost, selectors = decompose([row[0] for row in rows], left_n)
    recovered_types = []
    for row in row_types:
        r, count, work, sel = decompose(list(row), right_n)
        recovered_types.append(r)
        nodes += count
        cost += work
        selectors += sel
    reconstructed = [[simplify(g[x] * recovered_types[labels[x]][y])
                      for y in range(len(rows[0]))] for x in range(len(rows))]
    if transposed:
        reconstructed = list(map(list, zip(*reconstructed)))
    flattened = [z for row in reconstructed for z in row]
    assert flattened == values
    return flattened, nodes+1, cost+n, selectors+(len(row_types) == 2)


phases = (Rational(3, 5) + I*Rational(4, 5), Rational(5, 13) + I*Rational(12, 13))
count = 0
for n in range(1, 7):
    for family in ('nearest', 'star', 'reverse_star', 'parity', 'projection', 'product'):
        vals = []
        for bits in product((0, 1), repeat=n):
            if family == 'nearest':
                z = 1
                for j in range(n-1):
                    z *= phases[j % 2] ** (bits[j] * bits[j+1])
            elif family == 'star':
                z = 1
                for j in range(1, n):
                    z *= phases[j % 2] ** (bits[0] * bits[j])
            elif family == 'reverse_star':
                z = 1
                for j in range(n-1):
                    z *= phases[j % 2] ** (bits[-1] * bits[j])
            elif family == 'parity':
                z = phases[0] ** (sum(bits) % 2)
            elif family == 'projection':
                z = phases[0] ** int(all(bits))
            else:
                z = 1
                for j, bit in enumerate(bits):
                    z *= phases[j % 2] ** bit
            vals.append(simplify(z))
        _, nodes, work, selectors = decompose(vals, n)
        print(f'N={n}, {family}: nodes={nodes}, total interval lengths={work}, selectors={selectors}')
        count += 1
print(f'Exact recursive reconstruction and selector rank bounds verified for {count} examples.')

assert TRANSPOSED_BRANCHES > 0
print(f'Column-type alternative exercised at {TRANSPOSED_BRANCHES} recursive cuts.')
