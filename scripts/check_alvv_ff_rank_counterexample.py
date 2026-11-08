#!/usr/bin/env python3
"""Exact rational counterexample to ALVV Theorem 5.14(2), arXiv:1602.08828v2.

This checks the explicitly displayed minor in docs/paper-gaps/alvv16_ff_rank.tex.
It uses only the Python standard library and never estimates rank numerically.
"""
from fractions import Fraction as F
from itertools import permutations
from math import prod


Q = [[F(int(i == 0 and j == 0)) + F(int(i > 0 and j > 0), 3)
      for j in range(4)] for i in range(4)]
P = [[F(int(i == j)) - Q[i][j] for j in range(4)] for i in range(4)]
P0 = [[F(int(i == j and i != 0)) for j in range(4)] for i in range(4)]


def mul(a, b):
    return [[sum(a[i][k] * b[k][j] for k in range(len(b)))
             for j in range(len(b[0]))] for i in range(len(a))]


def tensor_entry(factors, row, col):
    """Entry in a Kronecker product, in lexicographic qubit coordinates."""
    value = F(1)
    for factor in reversed(factors):
        dim = len(factor)
        value *= factor[row % dim][col % dim]
        row //= dim
        col //= dim
    assert row == col == 0
    return value


def identity(dim):
    return [[F(int(i == j)) for j in range(dim)] for i in range(dim)]


def replacement_entry(row, col):
    """P0_01 + P_67 + 2 I - Q_23 Q_45 - Q_12 Q_34 Q_56."""
    return (tensor_entry([P0, identity(64)], row, col)
            + tensor_entry([identity(64), P], row, col)
            + 2 * F(int(row == col))
            - tensor_entry([identity(4), Q, Q, identity(4)], row, col)
            - tensor_entry([identity(2), Q, Q, Q, identity(2)], row, col))


def determinant(a):
    """Leibniz formula; all 7! summands are exact rational numbers."""
    result = F(0)
    for p in permutations(range(len(a))):
        inversions = sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))
        result += (-1) ** inversions * prod(a[i][p[i]] for i in range(len(a)))
    return result


def main():
    for projection in [Q, P, P0]:
        assert mul(projection, projection) == projection
        assert projection == list(map(list, zip(*projection)))
    assert all(projection[i][0] == 0 for projection in [P, P0] for i in range(4))
    # The reshuffling rows are (left output, left input), and its columns are
    # (right output, right input), for the cut 0123 | 4567.
    rows = [85, 0, 17, 1, 16, 34, 68]
    cols = [170, 0, 8, 128, 34, 136, 153]
    minor = [[replacement_entry(16 * (r // 16) + c // 16,
                                16 * (r % 16) + c % 16)
              for c in cols] for r in rows]
    integer_minor = [[int(27 * value) for value in row] for row in minor]
    assert [[F(value, 27) for value in row] for row in integer_minor] == minor
    expected = [[95, 69, -3, -3, 89, 75, 93],
                [60, 0, 0, 0, 36, 36, 54],
                [66, 36, -9, -9, 60, 42, 60],
                [-3, 0, 0, -9, 0, -9, -9],
                [-3, 0, -9, 0, 0, -9, -9],
                [68, 36, 0, 0, 60, 48, 66],
                [89, 45, 0, 0, 69, 69, 87]]
    assert integer_minor == expected
    det = determinant(minor)
    assert det == -F(512, 177147)
    assert determinant(integer_minor) == -30233088
    print('Local terms are symmetric idempotents annihilating |00>.')
    print('Rows:', rows)
    print('Columns:', cols)
    print('det(minor) =', det)
    print('det(27 * minor) =', determinant(integer_minor))
    print('OSR >= 7 > d^2 + 2 = 6. See the note for uniqueness and the upper bound.')


if __name__ == '__main__':
    main()
