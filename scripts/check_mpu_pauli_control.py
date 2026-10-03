#!/usr/bin/env python3
"""Check the rational four-qubit Pauli witness with exact arithmetic.

The witness and its orthogonal-walk realization are described in
docs/audits/2026-10-02_mpu_schmidt_unitary_obstruction.tex. This check
computes the three physical operator Schmidt ranks, which are separate
from the coefficient-space statements in the Lean development.
"""

import sympy as sp


def main() -> None:
    axes = [
        sp.Matrix(row) / 15
        for row in [
            (15, 0, 0), (0, 15, 0), (0, 0, 15), (9, 12, 0),
            (5, -10, -10), (-10, 5, -10), (-10, -10, 5), (-5, -2, -14),
        ]
    ]
    pauli = [
        sp.Matrix([[0, 1], [1, 0]]),
        sp.Matrix([[0, -sp.I], [sp.I, 0]]),
        sp.diag(1, -1),
    ]
    witness = sp.zeros(16)
    for label, axis in enumerate(axes):
        block = sum((axis[k] * pauli[k] for k in range(3)), sp.zeros(2))
        for i in range(2):
            for j in range(2):
                witness[8 * i + label, 8 * j + label] = block[i, j]
    assert (witness.H * witness - sp.eye(16)).applyfunc(sp.expand) == sp.zeros(16)

    ranks = []
    for cut in range(1, 4):
        left, right = 2**cut, 2 ** (4 - cut)
        unfolding = sp.Matrix(
            left**2, right**2,
            lambda row, col: witness[
                (row // left) * right + col // right,
                (row % left) * right + col % right,
            ],
        )
        ranks.append(unfolding.rank())
    assert ranks == [3, 3, 2]

    reflection = sp.eye(3) - sp.Rational(2, 3) * sp.ones(3)
    rotation = sp.Matrix([
        [0, sp.Rational(3, 5), -sp.Rational(4, 5)],
        [0, sp.Rational(4, 5), sp.Rational(3, 5)],
        [1, 0, 0],
    ])
    quarter_turn = sp.Matrix([[0, -1, 0], [1, 0, 0], [0, 0, 1]])
    origin = sp.Matrix([1, 0, 0])
    for a in range(2):
        for b in range(2):
            for c in range(2):
                assert axes[4 * a + 2 * b + c] == (
                    reflection**a * rotation**b * quarter_turn**c * origin
                )
    assert [matrix.det() for matrix in [reflection, rotation, quarter_turn]] == [-1, 1, 1]
    print("Exact Pauli witness: cut ranks (3, 3, 2); all eight orthogonal-walk labels agree.")


if __name__ == "__main__":
    main()
