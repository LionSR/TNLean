#!/usr/bin/env python3
"""Check the exact six-call controlled merging for Schmidt-rank-two unitaries.

Let A0,A1 be unitaries on one factor and let B_s=L P_s R on the
other, where L,R are unitary and P0,P1 are complementary projections.
Then Bplus=B0+B1 and Bminus=B0-B1 are unitary, and the involution
J=Bplus^dagger Bminus records the controlling sector coherently.

This script verifies the controlled merging identity on every basis
input with a clean record qubit, using exact SymPy arithmetic. The
outer control is left arbitrary, so the check includes both its
values and, by linearity, coherent superpositions. Examples include
noncommuting rational rotations and algebraic unitary factors,
unequal factor dimensions, and both orientations of the controller.

The argument and the six recursive child calls are explained in
docs/audits/2026-10-02_mpu_rank_two_circuits.tex. This finite check
does not establish the structural lemma or the asymptotic circuit
bound; those are proved mathematically in that note.

Run with: python3 scripts/check_mpu_rank_two_controlled_merging.py
Requires SymPy.
"""

from __future__ import annotations

from dataclasses import dataclass

import sympy as sp


def assert_equal(left: sp.Matrix, right: sp.Matrix, description: str) -> None:
    """Compare matrices in exact arithmetic, simplifying algebraic entries."""
    if left.shape != right.shape or any(sp.simplify(x) != 0 for x in left - right):
        raise AssertionError(description)


@dataclass(frozen=True)
class Example:
    """Unitary target factors and an orthogonal two-sector controller."""

    name: str
    a0: sp.Matrix
    a1: sp.Matrix
    left: sp.Matrix
    right: sp.Matrix
    sector_zero: sp.Matrix


def check_example(example: Example, controller_first: bool) -> None:
    da, db = example.a0.rows, example.left.rows
    ia, ib = sp.eye(da), sp.eye(db)
    data_identity = sp.eye(da * db)
    p0 = sp.diag(1, 0)
    p1 = sp.diag(0, 1)
    hadamard = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
    kron = sp.kronecker_product

    def data_product(a: sp.Matrix, b: sp.Matrix) -> sp.Matrix:
        return kron(b, a) if controller_first else kron(a, b)

    for factor in (example.a0, example.a1, example.left, example.right):
        assert_equal(factor.H * factor, sp.eye(factor.rows), "nonunitary input factor")
    q0 = example.sector_zero
    q1 = ib - q0
    assert_equal(q0.H, q0, "non-Hermitian sector")
    assert_equal(q0 * q0, q0, "non-idempotent sector")
    b0 = example.left * q0 * example.right
    b1 = example.left * q1 * example.right
    bplus, bminus = b0 + b1, b0 - b1
    involution = bplus.H * bminus
    assert_equal(involution.H, involution, "non-Hermitian relative unitary")
    assert_equal(involution * involution, ib, "relative unitary is not an involution")
    input_p0 = (ib + involution) / 2
    input_p1 = (ib - involution) / 2
    assert_equal(bplus * input_p0, b0, "wrong input sector zero")
    assert_equal(bplus * input_p1, b1, "wrong input sector one")

    unitary = data_product(example.a0, b0) + data_product(example.a1, b1)
    assert_equal(unitary.H * unitary, data_identity, "assembled operator is not unitary")

    # Full matrix order is outer control c, record z, and the two data factors.
    h_z = kron(sp.eye(2), hadamard, data_identity)

    def control_cz_b(b: sp.Matrix) -> sp.Matrix:
        return (
            kron(p0, sp.eye(2), data_identity)
            + kron(p1, p0, data_identity)
            + kron(p1, p1, data_product(ia, b))
        )

    # Operators compose from right to left. Record the sector with two calls.
    record = h_z * control_cz_b(bplus.H) * control_cz_b(bminus) * h_z
    targets = (
        kron(p0, sp.eye(2), data_identity)
        + kron(p1, p0, data_product(example.a0, ib))
        + kron(p1, p1, data_product(example.a1, ib))
    )
    # Two final calls simultaneously erase the sector and apply Bplus.
    controller = (
        kron(p0, sp.eye(2), data_identity)
        + kron(p1, p0, data_product(ia, bplus))
        + kron(p1, p1, data_product(ia, bminus))
    )
    merging = h_z * controller * h_z * targets * record
    expected = kron(p0, sp.eye(2), data_identity) + kron(p1, sp.eye(2), unitary)
    clean_columns = [c * 2 * da * db + x for c in range(2) for x in range(da * db)]
    assert_equal(
        merging[:, clean_columns],
        expected[:, clean_columns],
        f"six-call merging failed for {example.name}, controller_first={controller_first}",
    )


def main() -> None:
    identity = sp.eye(2)
    x = sp.Matrix([[0, 1], [1, 0]])
    phase = sp.diag(1, sp.I)
    hadamard = sp.Matrix([[1, 1], [1, -1]]) / sp.sqrt(2)
    rotation = sp.Matrix(
        [[sp.Rational(3, 5), -sp.Rational(4, 5)],
         [sp.Rational(4, 5), sp.Rational(3, 5)]]
    )
    second_rotation = sp.Matrix(
        [[sp.Rational(5, 13), -sp.Rational(12, 13)],
         [sp.Rational(12, 13), sp.Rational(5, 13)]]
    )
    cnot = sp.Matrix([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 0, 1], [0, 0, 1, 0]])
    examples = [
        Example("Pauli and phase", x, phase, rotation, hadamard, sp.diag(1, 0)),
        Example("two rational rotations", hadamard, rotation, phase,
                second_rotation, sp.diag(1, 0)),
        Example("rotated phase sector", phase, second_rotation, hadamard,
                rotation, sp.diag(1, 0)),
        Example("four-dimensional target", cnot, sp.kronecker_product(hadamard, phase),
                rotation, second_rotation, sp.diag(1, 0)),
        Example("four-dimensional controller", x, rotation,
                cnot * sp.kronecker_product(rotation, identity),
                sp.kronecker_product(hadamard, phase), sp.diag(1, 1, 0, 0)),
    ]
    for example in examples:
        for controller_first in (False, True):
            check_example(example, controller_first)
    print(f"Exact six-call controlled merging passes on {2 * len(examples)} examples.")


if __name__ == "__main__":
    main()
