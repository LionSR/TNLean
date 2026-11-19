#!/usr/bin/env python3
"""Exact endpoint audit of arXiv:2405.00439, Section V, `detectG`.

This is an executable calculation, not a Lean proof. It uses integer matrices
and signed permutations only. See the dated audit in docs/audits/.
"""

from __future__ import annotations

import itertools
import json
from dataclasses import dataclass


Matrix = tuple[tuple[int, int], tuple[int, int]]
I: Matrix = ((1, 0), (0, 1))
X: Matrix = ((0, 1), (1, 0))
Z: Matrix = ((1, 0), (0, -1))
NEG_I: Matrix = ((-1, 0), (0, -1))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def mul(a: Matrix, b: Matrix) -> Matrix:
    return (
        (a[0][0] * b[0][0] + a[0][1] * b[1][0],
         a[0][0] * b[0][1] + a[0][1] * b[1][1]),
        (a[1][0] * b[0][0] + a[1][1] * b[1][0],
         a[1][0] * b[0][1] + a[1][1] * b[1][1]),
    )


def dagger(a: Matrix) -> Matrix:
    # All entries in this calculation are real integers.
    return ((a[0][0], a[1][0]), (a[0][1], a[1][1]))


def matrix_product(factors: list[Matrix]) -> Matrix:
    value = I
    for factor in factors:
        value = mul(value, factor)
    return value


@dataclass(frozen=True)
class Geometry:
    a0: int
    a1: int
    a2: int
    b0: int
    b1: int
    b2: int

    @classmethod
    def from_ordered(cls, sites: tuple[int, ...], layout: str) -> Geometry:
        a0, low, high, b0, b2, b1 = sites
        a1, a2 = (high, low) if layout == "printed" else (low, high)
        return cls(a0, a1, a2, b0, b1, b2)

    def word(self, order: str) -> list[tuple[int, int, bool]]:
        # Entries are in written matrix-product order; the rightmost acts first.
        forward = [(self.a2, self.b2, False), (self.a1, self.b1, False),
                   (self.a0, self.b0, False)]
        if order == "increasing":
            forward.reverse()
        return [(self.a0, self.b1, True), (self.a2, self.b2, True),
                (self.a1, self.b0, True)] + forward


def local_factor(a: int, b: int, site: int, side: str, w: Matrix) -> Matrix:
    endpoint = a if side == "left" else b
    return mul(w if site == endpoint else I, X if a <= site <= b else I)


def detector_factors(g: Geometry, order: str, side: str, w: Matrix) -> list[Matrix]:
    factors = []
    for site in range(g.b1 + 2):
        word = []
        for a, b, adjoint in g.word(order):
            factor = local_factor(a, b, site, side, w)
            word.append(dagger(factor) if adjoint else factor)
        factors.append(matrix_product(word))
    return factors


def scalar_tensor(factors: list[Matrix]) -> int:
    """Return the scalar of a tensor product of I and -I, checking each factor."""
    sign = 1
    for factor in factors:
        require(factor in (I, NEG_I), f"Nonscalar local factor: {factor}")
        if factor == NEG_I:
            sign = -sign
    return sign


def expected_sign(order: str, side: str, w: Matrix) -> int:
    if w != Z:
        return 1
    return -1 if (order, side) in {
        ("chronological", "left"), ("increasing", "right")
    } else 1


def circuit_action(
    bits: int, size: int, interval: tuple[int, int] | None, side: str, adjoint: bool
) -> tuple[int, int]:
    """Apply retained two-site gates directly to a computational basis vector.

    The left circuit has layers (ZX) tensor X on even-odd pairs, then
    I tensor Z on odd-even pairs. The right circuit has X tensor (ZX),
    then Z tensor I. A gate is retained iff both its sites lie in the interval.
    The chain is periodic, while a supplied interval is a non-wrapping numeric
    interval with a <= b. A periodic-wrap bond is retained only when both of
    its sites belong to that numeric interval; no cyclic interval is inferred.
    """
    def contained(p: int, q: int) -> bool:
        return interval is None or (interval[0] <= p <= interval[1]
                                    and interval[0] <= q <= interval[1])

    gates: list[tuple[str, int]] = []
    for even in range(0, size, 2):
        odd = even + 1
        if contained(even, odd):
            gates.extend([("X", even), ("X", odd)])
            gates.append(("Z", even if side == "left" else odd))
    for odd in range(1, size, 2):
        even = (odd + 1) % size
        if contained(odd, even):
            gates.append(("Z", even if side == "left" else odd))
    if adjoint:
        gates.reverse()
    sign = 1
    for gate, site in gates:
        if gate == "X":
            bits ^= 1 << site
        elif (bits >> site) & 1:
            sign = -sign
    return bits, sign


def audit_circuits() -> int:
    size = 14
    # All left endpoints even and all right endpoints odd, with exterior sites.
    sites = (0, 2, 4, 7, 9, 11)
    evaluations = 0
    for side in ("left", "right"):
        for bits in range(1 << size):
            image, sign = circuit_action(bits, size, None, side, False)
            require(image == bits ^ ((1 << size) - 1) and sign == 1,
                    "Full circuit is not the claimed on-site symmetry")
        for layout in ("printed", "prose"):
            g = Geometry.from_ordered(sites, layout)
            for order in ("chronological", "increasing"):
                for bits in range(1 << size):
                    image, sign = bits, 1
                    for a, b, adjoint in reversed(g.word(order)):
                        image, step_sign = circuit_action(
                            image, size, (a, b), side, adjoint
                        )
                        sign *= step_sign
                    require(image == bits and sign == expected_sign(order, side, Z),
                            f"Circuit detector mismatch: {layout}, {order}, {side}")
                    evaluations += 1
    return evaluations


def audit_cyclic_orders() -> int:
    """Check clock/shift words via basis labels and root-of-unity exponents.

    For zeta=exp(2 pi i/m), u|q>=|q+1> and W|q>=zeta^q|q>.
    Exponents are integers modulo m; no roots are evaluated numerically.
    """
    evaluations = 0
    for m in range(2, 21):
        for layout in ("printed", "prose"):
            left = [0] + [2 * (m + 1 - r if layout == "printed" else r)
                          for r in range(1, m + 1)]
            right = [2 * m + 1] + [4 * m + 3 - 2 * r for r in range(1, m + 1)]
            # Written order of Y, then written chronological order of X.
            word = [(0, 1, True)]
            word += [(r, m + 2 - r, True) for r in range(m, 1, -1)]
            word += [(1, 0, True)]
            word += [(r, r, False) for r in range(m, -1, -1)]
            total_phase = 0
            for site in range(right[1] + 2):
                expected_phase = 0
                if site in left[1:]:
                    r = left.index(site)
                    expected_phase = (r if layout == "printed" else r - 1) % m
                for initial in range(m):
                    label, phase = initial, 0
                    for r, s, adjoint in reversed(word):
                        inside = left[r] <= site <= right[s]
                        endpoint = site == left[r]
                        if adjoint:
                            if endpoint:
                                phase -= label
                            if inside:
                                label = (label - 1) % m
                        else:
                            if inside:
                                label = (label + 1) % m
                            if endpoint:
                                phase += label
                    require(label == initial and phase % m == expected_phase,
                            f"Cyclic local word mismatch: {m}, {layout}, {site}")
                    evaluations += 1
                total_phase += expected_phase
            require(total_phase % m == (m * (m - 1) // 2) % m,
                    "Cyclic detector phase is not the triangular sum")
    return evaluations


def main() -> None:
    require(mul(X, X) == I and mul(Z, Z) == I, "Pauli involution failure")
    require(mul(Z, X) != mul(X, Z), "Pauli commutation failure")
    cases = 0
    for sites in itertools.combinations(range(9), 6):
        for layout, order, side, w in itertools.product(
            ("printed", "prose"), ("chronological", "increasing"),
            ("left", "right"), (I, X, Z)
        ):
            g = Geometry.from_ordered(sites, layout)
            actual = scalar_tensor(detector_factors(g, order, side, w))
            require(actual == expected_sign(order, side, w),
                    f"Local detector mismatch: {g}, {order}, {side}, {w}")
            cases += 1

    for gap in (1, 2, 5, 20, 100):
        sites = (0, 2 * gap, 4 * gap, 6 * gap + 1, 8 * gap + 1, 10 * gap + 1)
        for layout in ("printed", "prose"):
            g = Geometry.from_ordered(sites, layout)
            factors = detector_factors(g, "chronological", "left", Z)
            exceptional = [site for site, factor in enumerate(factors) if factor != I]
            require(exceptional == [max(g.a1, g.a2)],
                    "The left-endpoint defect is not at the claimed site")
            require(scalar_tensor(factors) == -1, "Separated counterexample failed")

    circuit_evaluations = audit_circuits()
    cyclic_evaluations = audit_cyclic_orders()
    print(json.dumps({
        "arithmetic": "integers and modular root-of-unity exponents; no floating point",
        "local_tensor_cases": cases,
        "complete_basis_circuit_detector_evaluations": circuit_evaluations,
        "circuit_sites": 14,
        "separation_parameters": [1, 2, 5, 20, 100],
        "cyclic_orders_checked": list(range(2, 21)),
        "cyclic_local_basis_evaluations": cyclic_evaluations,
        "cyclic_chronological_left_dressing": "-1 for even order; +1 for odd order",
        "detector_values_for_both_geometries": {
            "chronological_left_dressing": -1,
            "chronological_right_dressing": 1,
            "increasing_left_dressing": 1,
            "increasing_right_dressing": -1,
            "undressed_or_commuting_endpoint_dressing": 1,
        },
        "lean_verification": "not performed by this script",
    }, indent=2))


if __name__ == "__main__":
    main()
