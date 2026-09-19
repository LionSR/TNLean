"""Exact initial tests for the intrinsic-RFP next-target assessment.

Run from the repository root:
    python3 docs/audits/rfp_intrinsic/checks/next_targets.py
Requires SymPy. No random trials, data files, or generated source artifacts.
These checks do not replace the all-length arguments in next_targets.tex.
"""
from collections import Counter
from itertools import product

import sympy as sp


def fibonacci_purity():
    phi = (1 + sp.sqrt(5)) / 2
    records = []
    for t in (sp.Rational(1, 2), sp.Rational(2, 3)):
        z = (phi + 2) * (1 + phi * t)
        a = (1 + phi**2 * t**2) / z**2
        c = (phi**2 + (1 + phi**2) * t**2) / z**2
        transition = sp.Matrix([[a, c], [c, a + c]])
        plus, minus = a + phi * c, a - c / phi
        moments = []
        for n in range(1, 7):
            recurrence = (sp.Matrix([[7, phi**-4]]) * transition**n
                          * sp.Matrix([1, 0]))[0]
            formula = 2 * plus**n + 5 * minus**n
            assert sp.simplify(recurrence - formula) == 0
            moments.append(sp.simplify(formula))
        curvature = sp.simplify(moments[0] * moments[2] / moments[1]**2)
        records.append(curvature)
        print(f"Fibonacci t={t}: curvature={sp.N(curvature, 16)}; "
              "exact recurrence verified for N=1,...,6")
    assert sp.simplify(records[0] - records[1]) != 0
    r = sp.symbols('r', real=True)
    q = sp.Rational(5, 2)
    lhs = (1 + q*r)*(1 + q*r**3)/(1 + q*r**2)**2 - 1
    rhs = q*r*(1-r)**2/(1 + q*r**2)**2
    assert sp.cancel(lhs - rhs) == 0


def weighted_path_counts(group_order):
    """Near-group shape x*x=sum_g g+2*x, reciprocal x-channel weights."""
    x = group_order
    labels = range(group_order + 1)

    def fusion(a, b):
        if a != x and b != x:
            return {((a+b) % group_order): 1}
        if a != x or b != x:
            return {x: 1}
        return {**{g: 1 for g in range(group_order)}, x: 2}

    def weight(a, b, c, copy):
        return (1 if copy == 0 else -1) if a == b == c == x else 0

    histogram = Counter()
    entries = 0
    for a, b, c, d in product(labels, repeat=4):
        left, right = [], []
        for e, multiplicity in fusion(a, b).items():
            for i in range(multiplicity):
                for j in range(fusion(e, c).get(d, 0)):
                    left.append(weight(a,b,e,i) + weight(e,c,d,j))
        for f, multiplicity in fusion(b, c).items():
            for i in range(multiplicity):
                for j in range(fusion(a, f).get(d, 0)):
                    right.append(weight(b,c,f,i) + weight(a,f,d,j))
        assert Counter(left) == Counter(right)
        if left:
            histogram[len(left)] += 1
            entries += sum(v*v for v in Counter(left).values())
    expected = (Counter({1: 81, 2: 12, 7: 1}), 132) if group_order == 3 else (
        Counter({1: 32, 2: 8, 6: 1}), 66)
    assert (histogram, entries) == expected
    print(f"Z{group_order} near-group: block dimensions {dict(histogram)}, "
          f"weight-compatible entries {entries}; no pentagon solution claimed")


def pauli_refinement_obstruction():
    identity = sp.eye(2)
    pauli_x = sp.Matrix([[0, 1], [1, 0]])
    pauli_y = sp.Matrix([[0, -sp.I], [sp.I, 0]])
    pauli_z = sp.diag(1, -1)
    active = [identity/2, pauli_x/2]
    scalar = [pauli_y/2, pauli_z/2]
    tau = sp.diag(sp.Rational(1, 3), sp.Rational(2, 3))
    pairs = list(product(range(2), repeat=2))
    letters = {}
    for alpha, (u, up) in enumerate(pairs):
        for beta, (v, vp) in enumerate(pairs):
            logical = sp.Matrix([[a[u,v]*sp.conjugate(b[up,vp])
                                  for b in active] for a in active])
            letter = sp.zeros(5)
            letter[:4, :4] = sp.kronecker_product(logical, tau)
            letter[4, 4] = sum(b[u,v]*sp.conjugate(b[up,vp]) for b in scalar)
            letters[alpha, beta] = letter
    indices = list(product(range(4), repeat=2))
    traces = sp.Matrix(4, 4, lambda a,b: sp.trace(letters[a,b]))
    assert traces**2 == traces
    blocked = {(a,b): sum((sp.kronecker_product(letters[a,k], letters[k,b])
                           for k in range(4)), sp.zeros(25)) for a,b in indices}
    one = sp.Matrix.hstack(*(letters[a,b].reshape(25,1) for a,b in indices))
    two = sp.Matrix.hstack(*(blocked[a,b].reshape(625,1) for a,b in indices))
    assert one.rank() == 5 and two.rank() == 6
    assert letters[1,0] == letters[0,1]
    residual = blocked[1,0] - blocked[0,1]
    assert residual[4,14] == sp.Rational(1,24)
    print("Pauli seed: trace matrix idempotent, ranks 5 -> 6; "
          "M[1,0]=M[0,1] but blocked residual[4,14]=1/24. "
          "No linear refinement exists.")


if __name__ == '__main__':
    fibonacci_purity()
    weighted_path_counts(3)
    weighted_path_counts(2)
    pauli_refinement_obstruction()
    print("All exact checks passed.")
