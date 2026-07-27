#!/usr/bin/env python3
"""SDP checks for P7 (static versus channel RFP).

The Choi convention is input-first:
    J(Phi) = sum_ab E_ab tensor Phi(E_ab).
All tensor products use NumPy/CVXPY's row-major Kronecker ordering.

Run with the isolated environment used in the accompanying report:
    /tmp/p7_sdp_venv/bin/python checks/round2_p7_sdp.py
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

import cvxpy as cp
import numpy as np


def partial_trace_output(J, n_in: int, n_out: int):
    """Trace the output factor of an input-first Choi matrix."""
    return cp.bmat([
        [sum(J[a*n_out+u, b*n_out+u] for u in range(n_out))
         for b in range(n_in)]
        for a in range(n_in)
    ])


def choi_action(J, Y: np.ndarray, n_in: int, n_out: int):
    """Phi(Y), using J[(a,u),(b,v)] = Phi(E_ab)[u,v]."""
    return cp.bmat([
        [sum(Y[a, b] * J[a*n_out+u, b*n_out+v]
             for a in range(n_in) for b in range(n_in))
         for v in range(n_out)]
        for u in range(n_out)
    ])


def solve_channel(inputs, outputs, eps=2e-7, max_iters=200_000):
    """Find a CPTP map taking each input to the corresponding output."""
    n_in = inputs[0].shape[0]
    n_out = outputs[0].shape[0]
    J = cp.Variable((n_in*n_out, n_in*n_out), hermitian=True)
    constraints = [J >> 0, partial_trace_output(J, n_in, n_out) == np.eye(n_in)]
    closure_constraints = []
    for Y, Z in zip(inputs, outputs):
        c = choi_action(J, Y, n_in, n_out) == Z
        constraints.append(c)
        closure_constraints.append(c)
    prob = cp.Problem(cp.Minimize(0), constraints)
    value = prob.solve(solver="SCS", eps=eps, max_iters=max_iters,
                       acceleration_lookback=20, verbose=False)
    out = {"status": prob.status, "value": value, "n_in": n_in, "n_out": n_out}
    if J.value is not None:
        Jh = (J.value + J.value.conj().T) / 2
        out["min_choi_eig"] = float(np.linalg.eigvalsh(Jh).min())
        out["tp_residual"] = float(np.max(np.abs(
            np.array(partial_trace_output(cp.Constant(Jh), n_in, n_out).value)
            - np.eye(n_in))))
        out["closure_residual"] = float(max(
            np.max(np.abs(np.array(choi_action(cp.Constant(Jh), Y, n_in, n_out).value) - Z))
            for Y, Z in zip(inputs, outputs)))
        out["choi"] = Jh
    out["closure_duals"] = [None if c.dual_value is None else np.asarray(c.dual_value)
                            for c in closure_constraints]
    return out


def mk_closures(M: np.ndarray, k: int):
    """Return [M_k(E_pq)] in p,q lexicographic order.

    M has shape (D,D,d,d). For E_pq the virtual path starts at q and ends at p.
    """
    D, _, d, _ = M.shape
    ans = []
    for p in range(D):
        for q in range(D):
            cur = {(q,): np.array([[1.0 + 0j]])}
            for _step in range(k):
                nxt = {}
                for path, op in cur.items():
                    a = path[-1]
                    for b in range(D):
                        nxt[path + (b,)] = np.kron(op, M[a, b])
                cur = nxt
            total = np.zeros((d**k, d**k), dtype=complex)
            for path, op in cur.items():
                if path[-1] == p:
                    total += op
            ans.append(total)
    return ans


def test_pair(M: np.ndarray, k_small=1, k_large=2, **solver_kw):
    small = mk_closures(M, k_small)
    large = mk_closures(M, k_large)
    forward = solve_channel(small, large, **solver_kw)
    reverse = solve_channel(large, small, **solver_kw)
    return {"forward": strip_arrays(forward), "reverse": strip_arrays(reverse)}


def strip_arrays(x):
    if isinstance(x, dict):
        return {k: strip_arrays(v) for k, v in x.items() if k not in {"choi", "closure_duals"}}
    if isinstance(x, np.ndarray):
        return x.tolist()
    return x


def product_tensor(rho=None):
    if rho is None:
        rho = np.diag([0.7, 0.3])
    M = np.zeros((1, 1, 2, 2), dtype=complex)
    M[0, 0] = rho
    return M


def toric_tensor(q: float, normalized=True):
    """Diagonal virtual tensor. normalized=True inserts the necessary 1/2."""
    I = np.eye(2)
    Z = np.diag([1.0, -1.0])
    scale = 0.5 if normalized else 1.0
    M = np.zeros((2, 2, 2, 2), dtype=complex)
    M[0, 0] = scale * I
    M[1, 1] = scale * q * Z
    return M


def verify_toric_closures():
    """Regression tests for the virtual-index and normalization conventions."""
    q = 0.5
    M = toric_tensor(q)
    Z = np.diag([1.0, -1.0])
    for k in (1, 2, 3):
        closures = mk_closures(M, k)
        Zk = Z.copy()
        for _ in range(k - 1):
            Zk = np.kron(Zk, Z)
        assert np.allclose(closures[0], np.eye(2**k) / 2**k)
        assert np.allclose(closures[3], q**k * Zk / 2**k)
        assert np.allclose(closures[1], 0) and np.allclose(closures[2], 0)


def compact(result):
    def one(r):
        return {
            "status": r["status"],
            "min_eig": r.get("min_choi_eig"),
            "tp_res": r.get("tp_residual"),
            "closure_res": r.get("closure_residual"),
        }
    return {direction: one(result[direction]) for direction in ["forward", "reverse"]}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="checks/round2_p7_sdp_results.json")
    parser.add_argument("--quick", action="store_true")
    args = parser.parse_args()

    verify_toric_closures()
    results = {}
    results["product_1to2"] = compact(test_pair(product_tensor(), 1, 2))
    # The tensor printed in the derivation note lacks the normalization required
    # by trace preservation. Keep this as a deliberate diagnostic.
    results["toric_q1_as_printed_1to2"] = compact(test_pair(toric_tensor(1, False), 1, 2))
    results["toric_q1_normalized_1to2"] = compact(test_pair(toric_tensor(1, True), 1, 2))
    results["toric_q1_normalized_2to3"] = compact(test_pair(toric_tensor(1, True), 2, 3))

    qs = [0.0, 0.25, 0.5, 0.75, 1.0] if args.quick else [
        -1.0, -0.9, -0.75, -0.5, -0.25, -0.1, 0.0,
        0.1, 0.25, 0.5, 0.75, 0.9, 1.0
    ]
    scan = {}
    for q in qs:
        entry = {"1to2": compact(test_pair(toric_tensor(q), 1, 2))}
        entry["2to3"] = compact(test_pair(toric_tensor(q), 2, 3))
        scan[str(q)] = entry
        print(q, json.dumps(entry, sort_keys=True))
    results["normalized_toric_scan"] = scan

    path = Path(args.output)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(results, indent=2, sort_keys=True) + "\n")
    print(f"wrote {path}")


if __name__ == "__main__":
    main()
