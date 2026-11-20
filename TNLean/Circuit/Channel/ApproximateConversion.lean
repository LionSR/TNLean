/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormContractivity
import QICLean.Analysis.TraceNormVariational

/-!
# Trace norm on chain configurations

The trace norm of an operator on an `N`-site chain, after enumerating its configurations.
Approximate and asymptotic local channel conversions are QICLean's
`QuantumCircuit.IsApproxConversion` and `QuantumCircuit.IsAsymptoticConversion` at the ring
geometry `Geometry.ring N`.

## Main definitions

* `QuantumCircuit.chainTraceNorm` — trace norm of a matrix indexed by chain configurations.

## Main results

* `QuantumCircuit.chainTraceNorm_nonneg`, `QuantumCircuit.chainTraceNorm_add_le` —
  nonnegativity and the triangle inequality.

## References

* Piroli, Styliaris and Cirac, arXiv:2103.13367, paragraph "Phases of matter".
-/

open Matrix

noncomputable section

namespace QuantumCircuit

variable {d N : ℕ}

/-- Trace norm of a matrix on an `N`-site chain, after enumerating its configurations.
The trace norm is the sum of the singular values, not the ambient matrix norm. -/
def chainTraceNorm (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : ℝ :=
  traceNorm (equivReindexMap (Fintype.equivFin (Fin N → Fin d)) A)

theorem chainTraceNorm_nonneg (A : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    0 ≤ chainTraceNorm A := traceNorm_nonneg _

/-- Triangle inequality for the trace norm of chain operators. -/
theorem chainTraceNorm_add_le (A B : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) :
    chainTraceNorm (A + B) ≤ chainTraceNorm A + chainTraceNorm B := by
  simpa only [chainTraceNorm, map_add] using
    traceNorm_add_le (equivReindexMap (Fintype.equivFin _) A)
      (equivReindexMap (Fintype.equivFin _) B)

end QuantumCircuit
