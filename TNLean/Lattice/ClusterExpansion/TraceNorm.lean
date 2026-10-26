/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.TraceNormVariational

/-!
# The trace-norm form of the cluster-expansion bound

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1281–1301), turns the bound of eq. `perc2` on
expectation values, `Z⁻¹ |Tr O ρ(β) − Tr O ρ(β, l_proj)| ≤ ε ‖O‖` for every operator `O`, into
the trace-norm bound `|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁`. The source chooses `O` diagonal in an
eigenbasis of the difference, with entries the signs of its eigenvalues.

This file proves the step for an arbitrary square matrix, without assuming it Hermitian. The
trace norm of `D` is `Tr √(Dᴴ D)`. QICLean's trace-norm duality
(`Matrix.re_trace_sqrt_conjTranspose_mul_self_le_of_forall_norm_trace_mul_le`) bounds it by the
bound on expectation values at the single operator `O = Uᴴ`, where `D = U √(Dᴴ D)` is the polar
decomposition. For Hermitian `D` this `Uᴴ` may be taken to be the source's sign operator.

## Main results

* `TNLean.Lattice.ClusterExpansion.re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le`: the
  source's form, `|ρ − σ|₁ ≤ ε Tr ρ` from `|Tr O ρ − Tr O σ| ≤ ε ‖O‖ Tr ρ`, for `ε ≥ 0`.

## References

* M. B. Hastings, *Solving gapped Hamiltonians locally*, Phys. Rev. B 73 (2006) 085115,
  arXiv:cond-mat/0508554v3, Section IV, lines 1281–1301.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.Lattice.ClusterExpansion

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The trace-norm form of eq. `perc2`.** Let `ρ` and `σ` be square matrices and `ε ≥ 0`. If
`|Tr O ρ − Tr O σ| ≤ ε ‖O‖ Tr ρ` for every matrix `O`, then the trace norm of `ρ − σ` is at
most `ε Tr ρ`. For the thermal state `ρ = ρ(β) = e^{-βH}`, which is positive, `Tr ρ = Z` is its
trace norm `|ρ(β)|₁`, and this is Hastings' bound
`|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁` with
`ε = exp(N (xy)⁻¹ e^{-l_proj/ξ_perc}) − 1` after the size-threshold correction recorded in
`docs/paper-gaps/hastings05_percolation_cluster_size.tex`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1281–1301. -/
theorem re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le {ρ σ : Matrix n n ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ.trace.re)
    (h : ∀ O : Matrix n n ℂ, ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re) :
    (CFC.sqrt ((ρ - σ)ᴴ * (ρ - σ))).trace.re ≤ ε * ρ.trace.re := by
  refine re_trace_sqrt_conjTranspose_mul_self_le_of_forall_norm_trace_mul_le fun O hO ↦ ?_
  rw [Matrix.mul_sub, Matrix.trace_sub]
  calc ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re := h O
    _ ≤ ε * 1 * ρ.trace.re := by gcongr
    _ = ε * ρ.trace.re := by ring

end TNLean.Lattice.ClusterExpansion
