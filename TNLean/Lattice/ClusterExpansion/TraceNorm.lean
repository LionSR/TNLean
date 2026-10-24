/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.PolarUnitaryCorrection

/-!
# The trace-norm form of the cluster-expansion bound

Hastings, *Solving gapped Hamiltonians locally* (arXiv:cond-mat/0508554v3,
`References/cond-mat_0508554/proj3new.tex`, lines 1281–1301), turns the bound of eq. `perc2` on
expectation values, `Z⁻¹ |Tr O ρ(β) − Tr O ρ(β, l_proj)| ≤ ε ‖O‖` for every operator `O`, into
the trace-norm bound `|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁`. The source chooses `O` diagonal in an
eigenbasis of the difference, with entries the signs of its eigenvalues.

This file proves the step for an arbitrary square matrix `D`, without assuming it Hermitian. The
trace norm of `D` is `Tr √(Dᴴ D)`. The polar decomposition `D = U √(Dᴴ D)` with `U` unitary
(`Matrix.exists_unitary_polar_correction`) gives `Tr (Uᴴ D) = Tr √(Dᴴ D)`, and `‖Uᴴ‖ ≤ 1`, so the
bound on expectation values at the single operator `O = Uᴴ` bounds the trace norm. For Hermitian
`D` this `Uᴴ` may be taken to be the source's sign operator.

## Main results

* `TNLean.Lattice.ClusterExpansion.re_trace_sqrt_le_of_forall_norm_trace_mul_le`: if
  `‖Tr (O D)‖ ≤ ε` for every `O` with `‖O‖ ≤ 1`, then `Tr √(Dᴴ D) ≤ ε`.
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

/-- A unitary matrix has operator norm at most one.

A local copy of a general fact about unitary matrices, kept here until QICLean provides it for
matrices over any finite index. -/
theorem l2OpNorm_le_one_of_mem_unitaryGroup {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ) :
    ‖U‖ ≤ 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [Subsingleton.elim U 0]
  · exact (CStarRing.norm_of_mem_unitary hU).le

/-- **Trace-norm duality from the polar decomposition.** If `‖Tr (O D)‖ ≤ ε` for every matrix
`O` of operator norm at most one, then the trace norm `Tr √(Dᴴ D)` of `D` is at most `ε`. No
Hermitian hypothesis on `D` is needed: the polar decomposition `D = U √(Dᴴ D)` gives
`Tr (Uᴴ D) = Tr √(Dᴴ D)` with `‖Uᴴ‖ ≤ 1`. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 1291–1297.

A local copy of the duality for an arbitrary finite index type. QICLean proves its `Fin D` form
(`Matrix.exists_mem_unitaryGroup_trace_conjTranspose_mul_eq`); this lemma is removed once QICLean
states that result for any finite index. -/
theorem re_trace_sqrt_le_of_forall_norm_trace_mul_le {D : Matrix n n ℂ} {ε : ℝ}
    (h : ∀ O : Matrix n n ℂ, ‖O‖ ≤ 1 → ‖(O * D).trace‖ ≤ ε) :
    (CFC.sqrt (Dᴴ * D)).trace.re ≤ ε := by
  obtain ⟨U, hD, -⟩ := exists_unitary_polar_correction D
  have hUU : star (U : Matrix n n ℂ) * U = 1 := Unitary.star_mul_self_of_mem U.2
  have hO : star (U : Matrix n n ℂ) * D = CFC.sqrt (Dᴴ * D) := by
    conv_lhs => rw [hD]
    rw [← Matrix.mul_assoc, hUU, Matrix.one_mul]
  have hnorm : ‖star (U : Matrix n n ℂ)‖ ≤ 1 :=
    l2OpNorm_le_one_of_mem_unitaryGroup (Unitary.star_mem U.2)
  calc (CFC.sqrt (Dᴴ * D)).trace.re ≤ ‖(CFC.sqrt (Dᴴ * D)).trace‖ := Complex.re_le_norm _
    _ = ‖(star (U : Matrix n n ℂ) * D).trace‖ := by rw [hO]
    _ ≤ ε := h _ hnorm

/-- **The trace-norm form of eq. `perc2`.** Let `ρ` and `σ` be square matrices and `ε ≥ 0`. If
`|Tr O ρ − Tr O σ| ≤ ε ‖O‖ Tr ρ` for every matrix `O`, then the trace norm of `ρ − σ` is at
most `ε Tr ρ`. For the thermal state `ρ = ρ(β) = e^{-βH}`, which is positive, `Tr ρ = Z` is its
trace norm `|ρ(β)|₁`, and this is Hastings' bound
`|ρ(β) − ρ(β, l_proj)|₁ ≤ ε |ρ(β)|₁` with `ε = exp(N e^{-l_proj/ξ_perc}) − 1`.
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1281–1301. -/
theorem re_trace_sqrt_sub_le_of_forall_norm_trace_mul_sub_le {ρ σ : Matrix n n ℂ} {ε : ℝ}
    (hε : 0 ≤ ε) (hρ : 0 ≤ ρ.trace.re)
    (h : ∀ O : Matrix n n ℂ, ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re) :
    (CFC.sqrt ((ρ - σ)ᴴ * (ρ - σ))).trace.re ≤ ε * ρ.trace.re := by
  refine re_trace_sqrt_le_of_forall_norm_trace_mul_le fun O hO ↦ ?_
  rw [Matrix.mul_sub, Matrix.trace_sub]
  calc ‖(O * ρ).trace - (O * σ).trace‖ ≤ ε * ‖O‖ * ρ.trace.re := h O
    _ ≤ ε * 1 * ρ.trace.re := by gcongr
    _ = ε * ρ.trace.re := by ring

end TNLean.Lattice.ClusterExpansion
