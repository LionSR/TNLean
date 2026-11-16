/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ClusterTruncationCutRank
import TNLean.MPS.AreaLaw.OperatorMPOFromCutRank
import TNLean.Lattice.ClusterExpansion.NormalizedPathTail

/-!
# A matrix product operator for the corrected label truncation

The tensors are constructed from the actual nearest-neighbour interactions through their
finite cluster sum. The same operator satisfies the proved energy-normalized approximation
bound. Supporting ALVV, arXiv:1602.08828v2, `thm:cluster`, lines 1298–1303 and 2014–2115.

**Local fix (cutoff and normalization):** this theorem uses connected interaction-label
components, and a supplied lower energy normalizes the error. It does not assert the false
printed physical-support approximation; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

namespace TNLean.MPS.AreaLaw

open Matrix SimpleGraph
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open TNLean.Lattice.ClusterExpansion

open Classical in
/-- The actual interaction-label truncation is represented by site-dependent operator tensors
of virtual dimension `r² q^r`. All ranks and tensors are constructed from the supported
interactions. Supporting the corrected label version of ALVV, arXiv:1602.08828v2,
`thm:cluster`, lines 1298–1303 and 2014–2115. -/
theorem exists_mpo_cluster_truncation {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (β : ℝ) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
        MPOTensor.traceChainOperator A 1 := by
  exact MPOTensor.exists_traceChainOperator_of_operatorSchmidtRank_le (by omega)
    (Nat.mul_le_mul (one_le_pow₀ hr) (one_le_pow₀ hq)) _
    (operatorSchmidtRank_cluster_truncation_all_cuts_le hq hr h hs β)

open Classical in
/-- The constructed matrix product operator obeys the corrected energy-normalized tail bound.
This uses the actual nearest-neighbour Hamiltonian, with arbitrary Hermitian interactions of
norm at most one and an explicit lower energy. Supporting a corrected version of ALVV,
arXiv:1602.08828v2, `thm:cluster-approx` and `thm:cluster`, lines 1270–1303. -/
theorem exists_mpo_cluster_approximation {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (lambda β : ℝ) (hlo : (lambda : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      truncatedExp (pathGraph N) (fun C ↦ r ≤ C.card) h β =
          MPOTensor.traceChainOperator A 1 ∧
      Real.exp (β * lambda) *
        ‖NormedSpace.exp (-(β • ∑ i, h i)) - MPOTensor.traceChainOperator A 1‖ ≤
          Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  obtain ⟨A, hA⟩ := exists_mpo_cluster_truncation hq hr h hs β
  refine ⟨A, hA, ?_⟩
  rw [← hA]
  exact norm_exp_sub_truncatedExp_pathGraph_le hr h hh hnorm lambda β hlo hβ hsmall

end TNLean.MPS.AreaLaw
