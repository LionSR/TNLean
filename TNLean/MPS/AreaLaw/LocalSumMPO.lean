/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.OperatorMPOFromCutRank
import QICLean.Entropy.SupportedOperatorSchmidtRank
import QICLean.Entropy.FilterStationarity
import QICLean.Algebra.OperatorSchmidtBounds

/-!
# Actual operator tensors for a local sum and a scalar

The support-square bound and the constructed all-cut representation give a polynomial exact
representation of the untruncated part of a soft Hamiltonian. Supporting ALVV,
arXiv:1602.08828v2, `def:soft-trunc` and `lem:exp-approx-eff`, lines 1178–1185 and 1262–1268.
-/

open Matrix

namespace TNLean.MPS.AreaLaw

/-- An actual sum of supported nearest-neighbour terms and a scalar identity has actual
site-dependent operator tensors of dimension at most one plus the number of terms times the
square of the local dimension. No Hermiticity or positivity is required. Supporting ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_local_sum_add_scalar_mpo {N q : ℕ} (hq : 1 ≤ q)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ}) (c : ℂ) :
    ∃ A : Fin (N + 1) → MPOTensor q (1 + N * q ^ 2),
      (∑ i, h i) + c • 1 = MPOTensor.traceChainOperator A 1 := by
  classical
  apply MPOTensor.exists_traceChainOperator_of_operatorSchmidtRank_le (by omega) (by omega)
  intro k
  let X := leftBlock (N + 1) k
  let φ := Matrix.reindexAlgEquiv ℂ ℂ (Entropy.cutEquiv (fun _ : Fin (N + 1) ↦ q) X)
  have hterm (i : Fin N) : operatorSchmidtRank (φ (h i)) ≤ q ^ 2 := by
    change operatorSchmidtRank (Entropy.cutOperator X (h i)) ≤ _
    exact ((hs i).operatorSchmidtRank_cutOperator_le_pow_card hq).trans
      (Nat.pow_le_pow_right hq Finset.card_le_two)
  have hsum : operatorSchmidtRank (∑ i, φ (h i)) ≤ N * q ^ 2 := by
    exact (operatorSchmidtRank_sum_le Finset.univ _).trans
      ((Finset.sum_le_sum fun i _ ↦ hterm i).trans_eq (by simp))
  have hId : operatorSchmidtRank (φ (1 : Matrix _ _ ℂ)) ≤ 1 := by
    change operatorSchmidtRank (Entropy.cutOperator X (1 : Matrix _ _ ℂ)) ≤ 1
    exact Entropy.IsSupportedOn.operatorSchmidtRank_cutOperator_le_one
      (Entropy.isSupportedOn_one (n := fun _ : Fin (N + 1) ↦ q) ∅)
      (Or.inl (Finset.empty_subset _))
  change operatorSchmidtRank (φ ((∑ i, h i) + c • 1)) ≤ _
  rw [map_add, map_sum, map_smul]
  exact (operatorSchmidtRank_add_le _ _).trans
    ((Nat.add_le_add hsum ((operatorSchmidtRank_smul_le _ _).trans hId)).trans_eq (by omega))

end TNLean.MPS.AreaLaw
