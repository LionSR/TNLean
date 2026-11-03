/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ShiftedHeatMPO
import TNLean.MPS.MPDO.TraceChainLinearCombination
import QICLean.Analysis.SoftTruncationHeatExpansion

/-!
# Actual soft-truncation tensors from separate heat approximants

Each required heat operator is approximated directly by the constructed cluster MPO. The finite
weighted block sum has virtual dimension multiplied by the number of heat terms. Supporting a
corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cluster estimate):** the interaction-label selector and energy-normalized estimate
replace the false printed physical-support estimate; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`. No computational running time is asserted.
-/

open Matrix Finset
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual local interactions give actual soft-truncation tensors with an explicit coefficient
and cluster error budget. No heat approximation family or cut rank is supplied. Supporting the
corrected label route to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_softTruncation_mpo_of_cluster_order {N q r m : ℕ}
    (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps t : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i) (ht : 0 < t)
    (hsmall : 2 * (Real.exp ((m : ℝ) / t) - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q ((r ^ 2 * q ^ r) * (m + 1)),
      ‖cfc (Real.softTruncation t m) ((∑ i, h i) - (eps : ℂ) • 1) -
          MPOTensor.traceChainOperator A 1‖ ≤
        (t * (2 : ℝ) ^ (m + 1)) *
          (Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1) := by
  classical
  let U := (∑ i, h i) - (eps : ℂ) • (1 : Matrix (Fin (N + 1) → Fin q) _ ℂ)
  have hU : U.IsHermitian := (isHermitian_sum _ (fun i _ ↦ hh i)).sub
    (isHermitian_one.smul (by simp [isSelfAdjoint_iff]))
  have ha (a : Fin (m + 1)) : 0 ≤ (a.val : ℝ) / t ∧ (a.val : ℝ) / t ≤ (m : ℝ) / t := by
    constructor
    · positivity
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ a.isLt) ht.le
  have heach (a : Fin (m + 1)) := exists_shifted_heat_mpo hq hr h hs hh hnorm eps
    ((a.val : ℝ) / t) hlo (ha a).1
    ((mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr (ha a).2) 1) (by norm_num)).trans hsmall)
  choose A hA using heach
  obtain ⟨B, hB⟩ := MPOTensor.exists_traceChainOperator_linearCombination (by omega) A
    (fun a ↦ (Real.softTruncationHeatCoefficient t m a.val : ℂ))
  refine ⟨B, ?_⟩
  let δ := Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1
  have hb0 : 0 ≤ 2 * (Real.exp ((m : ℝ) / t) - 1) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
  have hδ : 0 ≤ δ := sub_nonneg.mpr (Real.one_le_exp (by positivity))
  have hA' (a : Fin (m + 1)) :
      ‖NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
        MPOTensor.traceChainOperator (A a) 1‖ ≤ δ := by
    apply (hA a).trans
    have hba : 0 ≤ 2 * (Real.exp ((a.val : ℝ) / t) - 1) :=
      mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_exp (ha a).1))
    dsimp only [δ]
    gcongr
    exact Nat.le_of_lt_succ a.isLt
  have hsoft := hU.cfc_softTruncation_eq_sum_heat t m
  rw [← Fin.sum_univ_eq_sum_range] at hsoft
  have hc := Real.sum_abs_softTruncationHeatCoefficient_le t m ht.le
  rw [← Fin.sum_univ_eq_sum_range] at hc
  rw [← hB]
  change ‖cfc (Real.softTruncation t m) U - _‖ ≤ _
  rw [hsoft]
  simp only [← Complex.coe_smul]
  rw [← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    _ ≤ ∑ a : Fin (m + 1), ‖(Real.softTruncationHeatCoefficient t m a.val : ℂ) •
        (NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
          MPOTensor.traceChainOperator (A a) 1)‖ := norm_sum_le _ _
    _ = ∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val| *
        ‖NormedSpace.exp (-(((a.val : ℝ) / t) • U)) -
          MPOTensor.traceChainOperator (A a) 1‖ := by
      simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val| * δ :=
      Finset.sum_le_sum fun a _ ↦ mul_le_mul_of_nonneg_left (hA' a) (abs_nonneg _)
    _ = (∑ a : Fin (m + 1), |Real.softTruncationHeatCoefficient t m a.val|) * δ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ (t * (2 : ℝ) ^ (m + 1)) * δ := mul_le_mul_of_nonneg_right hc hδ

end TNLean.MPS.AreaLaw
