/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.SoftTruncationMPO
import QICLean.Analysis.ExponentialGeometricTailOrder

/-!
# A logarithmic cluster order for the actual soft-truncation MPO

Taking scale at least three times the positive order puts every required heat time in the strict
small-time regime. A logarithmic ceiling chooses the actual cluster order from the error
budget. Supporting a corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cutoff, normalization and parameters):** this is the corrected interaction-label
construction at scale at least three times the order, not the printed physical-support estimate
or a computational runtime result; see `docs/paper-gaps/alvv16_cluster_approximation.tex`.

**Scope restriction (scale at least three times the order):** ALVV `lem:exp-approx-eff`, lines
1262–1268, allows any scale with `t′ < (ln 2/2) t`; this module takes `t ≥ 3m`, a sub-case of
that range. See `docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The common heat-time ceiling is strictly inside the cluster-expansion
regime. Numerical auxiliary to ALVV, arXiv:1602.08828v2,
`lem:exp-approx-eff`, lines 1262–1268. -/
theorem softHeat_base_bounds :
    0 < 2 * (Real.exp (1 / 3 : ℝ) - 1) ∧ 2 * (Real.exp (1 / 3 : ℝ) - 1) < 1 := by
  have hl : (1 / 3 : ℝ) < Real.log (3 / 2) := by
    have h := Real.log_lt_sub_one_of_pos (x := (3 / 2 : ℝ)⁻¹)
      (by norm_num) (by norm_num)
    rw [Real.log_inv] at h
    norm_num at h
    linarith
  have he : Real.exp (1 / 3 : ℝ) < 3 / 2 :=
    (Real.exp_lt_exp.mpr hl).trans_eq (Real.exp_log (by norm_num))
  have h1 : 1 < Real.exp (1 / 3 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  constructor <;> linarith

/-- A completely specified logarithmic cluster order gives actual soft-truncation tensors at
any prescribed accuracy, using any scale at least three times the positive order. All heat
approximants and tensors are constructed from the original local interactions.
Supporting a corrected ALVV,
arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_softTruncation_mpo_of_accuracy {N q m : ℕ} (hq : 1 ≤ q) (hm : 0 < m)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps t xi : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i)
    (hscale : 3 * (m : ℝ) ≤ t) (hxi : 0 < xi) :
    let W := t * (2 : ℝ) ^ (m + 1)
    let b := 2 * (Real.exp (1 / 3 : ℝ) - 1)
    let r := max 1 ⌈(Real.log (max 1 ((N : ℝ) ^ 2)) -
      Real.log (Real.log (1 + xi / W))) / (-Real.log b)⌉₊
    ∃ A : Fin (N + 1) → MPOTensor q ((r ^ 2 * q ^ r) * (m + 1)),
      ‖cfc (Real.softTruncation t m) ((∑ i, h i) - (eps : ℂ) • 1) -
        MPOTensor.traceChainOperator A 1‖ ≤ xi := by
  intro W b r
  have hmR : 0 < (m : ℝ) := Nat.cast_pos.mpr hm
  have ht : 0 < t := lt_of_lt_of_le (by positivity) hscale
  have hratio : (m : ℝ) / t ≤ 1 / 3 := (div_le_iff₀ ht).mpr (by linarith only [hscale])
  have hb := softHeat_base_bounds
  have hbudget := Real.exponential_geometric_tail_order (N : ℝ) W b xi
    (by dsimp only [W]; positivity) hb.1 hb.2 hxi
  change 0 < r ∧ W * (Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1) ≤ xi at hbudget
  have hbase : 2 * (Real.exp ((m : ℝ) / t) - 1) ≤ b := by
    exact mul_le_mul_of_nonneg_left
      (sub_le_sub_right (Real.exp_le_exp.mpr hratio) 1) (by norm_num)
  obtain ⟨A, hA⟩ := exists_softTruncation_mpo_of_cluster_order (m := m) hq hbudget.1 h hs hh hnorm
    eps t hlo ht (hbase.trans hb.2.le)
  refine ⟨A, hA.trans ?_⟩
  calc
    (t * (2 : ℝ) ^ (m + 1)) *
        (Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp ((m : ℝ) / t) - 1)) ^ r) - 1)
        ≤ W * (Real.exp ((N : ℝ) ^ 2 * b ^ r) - 1) := by
          dsimp only [W]
          gcongr
          exact mul_nonneg (by norm_num)
            (sub_nonneg.mpr (Real.one_le_exp (by positivity)))
    _ ≤ xi := hbudget.2

end TNLean.MPS.AreaLaw
