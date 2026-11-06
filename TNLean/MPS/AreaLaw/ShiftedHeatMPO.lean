/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ClusterTruncationMPO
import QICLean.Analysis.TraceExponentialPerturbation

/-!
# Constructed heat operators after a regional energy shift

The scalar shift is applied outside the local interactions. The proved energy-normalized
cluster estimate controls its effect exactly. Supporting the corrected interaction-label route
to ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268.

**Local fix (cluster cutoff and normalization):** this uses the corrected label selector and
normalized error, not the false printed physical-support estimate; see
`docs/paper-gaps/alvv16_cluster_approximation.tex`.
-/

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- Actual supported interactions and a lower energy produce actual tensors approximating the
heat operator of the shifted sum, without distributing the scalar shift among the local terms.
Supporting a corrected ALVV, arXiv:1602.08828v2, `lem:exp-approx-eff`, lines 1262–1268. -/
theorem exists_shifted_heat_mpo {N q r : ℕ} (hq : 1 ≤ q) (hr : 0 < r)
    (h : Fin N → Matrix (Fin (N + 1) → Fin q) (Fin (N + 1) → Fin q) ℂ)
    (hs : ∀ i, Entropy.IsSupportedOn (n := fun _ : Fin (N + 1) ↦ q)
      (h i) {i.castSucc, i.succ})
    (hh : ∀ i, (h i).IsHermitian) (hnorm : ∀ i, ‖h i‖ ≤ 1)
    (eps β : ℝ) (hlo : (eps : ℂ) • 1 ≤ ∑ i, h i) (hβ : 0 ≤ β)
    (hsmall : 2 * (Real.exp β - 1) ≤ 1) :
    ∃ A : Fin (N + 1) → MPOTensor q (r ^ 2 * q ^ r),
      ‖NormedSpace.exp (-(β • ((∑ i, h i) - (eps : ℂ) • 1))) -
          MPOTensor.traceChainOperator A 1‖ ≤
        Real.exp ((N : ℝ) ^ 2 * (2 * (Real.exp β - 1)) ^ r) - 1 := by
  classical
  obtain ⟨A, _hA, herr⟩ := exists_mpo_cluster_approximation hq hr h hs hh hnorm
    eps β hlo hβ hsmall
  let c : ℂ := (Real.exp (β * eps) : ℝ)
  obtain ⟨B, hB⟩ := MPOTensor.exists_traceChainOperator_one (by omega) A (c • 1)
  have hscaled : MPOTensor.traceChainOperator A (c • 1) =
      c • MPOTensor.traceChainOperator A 1 := by
    ext σ τ
    simp only [MPOTensor.traceChainOperator, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, Matrix.smul_apply]
  have hexp : NormedSpace.exp (-(β • ((∑ i, h i) - (eps : ℂ) • 1))) =
      c • NormedSpace.exp (-(β • ∑ i, h i)) := by
    have he : -(β • ((∑ i, h i) - (eps : ℂ) • 1)) =
        -(β • ∑ i, h i) + (β * eps) • (1 : Matrix _ _ ℂ) := by
      simp only [smul_sub, neg_sub]
      module
    rw [he, Matrix.exp_add_smul_one]
    rfl
  refine ⟨B, ?_⟩
  rw [hexp, ← hB, hscaled, ← smul_sub, norm_smul]
  simpa only [c, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using herr

end TNLean.MPS.AreaLaw
