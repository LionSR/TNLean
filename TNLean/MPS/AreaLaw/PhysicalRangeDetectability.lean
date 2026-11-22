/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.SupportProjection
import TNLean.MPS.AreaLaw.PhysicalDetectabilityGap
import QICLean.Analysis.WeightedProjection

/-!
# Detectability after replacing positive contractions by range projections

For a positive nearest-neighbour chain, replace each term by the orthogonal
projection onto its range. The replacement preserves physical supports and
the whole zero-energy kernel and increases the Hamiltonian in operator order.
The physical even/odd product therefore contracts the orthogonal complement
of the original kernel with its original gap. This is the reduction in ALVV,
arXiv:1602.08828v2, Section 6.1, lines 1457–1460, followed by `lem:dl`.
-/

open Matrix
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q : ℕ}

/-- Range projections of the actual positive local terms give the detectability
contraction for the original spectral gap and the full original ground kernel.
ALVV, arXiv:1602.08828v2, Section 6.1, lines 1457–1460, and `lem:dl`. -/
theorem norm_sq_physicalDetectability_supportProj_le
    (Φ : ManyBody.BondInteraction L q)
    (hh : ∀ i, (Φ.term i).PosSemidef) (hn : ∀ i, ‖Φ.term i‖ ≤ 1)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ e ∈ spectrum ℝ Φ.hamiltonian, e = 0 ∨ gamma ≤ e)
    {x : EuclideanSpace ℂ (Fin L → Fin q)}
    (horth : ∀ z : EuclideanSpace ℂ (Fin L → Fin q),
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0 →
        ⟪z, x⟫_ℂ = 0) :
    ‖physicalDetectability (Φ.supportProj hh) x‖ ^ 2 ≤ (4 / (4 + gamma)) * ‖x‖ ^ 2 := by
  let PΦ := Φ.supportProj hh
  have hp := ManyBody.Interaction.isStarProjection_supportProj_term Φ hh
  have hker (z : EuclideanSpace ℂ (Fin L → Fin q)) :
      Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) PΦ.hamiltonian z = 0 ↔
        Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0 := by
    have hk := ManyBody.Interaction.hamiltonian_supportProj_mulVec_eq_zero_iff Φ hh
      (WithLp.ofLp z)
    simpa only [← Matrix.ofLp_toEuclideanCLM, WithLp.ofLp_eq_zero] using hk
  have hdom : Φ.hamiltonian ≤ PΦ.hamiltonian :=
    ManyBody.Interaction.hamiltonian_le_hamiltonian_supportProj Φ hh hn
  set y := physicalDetectability PΦ x
  have hyorth (z : EuclideanSpace ℂ (Fin L → Fin q))
      (hz : Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian z = 0) :
      ⟪z, y⟫_ℂ = 0 :=
    (inner_physicalDetectability_eq PΦ hp ((hker z).mpr hz) x).trans (horth z hz)
  have hH : Φ.hamiltonian.IsHermitian :=
    (isSelfAdjoint_sum _ fun i _ ↦ (hh i).isHermitian.isSelfAdjoint).isHermitian
  have hlo := hH.mul_norm_sq_le_re_inner_of_spectral_gap hgap y hyorth
  have henergy : (⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) PΦ.hamiltonian y⟫_ℂ).re ≤
      4 * (‖x‖ ^ 2 - ‖y‖ ^ 2) :=
    re_inner_physicalDetectability_le PΦ hp x
  have hcomparison :
      (⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) Φ.hamiltonian y⟫_ℂ).re ≤
        (⟪y, Matrix.toEuclideanCLM (𝕜 := ℂ) (n := Fin L → Fin q) PΦ.hamiltonian y⟫_ℂ).re := by
    have hc := (ContinuousLinearMap.le_def.mp
      (Matrix.toEuclideanCLM_le_of_le hdom)).re_inner_nonneg_right y
    exact sub_nonneg.mp (by
      simpa only [_root_.sub_apply, inner_sub_right, map_sub, RCLike.re_to_complex] using hc)
  rw [div_mul_eq_mul_div, le_div_iff₀ (show 0 < 4 + gamma by linarith only [hgamma])]
  nlinarith only [hlo, henergy, hcomparison]

end TNLean.MPS.AreaLaw
