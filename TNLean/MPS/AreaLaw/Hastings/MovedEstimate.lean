/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.GaussianTimeAverage

/-!
# The cut-offs next to the Gaussian time average

This file is eq. `moved` of the proof of Lemma 1 of Hastings, *An area law for one-dimensional
quantum systems* (arXiv:0705.2024v4, `References/0705.2024/law16.tex`, lines 865–876): the
Gaussian time average `P_q(M)` of a Hermitian perturbation `M` of a gapped Hamiltonian `H`,
restricted to the range of two commuting cut-offs `O_L`, `O_R`, is close to the ground-state
projector `P₀ = |Ω⟩⟨Ω|`.

Writing `A = P_q(M)` and `B = O_L O_R`, the estimate splits as
`A B - P₀ = (A - P₀) B + (P₀ B - P₀)`. The first term is bounded by the gap-plus-perturbation
estimate `norm_gaussianTimeAverage_sub_groundProjector_le_add` times `‖B‖ ≤ 1`, and the second
by the overlap `η` of `Ω` with `B Ω`: since `B` and `P₀` are self-adjoint, taking adjoints turns
`P₀ B - P₀` into `B P₀ - P₀`, which acts by `x ↦ ⟨Ω, x⟩ (B Ω - Ω)` and so has norm at most
`‖B Ω - Ω‖ ≤ η`.

## Main results

* `TNLean.MPS.AreaLaw.Hastings.norm_gaussianTimeAverage_mul_mul_sub_groundProjector_le`:
  `‖P_q(M) O_L O_R - |Ω⟩⟨Ω|‖ ≤ exp(-q/2) + √q / ΔE · δ + η`, for `‖M - H‖ ≤ δ` and
  `‖Ω - O_L O_R Ω‖ ≤ η`.

## References

* M. B. Hastings, *An area law for one-dimensional quantum systems*, J. Stat. Mech. (2007)
  P08024, arXiv:0705.2024v4, `law16.tex`, lines 865–876.
-/

open Matrix
open scoped InnerProductSpace Matrix.Norms.L2Operator NNReal ComplexOrder

namespace TNLean.MPS.AreaLaw.Hastings

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **The cut-offs next to the time average.** Let `H` be Hermitian with a gapped ground vector
`Ω` of energy `0` and gap `ΔE > 0`, let `M` be Hermitian with `‖M - H‖ ≤ δ`, and let `O_L`,
`O_R` be commuting orthogonal projections with `‖Ω - O_L O_R Ω‖ ≤ η`. Then the Gaussian time
average `P_q(M)` restricted to the range of `O_L O_R` is close to the ground-state projector:
`‖P_q(M) O_L O_R - |Ω⟩⟨Ω|‖ ≤ exp(-q/2) + √q / ΔE · δ + η`.
Hastings, arXiv:0705.2024v4, `law16.tex`, lines 865–876. -/
theorem norm_gaussianTimeAverage_mul_mul_sub_groundProjector_le {M H : Matrix n n ℂ}
    (hM : M.IsHermitian) (hH : H.IsHermitian) {ΔE : ℝ} {Ω : EuclideanSpace ℂ n}
    (hΩ : IsGappedGroundState H 0 Ω ΔE) (hΔ : 0 < ΔE) {OL OR : Matrix n n ℂ}
    (hOL : IsStarProjection OL) (hOR : IsStarProjection OR) (hcomm : Commute OL OR) (q : ℝ)
    {δ η : ℝ} (hδ : ‖M - H‖ ≤ δ) (hη : ‖Ω - toEuclideanLin (OL * OR) Ω‖ ≤ η) :
    ‖gaussianTimeAverage q ΔE M * (OL * OR) -
        vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
      Real.exp (-q / 2) + Real.sqrt q / ΔE * δ + η := by
  have hΩnorm : ‖Ω‖ = 1 := hΩ.1
  have hη0 : (0 : ℝ) ≤ η := (norm_nonneg _).trans hη
  have hc : (0 : ℝ) ≤ Real.sqrt q / ΔE := div_nonneg (Real.sqrt_nonneg q) hΔ.le
  -- the perturbed gap estimate, with `‖M - H‖` relaxed to `δ`
  have hA : ‖gaussianTimeAverage q ΔE M -
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))‖ ≤
      Real.exp (-q / 2) + Real.sqrt q / ΔE * δ :=
    (norm_gaussianTimeAverage_sub_groundProjector_le_add hM hH hΩ hΔ q).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left hδ hc) _)
  -- `O_L O_R` is a self-adjoint contraction
  have hOLc : OLᴴ = OL := by rw [← star_eq_conjTranspose]; exact hOL.isSelfAdjoint.star_eq
  have hORc : ORᴴ = OR := by rw [← star_eq_conjTranspose]; exact hOR.isSelfAdjoint.star_eq
  have hBconj : (OL * OR)ᴴ = OL * OR := by rw [conjTranspose_mul, hORc, hOLc, ← hcomm.eq]
  have hB1 : ‖OL * OR‖ ≤ 1 :=
    (norm_mul_le _ _).trans (by nlinarith [hOL.norm_le, hOR.norm_le, norm_nonneg OL])
  -- the ground-state projector and its action
  have hPact : ∀ y : EuclideanSpace ℂ n, toEuclideanCLM (n := n) (𝕜 := ℂ)
      (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω))) y = ⟪Ω, y⟫_ℂ • Ω :=
    fun y => toEuclideanLin_vecMulVec_star_self_apply Ω y
  have hPconj : (vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))ᴴ =
      vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) := by
    rw [conjTranspose_vecMulVec, star_star]
  set A := gaussianTimeAverage q ΔE M with hAdef
  set P := vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)) with hPdef
  -- `‖P₀ O_L O_R - P₀‖ ≤ η`, via the adjoint `O_L O_R P₀ - P₀`
  have hkey : ‖P * (OL * OR) - P‖ ≤ η := by
    rw [← l2_opNorm_conjTranspose, conjTranspose_sub, conjTranspose_mul, hBconj, hPconj,
      cstar_norm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ hη0 fun x => ?_
    have happ : toEuclideanCLM (n := n) (𝕜 := ℂ) ((OL * OR) * P - P) x =
        ⟪Ω, x⟫_ℂ • (toEuclideanCLM (n := n) (𝕜 := ℂ) (OL * OR) Ω - Ω) := by
      rw [map_sub, map_mul, _root_.sub_apply, mul_apply_eq_comp, hPact x, map_smul, ← smul_sub]
    rw [happ, norm_smul]
    calc ‖⟪Ω, x⟫_ℂ‖ * ‖toEuclideanCLM (n := n) (𝕜 := ℂ) (OL * OR) Ω - Ω‖
        ≤ ‖Ω‖ * ‖x‖ * η := by
          gcongr
          · exact norm_inner_le_norm _ _
          · rw [norm_sub_rev]; exact hη
      _ = η * ‖x‖ := by rw [hΩnorm]; ring
  -- assemble
  have hsplit : A * (OL * OR) - P = (A - P) * (OL * OR) + (P * (OL * OR) - P) := by noncomm_ring
  calc ‖A * (OL * OR) - P‖
      = ‖(A - P) * (OL * OR) + (P * (OL * OR) - P)‖ := by rw [hsplit]
    _ ≤ ‖(A - P) * (OL * OR)‖ + ‖P * (OL * OR) - P‖ := norm_add_le _ _
    _ ≤ ‖A - P‖ * ‖OL * OR‖ + ‖P * (OL * OR) - P‖ := by gcongr; exact norm_mul_le _ _
    _ ≤ ‖A - P‖ * 1 + η := add_le_add (mul_le_mul_of_nonneg_left hB1 (norm_nonneg _)) hkey
    _ ≤ Real.exp (-q / 2) + Real.sqrt q / ΔE * δ + η := by
        rw [mul_one]; exact add_le_add_right hA η

end TNLean.MPS.AreaLaw.Hastings
