/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.LocalSolution.SupersiteFinalState

/-!
# Comparing the final energy with the physical Hamiltonian

The truncated local terms approximate the original Hamiltonian in operator norm.
Thus the count of final states uses the gap of the original Hamiltonian; it does
not require a separate gap assumption for the truncated sum. Two expectation
values are compared, each at an error bounded by the norm of that difference.

This is the comparison in Hastings, arXiv:cond-mat/0508554v3, Section II,
lines 709–730, following the truncation estimate of lines 373–410.
-/

open Matrix
open scoped Matrix.Norms.L2Operator InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Operator-norm approximation controls the difference of energy expectations.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730. -/
theorem abs_re_inner_sub_le_norm_sub (H T : Matrix ι ι ℂ)
    (v : EuclideanSpace ℂ ι) :
    |(⟪v, toEuclideanLin H v⟫_ℂ).re - (⟪v, toEuclideanLin T v⟫_ℂ).re| ≤
      ‖H - T‖ * ‖v‖ ^ 2 := by
  rw [← Complex.sub_re, ← inner_sub_right, ← LinearMap.sub_apply, ← map_sub]
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_)
  calc ‖v‖ * ‖toEuclideanLin (H - T) v‖ ≤ ‖v‖ * (‖H - T‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left (Entropy.norm_toEuclideanLin_le (H - T) v) (norm_nonneg _)
    _ = ‖H - T‖ * ‖v‖ ^ 2 := by ring

/-- For a unit vector, the energy error is at most the operator-norm error.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730. -/
theorem abs_re_inner_sub_le_of_norm_sub_le {H T : Matrix ι ι ℂ} {δ : ℝ}
    (hHT : ‖H - T‖ ≤ δ) {v : EuclideanSpace ℂ ι} (hv : ‖v‖ = 1) :
    |(⟪v, toEuclideanLin H v⟫_ℂ).re - (⟪v, toEuclideanLin T v⟫_ℂ).re| ≤ δ := by
  simpa only [hv, one_pow, mul_one] using
    (abs_re_inner_sub_le_norm_sub H T v).trans
      (mul_le_mul_of_nonneg_right hHT (sq_nonneg ‖v‖))

/-- The gap of the original Hamiltonian suffices for the count of final states.
If the approximate sum has energy at most its expectation in a ground state plus
`η`, its final states have physical energy at most `E₀ + 2δ + η`.
Hastings, arXiv:cond-mat/0508554v3, lines 709–730. -/
theorem card_le_two_mul_re_trace_of_approximation {H T P : Matrix ι ι ℂ}
    (hP : IsStarProjection P) {E₀ Δ δ η : ℝ} (hΔ : 0 < Δ)
    (hgap : ∀ v : EuclideanSpace ℂ ι,
      Δ * (‖v‖ ^ 2 - (⟪v, toEuclideanLin P v⟫_ℂ).re) ≤
        (⟪v, toEuclideanLin H v⟫_ℂ).re - E₀ * ‖v‖ ^ 2)
    {Ψ : EuclideanSpace ℂ ι} (hΨ : ‖Ψ‖ = 1)
    (hE₀ : (⟪Ψ, toEuclideanLin H Ψ⟫_ℂ).re = E₀) (hHT : ‖H - T‖ ≤ δ)
    (hbudget : 2 * δ + η ≤ Δ / 2)
    {κ : Type*} {φ : κ → EuclideanSpace ℂ ι} (hφ : Orthonormal ℂ φ) (s : Finset κ)
    (henergy : ∀ j ∈ s, (⟪φ j, toEuclideanLin T (φ j)⟫_ℂ).re ≤
      (⟪Ψ, toEuclideanLin T Ψ⟫_ℂ).re + η) :
    (s.card : ℝ) ≤ 2 * (trace P).re := by
  refine card_le_two_mul_re_trace hP hΔ hgap hφ s ?_
  intro j hj
  change (⟪φ j, toEuclideanLin H (φ j)⟫_ℂ).re ≤ E₀ + Δ / 2
  linarith [(abs_le.mp (abs_re_inner_sub_le_of_norm_sub_le hHT hΨ)).1,
    (abs_le.mp (abs_re_inner_sub_le_of_norm_sub_le hHT (hφ.1 j))).2, henergy j hj]

end TNLean.MPS.AreaLaw.LocalSolution
