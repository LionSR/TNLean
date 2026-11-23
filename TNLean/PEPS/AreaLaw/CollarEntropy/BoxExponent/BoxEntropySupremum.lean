/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Polygons.SafeRectangles.InitialBoxEstimate
import QICLean.ManyBody.Hamiltonian.GroundSpace

/-!
# From physical rectangle estimates to the uniform box supremum

The current box power applies to every safe physical rectangle, including the
zero-size case. Conversely, a large-rectangle original-state bound extends to
all sizes by the finite-dimensional entropy bound before taking the supremum.
Neither bridge constructs the physical entropy improvement.

Source: OpenAI area-law manuscript, `02-initial.tex`, lines 590--594, and
`08-scanner.tex`, lines 788--803,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace PlaneInteraction)

open ManyBody (IntRect IsSafe rectRegion)

namespace TNLean.PEPS.AreaLaw

/-- A uniform positive-scale box power supplies every physical rectangle,
including a possible zero-size rectangle. Source: `02-initial.tex`, lines 590--594. -/
theorem regionEntropy_le_of_boxEntropy_power
    {q R D₀ : ℕ} (hq : 1 ≤ q) {J Δ C e : ℝ} (he : 0 < 1 + e)
    (hbox : ∀ r : ℕ, 1 ≤ r → boxEntropy q R J Δ D₀ r ≤ C * (r : ℝ) ^ (1 + e))
    {Λ : Finset (ℤ × ℤ)} (h : PlaneInteraction Λ q R) (hh : ∀ X, (h.term X).IsHermitian)
        (hhJ : ∀ X, ‖h.term X‖ ≤ J) {E₀ : ℝ}
    {Ω : EuclideanSpace ℂ (↥Λ → Fin q)} (hΩ : ‖Ω‖ = 1) (hgap : IsGapped h.hamiltonian E₀ Δ)
    (hspan : groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω})
    (A : Finset ↥Λ) (Q : IntRect) (hsafe : IsSafe Λ A D₀ Q) :
    ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ (1 + e) := by
  by_cases hs : 1 ≤ Q.size
  · exact (regionEntropy_le_boxEntropy hq h hh hhJ hΩ hgap hspan hsafe le_rfl).trans
      (hbox Q.size hs)
  · have hs0 : Q.size = 0 := by omega
    have hcard : (rectRegion A Q).card = 0 :=
      Nat.le_zero.mp (by
        simpa only [hs0, zero_pow (by decide : 2 ≠ 0)] using card_rectRegion_le A Q)
    simpa only [hcard, Nat.cast_zero, zero_mul, hs0, Real.zero_rpow he.ne', mul_zero] using
      ManyBody.regionEntropy_le_card_mul_log hΩ (rectRegion A Q)

/-- A uniform large-rectangle bound extends across all small sizes and then
bounds the literal supremum. The new constant precedes every positive scale.
The small-size correction uses only the physical volume entropy bound.
Source: `08-scanner.tex`, lines 788--803. -/
theorem boxEntropy_power_le_of_large_rectangles
    {q R D₀ : ℕ} (hq : 1 ≤ q) {J Δ C p : ℝ} (hC : 0 ≤ C) (hp : 0 ≤ p) (N : ℕ)
    (hrect : ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
        (_ : ∀ X, ‖h.term X‖ ≤ J)
      (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
      groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
      ∀ (A : Finset ↥Λ) (Q : IntRect), IsSafe Λ A D₀ Q → N ≤ Q.size →
        ManyBody.regionEntropy Ω (rectRegion A Q) ≤ C * (Q.size : ℝ) ^ p) :
    ∀ r : ℕ, 1 ≤ r →
      boxEntropy q R J Δ D₀ r ≤
        (C + (N : ℝ) ^ 2 * Real.log q + 1) * (r : ℝ) ^ p := by
  let V := (N : ℝ) ^ 2 * Real.log q
  have hlq : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg (by exact_mod_cast hq)
  have hV : 0 ≤ V := mul_nonneg (sq_nonneg _) hlq
  intro r hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hpow : 1 ≤ (r : ℝ) ^ p := Real.one_le_rpow hr1 hp
  refine Real.sSup_le ?_ (by positivity)
  intro s hs
  obtain ⟨Λ, h, hh, hhJ, E₀, Ω, A, Q, hΩ, hgap, hspan, hsafe, hQr, rfl⟩ := hs
  by_cases hN : N ≤ Q.size
  · have hlarge := hrect Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe hN
    have hscale : (Q.size : ℝ) ^ p ≤ (r : ℝ) ^ p :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr hQr) hp
    exact hlarge.trans ((mul_le_mul_of_nonneg_left hscale hC).trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + V + 1)
        (Real.rpow_nonneg (Nat.cast_nonneg r) p)))
  · have hsmall : (rectRegion A Q).card ≤ N ^ 2 :=
      (card_rectRegion_le A Q).trans (Nat.pow_le_pow_left (by omega) 2)
    have hsmallR : ((rectRegion A Q).card : ℝ) ≤ (N : ℝ) ^ 2 := by exact_mod_cast hsmall
    have hbound : ManyBody.regionEntropy Ω (rectRegion A Q) ≤ V :=
      (ManyBody.regionEntropy_le_card_mul_log hΩ _).trans
        (mul_le_mul_of_nonneg_right hsmallR hlq)
    exact hbound.trans ((le_mul_of_one_le_right hV hpow).trans
      (mul_le_mul_of_nonneg_right (by linarith : V ≤ C + V + 1)
        (Real.rpow_nonneg (Nat.cast_nonneg r) p)))

end TNLean.PEPS.AreaLaw
