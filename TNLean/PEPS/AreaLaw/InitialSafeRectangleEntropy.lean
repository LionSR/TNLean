/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialBoxEstimate

/-!
# Uniform entropy of physical safe rectangles

One nonnegative constant and one initial exponent work simultaneously for
every admissible safety parameter and every physical ground-state instance.
The entropy is that of the actual region inside the rectangle. Its estimate
is derived from the supremum defining the safe-box entropy.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Proposition 3.3 (`prop:initial-box`), `02-initial.tex`,
lines 596–604; safe rectangles, lines 220–228; safe-box entropy, lines 590–594,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
This is an auxiliary pointwise consequence at the initial exponent.
Original formalization from the manuscript; no upstream Lean proof text reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- A uniform actual-state safe-rectangle bound at the initial exponent.
The constant and exponent depend only on `q, R, J, Δ` and precede every safety
parameter, domain, Hamiltonian, ground vector, cut and rectangle.
Source: `02-initial.tex`, lines 590–604 (`prop:initial-box`), at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`. -/
theorem exists_regionalEntropy_safe_rect_le_rpow
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 ≤ C ∧ 0 < e₀ ∧ e₀ < 1 ∧
      ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
        ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
          (E₀ : ℝ) (Ω : StateSpace Λ q),
          IsGappedGroundState Λ q h.operator E₀ Ω Δ →
          ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
            regionalEntropy Λ q Ω (rectRegion A Q) ≤
              C * (Q.size : ℝ) ^ (1 + e₀) := by
  obtain ⟨C₀, e₀, he₀, he₀', hbox⟩ := exists_boxEntropy_le_rpow q R hq hJ hΔ
  have hC₀ : 0 ≤ C₀ := by
    simpa only [Nat.cast_one, Real.one_rpow, mul_one] using
      (boxEntropy_nonneg (q := q) (R := R) (J := J) (Δ := Δ) (D₀ := 2 * R + 11) 1).trans
        (hbox (2 * R + 11) (Nat.lt_succ_self (2 * R + 10)) 1 le_rfl)
  refine ⟨C₀, e₀, hC₀, he₀, he₀', fun D₀ hD₀ Λ h E₀ Ω hgs A Q hsafe ↦ ?_⟩
  exact (regionalEntropy_le_boxEntropy hq h hgs hsafe le_rfl).trans
    (hbox D₀ hD₀ Q.size Q.one_le_size)

end TNLean.PEPS.AreaLaw
