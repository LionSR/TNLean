/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegionalStates
import TNLean.PEPS.AreaLaw.Scan.RoundedScalePower
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundedClearance
import TNLean.PEPS.AreaLaw.WeakRectangleShellEntropy
import Mathlib.Data.Nat.Log

/-!
# Uniform entropy estimates for rounded rectangle shells

A pointwise safe-rectangle entropy bound at a current exponent controls
the actual rounded collar of the same unit vector. The collar exponent
is fixed from the initial exponent. One threshold precedes the positive
lower exponent and every finite domain, local dimension, safety parameter,
vector, cut and rectangle.
A positive lower bound for the current exponent makes the coefficient
uniform throughout the specified interval of exponents. Nonnegativity of
the pointwise coefficient follows from the parent rectangle estimate; it is
not an additional premise.

This is a conditional shell estimate. The pointwise safe-rectangle estimate
is an explicit hypothesis; neither that hypothesis nor the physical
one-step improvement of Proposition 9.5 is proved here.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:bootstrap-parameters`, lines 693–703, and the
shell estimate in the proof of `prop:small-box`, lines 705–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw

/-- A fixed lower exponent gives a uniform rounded-shell coefficient for every
current exponent up to the initial exponent. The threshold is chosen before
the lower exponent and all geometric and physical data. The conclusion concerns
the same unit vector as the supplied pointwise safe-rectangle estimate.
Source: auxiliary to `08-scanner.tex`, lines 693–703 and 705–729. -/
theorem exists_regionalEntropy_rounded_shell_le_uniform_rpow
    {C₂ e₀ : ℝ} (hC₂ : 0 < C₂) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ b : ℝ, 0 < b →
      ∀ (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ), 1 ≤ D₀ →
        ∀ (Ω : StateSpace Λ q), ‖Ω‖ = 1 →
          ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
            N ≤ Q.size →
            ∀ e : ℝ, b ≤ e → e ≤ e₀ →
              ∀ C : ℝ,
                (∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
                  regionalEntropy Λ q Ω (rectRegion A Q') ≤
                    C * (Q'.size : ℝ) ^ (1 + e)) →
                let η := 1 - Scan.BootstrapParameters.ell e₀
                let L := Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^ η)
                ∀ j : ℕ, j ≤ L →
                  regionalEntropy Λ q Ω
                    (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
                    C * (24 + 64 / ((2 : ℝ) ^ b - 1)) *
                      (C₂ + 1) ^ (η * e₀) * (Q.size : ℝ) ^ (1 + η * e) := by
  obtain ⟨_, _, _, hℓ₁, _⟩ := Scan.BootstrapParameters.parameter_bounds he₀ he₀₁
  obtain ⟨N, hN₁, hN⟩ := Scan.exists_bootstrap_collar_clearance hC₂ he₀ he₀₁
  refine ⟨N, hN₁, ?_⟩
  intro b hb Λ q D₀ hD₀ Ω hΩ A Q hsafe hs e hbe hee₀ C hbox
  dsimp only
  intro j hj
  let η : ℝ := 1 - Scan.BootstrapParameters.ell e₀
  let L : ℕ := Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^ η)
  have hη : 0 < η := sub_pos.mpr hℓ₁
  have he : 0 < e := hb.trans_le hbe
  have hs₁ : 1 ≤ Q.size := hN₁.trans hs
  have hspos : (0 : ℝ) < Q.size := by
    exact_mod_cast (show 0 < Q.size by omega)
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right (Real.rpow_pos_of_pos hspos (1 + e))).mp
      ((regionalEntropy_nonneg Λ q Ω hΩ (rectRegion A Q)).trans (hbox Q hsafe))
  obtain ⟨hLpos, htwo, hclearance⟩ := hN Q.size hs
  have hL : L ≤ Q.size := (Nat.le_mul_of_pos_left L zero_lt_two).trans htwo
  have hbudget : D₀ * L + L ≤ D₀ * Q.size := hclearance D₀ hD₀
  have hshell := IntRect.regionalEntropy_shell_le_of_safe_box
    Λ q D₀ Ω hΩ A Q hsafe j L (Nat.log 2 L) hj hL
    (Nat.pow_log_le_self 2 hLpos.ne')
    (Nat.lt_pow_succ_log_self (b := 2) (by decide) L) hbudget e C he hC hbox
  have hpower : (L : ℝ) ^ e ≤
      (C₂ + 1) ^ (η * e) * (Q.size : ℝ) ^ (η * e) :=
    floor_rpow_ceil_mul_rpow_le hC₂.le hη.le he.le Q.size hs₁
  have hcoefficient :
      (24 + 64 / ((2 : ℝ) ^ e - 1)) * (C₂ + 1) ^ (η * e) ≤
        (24 + 64 / ((2 : ℝ) ^ b - 1)) * (C₂ + 1) ^ (η * e₀) :=
    Scan.rounded_shell_coefficient_uniform_le hb hbe hee₀ hη.le hC₂.le
  have hden : 0 < (2 : ℝ) ^ e - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) he)
  have hcoeff_nonneg :
      0 ≤ C * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) := by positivity
  calc
    _ ≤ C * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) * (L : ℝ) ^ e :=
      hshell
    _ ≤ C * (24 + 64 / ((2 : ℝ) ^ e - 1)) * (Q.size : ℝ) *
        ((C₂ + 1) ^ (η * e) * (Q.size : ℝ) ^ (η * e)) :=
      mul_le_mul_of_nonneg_left hpower hcoeff_nonneg
    _ = C * ((24 + 64 / ((2 : ℝ) ^ e - 1)) * (C₂ + 1) ^ (η * e)) *
        (Q.size : ℝ) ^ (1 + η * e) := by
      rw [Real.rpow_add hspos, Real.rpow_one]
      ring
    _ ≤ C * ((24 + 64 / ((2 : ℝ) ^ b - 1)) * (C₂ + 1) ^ (η * e₀)) *
        (Q.size : ℝ) ^ (1 + η * e) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcoefficient hC)
        (Real.rpow_nonneg (Nat.cast_nonneg Q.size) _)
    _ = _ := by ring

end TNLean.PEPS.AreaLaw
