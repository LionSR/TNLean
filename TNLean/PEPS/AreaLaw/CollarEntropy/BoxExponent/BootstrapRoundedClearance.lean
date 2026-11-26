/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Analysis.Real.ExplicitThresholds
import TNLean.PEPS.AreaLaw.Collar.Scales.Budgets
import TNLean.PEPS.AreaLaw.CollarEntropy.BoxExponent.BootstrapParameters
import TNLean.PEPS.AreaLaw.Polygons.SafeRectangles.SafeRectangleDilation
import TNLean.PEPS.AreaLaw.Collar.Scales.RoundedScalePower
import QICLean.ManyBody.Hamiltonian.GroundSpace
import TNLean.PEPS.AreaLaw.RegionalStates.Regions.ZeroBoundary
import Mathlib.Data.Nat.Log

/-!
# Rounded collar clearance

For a fixed positive enlargement constant and an exponent strictly between
zero and one, the rounded collar depth at the enlarged integer scale is
eventually at most half the original side length. This supplies the scalar
clearance budget for every natural safety parameter at least one.

For the fixed bootstrap parameters, the threshold depends only on the
enlargement constant and the initial entropy exponent. It is chosen before
all side lengths and safety parameters. The collar exponent is one minus
the fixed improvement fraction, rather than the window-width exponent.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*, September 24,
2026, the collar scale `scanner:scales`, `08-scanner.tex`, lines 32–41;
the fixed choice `scanner:bootstrap-parameters`, lines 693–703; and the
covering-square clearance in the proof of Proposition 9.5 (`prop:small-box`),
lines 705–729, at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
These are auxiliary numerical estimates for the rectangle covering argument.
Original formalization from the manuscript; no upstream Lean proof text reused.

## Initial entropy estimate for the rounded bootstrap collar

The initial safe-rectangle estimate controls the actual shell at the rounded
collar scale. The threshold is chosen before the safety parameter and physical
instance. Its dependence is only on the fixed physical parameters and enlargement
constant. The exponent is strictly smaller than the initial rectangle exponent.

This is the initial-exponent shell input, rather than the improvement of the
safe-box exponent in Proposition 9.5.

### References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`02-initial.tex`, Proposition 3.3, lines 590–604, and `08-scanner.tex`,
`scanner:scales`, lines 32–41, and the proof of `prop:small-box`, lines 693–729,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The numerical estimates are independent formalizations; no upstream Lean proof
text is reused.

## Uniform entropy estimates for rounded rectangle shells

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

open ManyBody (IntRect IsSafe rectRegion)

section

namespace TNLean.PEPS.AreaLaw.Scan

open Filter

/-- A rounded sublinear scale at `n = ⌈C₂ s⌉` is eventually at most `s / 2`.
The threshold depends only on `C₂` and `η`.
Source: the safe covering-square clearance in `08-scanner.tex`, lines 705–729;
the actual collar specializes this statement to `η = 1 - ℓ`.
The rounded scale uses a fixed exponent strictly between zero and one. -/
theorem exists_two_mul_floor_rpow_ceil_mul_le {C₂ η : ℝ}
    (hC₂ : 0 < C₂) (hη : 0 < η) (hη₁ : η < 1) :
    ∃ N : ℕ, ∀ s : ℕ, N ≤ s →
      2 * Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) ≤ s := by
  have hlarge := eventually_le_natCast_rpow (sub_pos.mpr hη₁)
    (2 * (C₂ + 1) ^ η)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hlarge
  refine ⟨max N 1, fun s hs ↦ ?_⟩
  have hs₁ : 1 ≤ s := (le_max_right N 1).trans hs
  have hsN : N ≤ s := (le_max_left N 1).trans hs
  have hlargeS := hN s hsN
  have hceil : (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ≤ (C₂ + 1) * (s : ℝ) :=
    Nat.ceil_le_add_one_mul_of_le_mul (mul_nonneg hC₂.le (Nat.cast_nonneg s))
      le_rfl (by exact_mod_cast hs₁)
  have hfloor : (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ≤
      (C₂ + 1) ^ η * (s : ℝ) ^ η := by
    calc
      _ ≤ (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η := Nat.floor_le (by positivity)
      _ ≤ ((C₂ + 1) * (s : ℝ)) ^ η :=
        Real.rpow_le_rpow (by positivity) hceil hη.le
      _ = _ := Real.mul_rpow (by positivity) (by positivity)
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hreal : (2 : ℝ) * Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) ≤ s := by
    calc
      _ ≤ 2 * ((C₂ + 1) ^ η * (s : ℝ) ^ η) :=
        mul_le_mul_of_nonneg_left hfloor (by norm_num)
      _ = (2 * (C₂ + 1) ^ η) * (s : ℝ) ^ η := by ring
      _ ≤ (s : ℝ) ^ (1 - η) * (s : ℝ) ^ η :=
        mul_le_mul_of_nonneg_right hlargeS (by positivity)
      _ = s := by rw [← Real.rpow_add hspos]; simp
  exact_mod_cast hreal

/-- Half the parent side length is sufficient for the scalar shell-clearance
budget at every safety parameter at least one.
Source: the covering-square clearance in `08-scanner.tex`, lines 723–729. -/
theorem mul_collar_add_collar_le_of_two_mul_le {D₀ L s : ℕ}
    (hD₀ : 1 ≤ D₀) (htwo : 2 * L ≤ s) :
    D₀ * L + L ≤ D₀ * s := by
  have hscaled := Nat.mul_le_mul_left D₀ htwo
  have hL : L ≤ D₀ * L := by
    simpa only [one_mul] using Nat.mul_le_mul_right L hD₀
  calc
    D₀ * L + L ≤ D₀ * L + D₀ * L := Nat.add_le_add_left hL _
    _ = D₀ * (2 * L) := by ring
    _ ≤ D₀ * s := hscaled

/-- A single threshold gives a positive fixed bootstrap collar, bounds it by
half the parent side length, and supplies clearance for every safety parameter.
The threshold depends only on `C₂` and `e₀`.
Source: `scanner:bootstrap-parameters` and the safe-box clearance argument,
`08-scanner.tex`, lines 693–729; `scanner:scales`, lines 32–41. -/
theorem exists_bootstrap_collar_clearance {C₂ e₀ : ℝ}
    (hC₂ : 0 < C₂) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ s : ℕ, N ≤ s →
      let L := Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^
        (1 - BootstrapParameters.ell e₀))
      0 < L ∧ 2 * L ≤ s ∧
        ∀ D₀ : ℕ, 1 ≤ D₀ → D₀ * L + L ≤ D₀ * s := by
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := BootstrapParameters.parameter_bounds he₀ he₀₁
  obtain ⟨N, hN⟩ := exists_two_mul_floor_rpow_ceil_mul_le hC₂
    (sub_pos.mpr hℓ₁) (sub_lt_self 1 hℓ)
  refine ⟨max N 1, le_max_right _ _, fun s hs ↦ ?_⟩
  have hs₁ : 1 ≤ s := (le_max_right N 1).trans hs
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hceil : 0 < Nat.ceil (C₂ * (s : ℝ)) := Nat.ceil_pos.mpr (mul_pos hC₂ hspos)
  have hceil₁ : (1 : ℝ) ≤ Nat.ceil (C₂ * (s : ℝ)) := by
    exact_mod_cast (Nat.succ_le_of_lt hceil)
  have hLpos := Nat.floor_pos.mpr (Real.one_le_rpow hceil₁ (sub_pos.mpr hℓ₁).le)
  have htwo := hN s ((le_max_left N 1).trans hs)
  exact ⟨hLpos, htwo, fun D₀ hD₀ ↦
    mul_collar_add_collar_le_of_two_mul_le hD₀ htwo⟩

end TNLean.PEPS.AreaLaw.Scan

end

section

open scoped Matrix.Norms.L2Operator

open ManyBody (IsGapped groundSpace PlaneInteraction)

namespace TNLean.PEPS.AreaLaw

/-- The initial exponent controls all sufficiently large actual rounded collars,
with one threshold before the safety parameter and original ground vector.
Source: Proposition 3.3, `02-initial.tex`, lines 590–604, and the initial shell
input to Proposition 9.5, `08-scanner.tex`, lines 693–729. -/
theorem exists_regionEntropy_initial_rounded_collar_le_rpow
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 ≤ C ∧ 0 < e₀ ∧ e₀ < 1 ∧
      ∀ C₂ : ℝ, 0 < C₂ → ∃ N : ℕ, 1 ≤ N ∧
        ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
          ∀ (Λ : Finset (ℤ × ℤ)) (h : PlaneInteraction Λ q R) (_ : ∀ X, (h.term X).IsHermitian)
              (_ : ∀ X, ‖h.term X‖ ≤ J)
            (E₀ : ℝ) (Ω : EuclideanSpace ℂ (↥Λ → Fin q)),
            ‖Ω‖ = 1 → IsGapped h.hamiltonian E₀ Δ →
            groundSpace h.hamiltonian E₀ = Submodule.span ℂ {Ω} →
            ∀ (A : Finset ↥Λ) (Q : IntRect), IsSafe Λ A D₀ Q →
              N ≤ Q.size →
              let η := 1 - Scan.BootstrapParameters.ell e₀
              let L := Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^ η)
              ∀ j : ℕ, j ≤ L →
                ManyBody.regionEntropy Ω
                  (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
                  C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) *
                    (C₂ + 1) ^ (η * e₀) * (Q.size : ℝ) ^ (1 + η * e₀) := by
  obtain ⟨C, e₀, hC, he₀, he₀₁, hshell⟩ :=
    exists_regionEntropy_weak_rectangle_shell_le_rpow q R hq hJ hΔ
  refine ⟨C, e₀, hC, he₀, he₀₁, ?_⟩
  intro C₂ hC₂
  obtain ⟨_, _, _, hℓ₁, _⟩ := Scan.BootstrapParameters.parameter_bounds he₀ he₀₁
  obtain ⟨N, hN₁, hN⟩ := Scan.exists_bootstrap_collar_clearance hC₂ he₀ he₀₁
  refine ⟨N, hN₁, ?_⟩
  intro D₀ hD₀ Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe hs
  dsimp only
  intro j hj
  have hs₁ : 1 ≤ Q.size := hN₁.trans hs
  obtain ⟨_, htwo, hclearance⟩ := hN Q.size hs
  have hL : Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^
      (1 - Scan.BootstrapParameters.ell e₀)) ≤ Q.size := by omega
  have hbudget := hclearance D₀ (show 1 ≤ D₀ by omega)
  have hpower := floor_rpow_ceil_mul_rpow_le hC₂.le
    (sub_pos.mpr hℓ₁).le he₀.le Q.size hs₁
  have hden : 0 < (2 : ℝ) ^ e₀ - 1 :=
    sub_pos.mpr (Real.one_lt_rpow (by norm_num) he₀)
  have hcoeff : 0 ≤ C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) * (Q.size : ℝ) := by
    positivity
  calc
    _ ≤ C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) * (Q.size : ℝ) *
        (Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^
          (1 - Scan.BootstrapParameters.ell e₀)) : ℝ) ^ e₀ :=
      hshell D₀ hD₀ Λ h hh hhJ E₀ Ω hΩ hgap hspan A Q hsafe j _ hj hL hbudget
    _ ≤ C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) * (Q.size : ℝ) *
        ((C₂ + 1) ^ ((1 - Scan.BootstrapParameters.ell e₀) * e₀) *
          (Q.size : ℝ) ^ ((1 - Scan.BootstrapParameters.ell e₀) * e₀)) :=
      mul_le_mul_of_nonneg_left hpower hcoeff
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast (show 0 < Q.size by omega)),
        Real.rpow_one]
      ring

end TNLean.PEPS.AreaLaw

end

section

namespace TNLean.PEPS.AreaLaw

/-- A fixed lower exponent gives a uniform rounded-shell coefficient for every
current exponent up to the initial exponent. The threshold is chosen before
the lower exponent and all geometric and physical data. The conclusion concerns
the same unit vector as the supplied pointwise safe-rectangle estimate.
Source: auxiliary to `08-scanner.tex`, lines 693–703 and 705–729. -/
theorem exists_regionEntropy_rounded_shell_le_uniform_rpow
    {C₂ e₀ : ℝ} (hC₂ : 0 < C₂) (he₀ : 0 < e₀) (he₀₁ : e₀ < 1) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ b : ℝ, 0 < b →
      ∀ (Λ : Finset (ℤ × ℤ)) (q D₀ : ℕ), 1 ≤ D₀ →
        ∀ (Ω : EuclideanSpace ℂ (↥Λ → Fin q)), ‖Ω‖ = 1 →
          ∀ (A : Finset ↥Λ) (Q : IntRect), IsSafe Λ A D₀ Q →
            N ≤ Q.size →
            ∀ e : ℝ, b ≤ e → e ≤ e₀ →
              ∀ C : ℝ,
                (∀ Q' : IntRect, IsSafe Λ A D₀ Q' →
                  ManyBody.regionEntropy Ω (rectRegion A Q') ≤
                    C * (Q'.size : ℝ) ^ (1 + e)) →
                let η := 1 - Scan.BootstrapParameters.ell e₀
                let L := Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^ η)
                ∀ j : ℕ, j ≤ L →
                  ManyBody.regionEntropy Ω
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
      ((regionEntropy_nonneg Λ q Ω hΩ (rectRegion A Q)).trans (hbox Q hsafe))
  obtain ⟨hLpos, htwo, hclearance⟩ := hN Q.size hs
  have hL : L ≤ Q.size := (Nat.le_mul_of_pos_left L zero_lt_two).trans htwo
  have hbudget : D₀ * L + L ≤ D₀ * Q.size := hclearance D₀ hD₀
  have hshell := IntRect.regionEntropy_shell_le_of_safe_box
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

end
