/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.InitialWeakRectangleShellEntropy
import TNLean.PEPS.AreaLaw.Scan.BootstrapRoundedClearance

/-!
# Initial entropy estimate for the rounded bootstrap collar

The initial safe-rectangle estimate controls the actual shell at the rounded
collar scale. The threshold is chosen before the safety parameter and physical
instance. Its dependence is only on the fixed physical parameters and enlargement
constant. The exponent is strictly smaller than the initial rectangle exponent.

This is the initial-exponent shell input, rather than the improvement of the
safe-box exponent in Proposition 9.5.

## References

OpenAI, *A two-dimensional area law from a global spectral gap*,
`02-initial.tex`, Proposition 3.3, lines 590–604, and `08-scanner.tex`,
`scanner:scales`, lines 32–41, and the proof of `prop:small-box`, lines 693–729,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The numerical estimates are independent formalizations; no upstream Lean proof
text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- Powers of the rounded sublinear scale obey an explicit homogeneous bound.
Auxiliary to the rounded collar in `08-scanner.tex`, lines 32–41 and 705–729,
at the manuscript revision stated above. -/
theorem floor_rpow_ceil_mul_rpow_le {C₂ η e : ℝ} (hC₂ : 0 ≤ C₂)
    (hη : 0 ≤ η) (he : 0 ≤ e) (s : ℕ) (hs : 1 ≤ s) :
    (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ^ e ≤
      (C₂ + 1) ^ (η * e) * (s : ℝ) ^ (η * e) := by
  have hs₁ : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hceil : (Nat.ceil (C₂ * (s : ℝ)) : ℝ) ≤ (C₂ + 1) * (s : ℝ) := by
    have hlt := Nat.ceil_lt_add_one (mul_nonneg hC₂ (Nat.cast_nonneg s))
    nlinarith
  have hfloor : (Nat.floor ((Nat.ceil (C₂ * (s : ℝ)) : ℝ) ^ η) : ℝ) ≤
      ((C₂ + 1) * (s : ℝ)) ^ η :=
    (Nat.floor_le (by positivity)).trans
      (Real.rpow_le_rpow (by positivity) hceil hη)
  calc
    _ ≤ (((C₂ + 1) * (s : ℝ)) ^ η) ^ e :=
      Real.rpow_le_rpow (by positivity) hfloor he
    _ = ((C₂ + 1) * (s : ℝ)) ^ (η * e) :=
      (Real.rpow_mul (by positivity) η e).symm
    _ = _ := Real.mul_rpow (by positivity) (by positivity)

/-- The initial exponent controls all sufficiently large actual rounded collars,
with one threshold before the safety parameter and original ground vector.
Source: Proposition 3.3, `02-initial.tex`, lines 590–604, and the initial shell
input to Proposition 9.5, `08-scanner.tex`, lines 693–729. -/
theorem exists_regionalEntropy_initial_rounded_collar_le_rpow
    (q R : ℕ) (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C e₀ : ℝ, 0 ≤ C ∧ 0 < e₀ ∧ e₀ < 1 ∧
      ∀ C₂ : ℝ, 0 < C₂ → ∃ N : ℕ, 1 ≤ N ∧
        ∀ D₀ : ℕ, 2 * R + 10 < D₀ →
          ∀ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
            (E₀ : ℝ) (Ω : StateSpace Λ q),
            IsGappedGroundState Λ q h.operator E₀ Ω Δ →
            ∀ (A : Finset (Site Λ)) (Q : IntRect), IsSafe Λ A D₀ Q →
              N ≤ Q.size →
              let η := 1 - Scan.BootstrapParameters.ell e₀
              let L := Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^ η)
              ∀ j : ℕ, j ≤ L →
                regionalEntropy Λ q Ω
                  (A.filter fun x ↦ x.1 ∈ (Q.dilate j).toFinset \ Q.toFinset) ≤
                  C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) *
                    (C₂ + 1) ^ (η * e₀) * (Q.size : ℝ) ^ (1 + η * e₀) := by
  obtain ⟨C, e₀, hC, he₀, he₀₁, hshell⟩ :=
    exists_regionalEntropy_weak_rectangle_shell_le_rpow q R hq hJ hΔ
  refine ⟨C, e₀, hC, he₀, he₀₁, ?_⟩
  intro C₂ hC₂
  obtain ⟨_, _, hℓ, hℓ₁, _⟩ := Scan.BootstrapParameters.parameter_bounds he₀ he₀₁
  obtain ⟨N, hN⟩ := Scan.exists_two_mul_floor_rpow_ceil_mul_le hC₂
    (sub_pos.mpr hℓ₁) (sub_lt_self 1 hℓ)
  refine ⟨max N 1, le_max_right _ _, ?_⟩
  intro D₀ hD₀ Λ h E₀ Ω hgs A Q hsafe hs
  dsimp only
  intro j hj
  have hs₁ : 1 ≤ Q.size := (le_max_right N 1).trans hs
  have htwo := hN Q.size ((le_max_left N 1).trans hs)
  have hL : Nat.floor ((Nat.ceil (C₂ * (Q.size : ℝ)) : ℝ) ^
      (1 - Scan.BootstrapParameters.ell e₀)) ≤ Q.size := by omega
  have hbudget := Scan.mul_collar_add_collar_le_of_two_mul_le
    (show 1 ≤ D₀ by omega) htwo
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
      hshell D₀ hD₀ Λ h E₀ Ω hgs A Q hsafe j _ hj hL hbudget
    _ ≤ C * (24 + 64 / ((2 : ℝ) ^ e₀ - 1)) * (Q.size : ℝ) *
        ((C₂ + 1) ^ ((1 - Scan.BootstrapParameters.ell e₀) * e₀) *
          (Q.size : ℝ) ^ ((1 - Scan.BootstrapParameters.ell e₀) * e₀)) :=
      mul_le_mul_of_nonneg_left hpower hcoeff
    _ = _ := by
      rw [Real.rpow_add (by exact_mod_cast (show 0 < Q.size by omega)),
        Real.rpow_one]
      ring

end TNLean.PEPS.AreaLaw
