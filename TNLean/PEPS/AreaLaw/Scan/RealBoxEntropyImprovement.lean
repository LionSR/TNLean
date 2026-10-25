/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.SafeRectangleAreaLaw
import TNLean.PEPS.AreaLaw.Scan.BootstrapParameters

/-!
# Improvement of the safe-box exponent at real clearance

For fixed physical parameters, an initial exponent and an input coefficient,
one output coefficient applies to every intermediate exponent and every real
clearance. The input and output refer to the same supremum over safe rectangles.

The implication is a consequence of the uniform linear safe-rectangle bound.
It is therefore subsequent to the area law; it is not used in the proof of
that theorem. The scanner construction also proves the version with integer clearance
independently of the area law.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `08-scanner.tex`, lines 707–790, following
  `scanner:bootstrap-parameters` and using `scanner:bootstrap-energy` and
  `scanner:bootstrap-comparison`. The fixed real clearance and the safe-box
  supremum are those of `02-initial.tex`, lines 223–228 and 590–594.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized; no upstream Lean proof text reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Scan

/-- A bound with exponent `1 + e` implies the scanner's improved exponent
`1 + (1 - ell e₀) * e` for the literal supremum at the same real clearance.
The output coefficient is chosen before the intermediate exponent, clearance
and every physical instance. The initial exponent and improvement fraction
remain fixed throughout the implication.
Source: `08-scanner.tex`, lines 707–790, in the proof of Proposition 9.5
(`prop:small-box`); real safety and the supremum are defined in
`02-initial.tex`, lines 223–228 and 590–594. -/
theorem exists_uniform_boxEntropy_improvement_real
    (q R : ℕ) (hq : 1 ≤ q) {J Δ e₀ Cbox : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (he₀ : (Exponents.boxError : ℝ) < e₀) (he₀₁ : e₀ < 1) (_hCbox : 0 ≤ Cbox) :
    ∃ C : ℝ, 0 < C ∧
      ∀ e : ℝ, (Exponents.boxError : ℝ) < e → e ≤ e₀ →
      ∀ d : ℝ, 2 * (R : ℝ) + 10 < d →
        let F : ℕ → ℝ := fun r ↦ sSup
          {s : ℝ | ∃ (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
            (E₀ : ℝ) (Ω : StateSpace Λ q) (A : Finset (Site Λ)) (Q : IntRect),
            IsGappedGroundState Λ q h.operator E₀ Ω Δ ∧
              (∀ t ∈ Q.toFinset, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
                d * (Q.size : ℝ) < (supDist t z : ℝ)) ∧
              Q.size ≤ r ∧ s = regionalEntropy Λ q Ω (rectRegion A Q)}
        (∀ r : ℕ, 1 ≤ r → F r ≤ Cbox * (r : ℝ) ^ (1 + e)) →
          ∀ r : ℕ, 1 ≤ r →
            F r ≤ C * (r : ℝ) ^ (1 + (1 - BootstrapParameters.ell e₀) * e) := by
  classical
  obtain ⟨K, hK, hlinear⟩ :=
    exists_regionalEntropy_safe_rect_le_linear q R hq hJ hΔ
  refine ⟨max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro e he _hee₀ d hd F _hbox r hr
  refine (Real.sSup_le (fun s hs ↦ ?_) (mul_nonneg hK (Nat.cast_nonneg r))).trans ?_
  · obtain ⟨Λ, h, E₀, Ω, A, Q, hgs, hclear, hQ, rfl⟩ := hs
    exact (hlinear d
      (le_trans (show (0 : ℝ) ≤ 2 * (R : ℝ) + 10 by positivity) (le_of_lt hd))
      Λ h E₀ Ω hgs A Q hclear).trans
        (mul_le_mul_of_nonneg_left (by exact_mod_cast hQ) hK)
  · exact mul_le_mul (le_max_left K 1)
      (by
        simpa only [Real.rpow_one] using
          (Real.rpow_le_rpow_of_exponent_le
            (show (1 : ℝ) ≤ (r : ℝ) by exact_mod_cast hr)
            (show (1 : ℝ) ≤ 1 + (1 - BootstrapParameters.ell e₀) * e from
              le_add_of_nonneg_right (mul_nonneg
                (sub_nonneg.mpr (le_of_lt
                  (BootstrapParameters.parameter_bounds
                    (lt_trans (by norm_num [Exponents.boxError]) he₀)
                    he₀₁).2.2.2.1))
                (le_of_lt (lt_trans (by norm_num [Exponents.boxError]) he))))))
      (Nat.cast_nonneg r) (hK.trans (le_max_left K 1))

end TNLean.PEPS.AreaLaw.Scan
