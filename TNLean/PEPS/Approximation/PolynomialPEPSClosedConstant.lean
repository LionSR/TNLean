/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PolynomialPEPSExplicitConstant
import TNLean.PEPS.Approximation.ExactFiniteException
import TNLean.PEPS.AreaLaw.SquareAreaLawExplicitConstant
import TNLean.PEPS.Approximation.AngularInformationFromGap

/-!
# The polynomial PEPS approximation with explicit constants

Theorem 1.1 of the polynomial-PEPS manuscript asserts that constants `C, c > 0`, depending only
on `q, J, Δ`, exist. This module names them. The area-law constant is the closed-form constant
`uniformAreaLawConstantClosed q 1 J Δ` of the range-one area law, the angular scale and its size
threshold are the closed forms of Proposition 3.4 at clearance `angularConstant / 2`, diameter
ratio `1`, at most `4` marked points and accuracy `L⁻⁶⁰`, and the sizes below the threshold are
absorbed into the prefactor `q ^ (L₀ * L₀)` of the exact small-size representation.

This is an auxiliary result: the source theorem asserts only that the constants exist, and
`polynomialPEPSApproximation` is that statement.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 1.1
(`00-introduction.tex`) and its proof in §8 (`07-assembly.tex`, lines 9–214), at revision
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The area-law constant of Proposition 2.1 at the closed form of the range-one area law. -/
noncomputable def pepsAreaLawConstant (q : ℕ) (J Δ : ℝ) : ℝ :=
  AreaLaw.uniformAreaLawConstantClosed q 1 J Δ

/-- The angular slope of Proposition 3.4 at clearance `angularConstant / 2` and accuracy
`L⁻⁶⁰` (`02-information.tex`, lines 635–658). -/
noncomputable def pepsAngularScale (J Δ : ℝ) : ℝ :=
  angularScale J Δ (angularConstant / 2) ((60 : ℕ) : ℝ)

/-- The angular size threshold of Proposition 3.4 at clearance `angularConstant / 2`, diameter
ratio `1`, at most `4` marked points and accuracy `L⁻⁶⁰`. -/
noncomputable def pepsAngularThreshold (q : ℕ) (J Δ : ℝ) : ℝ :=
  angularThresholdClosed q J Δ (angularConstant / 2) 1 4 ((60 : ℕ) : ℝ)

/-- The size threshold above which the dyadic protocol applies. -/
noncomputable def pepsSizeThreshold (q : ℕ) (J Δ : ℝ) : ℕ :=
  pepsSizeThresholdOf (pepsAngularThreshold q J Δ)

/-- The bond exponent `c` of Theorem 1.1. -/
noncomputable def pepsBondExponent (q : ℕ) (J Δ : ℝ) : ℝ :=
  pepsBondExponentOf q J Δ (pepsAreaLawConstant q J Δ) (pepsAngularScale J Δ)

/-- The bond prefactor `C` of Theorem 1.1: the prefactor above the size threshold, enlarged to
`q ^ (L₀ * L₀)` to cover the smaller sizes (`07-assembly.tex`, lines 203–214). -/
noncomputable def pepsBondPrefactor (q : ℕ) (J Δ : ℝ) : ℝ :=
  max (pepsLargeSizePrefactorOf q (pepsAngularScale J Δ))
    (q ^ (pepsSizeThreshold q J Δ * pepsSizeThreshold q J Δ) : ℕ)

/-- The bond prefactor of Theorem 1.1 is positive. -/
theorem pepsBondPrefactor_pos (q : ℕ) (J Δ : ℝ) : 0 < pepsBondPrefactor q J Δ :=
  (pepsLargeSizePrefactorOf_pos q _).trans_le (le_max_left _ _)

/-- The bond exponent of Theorem 1.1 is positive. -/
theorem pepsBondExponent_pos (q : ℕ) (J Δ : ℝ) : 0 < pepsBondExponent q J Δ :=
  pepsBondExponentOf_pos q J Δ _ _

/-- **Theorem 1.1 with explicit constants.** For `q ≥ 2` and `J, Δ > 0`, every unit gapped
ground vector of every square-grid Hamiltonian of the model on an `L × L` grid with `L ≥ 2`
has a PEPS approximation with bond dimensions at most `C L^c` and normalized error at most
`L⁻¹`, at `C = pepsBondPrefactor q J Δ > 0` and `c = pepsBondExponent q J Δ > 0`.
Source: polynomial-PEPS Theorem 1.1 and its proof in §8 (`07-assembly.tex`, lines 9–214). -/
theorem polynomialPEPSApproximation_explicit {q : ℕ} (hq : 2 ≤ q) {J Δ : ℝ} (hJ : 0 < J)
    (hΔ : 0 < Δ) :
    ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
      h.IsGappedGroundState E₀ Ω Δ →
        HasPEPSApproximation (pepsBondPrefactor q J Δ) (pepsBondExponent q J Δ) L q Ω := by
  have hA := AreaLaw.squareEntropyAreaLawAt_closed (q := q) (by omega) hJ.le hΔ
  have hD : IsAngularScale q J Δ (angularConstant / 2) 1 4 60 (pepsAngularScale J Δ)
      (pepsAngularThreshold q J Δ) :=
    isAngularScale_closed_le (by omega) hJ.le hΔ (p := 60) (by norm_num [angularConstant]) 4
      (by norm_num) le_rfl le_rfl
  have hlarge := polynomialPEPSApproximation_of_ratios hq hJ hΔ hA
    (one_le_angularScale _ _ _ _) hD
  intro L hL h E₀ Ω hΩ
  exact hasPEPSApproximation_of_sufficiently_large_le (by omega) hL
    (pepsBondExponent_pos q J Δ).le hΩ.1 (fun hL₀ ↦ hlarge L hL hL₀ h E₀ Ω hΩ)

end TNLean.PEPS.Approximation
