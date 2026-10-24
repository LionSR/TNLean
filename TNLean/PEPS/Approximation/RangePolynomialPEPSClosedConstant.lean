/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PolynomialPEPSExplicitConstant
import TNLean.PEPS.Approximation.ExactFiniteException
import TNLean.PEPS.Approximation.RangeAngularInformation
import TNLean.PEPS.Approximation.RangeNestedPatchApproximation
import TNLean.PEPS.Approximation.RangePolynomialPEPS
import TNLean.PEPS.AreaLaw.SquareAreaLawExplicitConstant

/-!
# The polynomial PEPS approximation at interaction range `R` with explicit constants

This module proves `RangePolynomialPEPSApproximation`, with its constants written as functions of
`q, R, J, Δ`. They are assembled in the order of §8 of the polynomial-PEPS manuscript:

1. The area-law constant is the closed-form constant `uniformAreaLawConstantClosed q R J Δ` of
   the area law at range `R`.
2. The angular scale and its size threshold are the closed forms of Proposition 3.4 at range `R`.
   They are taken at clearance `angularConstant / 2`, diameter ratio `1`, at most `4` marked
   points and accuracy `L⁻⁶⁰`.
3. The patch exponent is that of Proposition 4.1 at range `R`, at `B₀ = 20 D` and power `60`.
4. The sizes below the threshold are absorbed into the prefactor `q ^ (L₀ * L₀)` of the exact
   small-size representation.

The constants at `R = 1` are not those of `polynomialPEPSApproximation_explicit`. The range-`R`
reset width, angular threshold and patch filter exponent are different, larger closed forms, so
the nearest-neighbour statement keeps its own constants.

This is an extension of the source, which treats only site and nearest-neighbour interactions.

Source: OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 1.1
(`00-introduction.tex`, lines 36–57) and its proof in §8 (`07-assembly.tex`, lines 9–214), read
with interactions of range `R` as in *A two-dimensional area law from a global spectral gap*,
Theorem 1.1, at revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The area-law constant of Proposition 2.1 at range `R`, the closed form of the area law. -/
noncomputable def rangePEPSAreaLawConstant (q R : ℕ) (J Δ : ℝ) : ℝ :=
  AreaLaw.uniformAreaLawConstantClosed q R J Δ

/-- The angular slope of Proposition 3.4 at range `R`, at clearance `angularConstant / 2` and
accuracy `L⁻⁶⁰` (`02-information.tex`, lines 635–658). -/
noncomputable def rangePEPSAngularScale (R : ℕ) (J Δ : ℝ) : ℝ :=
  rangeAngularScale R J Δ (angularConstant / 2) ((60 : ℕ) : ℝ)

/-- The angular size threshold of Proposition 3.4 at range `R`, at clearance
`angularConstant / 2`, diameter ratio `1`, at most `4` marked points and accuracy `L⁻⁶⁰`. -/
noncomputable def rangePEPSAngularThreshold (q R : ℕ) (J Δ : ℝ) : ℝ :=
  rangeAngularThreshold q R J Δ (angularConstant / 2) 1 4 ((60 : ℕ) : ℝ)

/-- The size threshold above which the dyadic protocol applies at range `R`. -/
noncomputable def rangePEPSSizeThreshold (q R : ℕ) (J Δ : ℝ) : ℕ :=
  pepsSizeThresholdOf (rangePEPSAngularThreshold q R J Δ)

/-- The patch exponent of Proposition 4.1 at range `R`, at `B₀ = 20 D` for the angular slope `D`,
power `60` and the area-law constant at range `R` (`03-patches.tex`, lines 26–49). -/
noncomputable def rangePEPSPatchExponent (q R : ℕ) (J Δ : ℝ) : ℝ :=
  rangeAdaptivePatchExponent q R J Δ (20 * rangePEPSAngularScale R J Δ) 60
    (rangePEPSAreaLawConstant q R J Δ)

/-- The bond exponent `c` of the polynomial PEPS approximation at range `R`. -/
noncomputable def rangePEPSBondExponent (q R : ℕ) (J Δ : ℝ) : ℝ :=
  pepsBondExponentOfPatch (rangePEPSPatchExponent q R J Δ)

/-- The bond prefactor `C` of the polynomial PEPS approximation at range `R`: the prefactor above
the size threshold, enlarged to `q ^ (L₀ * L₀)` to cover the smaller sizes
(`07-assembly.tex`, lines 203–214). -/
noncomputable def rangePEPSBondPrefactor (q R : ℕ) (J Δ : ℝ) : ℝ :=
  max (pepsLargeSizePrefactorOf q (rangePEPSAngularScale R J Δ))
    (q ^ (rangePEPSSizeThreshold q R J Δ * rangePEPSSizeThreshold q R J Δ) : ℕ)

/-- The angular slope at range `R` is at least one. -/
theorem one_le_rangePEPSAngularScale (R : ℕ) (J Δ : ℝ) : 1 ≤ rangePEPSAngularScale R J Δ :=
  one_le_angularCellResetSlope _ _ _

/-- The bond prefactor at range `R` is positive. -/
theorem rangePEPSBondPrefactor_pos (q R : ℕ) (J Δ : ℝ) : 0 < rangePEPSBondPrefactor q R J Δ :=
  (pepsLargeSizePrefactorOf_pos q _).trans_le (le_max_left _ _)

/-- The bond exponent at range `R` is positive. -/
theorem rangePEPSBondExponent_pos (q R : ℕ) (J Δ : ℝ) : 0 < rangePEPSBondExponent q R J Δ :=
  pepsBondExponentOfPatch_pos _

/-- **The polynomial PEPS approximation at range `R` with explicit constants.** For `q ≥ 2`,
`R ≥ 1` and `J, Δ > 0`, every ground vector at range `R` on an `L × L` grid with `L ≥ 2` has a
PEPS approximation with bond dimensions at most `C L^c` and normalized error at most `L⁻¹`, at
`C = rangePEPSBondPrefactor q R J Δ > 0` and `c = rangePEPSBondExponent q R J Δ > 0`.

Source: polynomial-PEPS Theorem 1.1 and its proof in §8 (`07-assembly.tex`, lines 9–214), read
with interactions of range `R`. -/
theorem rangePolynomialPEPSApproximation_explicit {q R : ℕ} (hq : 2 ≤ q) (hR : 1 ≤ R)
    {J Δ : ℝ} (hJ : 0 < J) (hΔ : 0 < Δ) :
    ∀ L : ℕ, 2 ≤ L → ∀ Ω : StateSpace L q, IsRangeSquareGroundState q R J Δ L Ω →
      HasPEPSApproximation (rangePEPSBondPrefactor q R J Δ) (rangePEPSBondExponent q R J Δ)
        L q Ω := by
  have hA := AreaLaw.squareEntropyAreaLawAt_range_closed q R (by omega) hJ.le hΔ
  have hD : IsAngularScale q (IsRangeSquareGroundState q R J Δ) (angularConstant / 2) 1 4 60
      (rangePEPSAngularScale R J Δ) (rangePEPSAngularThreshold q R J Δ) :=
    isAngularScale_range_closed_le (by omega) hJ.le hΔ (by norm_num [angularConstant]) 4
      (p := 60) (by norm_num) le_rfl le_rfl
  have hD1 := one_le_rangePEPSAngularScale R J Δ
  have hB₀ : (0 : ℝ) < 20 * rangePEPSAngularScale R J Δ := by linarith
  have hlarge := hasPEPSApproximation_of_patchSupply hq
    (fun _ _ hΩ ↦ IsRangeSquareGroundState.norm_eq_one hΩ) hD1 hD
    fun L hL Ω hΩ ↦ AdaptivePatchSupply.cellCenterPos
      (hA.rangeAdaptivePatchSupply (by omega) hR hJ hΔ (B₀ := 20 * rangePEPSAngularScale R J Δ)
        (p := 60) hB₀ (by norm_num) L hL Ω hΩ)
  intro L hL Ω hΩ
  exact hasPEPSApproximation_of_sufficiently_large_le (by omega) hL
    (rangePEPSBondExponent_pos q R J Δ).le hΩ.norm_eq_one (fun hL₀ ↦ hlarge L hL hL₀ Ω hΩ)

/-- **The polynomial PEPS approximation at range `R`.** The constants are those of
`rangePolynomialPEPSApproximation_explicit`.

Source: polynomial-PEPS Theorem 1.1 (`00-introduction.tex`, lines 36–57), read with
interactions of range `R`. -/
theorem rangePolynomialPEPSApproximation : RangePolynomialPEPSApproximation :=
  fun q hq R hR J Δ hJ hΔ ↦ ⟨rangePEPSBondPrefactor q R J Δ, rangePEPSBondExponent q R J Δ,
    rangePEPSBondPrefactor_pos q R J Δ, rangePEPSBondExponent_pos q R J Δ,
    rangePolynomialPEPSApproximation_explicit hq hR hJ hΔ⟩

end TNLean.PEPS.Approximation
