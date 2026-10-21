/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularInformationFromCollar
import TNLean.PEPS.Approximation.CellConditionalInformationFromGap
import TNLean.PEPS.Approximation.RangeInformationReset
import TNLean.PEPS.Approximation.RangeSquareGroundState

/-!
# Information under angular separation at interaction range `R`

Proposition 3.4 of the polynomial-PEPS manuscript at interaction range `R`, with explicit
constants: for the family `IsRangeSquareGroundState q R J Δ` of unit gapped ground vectors of
Hamiltonians of range `R` on the `L × L` square, every slope `D ≥ rangeAngularScale R J Δ a p`
and every threshold `L₀ ≥ rangeAngularThreshold q R J Δ a A₀ m₀ p` form an angular scale
(`isAngularScale_range_closed_le`).

The proof of Proposition 3.4 uses the Hamiltonian only through two estimates for the states of
the family: the cell bound of Lemma 3.2 on the square (`SquareCellInformationBound`) and the
information reset of Lemma 3.3 (`SquareResetBound`). For any family with these two estimates the
proposition is `isAngularScale_of_bounds`, in
`TNLean.PEPS.Approximation.AngularInformationFromCollar`, which also gives the range-one
statements. This file supplies the two estimates for the
range-`R` family: the cell bound from the integer-domain bound at range `R`
(`cell_conditionalMutualInformation_le_closed`), and the reset from Lemma 3.3 at range `R`
(`TNLean.Lattice.LocalHamiltonian.information_reset_of_rangeResetThreshold_le`), both read in
the coordinates of the square.

The manuscript states Proposition 3.4 for site and nearest-neighbour terms only, which is range
one; the statements at range `R` extend it. The range-one statements, `isAngularScale_closed_le`
with `angularScale` and `angularThresholdClosed`, are unchanged.

## Main statements

* `IsRangeSquareGroundState.squareCellInformationBound`,
  `IsRangeSquareGroundState.squareResetBound`: the estimates at range `R`.
* `rangeAngularScale`, `rangeAngularThreshold`: the slope and threshold at range `R`.
* `isAngularScale_range_closed_le`: Proposition 3.4 at range `R`.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 3.2 (`lem:cell-cmi`), `02-information.tex`, lines 161–311,
  Lemma 3.3 (`lem:reset`), lines 334–630, and Proposition 3.4 (`prop:angular`),
  lines 635–785. Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open TNLean.PEPS.AreaLaw TNLean.PEPS.AreaLaw.Geometry AngularGrid

/-! ### The two estimates at range `R` -/

/-- **The cell bound of Lemma 3.2 at range `R` for the range-`R` family,** with the closed-form
constants `cellInformationConstantClosed q R J Δ c` and `cellInformationExponentClosed q R J Δ c`.
The manuscript states Lemma 3.2 for range one only; this extends it to range `R`.
Source: `02-information.tex`, Lemma 3.2, lines 161–311. -/
theorem IsRangeSquareGroundState.squareCellInformationBound {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) {c : ℝ} (hc : 0 < c) :
    SquareCellInformationBound q (IsRangeSquareGroundState q R J Δ) c
      (cellInformationConstantClosed q R J Δ c) (cellInformationExponentClosed q R J Δ c) := by
  intro s hs o m₀ A hm₀ L Ω hΩ
  obtain ⟨H, E₀, hgap⟩ := hΩ
  exact cell_conditionalMutualInformation_le_square_of_rectangle Ω o m₀ A
    (cell_conditionalMutualInformation_le_closed hq hJ hΔ hc s hs (o - (1, 1)) m₀ A hm₀
      (rectangularDomain L L) H E₀ (squareAreaLawState Ω) hgap)

/-- The mutual information of a state of the square equals that of its placement on the integer
square, for the corresponding sets of sites. -/
theorem mutualInformation_squareAreaLawState {q L : ℕ} (Ω : StateSpace L q)
    (X Y : Finset (SquareLatticeVertex L L)) :
    FiniteProduct.mutualInformation (fun _ : Site (rectangularDomain L L) ↦ Fin q)
        (squareAreaLawState Ω) (X.map (rectangleSiteEquiv L L).toEmbedding)
        (Y.map (rectangleSiteEquiv L L).toEmbedding) =
      FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω X Y := by
  simp only [FiniteProduct.mutualInformation, squareAreaLawState,
    show rectangleConfigurationEquiv L L q =
      (rectangleSiteEquiv L L).arrowCongr (Equiv.refl (Fin q)) from rfl,
    ← Finset.map_union, finiteProductEntropy_relabel]

/-- **The information reset of Lemma 3.3 at range `R` for the range-`R` family,** with the
width `rangeResetWidth R J Δ p` and the threshold `rangeResetThreshold q R J Δ p`. The
manuscript states Lemma 3.3 for range one only; this extends it to range `R`.
Source: `02-information.tex`, Lemma 3.3, lines 334–353. -/
theorem IsRangeSquareGroundState.squareResetBound {q R : ℕ} (hq : 1 ≤ q) {J Δ p : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) (hp : 0 < p) :
    SquareResetBound q (IsRangeSquareGroundState q R J Δ) p (rangeResetWidth R J Δ p)
      (rangeResetThreshold q R J Δ p) := by
  intro L hL Ω hΩ Rg C R₀ C₀ hRC hR₀ hC₀ b hb hI hRw hCw
  obtain ⟨H, E₀, hgap⟩ := hΩ
  set σ := rectangleSiteEquiv L L
  have hval (v : SquareLatticeVertex L L) : (σ v).1 = rectangleEmbedding v :=
    rectangleSiteEquiv_val L L v
  have hfar {T T₀ : Finset (SquareLatticeVertex L L)}
      (hT : ∀ x ∈ T₀, ∀ y, y ∉ T → rangeResetWidth R J Δ p * (1 + b + Real.log L) <
        (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) :
      ∀ x ∈ T₀.map σ.toEmbedding, ∀ y, y ∉ T.map σ.toEmbedding →
        rangeResetWidth R J Δ p * (1 + b + Real.log L) < (supDist x.1 y.1 : ℝ) := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨v, rfl⟩ := σ.surjective y
    have hv : v ∉ T := fun h ↦ hy (Finset.mem_map_of_mem _ h)
    simpa only [Equiv.toEmbedding_apply, hval] using hT u hu v hv
  have h := H.information_reset_of_rangeResetThreshold_le hq hJ hΔ hp hL E₀
    (squareAreaLawState Ω) hgap (Rg.map σ.toEmbedding) (C.map σ.toEmbedding)
    (R₀.map σ.toEmbedding) (C₀.map σ.toEmbedding)
    ((Finset.disjoint_map σ.toEmbedding).mpr hRC) (Finset.map_subset_map.mpr hR₀)
    (Finset.map_subset_map.mpr hC₀) b hb
    ((mutualInformation_squareAreaLawState Ω Rg C).trans_le hI) (hfar hRw) (hfar hCw)
  rwa [mutualInformation_squareAreaLawState] at h

/-! ### Proposition 3.4 at range `R` -/

/-- **The slope of Proposition 3.4 at range `R`:**
`D_R = max(1, 12 C_{p,R} / a', 1 / d)` with the reset width `C_{p,R} = rangeResetWidth R J Δ p`,
`a' = angularMargin a` and `d = angularCellSide a`. The range-one slope is
`angularScale J Δ a p`, with the range-one reset width.
Source: `02-information.tex`, lines 751–755, at range `R`. -/
def rangeAngularScale (R : ℕ) (J Δ a p : ℝ) : ℝ :=
  angularCellResetSlope (rangeResetWidth R J Δ p) (angularMargin a) (angularCellSide a)

/-- **The size threshold of Proposition 3.4 at range `R`:** the larger of the cell-reset
threshold at the reset width `rangeResetWidth R J Δ p`, the closed-form cell constants
`cellInformationConstantClosed q R J Δ c` and `cellInformationExponentClosed q R J Δ c` at the
clearance coefficient `c = angularClearance a a' d`, and the cell count `angularCellCount a A₀ m₀`,
and the reset threshold `rangeResetThreshold q R J Δ p`. Explicit in `q, R, J, Δ, a, A₀, m₀, p`.
Source: `02-information.tex`, lines 692–785, at range `R`. -/
def rangeAngularThreshold (q R : ℕ) (J Δ a A₀ : ℝ) (m₀ : ℕ) (p : ℝ) : ℝ :=
  max (angularCellResetThreshold (angularMargin a) (angularCellSide a) (rangeResetWidth R J Δ p)
      (cellInformationConstantClosed q R J Δ
        (angularClearance a (angularMargin a) (angularCellSide a)))
      (angularCellCount a A₀ m₀)
      (cellInformationExponentClosed q R J Δ
        (angularClearance a (angularMargin a) (angularCellSide a))))
    (rangeResetThreshold q R J Δ p)

/-- The closed form `D_R = 2400 C_{p,R} / min(a, 1)` of the slope of Proposition 3.4 at
range `R`. -/
theorem rangeAngularScale_eq (R : ℕ) {J Δ a p : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (ha : 0 < a)
    (hp : 0 < p) :
    rangeAngularScale R J Δ a p = 2400 * rangeResetWidth R J Δ p / min a 1 := by
  have hm : 0 < min a 1 := lt_min ha one_pos
  have hm1 : min a 1 ≤ 1 := min_le_right _ _
  have hCp : 1 ≤ rangeResetWidth R J Δ p := by
    have := rangeResetRadius_pos R hJ hΔ (by linarith : 0 ≤ 2 * p + 10)
    have : (0 : ℝ) ≤ R := Nat.cast_nonneg R
    unfold rangeResetWidth; linarith
  have h1 : 12 * rangeResetWidth R J Δ p / angularMargin a =
      2400 * rangeResetWidth R J Δ p / min a 1 := by
    unfold angularMargin
    field_simp
    ring
  have h2 : 1 / angularCellSide a = 1600 / min a 1 := by
    unfold angularCellSide angularMargin
    field_simp
    ring
  have hX : 1 ≤ 2400 * rangeResetWidth R J Δ p / min a 1 := by
    rw [le_div_iff₀ hm]
    linarith
  have hY : 1600 / min a 1 ≤ 2400 * rangeResetWidth R J Δ p / min a 1 :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  unfold rangeAngularScale angularCellResetSlope
  rw [h1, h2, max_eq_left hY, max_eq_right hX]

/-- **Proposition 3.4 at range `R`, at closed-form constants.** For `q ≥ 1`, `J ≥ 0`,
`Δ > 0`, `a > 0`, `m₀ ∈ ℕ` and an integer `p > 0`, every slope
`D ≥ rangeAngularScale R J Δ a p` and every threshold `L₀ ≥ rangeAngularThreshold q R J Δ a A₀ m₀ p`
form an angular scale for the unit gapped ground vectors of Hamiltonians of range `R` on the
square.

The manuscript states Proposition 3.4 for site and nearest-neighbour terms only, which is range
one; this is its extension to range `R`. The range-one statement is `isAngularScale_closed_le`.
Source: `02-information.tex`, Proposition 3.4 (`prop:angular`), lines 635–785. -/
theorem isAngularScale_range_closed_le {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J)
    (hΔ : 0 < Δ) {a A₀ : ℝ} (ha : 0 < a) (m₀ : ℕ) {p : ℕ} (hp : 0 < p) {D L₀ : ℝ}
    (hD : rangeAngularScale R J Δ a p ≤ D)
    (hL₀ : rangeAngularThreshold q R J Δ a A₀ m₀ p ≤ L₀) :
    IsAngularScale q (IsRangeSquareGroundState q R J Δ) a A₀ m₀ p D L₀ := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have ha' : 0 < angularMargin a := div_pos (lt_min ha zero_lt_one) (by norm_num)
  have ha'a : angularMargin a < a / 100 :=
    show min a 1 / 200 < a / 100 by linarith [min_le_left a 1]
  have hd : 0 < angularCellSide a := div_pos ha' (by norm_num)
  have hda' : angularCellSide a < angularMargin a / 4 :=
    div_lt_div_of_pos_left ha' (by norm_num) (by norm_num)
  have hc : 0 < angularClearance a (angularMargin a) (angularCellSide a) :=
    div_pos (angular_clearance_pos ha' ha'a hda') hd
  exact isAngularScale_of_bounds (fun _ _ hΩ ↦ hΩ.norm_eq_one) ha m₀ hp
    (IsRangeSquareGroundState.squareCellInformationBound hq hJ hΔ hc)
    (IsRangeSquareGroundState.squareResetBound hq hJ hΔ hp')
    (cellInformationConstantClosed_pos q R J Δ _)
    (cellInformationExponentClosed_pos q R J Δ _).le (rangeResetWidth_pos R hJ hΔ hp') hD hL₀

end TNLean.PEPS.Approximation
