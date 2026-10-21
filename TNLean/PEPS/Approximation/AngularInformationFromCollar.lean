/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/

import TNLean.PEPS.Approximation.AngularAnnularInformationInduction
import TNLean.PEPS.Approximation.AngularSingleScaleReset

/-!
# Angular information from the sublinear collar estimate

For each prescribed accuracy, the cell estimate and information reset give
one logarithmic lower scale that works at every annulus. The finite annular
induction then bounds the mutual information of the original physical
regions in the original ground state. All constants are chosen before the
system size, Hamiltonian, marked points, regions, and scale. They are named. The slope is
`angularScale J Δ a p = max(1, 12 C_p / a', 1 / d)`, with `a' = min(a, 1) / 200`, `d = a' / 8`
and the reset width `C_p` of Lemma 3.3. The slope equals `2400 C_p / min(a, 1)`
(`angularScale_eq`). The size threshold is
`angularThreshold q J Δ a A₀ m₀ p C_tpl N C_a N_a`, a function of the collar threshold `N`
and the amplification constant and threshold `C_a`, `N_a`
(`angularInformationBound_of_sublinearCollarBoundAt_le`).

The proof uses the Hamiltonian only through the cell bound and the reset. It is given for any
family of unit states with these two estimates (`SquareCellInformationBound`,
`SquareResetBound`) as `angularInformation_of_bounds` and `isAngularScale_of_bounds`, and the
range-one statements are its instances at the open-square model.

**Scope restriction (sublinear collar bound):** The sublinear collar
estimate remains an explicit premise. This is the corresponding implication
in Proposition 3.4, not a derivation of the collar estimate. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`. The unconditional
Proposition 3.4 is `angularInformationBound` in
`TNLean.PEPS.Approximation.AngularInformationFromGap`.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`),
`02-information.tex`, lines 635–785, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

/-- The padding coefficient `a' = min(a, 1) / 200` of the proof of Proposition 3.4, which
satisfies `a' < min(a / 100, 1 / 100)`.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 662–664. -/
noncomputable def angularMargin (a : ℝ) : ℝ := min a 1 / 200

/-- The cell-side coefficient `d = a' / 8` of the proof of Proposition 3.4, with
`a' = angularMargin a`; it satisfies `0 < d < a' / 4`.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 663–664. -/
noncomputable def angularCellSide (a : ℝ) : ℝ := angularMargin a / 8

/-- The bound `(m₀ + 1)(2 ⌈(max(A₀, 2) + 3a'/2) / d⌉ + 3)²` on the number of new cells at one
annular scale, with `a' = angularMargin a` and `d = angularCellSide a`.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 685–689 and 713–716. -/
noncomputable def angularCellCount (a A₀ : ℝ) (m₀ : ℕ) : ℕ :=
  (m₀ + 1) * (2 * ⌈(max A₀ 2 + (3 / 2) * angularMargin a) / angularCellSide a⌉₊ + 3) ^ 2

/-- **The slope `D` of Proposition 3.4:**
`D = max(1, 12 C_p / a', 1 / d)` with the reset width `C_p = resetWidth J Δ p` of Lemma 3.3,
`a' = angularMargin a` and `d = angularCellSide a`. For `J ≥ 0`, `Δ > 0`, `a > 0` and `p > 0`
it equals `2400 C_p / min(a, 1)` (`angularScale_eq`). It does not depend on the collar or
amplification constants, nor on `A₀` and `m₀`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 638 and
751–755. -/
noncomputable def angularScale (J Δ a p : ℝ) : ℝ :=
  angularCellResetSlope (resetWidth J Δ p) (angularMargin a) (angularCellSide a)

/-- **The size threshold `L₀` of Proposition 3.4:** the single-scale reset threshold
`angularSingleScaleThreshold` at `a' = angularMargin a`, `d = angularCellSide a`, the cell
count `angularCellCount a A₀ m₀`, the template constant `C_tpl`, the collar threshold `N` and
the amplification constant and threshold `C_a`, `N_a`.

Source: polynomial-PEPS manuscript, Proposition 3.4, `02-information.tex`, lines 638 and
727–774. -/
noncomputable def angularThreshold (q : ℕ) (J Δ a A₀ : ℝ) (m₀ : ℕ) (p Ctpl : ℝ) (N : ℕ)
    (Ca : ℝ) (Na : ℕ) : ℝ :=
  angularSingleScaleThreshold q J Δ a (angularMargin a) (angularCellSide a) p Ctpl N Ca Na
    (angularCellCount a A₀ m₀)

/-- The slope of Proposition 3.4 is at least one. -/
theorem one_le_angularScale (J Δ a p : ℝ) : 1 ≤ angularScale J Δ a p :=
  one_le_angularCellResetSlope _ _ _

/-- The slope of Proposition 3.4 is positive. -/
theorem angularScale_pos (J Δ a p : ℝ) : 0 < angularScale J Δ a p :=
  zero_lt_one.trans_le (one_le_angularScale J Δ a p)

/-- The size threshold of Proposition 3.4 is at least `e`. -/
theorem exp_one_le_angularThreshold (q : ℕ) (J Δ a A₀ : ℝ) (m₀ : ℕ) (p Ctpl : ℝ) (N : ℕ)
    (Ca : ℝ) (Na : ℕ) : Real.exp 1 ≤ angularThreshold q J Δ a A₀ m₀ p Ctpl N Ca Na :=
  exp_one_le_angularSingleScaleThreshold _ _ _ _ _ _ _ _ _ _ _ _

/-- The closed form `D = 2400 C_p / min(a, 1)` of the slope of Proposition 3.4, where
`C_p = resetWidth J Δ p = 1280 e² (J/Δ)(2p + 40) + 4p + 52` (`resetWidth_eq`). -/
theorem angularScale_eq {J Δ a p : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) (ha : 0 < a) (hp : 0 < p) :
    angularScale J Δ a p = 2400 * resetWidth J Δ p / min a 1 := by
  have hm : 0 < min a 1 := lt_min ha one_pos
  have hm1 : min a 1 ≤ 1 := min_le_right _ _
  have hCp : 52 ≤ resetWidth J Δ p := by
    rw [resetWidth_eq]
    have : 0 ≤ 1280 * Real.exp 2 * (J / Δ) * (2 * p + 40) :=
      mul_nonneg (mul_nonneg (by positivity) (div_nonneg hJ hΔ.le)) (by linarith)
    linarith
  have h1 : 12 * resetWidth J Δ p / angularMargin a = 2400 * resetWidth J Δ p / min a 1 := by
    unfold angularMargin
    field_simp
    ring
  have h2 : 1 / angularCellSide a = 1600 / min a 1 := by
    unfold angularCellSide angularMargin
    field_simp
    ring
  have hX : 1 ≤ 2400 * resetWidth J Δ p / min a 1 := by
    rw [le_div_iff₀ hm]
    linarith
  have hY : 1600 / min a 1 ≤ 2400 * resetWidth J Δ p / min a 1 :=
    div_le_div_of_nonneg_right (by linarith) hm.le
  unfold angularScale angularCellResetSlope
  rw [h1, h2, max_eq_left hY, max_eq_right hX]

/-- **Proposition 3.4 for a family of unit states with the two estimates.** If the states of
`G` are unit vectors and satisfy the cell bound with constants `C₁ > 0`, `K ≥ 0` at the
clearance coefficient of `a' = angularMargin a`, `d = angularCellSide a`, and the reset bound
with width `C_p > 0` and threshold `L₀`, then every slope
`D ≥ angularCellResetSlope C_p a' d` and every threshold
`L₁ ≥ max (angularCellResetThreshold a' d C_p C₁ (angularCellCount a A₀ m₀) K) L₀` satisfy the
conclusion of Proposition 3.4 for `G`.
Source: `02-information.tex`, Proposition 3.4 (`prop:angular`), lines 635–785. -/
theorem angularInformation_of_bounds {q : ℕ} {G : ∀ L : ℕ, StateSpace L q → Prop}
    (hnorm : ∀ L (Ω : StateSpace L q), G L Ω → ‖Ω‖ = 1) {a A₀ Cp L₀ C₁ K : ℝ} (ha : 0 < a)
    (m₀ : ℕ) {p : ℝ} (hp : 0 < p)
    (hcell : SquareCellInformationBound q G
      (angularClearance a (angularMargin a) (angularCellSide a)) C₁ K)
    (hreset : SquareResetBound q G p Cp L₀) (hC₁ : 0 < C₁) (hK : 0 ≤ K) (hCp : 0 < Cp)
    {D L₁ : ℝ} (hD : angularCellResetSlope Cp (angularMargin a) (angularCellSide a) ≤ D)
    (hL₁ : max (angularCellResetThreshold (angularMargin a) (angularCellSide a) Cp C₁
      (angularCellCount a A₀ m₀) K) L₀ ≤ L₁) :
    ∀ L : ℕ, L₁ ≤ L → ∀ Ω : StateSpace L q, G L Ω →
      ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
      ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
      ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
        (∀ x ∈ X, ∀ y ∈ X, dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n) →
        AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n (D * Real.log L) a V →
        FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω X E ≤
          (L : ℝ) ^ (-p) := by
  classical
  have ha' : 0 < angularMargin a := div_pos (lt_min ha zero_lt_one) (by norm_num)
  have ha'a : angularMargin a < a / 100 :=
    show min a 1 / 200 < a / 100 by linarith [min_le_left a 1]
  have ha'1 : angularMargin a ≤ 1 / 200 :=
    div_le_div_of_nonneg_right (min_le_right a 1) (by norm_num)
  have hd : 0 < angularCellSide a := div_pos ha' (by norm_num)
  have hda' : angularCellSide a < angularMargin a / 4 :=
    div_lt_div_of_pos_left ha' (by norm_num) (by norm_num)
  have hd1 : angularCellSide a ≤ 1 := show angularMargin a / 8 ≤ 1 by linarith
  have hreset' := angular_single_scale_reset_of_bounds hcell hreset hC₁ hK hCp ha' ha'a hd hda'
    hd1 hp (angularCellCount a A₀ m₀) hD
  have hD1 : 1 ≤ D := (one_le_angularCellResetSlope _ _ _).trans hD
  have hLe : Real.exp 1 ≤ L₁ :=
    ((exp_one_le_angularCellResetThreshold _ _ _ _ _ _).trans (le_max_left _ _)).trans hL₁
  intro L hL Ω hΩ V hV X E _hXE n hn _hnL hdiam hsep
  have hlog : 1 ≤ Real.log (L : ℝ) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hLe.trans hL))).2 (hLe.trans hL)
  have ht : 0 < D * Real.log (L : ℝ) :=
    mul_pos (zero_lt_one.trans_le hD1) (zero_lt_one.trans_le hlog)
  let c := chooseDyadicCutoff ht hn
  apply mutualInformation_le_of_annular_reset Ω (hnorm L Ω hΩ) (ht.trans_le hn) ha.le ha' ha'a
    hd hda' (Real.rpow_nonneg (Nat.cast_nonneg L) (-p)) hdiam hV hsep c
  intro j hj Aold hAold S hS hcard hold
  refine hreset' L (hL₁.trans hL) Ω hΩ (dyadicScale n j)
    (c.lower_at (ht.trans_le hn).le hj) (0, 0) Aold
    (cumulativeLayer (sitePosition L '' X) n V c.last j) (sitePosition L '' E)
    hAold ?_ S hS hcard hold
  intro x hx y hy
  simpa only [div_mul_eq_mul_div] using
    cumulativeLayer_separation c (ht.trans_le hn).le ha.le hsep hj hx hy

/-- **Proposition 3.4 at an integer accuracy for a family of unit states with the two
estimates:** the slopes and thresholds of `angularInformation_of_bounds` form an angular scale
for `G`.
Source: `02-information.tex`, Proposition 3.4 (`prop:angular`), lines 635–785;
`06-geometry.tex`, lines 62–63 and 440–445. -/
theorem isAngularScale_of_bounds {q : ℕ} {G : ∀ L : ℕ, StateSpace L q → Prop}
    (hnorm : ∀ L (Ω : StateSpace L q), G L Ω → ‖Ω‖ = 1) {a A₀ Cp L₀ C₁ K : ℝ} (ha : 0 < a)
    (m₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hcell : SquareCellInformationBound q G
      (angularClearance a (angularMargin a) (angularCellSide a)) C₁ K)
    (hreset : SquareResetBound q G p Cp L₀) (hC₁ : 0 < C₁) (hK : 0 ≤ K) (hCp : 0 < Cp)
    {D L₁ : ℝ} (hD : angularCellResetSlope Cp (angularMargin a) (angularCellSide a) ≤ D)
    (hL₁ : max (angularCellResetThreshold (angularMargin a) (angularCellSide a) Cp C₁
      (angularCellCount a A₀ m₀) K) L₀ ≤ L₁) :
    IsAngularScale q G a A₀ m₀ p D L₁ :=
  IsAngularScale.of_sitePosition
    (angularInformation_of_bounds hnorm ha m₀ (by exact_mod_cast hp) hcell hreset hC₁ hK hCp hD
      hL₁)

/-- **Proposition 3.4 under the sublinear collar bound, with explicit constants.** Assume the
range-one sublinear collar bound with constant `C` and threshold `N`, and the range-one
amplification bound at the input constant `max(C, 1)` and order `1` with constant `C_a` and
threshold `N_a`. For `a > 0`, `m₀ ∈ ℕ` and `p > 0`, every slope `D ≥ angularScale J Δ a p`
and every threshold `L₀ ≥ angularThreshold q J Δ a A₀ m₀ p C_tpl N C_a N_a` satisfy the
conclusion of Proposition 3.4. The threshold does not depend on `D`, so the slope can be
enlarged afterwards.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`), `02-information.tex`,
lines 635–658 (statement) and 660–785 (proof), with the slope `D ≥ 4 C_4 / c_*` at
lines 751–755. -/
theorem angularInformationBound_of_sublinearCollarBoundAt_le {q : ℕ} (hq : 1 ≤ q)
    {J Δ D₀ Ctpl C Ca : ℝ} {N Na : ℕ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na)
    {a A₀ : ℝ} (ha : 0 < a) (m₀ : ℕ) {p : ℝ} (hp : 0 < p) {D L₀ : ℝ}
    (hD : angularScale J Δ a p ≤ D)
    (hL₀ : angularThreshold q J Δ a A₀ m₀ p Ctpl N Ca Na ≤ L₀) :
    ∀ L : ℕ, L₀ ≤ L →
      ∀ h : SquareHamiltonian L q J, ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ →
        ∀ V : Finset (ℝ × ℝ), V.card ≤ m₀ →
        ∀ X E : Finset (SquareLatticeVertex L L), Disjoint X E →
        ∀ n : ℝ, D * Real.log L ≤ n → n ≤ A₀ * L →
          (∀ x ∈ X, ∀ y ∈ X, dist (sitePosition L x) (sitePosition L y) ≤ A₀ * n) →
          AngularSeparation (sitePosition L '' X) (sitePosition L '' E) n (D * Real.log L) a V →
          FiniteProduct.mutualInformation (fun _ : SquareLatticeVertex L L ↦ Fin q) Ω X E ≤
            (L : ℝ) ^ (-p) := by
  have ha' : 0 < angularMargin a := div_pos (lt_min ha zero_lt_one) (by norm_num)
  have ha'a : angularMargin a < a / 100 :=
    show min a 1 / 200 < a / 100 by linarith [min_le_left a 1]
  have hd : 0 < angularCellSide a := div_pos ha' (by norm_num)
  have hda' : angularCellSide a < angularMargin a / 4 :=
    div_lt_div_of_pos_left ha' (by norm_num) (by norm_num)
  set c := angularClearance a (angularMargin a) (angularCellSide a)
  have hc : 0 < c := div_pos (AngularGrid.angular_clearance_pos ha' ha'a hda') hd
  have hcell : SquareCellInformationBound q (IsSquareGroundState q J Δ) c
      (cellInformationConstant q c Ctpl N Ca Na) (cellInformationExponent c Ctpl N Ca Na) :=
    fun s hs o m₀ A hm₀ L Ω ⟨h, E₀, hΩ⟩ ↦
      cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt hJ hcol hamp hc
        s hs o m₀ A hm₀ L h E₀ Ω hΩ
  intro L hL h E₀ Ω hΩ
  exact angularInformation_of_bounds (fun _ _ hΩ ↦ hΩ.norm_eq_one) ha m₀ hp hcell
    (IsSquareGroundState.squareResetBound q hq J hJ hΔ hp)
    (cellInformationConstant_pos q c Ctpl N Ca Na)
    (cellInformationExponent_pos c Ctpl N Ca Na).le (resetWidth_pos hJ hΔ hp) hD hL₀
    L hL Ω ⟨h, E₀, hΩ⟩

/-- **Proposition 3.4 at an integer accuracy under the sublinear collar bound, with explicit
constants,** for sites placed at any common translation of `Λ_L`: every slope
`D ≥ angularScale J Δ a p` and every threshold
`L₀ ≥ angularThreshold q J Δ a A₀ m₀ p C_tpl N C_a N_a` form an angular scale.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`), `02-information.tex`,
lines 635–785; `06-geometry.tex`, lines 62–63 and 440–445. -/
theorem isAngularScale_of_sublinearCollarBoundAt_le {q : ℕ} (hq : 1 ≤ q)
    {J Δ D₀ Ctpl C Ca : ℝ} {N Na : ℕ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na)
    {a A₀ : ℝ} (ha : 0 < a) (m₀ : ℕ) {p : ℕ} (hp : 0 < p) {D L₀ : ℝ}
    (hD : angularScale J Δ a p ≤ D)
    (hL₀ : angularThreshold q J Δ a A₀ m₀ p Ctpl N Ca Na ≤ L₀) :
    IsAngularScale q (IsSquareGroundState q J Δ) a A₀ m₀ p D L₀ :=
  IsAngularScale.of_sitePosition fun L hL Ω ⟨h, E₀, hΩ⟩ ↦
    angularInformationBound_of_sublinearCollarBoundAt_le hq hJ hΔ hcol hamp ha m₀
      (by exact_mod_cast hp) hD hL₀ L hL h E₀ Ω hΩ

/-- **Proposition 3.4 at an integer accuracy, at the named amplification constants.** Under
the range-one sublinear collar bound with constant `C` and threshold `N`, every slope
`D ≥ angularScale J Δ a p` and every threshold `L₀` at least `angularThreshold` at the
amplification constant `collarAmplificationConstant q 1 J Δ C` and threshold
`collarAmplificationThreshold q 1 J Δ C` form an angular scale. The collar bound remains a
premise until its constant and threshold are named.

Source: polynomial-PEPS manuscript, Proposition 3.4 (`prop:angular`), `02-information.tex`,
lines 635–785; area-law Proposition 10.2 (`prop:amplification`), `09-amplification.tex`,
lines 261–296. -/
theorem isAngularScale_of_sublinearCollarBoundAt_le_explicit {q : ℕ} (hq : 1 ≤ q)
    {J Δ D₀ Ctpl C : ℝ} {N : ℕ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    {a A₀ : ℝ} (ha : 0 < a) (m₀ : ℕ) {p : ℕ} (hp : 0 < p) {D L₀ : ℝ}
    (hD : angularScale J Δ a p ≤ D)
    (hL₀ : angularThreshold q J Δ a A₀ m₀ p Ctpl N (collarAmplificationConstant q 1 J Δ C)
      (collarAmplificationThreshold q 1 J Δ C) ≤ L₀) :
    IsAngularScale q (IsSquareGroundState q J Δ) a A₀ m₀ p D L₀ :=
  isAngularScale_of_sublinearCollarBoundAt_le hq hJ hΔ hcol
    (amplificationBoundAt_collarAmplification hΔ C) ha m₀ hp hD hL₀

/-- The sublinear collar estimate at interaction range one implies angular
information decay with all constants uniform over the subsequent physical
systems, marked points, regions, and annular scales. The constants are
`angularScale J Δ a p` and `angularThreshold`, at the collar constants and at the
amplification constants `collarAmplificationConstant` and `collarAmplificationThreshold`
(`angularInformationBound_of_sublinearCollarBoundAt_le`).

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 635–785. -/
theorem angularInformationBound_of_sublinearCollarBound {q : ℕ} (hq : 1 ≤ q)
    {J Δ D₀ Ctpl : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl) :
    AngularInformationBound q J Δ := by
  intro a A₀ ha _hA₀ m₀ p hp
  obtain ⟨C, N, Ca, Na, hcol, hamp⟩ :=
    exists_sublinearCollarBoundAt_amplificationBoundAt hΔ hcol
  exact ⟨_, _, angularInformationBound_of_sublinearCollarBoundAt_le hq hJ hΔ hcol hamp ha m₀ hp
    le_rfl le_rfl⟩

end TNLean.PEPS.Approximation
