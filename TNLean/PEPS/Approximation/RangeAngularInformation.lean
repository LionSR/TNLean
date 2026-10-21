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
information reset of Lemma 3.3 (`SquareResetBound`). The first part of this file runs the proof
of the proposition for any family of states with these two estimates
(`angular_single_scale_reset_of_bounds`, `isAngularScale_of_bounds`). The second part supplies
them for the range-`R` family: the cell bound from the integer-domain bound at range `R`
(`cell_conditionalMutualInformation_le_closed`), and the reset from Lemma 3.3 at range `R`
(`TNLean.Lattice.LocalHamiltonian.information_reset_of_rangeResetThreshold_le`), both read in
the coordinates of the square.

The manuscript states Proposition 3.4 for site and nearest-neighbour terms only, which is range
one; the statements at range `R` extend it. The range-one statements, `isAngularScale_closed_le`
with `angularScale` and `angularThresholdClosed`, and the proofs leading to them are unchanged.

## Main statements

* `SquareCellInformationBound`, `SquareResetBound`: the two estimates for a family of states.
* `isAngularScale_of_bounds`: Proposition 3.4 for a family with these estimates.
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

/-! ### The two estimates for a family of states -/

open Classical in
/-- **The cell bound of Lemma 3.2 on the square for a family of states,** with prefactor `C₁`
and exponent `K` at the clearance coefficient `c`: for every state `Ω` of the family, every cell
`G` of the grid of side `s ≥ 1`, every union `B` of other cells and every region `E` outside
`G ∪ B` at distance at least `c s` from the closed cell, `I_Ω(G : E | B) ≤ C₁ (1 + log s)^K`.
Source: `02-information.tex`, Lemma 3.2, lines 161–178. -/
def SquareCellInformationBound (q : ℕ) (G : ∀ L : ℕ, StateSpace L q → Prop) (c C₁ K : ℝ) :
    Prop :=
  ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)), m₀ ∉ A →
    ∀ (L : ℕ) (Ω : StateSpace L q), G L Ω →
      let Gc : Finset (Vertex L) :=
        Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
      let B : Finset (Vertex L) := Finset.univ.filter
        (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
      ∀ E : Finset (Vertex L), E ⊆ (Gc ∪ B)ᶜ →
        (∀ x ∈ closure (AngularGrid.cell o s m₀),
          ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
        FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
          Ω Gc E B ≤ C₁ * (1 + Real.log s) ^ K

/-- **The information reset of Lemma 3.3 for a family of states,** with width `C_p` and size
threshold `L₀` at the accuracy `L^(-p)`.
Source: `02-information.tex`, Lemma 3.3, lines 334–353. -/
def SquareResetBound (q : ℕ) (G : ∀ L : ℕ, StateSpace L q → Prop) (p Cp L₀ : ℝ) : Prop :=
  ∀ L : ℕ, L₀ ≤ L → ∀ Ω : StateSpace L q, G L Ω →
    ∀ (R C R₀ C₀ : Finset (SquareLatticeVertex L L)), Disjoint R C → R₀ ⊆ R → C₀ ⊆ C →
    ∀ b : ℝ, 0 ≤ b → FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
    (∀ x ∈ R₀, ∀ y, y ∉ R → Cp * (1 + b + Real.log L) <
      (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
    (∀ x ∈ C₀, ∀ y, y ∉ C → Cp * (1 + b + Real.log L) <
      (supDist (rectangleEmbedding x) (rectangleEmbedding y) : ℝ)) →
    FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤ (L : ℝ) ^ (-p)

/-! ### Proposition 3.4 for a family with the two estimates -/

open Classical in
/-- **The information reset for the padded annular regions, for a family of states.** The
proof of `angular_information_reset_of_resetThreshold_le` with a reset bound of the family.
Source: `02-information.tex`, lines 729–745. -/
theorem angular_information_reset_of_squareResetBound {q : ℕ}
    {G : ∀ L : ℕ, StateSpace L q → Prop} {p Cp L₀ : ℝ} (hreset : SquareResetBound q G p Cp L₀) :
    ∀ L : ℕ, L₀ ≤ L → ∀ Ω : StateSpace L q, G L Ω →
      ∀ (o : ℝ × ℝ) (A E : Set (ℝ × ℝ)) (a' d s : ℝ),
        0 ≤ a' → 0 < d → 0 < s →
        let R : Finset (SquareLatticeVertex L L) := Finset.univ.filter
          (fun v ↦ sitePosition L v ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
        let C : Finset (SquareLatticeVertex L L) := Finset.univ.filter
          (fun v ↦ sitePosition L v ∈ near ((3 / 2) * a' * s) E)
        let R₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
          (fun v ↦ sitePosition L v ∈ near (a' * s) A)
        let C₀ : Finset (SquareLatticeVertex L L) := Finset.univ.filter
          (fun v ↦ sitePosition L v ∈ near (a' * s) E)
        Disjoint R C → ∀ b : ℝ, 0 ≤ b →
          FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R C ≤ b →
          Cp * (1 + b + Real.log L) ≤ a' * s / 2 →
          FiniteProduct.mutualInformation (fun _ ↦ Fin q) Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  intro L hL Ω hΩ o A E a' d s ha' hd hs R C R₀ C₀ hRC b hb hI hw
  have hsub := angular_core_subsets (o := o) Set.univ A E ha' hd hs
  have hR₀ : R₀ ⊆ R := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      (hsub.1 ⟨Set.mem_univ _, (Finset.mem_filter.mp hv).2⟩).2⟩
  have hC₀ : C₀ ⊆ C := fun v hv ↦
    Finset.mem_filter.mpr ⟨Finset.mem_univ v,
      (hsub.2 ⟨Set.mem_univ _, (Finset.mem_filter.mp hv).2⟩).2⟩
  apply hreset L hL Ω hΩ R C R₀ C₀ hRC hR₀ hC₀ b hb hI
  · intro x hx y hy
    have hx' : sitePosition L x ∈ Set.univ ∩ near (a' * s) A :=
      ⟨Set.mem_univ _, (Finset.mem_filter.mp hx).2⟩
    have hy' : sitePosition L y ∈ Set.univ \ selectedRegion o (d * s) ((3 / 2) * a' * s) A :=
      ⟨Set.mem_univ _, fun hmem ↦ hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)⟩
    have hdist := angular_target_core_clearance (o := o) hd hs hx' hy'
    simpa only [dist_sitePosition_eq_supDist] using hw.trans_lt hdist
  · intro x hx y hy
    have hdist := angular_exterior_core_clearance
      (Λ := Set.univ) (E := E) (a' := a') (s := s)
      (x := sitePosition L x) (y := sitePosition L y)
      ⟨Set.mem_univ _, (Finset.mem_filter.mp hx).2⟩
      ⟨Set.mem_univ _, fun hmem ↦ hy (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hmem⟩)⟩
    simpa only [dist_sitePosition_eq_supDist] using hw.trans_lt hdist

open Classical in
/-- **Uniform information reset at one annular scale, for a family of states.** The proof of
`angular_single_scale_reset_of_sublinearCollarBoundAt` with a cell bound and a reset bound of
the family: every slope `D ≥ angularCellResetSlope C_p a' d` and every size at least
`max (angularCellResetThreshold a' d C_p C₁ M K) L₀` give the information reset at every scale
`s ≥ D log L`.
Source: `02-information.tex`, Proposition 3.4, lines 692–780. -/
theorem angular_single_scale_reset_of_bounds {q : ℕ} {G : ∀ L : ℕ, StateSpace L q → Prop}
    {a a' d p Cp L₀ C₁ K : ℝ}
    (hcell : SquareCellInformationBound q G (angularClearance a a' d) C₁ K)
    (hreset : SquareResetBound q G p Cp L₀) (hC₁ : 0 < C₁) (hK : 0 ≤ K) (hCp : 0 < Cp)
    (ha' : 0 < a') (ha'a : a' < a / 100) (hd : 0 < d) (hda : d < a' / 4) (hd1 : d ≤ 1)
    (hp : 0 < p) (M : ℕ) {D : ℝ} (hD : angularCellResetSlope Cp a' d ≤ D) :
    ∀ L : ℕ, max (angularCellResetThreshold a' d Cp C₁ M K) L₀ ≤ (L : ℝ) →
      ∀ Ω : StateSpace L q, G L Ω →
        ∀ s : ℝ, D * Real.log (L : ℝ) ≤ s →
          ∀ (o : ℝ × ℝ) (Aold A E : Set (ℝ × ℝ)), Aold ⊆ A →
            (∀ x ∈ A, ∀ y ∈ E, (a / 2) * s ≤ dist x y) →
            ∀ S : Finset (ℤ × ℤ),
              (∀ i, i ∈ S ↔
                touches o (d * s) ((3 / 2) * a' * s) A i ∧
                ¬ touches o (d * s) ((3 / 2) * a' * s) Aold i) →
              S.card ≤ M →
              let Rold : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) Aold)
              let Cs : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near ((3 / 2) * a' * s) E)
              let R₀ : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near (a' * s) A)
              let C₀ : Finset (Vertex L) := Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ near (a' * s) E)
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                Ω Rold Cs ≤ (L : ℝ) ^ (-p) →
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q)
                Ω R₀ C₀ ≤ (L : ℝ) ^ (-p) := by
  let c := angularClearance a a' d
  have hc : 0 < c := div_pos (angular_clearance_pos ha' ha'a hda) hd
  have hreset' := angular_information_reset_of_squareResetBound hreset
  have hwidth := angular_reset_width_lt_of_cell_information (N := (M : ℝ)) ha' hd hd1
    hCp hC₁ (Nat.cast_nonneg M) hK hp hD
  intro L hL Ω hΩ s hs o Aold A E hA hsep S hS hSN Rold Cs R₀ C₀ hold
  obtain ⟨hds, hw⟩ := hwidth L ((le_max_left _ _).trans hL) s hs
  have hs0 : 0 < s := (mul_pos_iff_of_pos_left hd).mp (zero_lt_one.trans_le hds)
  have hclear : ∀ x ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A,
      ∀ v ∈ Cs, c * (d * s) ≤ dist x (sitePosition L v) := by
    intro x hx v hv
    have hdist := angular_selectedRegion_clearance hd hs0 hsep hx (Finset.mem_filter.mp hv).2
    have hcoef : c * (d * s) = (a / 2 - 3 * a' - d) * s := by
      simp only [c, angularClearance]
      field_simp
    simpa only [hcoef] using hdist
  have hMI := mutualInformation_selectedRegion_le_of_cell_bound Ω Cs
    (zero_lt_one.trans_le hds) hc hA S hS hclear
    (fun i _ I hi ↦ hcell (d * s) hds o i I hi L Ω hΩ Cs) hold
  let R : Finset (Vertex L) := Finset.univ.filter
    (fun v ↦ sitePosition L v ∈ selectedRegion o (d * s) ((3 / 2) * a' * s) A)
  have hRC : Disjoint R Cs := by
    apply Finset.disjoint_left.mpr
    intro v hv hvC
    have hdist := hclear (sitePosition L v) (Finset.mem_filter.mp hv).2 v hvC
    rw [dist_self] at hdist
    exact (not_le_of_gt (mul_pos hc (zero_lt_one.trans_le hds))) hdist
  have hcost : 0 ≤ C₁ * (1 + Real.log (d * s)) ^ K :=
    mul_nonneg hC₁.le (Real.rpow_nonneg (by linarith [Real.log_nonneg hds]) _)
  have hcard : (S.card : ℝ) ≤ M := by exact_mod_cast hSN
  let b := (L : ℝ) ^ (-p) + (M : ℝ) * (C₁ * (1 + Real.log (d * s)) ^ K)
  have hb : 0 ≤ b := add_nonneg (Real.rpow_nonneg (Nat.cast_nonneg L) _)
    (mul_nonneg (Nat.cast_nonneg M) hcost)
  have hbound : FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω R Cs ≤ b :=
    hMI.trans (add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcard hcost))
  have hw' : Cp * (1 + b + Real.log (L : ℝ)) ≤ a' * s / 2 := by
    dsimp [b]
    nlinarith only [hw, mul_pos ha' hs0]
  exact hreset' L ((le_max_right _ _).trans hL) Ω hΩ o A E a' d s
    ha'.le hd hs0 hRC b hb hbound hw'

/-- **Proposition 3.4 for a family of unit states with the two estimates.** If the states of
`G` are unit vectors and satisfy the cell bound with constants `C₁ > 0`, `K ≥ 0` at the
clearance coefficient of `a' = angularMargin a`, `d = angularCellSide a`, and the reset bound
with width `C_p > 0` and threshold `L₀`, then every slope
`D ≥ angularCellResetSlope C_p a' d` and every threshold
`L₁ ≥ max (angularCellResetThreshold a' d C_p C₁ (angularCellCount a A₀ m₀) K) L₀` form an
angular scale for `G`.
Source: `02-information.tex`, Proposition 3.4 (`prop:angular`), lines 635–785. -/
theorem isAngularScale_of_bounds {q : ℕ} {G : ∀ L : ℕ, StateSpace L q → Prop}
    (hnorm : ∀ L (Ω : StateSpace L q), G L Ω → ‖Ω‖ = 1) {a A₀ Cp L₀ C₁ K : ℝ} (ha : 0 < a)
    (m₀ : ℕ) {p : ℕ} (hp : 0 < p)
    (hcell : SquareCellInformationBound q G
      (angularClearance a (angularMargin a) (angularCellSide a)) C₁ K)
    (hreset : SquareResetBound q G p Cp L₀) (hC₁ : 0 < C₁) (hK : 0 ≤ K) (hCp : 0 < Cp)
    {D L₁ : ℝ} (hD : angularCellResetSlope Cp (angularMargin a) (angularCellSide a) ≤ D)
    (hL₁ : max (angularCellResetThreshold (angularMargin a) (angularCellSide a) Cp C₁
      (angularCellCount a A₀ m₀) K) L₀ ≤ L₁) :
    IsAngularScale q G a A₀ m₀ p D L₁ := by
  classical
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
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
    hd1 hp' (angularCellCount a A₀ m₀) hD
  have hD1 : 1 ≤ D := (one_le_angularCellResetSlope _ _ _).trans hD
  have hLe : Real.exp 1 ≤ L₁ :=
    ((exp_one_le_angularCellResetThreshold _ _ _ _ _ _).trans (le_max_left _ _)).trans hL₁
  refine IsAngularScale.of_sitePosition fun L hL Ω hΩ V hV X E _hXE n hn _hnL hdiam hsep ↦ ?_
  have hlog : 1 ≤ Real.log (L : ℝ) :=
    (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le (hLe.trans hL))).2 (hLe.trans hL)
  have ht : 0 < D * Real.log (L : ℝ) :=
    mul_pos (zero_lt_one.trans_le hD1) (zero_lt_one.trans_le hlog)
  let c := chooseDyadicCutoff ht hn
  apply mutualInformation_le_of_annular_reset Ω (hnorm L Ω hΩ) (ht.trans_le hn) ha.le ha' ha'a
    hd hda' (Real.rpow_nonneg (Nat.cast_nonneg L) (-(p : ℝ))) hdiam hV hsep c
  intro j hj Aold hAold S hS hcard hold
  refine hreset' L (hL₁.trans hL) Ω hΩ (dyadicScale n j)
    (c.lower_at (ht.trans_le hn).le hj) (0, 0) Aold
    (cumulativeLayer (sitePosition L '' X) n V c.last j) (sitePosition L '' E)
    hAold ?_ S hS hcard hold
  intro x hx y hy
  simpa only [div_mul_eq_mul_div] using
    cumulativeLayer_separation c (ht.trans_le hn).le ha.le hsep hj hx hy

/-! ### The two estimates at range `R` -/

open Classical in
/-- **The cell bound on the square from the cell bound on the integer square.** If, for a state
`Ω` of the square, the cell bound of Lemma 3.2 holds for its placement on the integer square
with the grid origin `o - (1, 1)`, then it holds on the square with the origin `o`. A common
translation by `(1, 1)` identifies the two placements of the sites.
Source: `02-information.tex`, Lemma 3.2, lines 161–178, and its application in
Proposition 3.4, lines 688–737. -/
theorem cell_conditionalMutualInformation_le_square_of_rectangle {q L : ℕ}
    (Ω : StateSpace L q) {s c C₀ : ℝ} (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ))
    (hbound : ∀ E : Finset (Site (rectangularDomain L L)),
      E ⊆ (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          x.val ∈ CellPartition.cellSample (o - (1, 1)) s m₀) ∪
        Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          CellPartition.cellIndex (o - (1, 1)) s (integerPoint x.val) ∈ A))ᶜ →
      (∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner (o - (1, 1)) s m₀) s),
        ∀ y ∈ E, c * s ≤ dist x (integerPoint y.val)) →
      FiniteProduct.conditionalMutualInformation
        (fun _ : Site (rectangularDomain L L) ↦ Fin q) (squareAreaLawState Ω)
        (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          x.val ∈ CellPartition.cellSample (o - (1, 1)) s m₀)) E
        (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
          CellPartition.cellIndex (o - (1, 1)) s (integerPoint x.val) ∈ A)) ≤ C₀) :
    let G : Finset (Vertex L) :=
      Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
    let B : Finset (Vertex L) := Finset.univ.filter
      (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
    ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
      (∀ x ∈ closure (AngularGrid.cell o s m₀),
        ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
      FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
        Ω G E B ≤ C₀ := by
  intro G B E hE hclear
  let σ := rectangleSiteEquiv L L
  let o' : ℝ × ℝ := o - (1, 1)
  have hpos (v : Vertex L) :
      integerPoint (σ v).val + (1, 1) = sitePosition L v := by
    simp [σ, integerPoint, sitePosition, rectangleSiteEquiv_val, rectangleEmbedding]
  have hindex (x : ℝ × ℝ) :
      CellPartition.cellIndex o' s x = AngularGrid.owner o s (x + (1, 1)) := by
    unfold CellPartition.cellIndex AngularGrid.owner
    congr 2 <;> simp only [o', Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add] <;>
      ring
  have hboxshift (x : ℝ × ℝ) :
      x ∈ CellPartition.box (CellPartition.cellCorner o' s m₀) s ↔
        x + (1, 1) ∈ AngularGrid.cell o s m₀ := by
    simp only [CellPartition.box, CellPartition.cellCorner, AngularGrid.cell, o',
      Set.mem_ofPred_eq, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add,
      add_mul, one_mul]
    constructor <;> rintro ⟨h₁, h₂, h₃, h₄⟩ <;> refine ⟨?_, ?_, ?_, ?_⟩ <;>
      linarith only [h₁, h₂, h₃, h₄]
  have hG : (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
      x.val ∈ CellPartition.cellSample o' s m₀)) = G.map σ.toEmbedding := by
    ext y
    obtain ⟨v, rfl⟩ := σ.surjective y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, G, CellPartition.cellSample, CellPartition.mem_latticeBox,
      hboxshift, hpos]
  have hB : (Finset.univ.filter (fun x : Site (rectangularDomain L L) ↦
      CellPartition.cellIndex o' s (integerPoint x.val) ∈ A)) = B.map σ.toEmbedding := by
    ext y
    obtain ⟨v, rfl⟩ := σ.surjective y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
      Equiv.symm_apply_apply, B, hindex, hpos]
  have hcl : Set.MapsTo (fun x : ℝ × ℝ ↦ x + (1, 1))
      (closure (CellPartition.box (CellPartition.cellCorner o' s m₀) s))
      (closure (AngularGrid.cell o s m₀)) :=
    (show Set.MapsTo (fun x : ℝ × ℝ ↦ x + (1, 1))
      (CellPartition.box (CellPartition.cellCorner o' s m₀) s)
      (AngularGrid.cell o s m₀) from fun x hx ↦ (hboxshift x).mp hx).closure
      (continuous_id.add continuous_const)
  change ∀ E : Finset (Site (rectangularDomain L L)), _ at hbound
  rw [hG, hB] at hbound
  have hE' : E.map σ.toEmbedding ⊆ (G.map σ.toEmbedding ∪ B.map σ.toEmbedding)ᶜ := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    apply Finset.mem_compl.mpr
    intro hyGB
    exact Finset.mem_compl.mp (hE hv) (by
      simpa only [← Finset.map_union, Finset.mem_map_equiv, Equiv.toEmbedding_apply,
        Equiv.symm_apply_apply] using hyGB)
  have hclear' : ∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner o' s m₀) s),
      ∀ y ∈ E.map σ.toEmbedding, c * s ≤ dist x (integerPoint y.val) := by
    intro x hx y hy
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hy
    have hh := hclear (x + (1, 1)) (hcl hx) v hv
    simpa only [Equiv.toEmbedding_apply, ← hpos, dist_add_right] using hh
  have hfinal := hbound (E.map σ.toEmbedding) hE' hclear'
  simpa only [squareAreaLawState, show rectangleConfigurationEquiv L L q =
    σ.arrowCongr (Equiv.refl (Fin q)) from rfl,
    FiniteProduct.conditionalMutualInformation, ← Finset.map_union,
    finiteProductEntropy_relabel] using hfinal

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
