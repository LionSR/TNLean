/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.CoarseInformationFromGap
import TNLean.PEPS.Approximation.SquareCellConditionalInformation

/-!
# Cell information from the original spectral gap

The original full-system gap gives a uniform conditional-information bound for one grid
cell, conditioned on an arbitrary union of other cells. The proof applies the physical
sublinear collar theorem at range one, clearance 13 and template constant 24, then uses
the square-grid cell estimate. The state, exterior region and conditioning cells are unchanged.

At the closed-form collar constant and threshold `collarConstantClosed q R J Δ` and
`collarThresholdClosed q R J Δ`, the prefactor and exponent of the cell bound are closed-form
functions of `q, R, J, Δ` and the clearance coefficient `c` (`cellInformationConstantClosed`,
`cellInformationExponentClosed`). The square statement takes them at range one. At every range
`R`, `cell_conditionalMutualInformation_le_closed` gives the cell bound on finite integer domains
at these constants, with no collar or amplification premise. The source has only site and
nearest-neighbour terms, so range `R` extends it.

Source: polynomial-PEPS manuscript, Lemma 3.2, `02-information.tex`, lines 163–222
and 304–311, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

/-- The prefactor of Lemma 3.2 at closed-form constants and range `R`:
`cellInformationConstant` at the template constant `24`, the collar threshold
`collarThresholdClosed q R J Δ`, and the amplification constant and threshold at the collar
constant `collarConstantClosed q R J Δ`. The source has range one; range `R` extends it.
Source: polynomial-PEPS Lemma 3.2, `02-information.tex`, lines 163–222. -/
noncomputable def cellInformationConstantClosed (q R : ℕ) (J Δ c : ℝ) : ℝ :=
  cellInformationConstant q c 24 (collarThresholdClosed q R J Δ)
    (collarAmplificationConstant q R J Δ (collarConstantClosed q R J Δ))
    (collarAmplificationThreshold q R J Δ (collarConstantClosed q R J Δ))

/-- The exponent of Lemma 3.2 at closed-form constants and range `R`:
`cellInformationExponent` at the constants of `cellInformationConstantClosed`. Source:
polynomial-PEPS Lemma 3.2, `02-information.tex`, lines 163–222. -/
noncomputable def cellInformationExponentClosed (q R : ℕ) (J Δ c : ℝ) : ℝ :=
  cellInformationExponent c 24 (collarThresholdClosed q R J Δ)
    (collarAmplificationConstant q R J Δ (collarConstantClosed q R J Δ))
    (collarAmplificationThreshold q R J Δ (collarConstantClosed q R J Δ))

/-- The closed-form prefactor of Lemma 3.2 is positive. -/
theorem cellInformationConstantClosed_pos (q R : ℕ) (J Δ c : ℝ) :
    0 < cellInformationConstantClosed q R J Δ c :=
  cellInformationConstant_pos _ _ _ _ _ _

/-- The closed-form exponent of Lemma 3.2 is positive. -/
theorem cellInformationExponentClosed_pos (q R : ℕ) (J Δ c : ℝ) :
    0 < cellInformationExponentClosed q R J Δ c :=
  cellInformationExponent_pos _ _ _ _ _

open Classical in
/-- **Lemma 3.2 at range `R` and closed-form constants.** For `q ≥ 1`, `J ≥ 0`, `Δ > 0` and
`c > 0`, the conditional information of one cell of a finite integer domain, given the sample
of an arbitrary union of other cells, in a gapped ground state of a range-`R` Hamiltonian with
interaction bound `J`, is at most
`cellInformationConstantClosed q R J Δ c * (1 + log s) ^ cellInformationExponentClosed q R J Δ c`
for every region at distance at least `c s` from the closed cell. There is no collar or
amplification premise. The source has only site and nearest-neighbour terms; range `R` extends
it. Source: polynomial-PEPS Lemma 3.2, `02-information.tex`, lines 163–222 and 304–311. -/
theorem cell_conditionalMutualInformation_le_closed
    {q R : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
      m₀ ∉ A →
      ∀ (Λ : Finset (ℤ × ℤ)) (h : Lattice.LocalHamiltonian Λ q R J)
        (E₀ : ℝ) (Ω : Lattice.StateSpace Λ q),
        Lattice.IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        let G : Finset (Site Λ) :=
          Finset.univ.filter (fun x ↦ x.val ∈ CellPartition.cellSample o s m₀)
        let B : Finset (Site Λ) := Finset.univ.filter
          (fun x ↦ CellPartition.cellIndex o s (AreaLaw.Geometry.integerPoint x.val) ∈ A)
        ∀ E : Finset (Site Λ), E ⊆ (G ∪ B)ᶜ →
          (∀ x ∈ closure (CellPartition.box (CellPartition.cellCorner o s m₀) s),
            ∀ y ∈ E, c * s ≤ dist x (AreaLaw.Geometry.integerPoint y.val)) →
          FiniteProduct.conditionalMutualInformation (fun _ : Site Λ ↦ Fin q)
            Ω G E B ≤ cellInformationConstantClosed q R J Δ c *
              (1 + Real.log s) ^ cellInformationExponentClosed q R J Δ c :=
  cell_conditionalMutualInformation_le_of_sublinearCollarBoundAt
    (sublinearCollarBoundAt_closed (R := R) (D₀ := 2 * (R : ℝ) + 11) hq hJ hΔ (by linarith))
    (amplificationBoundAt_collarAmplification hΔ _) hc

open Classical in
/-- **Lemma 3.2 on the original open square, at closed-form constants.** For `q ≥ 1`,
`J ≥ 0`, `Δ > 0` and `c > 0`, the cell conditional-information bound holds with the
prefactor `cellInformationConstantClosed q 1 J Δ c` and the exponent
`cellInformationExponentClosed q 1 J Δ c`. There is no collar or amplification premise.
Source: polynomial-PEPS Lemma 3.2, `02-information.tex`, lines 163–222 and 304–311. -/
theorem cell_conditionalMutualInformation_le_square_closed
    {q : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
      m₀ ∉ A →
      ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
        h.IsGappedGroundState E₀ Ω Δ →
        let G : Finset (Vertex L) :=
          Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
        let B : Finset (Vertex L) := Finset.univ.filter
          (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
        ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
          (∀ x ∈ closure (AngularGrid.cell o s m₀),
            ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
          FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
            Ω G E B ≤ cellInformationConstantClosed q 1 J Δ c *
              (1 + Real.log s) ^ cellInformationExponentClosed q 1 J Δ c :=
  cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt_explicit hJ hΔ
    (sublinearCollarBoundAt_closed (R := 1) (D₀ := 13) hq hJ hΔ (by norm_num)) hc

open Classical in
/-- Conditional mutual information of a square cell in an original gapped
square-grid ground state. The constants are uniform over the scale, translated
grid, conditioning cells, Hamiltonian, ground vector and exterior region.
Source: polynomial-PEPS manuscript, Lemma 3.2, `02-information.tex`, lines
163–222 and 304–311, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The statement includes the cases of local dimension one and interaction bound
zero; it imposes no collar or area-law premise. -/
theorem exists_cell_conditionalMutualInformation_le_square
    {q : ℕ} (hq : 1 ≤ q) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    {c : ℝ} (hc : 0 < c) :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (m₀ : ℤ × ℤ) (A : Set (ℤ × ℤ)),
        m₀ ∉ A →
        ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          let G : Finset (Vertex L) :=
            Finset.univ.filter (fun v ↦ sitePosition L v ∈ AngularGrid.cell o s m₀)
          let B : Finset (Vertex L) := Finset.univ.filter
            (fun v ↦ AngularGrid.owner o s (sitePosition L v) ∈ A)
          ∀ E : Finset (Vertex L), E ⊆ (G ∪ B)ᶜ →
            (∀ x ∈ closure (AngularGrid.cell o s m₀),
              ∀ y ∈ E, c * s ≤ dist x (sitePosition L y)) →
            FiniteProduct.conditionalMutualInformation (fun _ : Vertex L ↦ Fin q)
              Ω G E B ≤ C₁ * (1 + Real.log s) ^ K := by
  have hcol : AreaLaw.SublinearCollarBound q 1 J Δ 13 24 :=
    AreaLaw.sublinearCollarBound_real q 1 hq hJ hΔ (by norm_num) (by norm_num)
  exact exists_cell_conditionalMutualInformation_le_square_of_sublinearCollarBound
    hJ hΔ hcol hc

end TNLean.PEPS.Approximation
