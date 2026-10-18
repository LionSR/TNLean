/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.AngularWholeCellInformation
import TNLean.PEPS.Approximation.SquareCellConditionalInformation

/-!
# Information of a selected group of square-lattice cells

The original ground state satisfies a uniform information bound for each finite
group of newly selected cells. The old selected region remains in the conditioning
system, and the constants are independent of the subsequent grid and Hamiltonian.
They are the named constants `cellInformationConstant` and `cellInformationExponent` of
Lemma 3.2 (`mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt`).

**Scope restriction (sublinear collar bound):** The sublinear collar estimate is
an explicit premise. This theorem supplies the corresponding conditional step in
polynomial-PEPS Proposition 3.4; it does not derive the collar estimate. See
`docs/paper-gaps/polypeps_angular_annular_geometry_scope.tex`.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 163–311 and 692–732, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

open AngularGrid

open Classical in
/-- **Information of a selected group of cells, with named constants.** Under the range-one
sublinear collar bound with constant `C` and threshold `N`, and the range-one amplification
bound at the input constant `max(C, 1)` and order `1` with constant `C_a` and threshold `N_a`,
adding the newly selected physical cells raises the information with the exterior by at most
`C₁ (1 + log s) ^ K` per cell, with `C₁ = cellInformationConstant q c C_tpl N C_a N_a` and
`K = cellInformationExponent c C_tpl N C_a N_a` of Lemma 3.2.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 161–178 and 713–734. The sublinear collar bound is
an explicit premise of this intermediate implication. -/
theorem mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt
    {q : ℕ} {J Δ D₀ Ctpl C Ca : ℝ} {N Na : ℕ} (hJ : 0 ≤ J)
    (hcol : AreaLaw.SublinearCollarBoundAt q 1 J Δ D₀ Ctpl C N)
    (hamp : AreaLaw.AmplificationBoundAt q 1 J Δ (max C 1) 1 Ca Na)
    {c : ℝ} (hc : 0 < c) :
    ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (r : ℝ) (Aold A : Set (ℝ × ℝ)),
      Aold ⊆ A → ∀ S : Finset (ℤ × ℤ),
        (∀ i, i ∈ S ↔ touches o s r A i ∧ ¬ touches o s r Aold i) →
        ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
          h.IsGappedGroundState E₀ Ω Δ →
          ∀ (E : Finset (Vertex L)) (b₀ : ℝ),
            (∀ x ∈ selectedRegion o s r A, ∀ v ∈ E,
              c * s ≤ dist x (sitePosition L v)) →
            FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
              (Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold)) E ≤ b₀ →
            FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
              (Finset.univ.filter
                (fun v ↦ sitePosition L v ∈ selectedRegion o s r A)) E ≤
              b₀ + (S.card : ℝ) * (cellInformationConstant q c Ctpl N Ca Na *
                (1 + Real.log s) ^ cellInformationExponent c Ctpl N Ca Na) := by
  have hcell :=
    cell_conditionalMutualInformation_le_square_of_sublinearCollarBoundAt hJ hcol hamp hc
  intro s hs o r Aold A hA S hS L h E₀ Ω hΩ E b₀ hclear hold
  exact mutualInformation_selectedRegion_le_of_cell_bound Ω E
    (zero_lt_one.trans_le hs) hc hA S hS hclear
    (fun i _ I hi ↦ hcell s hs o i I hi L h E₀ Ω hΩ E) hold

open Classical in
/-- The original-gap collar hypothesis gives uniform information costs for
adding the actual newly selected physical cells. The constants precede the
scale, grid, ambient sets, physical Hamiltonian, ground vector and exterior.
The old information estimate is retained as the induction input. The constants
are `cellInformationConstant` and `cellInformationExponent`
(`mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt`), at the collar
constant and threshold and at the amplification constant and threshold supplied by
`amplificationBound`.

Source: polynomial-PEPS manuscript, Lemma 3.2 and Proposition 3.4,
`02-information.tex`, lines 163–311 and 692–732. The sublinear collar bound is
an explicit premise of this intermediate implication. -/
theorem exists_mutualInformation_selectedRegion_le_square_of_sublinearCollarBound
    {q : ℕ} {J Δ D₀ Ctpl : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ)
    (hcol : AreaLaw.SublinearCollarBound q 1 J Δ D₀ Ctpl)
    {c : ℝ} (hc : 0 < c) :
    ∃ C₁ K : ℝ, 0 < C₁ ∧ 0 ≤ K ∧
      ∀ s : ℝ, 1 ≤ s → ∀ (o : ℝ × ℝ) (r : ℝ) (Aold A : Set (ℝ × ℝ)),
        Aold ⊆ A → ∀ S : Finset (ℤ × ℤ),
          (∀ i, i ∈ S ↔ touches o s r A i ∧ ¬ touches o s r Aold i) →
          ∀ (L : ℕ) (h : SquareHamiltonian L q J) (E₀ : ℝ) (Ω : StateSpace L q),
            h.IsGappedGroundState E₀ Ω Δ →
            ∀ (E : Finset (Vertex L)) (b₀ : ℝ),
              (∀ x ∈ selectedRegion o s r A, ∀ v ∈ E,
                c * s ≤ dist x (sitePosition L v)) →
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
                (Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ selectedRegion o s r Aold)) E ≤ b₀ →
              FiniteProduct.mutualInformation (fun _ : Vertex L ↦ Fin q) Ω
                (Finset.univ.filter
                  (fun v ↦ sitePosition L v ∈ selectedRegion o s r A)) E ≤
                b₀ + (S.card : ℝ) * (C₁ * (1 + Real.log s) ^ K)
 := by
  obtain ⟨C, N, hcol⟩ := hcol
  obtain ⟨Ca, Na, hamp⟩ := exists_amplificationBoundAt_max_one (q := q) (R := 1) (J := J) hΔ C
  exact ⟨_, _, cellInformationConstant_pos q c Ctpl N Ca Na,
    (cellInformationExponent_pos c Ctpl N Ca Na).le,
    mutualInformation_selectedRegion_le_square_of_sublinearCollarBoundAt hJ hcol hamp hc⟩

end TNLean.PEPS.Approximation
