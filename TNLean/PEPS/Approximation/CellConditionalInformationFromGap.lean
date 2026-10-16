/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareCellConditionalInformation
import TNLean.PEPS.AreaLaw.PhysicalCollarInformation

/-!
# Cell information from the original spectral gap

The original full-system gap gives a uniform conditional-information bound for one grid
cell, conditioned on an arbitrary union of other cells. The proof applies the physical
sublinear collar theorem at range one, clearance 13 and template constant 24, then uses
the square-grid cell estimate. The state, exterior region and conditioning cells are unchanged.

Source: polynomial-PEPS manuscript, Lemma 3.2, `02-information.tex`, lines 163–222
and 304–311, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

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
