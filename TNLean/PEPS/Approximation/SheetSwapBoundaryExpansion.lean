/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import QICLean.ManyBody.Sites.PlacedConfiguration
import QICLean.ManyBody.Sites.ProductVector
import QICLean.ManyBody.Entropy.Cut.RegionUnion
import TNLean.Lattice.RegionalSwapSupport
import TNLean.PEPS.RegionBlock.Basic

/-!
# The crossing-edge expansion of a swapped Hamiltonian

The difference between a doubled square Hamiltonian and its conjugate by the
regional sheet swap is the sum of the corresponding differences for the
original crossing-edge interactions. All site interactions and all remaining
edge interactions cancel.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*
  (September 24, 2026), `02-information.tex`, lines 416–424 and 513–524,
  revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped Matrix.Norms.L2Operator

open ManyBody (Edge SquareLatticeVertex squareLatticeGraph SquareInteraction)

open Matrix
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- Only the original crossing-edge interactions contribute to the partial-swap
perturbation. The individual interactions need not be Hermitian, and zero local
dimension and empty square grids are included.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem _root_.ManyBody.SquareInteraction.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing
    {L q : ℕ} (h : SquareInteraction L q) (R : Finset (SquareLatticeVertex L L)) :
    let F := TNLean.Lattice.sheetSwapOp q R
    F * doubledHamiltonian h.hamiltonian * Fᴴ - doubledHamiltonian h.hamiltonian =
      ∑ e ∈ Finset.univ.filter (IsRegionBoundaryEdge R),
        (F * doubledHamiltonian (h.term (.inr e)) * Fᴴ -
          doubledHamiltonian (h.term (.inr e))) := by
  classical
  let δ : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (LinearMap.mulLeftRight ℂ
      (TNLean.Lattice.sheetSwapOp q R, (TNLean.Lattice.sheetSwapOp q R)ᴴ) -
      LinearMap.id).comp
      ((Matrix.kroneckerBilinear (R := ℂ)).flip
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
        Matrix.kroneckerBilinear (R := ℂ)
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ))
  change δ h.hamiltonian = ∑ e ∈ Finset.univ.filter (IsRegionBoundaryEdge R), δ (h.term (.inr e))
  simp only [ManyBody.Interaction.hamiltonian, Fintype.sum_sum_type, map_add, map_sum]
  have hcancel {S : Finset (SquareLatticeVertex L L)}
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin q) S)
      (hS : S ⊆ R ∨ Disjoint S R) :
      δ A = 0 :=
    sub_eq_zero.mpr
      (TNLean.Lattice.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
        hA hS)
  have hedge (e : Edge (squareLatticeGraph L L)) (he : ¬ IsRegionBoundaryEdge R e) :
      δ (h.term (.inr e)) = 0 := by
    apply hcancel (h.mem (.inr e))
    simp only [ManyBody.squareLatticeSiteOrEdgeSupport, IsRegionBoundaryEdge,
      Finset.insert_subset_iff, Finset.singleton_subset_iff, Finset.disjoint_insert_left,
      Finset.disjoint_singleton_left] at he ⊢
    tauto
  have hsite (v : SquareLatticeVertex L L) : δ (h.term (.inl v)) = 0 :=
    hcancel (h.mem (.inl v)) (by
      simp only [ManyBody.squareLatticeSiteOrEdgeSupport, Finset.singleton_subset_iff,
        Finset.disjoint_singleton_left]
      exact em _)
  rw [Finset.sum_eq_zero fun v _ => hsite v, zero_add]
  refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
  intro e _ hne
  exact hedge e fun hb => hne (Finset.mem_filter.mpr ⟨Finset.mem_univ e, hb⟩)

end TNLean.PEPS.Approximation
