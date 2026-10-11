/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SheetSwapDoubledCancellation
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

open Matrix
open scoped BigOperators

namespace TNLean.PEPS.Approximation

/-- Only the original crossing-edge interactions contribute to the partial-swap
perturbation. The individual interactions need not be Hermitian, and zero local
dimension and empty square grids are included.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem SquareHamiltonian.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J)
    (R : Finset (SquareLatticeVertex L L)) :
    let F := EncodedFrame.sheetSwapOp q R
    F * doubledHamiltonian h.operator * Fᴴ - doubledHamiltonian h.operator =
      ∑ e ∈ Finset.univ.filter (IsRegionBoundaryEdge R),
        (F * doubledHamiltonian (h.edgeTerm e) * Fᴴ -
          doubledHamiltonian (h.edgeTerm e)) := by
  classical
  let δ : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (LinearMap.mulLeftRight ℂ
      (EncodedFrame.sheetSwapOp q R, (EncodedFrame.sheetSwapOp q R)ᴴ) -
      LinearMap.id).comp
      ((Matrix.kroneckerBilinear (R := ℂ)).flip
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
        Matrix.kroneckerBilinear (R := ℂ)
          (1 : Matrix (Configuration L q) (Configuration L q) ℂ))
  change δ h.operator = ∑ e ∈ Finset.univ.filter (IsRegionBoundaryEdge R), δ (h.edgeTerm e)
  simp only [SquareHamiltonian.operator, map_add, map_sum]
  done

end TNLean.PEPS.Approximation
