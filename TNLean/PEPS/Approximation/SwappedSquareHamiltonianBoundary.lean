/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SheetSwapBoundaryExpansion
import TNLean.PEPS.Approximation.SheetSwapConjugateSupport
import TNLean.PEPS.Approximation.SheetSwapDoubledTermNorm
import TNLean.PEPS.SquareLatticeEdgeCount
import QICLean.Algebra.L2OpNormReindex

/-!
# The boundary perturbation of a doubled square Hamiltonian

The partial swap changes only the original interactions crossing the chosen
region. In paired-site coordinates, the resulting perturbation is supported
on their endpoints and has norm at most eight times the interaction bound
times the number of sites.

The original individual interactions need not be Hermitian. No sign assumption
on the interaction bound is added: on a nonempty grid it follows from any
original site bound, whereas an empty grid has zero Hamiltonian.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `02-information.tex`, lines 416–424 and 513–524,
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.PEPS.Approximation

/-- The actual partial-swap perturbation is supported on the endpoints of
the original crossing edges and has norm at most `8 J L²`. Empty grids and
zero local dimension are included, and the original individual interactions
need not be Hermitian.

Source: polynomial-PEPS manuscript, `02-information.tex`, lines 416–424 and 513–524. -/
theorem SquareHamiltonian.swapped_doubled_boundary_bound
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J)
    (R : Finset (SquareLatticeVertex L L)) :
    let p := sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.operator)
    let F := Matrix.reindex p p (EncodedFrame.sheetSwapOp q R)
    let boundary : Finset (Edge (squareLatticeGraph L L)) :=
      Finset.univ.filter (IsRegionBoundaryEdge R)
    let Z := boundary.biUnion fun e ↦ ({e.1.1, e.1.2} : Finset (SquareLatticeVertex L L))
    F * K * Fᴴ - K ∈ supportedOperators (q * q) (Z : Set (SquareLatticeVertex L L)) ∧
      ‖F * K * Fᴴ - K‖ ≤ 8 * J * (L : ℝ) ^ 2 := by
  classical
  intro p K F boundary Z
  have hsum := congrArg (Matrix.reindex p p)
    (h.sheetSwapOp_conj_doubled_operator_sub_eq_sum_crossing R)
  simp only [← Matrix.coe_reindexRingEquiv, map_sum, map_sub, map_mul] at hsum
  change F * K * Fᴴ - K = ∑ e ∈ boundary,
    (F * Matrix.reindex p p (doubledHamiltonian (h.edgeTerm e)) * Fᴴ -
      Matrix.reindex p p (doubledHamiltonian (h.edgeTerm e))) at hsum
  have hnorm (A : Matrix (Configuration L q) (Configuration L q) ℂ) :
      ‖F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ -
        Matrix.reindex p p (doubledHamiltonian A)‖ ≤ 4 * ‖A‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      (Matrix.l2_opNorm_reindex_equiv p
        (EncodedFrame.sheetSwapOp q R * doubledHamiltonian A *
          (EncodedFrame.sheetSwapOp q R)ᴴ - doubledHamiltonian A)).trans_le
        (EncodedFrame.norm_sheetSwapOp_conj_doubledHamiltonian_sub_le R A)
  have hplain (S : Finset (SquareLatticeVertex L L))
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ supportedOperators q (S : Set (SquareLatticeVertex L L))) :
      Matrix.reindex p p (doubledHamiltonian A) ∈
        supportedOperators (q * q) (S : Set (SquareLatticeVertex L L)) := by
    simpa only [Matrix.conjTranspose_submatrix, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv,
      EncodedFrame.sheetSwapOp_conj_doubledHamiltonian_eq_of_mem_supportedOperators
        (R := ∅) hA (Or.inr (by simp))] using!
      EncodedFrame.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators ∅ S hA
  have hlocal (S : Finset (SquareLatticeVertex L L))
      {A : Matrix (Configuration L q) (Configuration L q) ℂ}
      (hA : A ∈ supportedOperators q (S : Set (SquareLatticeVertex L L))) :
      F * Matrix.reindex p p (doubledHamiltonian A) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian A) ∈
        supportedOperators (q * q) (S : Set (SquareLatticeVertex L L)) :=
    (supportedOperators (q * q) (S : Set (SquareLatticeVertex L L))).sub_mem
      (EncodedFrame.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators R S hA)
      (hplain S hA)
  have hsupport : F * K * Fᴴ - K ∈
      supportedOperators (q * q) (Z : Set (SquareLatticeVertex L L)) :=
    hsum.symm ▸ (supportedOperators (q * q) (Z : Set (SquareLatticeVertex L L))).sum_mem
      (fun e he ↦ supportedOperators_mono
        (Finset.coe_subset.mpr (Finset.subset_biUnion_of_mem
          (fun e : Edge (squareLatticeGraph L L) ↦
            ({e.1.1, e.1.2} : Finset (SquareLatticeVertex L L))) he))
        (hlocal {e.1.1, e.1.2}
          (by simpa only [Finset.coe_insert, Finset.coe_singleton] using h.edge_supported e)))
  have hbound : ‖F * K * Fᴴ - K‖ ≤ (boundary.card : ℝ) * (4 * J) := by
    simpa only [hsum, nsmul_eq_mul] using
      (norm_sum_le boundary (fun e ↦
        F * Matrix.reindex p p (doubledHamiltonian (h.edgeTerm e)) * Fᴴ -
          Matrix.reindex p p (doubledHamiltonian (h.edgeTerm e)))).trans
        (Finset.sum_le_card_nsmul boundary _ (4 * J) (fun e _ ↦
          (hnorm (h.edgeTerm e)).trans
            (mul_le_mul_of_nonneg_left (h.edge_norm_le e) (by norm_num))))
  done

end TNLean.PEPS.Approximation
