/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SwappedPlaneInteraction
import TNLean.PEPS.AreaLaw.TailParameter

/-!
# The edge-boundary norm of a partially swapped doubled Hamiltonian

For a finite-domain Hamiltonian of interaction range `R` and term bound `J ≥ 0`,
the partial swap changes its doubled Hamiltonian by an operator of norm at most
`4 μ_R v_R J` times the number of boundary edges of the swapped region, where
`v_R = 1 + 2 R (R + 1)` and `μ_R = 2^(v_R - 1)`.

This is a finite-range extension of the polynomial-PEPS manuscript,
`02-information.tex`, lines 416–424 and 513–524. The crossing-support count is
from the area-law manuscript, `02-initial.tex`, lines 202–206.
The whole-domain estimate in `SwappedPlaneInteraction` remains available.
-/

open Matrix QuantumCircuit
open scoped BigOperators Kronecker Matrix.Norms.L2Operator

open ManyBody (AdmissibleSupport PlaneInteraction)

namespace ManyBody.PlaneInteraction

open TNLean.Lattice

/-- The edge-boundary norm estimate for the actual swapped doubled Hamiltonian.
This finite-range extension combines polynomial-PEPS `02-information.tex`,
lines 416–424 and 513–524, with the area-law crossing-support count in
`02-initial.tex`, lines 202–206. The coefficient retains the diamond count
`v_R = 1 + 2 R (R + 1)`. -/
theorem swapped_doubled_boundary_bound_edgeBoundary
    {Λ : Finset (ℤ × ℤ)} {q R : ℕ} {J : ℝ}
    (h : PlaneInteraction Λ q R) (hhJ : ∀ X, ‖h.term X‖ ≤ J) (hJ : 0 ≤ J)
    (A : Finset (Site Λ)) :
    let p := sitePairConfigurationEquiv (Site Λ) q q
    let K := Matrix.reindex p p (doubledHamiltonian h.hamiltonian)
    let F := Matrix.reindex p p (sheetSwapOp q A)
    ‖F * K * Fᴴ - K‖ ≤
      swapBoundaryCoefficient R * ((1 + 2 * R * (R + 1) : ℕ) : ℝ) *
        J * ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) := by
  intro p K F
  classical
  have hsum := h.sheetSwapOp_conj_doubled_hamiltonian_sub_eq_sum_crossing A
  have hpaired : ‖F * K * Fᴴ - K‖ =
      ‖sheetSwapOp q A * doubledHamiltonian h.hamiltonian * (sheetSwapOp q A)ᴴ -
        doubledHamiltonian h.hamiltonian‖ := by
    simpa only [Matrix.reindex_apply, Matrix.submatrix_sub, Pi.sub_apply,
      ← Matrix.submatrix_mul_equiv (e₂ := p.symm), ← Matrix.conjTranspose_submatrix] using!
      Matrix.l2_opNorm_reindex_equiv p
        (sheetSwapOp q A * doubledHamiltonian h.hamiltonian * (sheetSwapOp q A)ᴴ -
          doubledHamiltonian h.hamiltonian)
  rw [hpaired, hsum]
  refine (norm_sum_le _ _).trans ?_
  have hterm (X : AdmissibleSupport Λ R) :
      ‖sheetSwapOp q A * doubledHamiltonian (h.term X) * (sheetSwapOp q A)ᴴ -
        doubledHamiltonian (h.term X)‖ ≤ 4 * J :=
    (TNLean.PEPS.EncodedFrame.norm_sheetSwapOp_conj_doubledHamiltonian_sub_le A (h.term X)).trans
      (mul_le_mul_of_nonneg_left (hhJ X) (by norm_num))
  refine (Finset.sum_le_card_nsmul _ _ (4 * J) (fun X _ ↦ hterm X)).trans ?_
  have hcard : ((ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card : ℝ) ≤
      ((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) *
        (((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) := by
    exact_mod_cast TNLean.PEPS.AreaLaw.card_crossingTerms_le_edgeBoundary Λ R A
  calc
    _ = ((ManyBody.crossingTerms (fun X : AdmissibleSupport Λ R ↦ X.1) A).card : ℝ) * (4 * J) :=
      nsmul_eq_mul _ _
    _ ≤ (((edgeBoundary (planeDomainGraph Λ) A).card : ℝ) *
        (((1 + 2 * R * (R + 1)) * 2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ)) * (4 * J) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      simp only [swapBoundaryCoefficient, Nat.cast_mul]
      ring

end ManyBody.PlaneInteraction
