/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
import TNLean.PEPS.Approximation.SheetSwapCorrection
import TNLean.PEPS.Approximation.SheetSwapConjugateSupport
import TNLean.Circuit.SitewiseTensorSupport
import QICLean.Analysis.DoubledSystemGap

/-!
# The local interactions of the partially swapped doubled Hamiltonian

Take the Hermitian part of each original site and edge interaction, double
it, pair the two coordinates at every site, and conjugate by the actual
partial swap. Each resulting term acts on its original designated support
and has norm at most twice the original bound. The sum is exactly the
partially swapped doubled Hamiltonian, since the original total is Hermitian.

## References

OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `00-introduction.tex`, `eq:model`, and
`02-information.tex`, lines 416–424 and 498–524, revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.Approximation

/-- The actual local interaction family of the swapped doubled Hamiltonian.
Its term at each original support is the conjugated doubled Hermitian part;
unused admissible supports carry zero. Only the original total is required
to be Hermitian. No ground-state or gap hypothesis is needed.

Source: polynomial-PEPS `eq:model` and `02-information.tex`, lines 416–424,
where pairing the two replicas at each site preserves range one. -/
theorem SquareHamiltonian.exists_swapped_doubled_localHamiltonian
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) (hJ : 0 ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let p := QuantumCircuit.sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
    let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
    let F := Matrix.reindex p p (EncodedFrame.sheetSwapOp q R)
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.operator)
    ∃ g : AreaLaw.LocalHamiltonian (AreaLaw.rectangularDomain L L) (q * q) 1 (2 * J),
      g.term = Function.extend (squareAreaLawSupport L)
        (fun i : SquareInteraction L =>
          Matrix.reindex e e
            (F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i)) * Fᴴ)) 0 ∧
      g.operator = Matrix.reindex e e (F * K * Fᴴ) := by
  classical
  intro p e F K
  let B (i : SquareInteraction L) :=
    F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i)) * Fᴴ
  have hBsupport (i : SquareInteraction L) : B i ∈
      QuantumCircuit.supportedOperators (q * q) (squareInteractionSupport i : Set (Vertex L)) :=
    EncodedFrame.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators R
      (squareInteractionSupport i) (h.hermitianTerm_mem_supportedOperators i)
  have hFn : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv p (EncodedFrame.sheetSwapOp q R)).le.trans
      (EncodedFrame.norm_sheetSwapOp_le_one R)
  have hDn (i : SquareInteraction L) : ‖Matrix.doubledHamiltonian (h.hermitianTerm i)‖ ≤
      J + J :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.l2_opNorm_kronecker_one_le _).trans (h.hermitianTerm_norm_le i))
      ((Matrix.l2_opNorm_one_kronecker_rect_le _).trans (h.hermitianTerm_norm_le i)))
  have hBn (i : SquareInteraction L) : ‖B i‖ ≤ 2 * J := by
    simpa only [B, one_mul, mul_one, two_mul] using
      norm_mul_le_of_le
        (norm_mul_le_of_le hFn ((Matrix.l2_opNorm_reindex_equiv p _).le.trans (hDn i)))
        ((Matrix.l2_opNorm_conjTranspose F).trans_le hFn)
  have hDH (i : SquareInteraction L) :
      (Matrix.doubledHamiltonian (h.hermitianTerm i)).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.doubledHamiltonian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (h.hermitianTerm_isHermitian i).eq]
  have hBH (i : SquareInteraction L) : (B i).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose F ((hDH i).reindex p)
  have hBedge (a : Edge (squareLatticeGraph L L)) :
      B (.inr ((forwardSquareEdgeEquiv L).symm a)) ∈
        QuantumCircuit.supportedOperators (q * q) {a.1.1, a.1.2} := by
    simpa only [squareInteractionSupport, Finset.coe_insert, Finset.coe_singleton,
      forwardSquareEdgeEquiv_symm_val] using
        hBsupport (.inr ((forwardSquareEdgeEquiv L).symm a))
  have hBsite (v : Vertex L) :
      B (.inl v) ∈ QuantumCircuit.supportedOperators (q * q) {v} := by
    simpa only [squareInteractionSupport, Finset.coe_singleton] using hBsupport (.inl v)
  done

end TNLean.PEPS.Approximation
