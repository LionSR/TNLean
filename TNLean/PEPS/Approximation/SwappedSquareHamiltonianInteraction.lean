/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularHamiltonian
import TNLean.PEPS.Approximation.Basic
import TNLean.PEPS.Approximation.SquareGridContraction
import TNLean.Lattice.Sheet.SwapCorrection
import TNLean.Lattice.RegionalSwapSupport
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

open ManyBody (SquareLatticeVertex SquareLatticeSiteOrEdge squareLatticeSiteOrEdgeSupport
  SquareInteraction)

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.Approximation

/-- The actual local interaction family of the swapped doubled Hamiltonian.
Its term at each original support is the conjugated doubled Hermitian part;
unused admissible supports carry zero. Only the original total is required
to be Hermitian. No ground-state or gap hypothesis is needed.

Source: polynomial-PEPS `eq:model` and `02-information.tex`, lines 416–424,
where pairing the two replicas at each site preserves range one. -/
theorem _root_.ManyBody.SquareInteraction.exists_swapped_doubled_planeInteraction
    {L q : ℕ} {J : ℝ} (h : SquareInteraction L q) (hh : h.hamiltonian.IsHermitian)
        (hhJ : ∀ i, ‖h.term i‖ ≤ J) (hJ : 0 ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let p := QuantumCircuit.sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
    let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
    let F := Matrix.reindex p p (TNLean.Lattice.sheetSwapOp q R)
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.hamiltonian)
    ∃ g : ManyBody.PlaneInteraction (AreaLaw.rectangularDomain L L) (q * q) 1,
      (∀ X, (g.term X).IsHermitian) ∧ (∀ X, ‖g.term X‖ ≤ 2 * J) ∧ g.term =
          Function.extend (AreaLaw.rectangleAreaLawSupport L L)
        (fun i : SquareLatticeSiteOrEdge L L =>
          Matrix.reindex e e
            (F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i)) * Fᴴ)) 0 ∧
      g.hamiltonian = Matrix.reindex e e (F * K * Fᴴ) := by
  classical
  intro p e F K
  let B (i : SquareLatticeSiteOrEdge L L) :=
    F * Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i)) * Fᴴ
  have hBsupport (i : SquareLatticeSiteOrEdge L L) : B i ∈
      ManyBody.supportedOperators (fun _ ↦ Fin (q * q))
          (squareLatticeSiteOrEdgeSupport i : Finset (Vertex L)) :=
    TNLean.Lattice.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators R
      (squareLatticeSiteOrEdgeSupport i)
          (h.hermitianPart.mem i)
  have hFn : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv p (TNLean.Lattice.sheetSwapOp q R)).le.trans
      (TNLean.Lattice.norm_sheetSwapOp_le_one R)
  have hDn (i : SquareLatticeSiteOrEdge L L) : ‖Matrix.doubledHamiltonian
      (h.hermitianPart.term i)‖ ≤
      J + J :=
    (norm_add_le _ _).trans (add_le_add
      ((Matrix.l2_opNorm_kronecker_one_le _).trans
          ((h.norm_hermitianPart_term_le i).trans (hhJ i)))
      ((Matrix.l2_opNorm_one_kronecker_le _).trans
          ((h.norm_hermitianPart_term_le i).trans (hhJ i))))
  have hBn (i : SquareLatticeSiteOrEdge L L) : ‖B i‖ ≤ 2 * J := by
    simpa only [B, one_mul, mul_one, two_mul] using
      norm_mul_le_of_le
        (norm_mul_le_of_le hFn ((Matrix.l2_opNorm_reindex_equiv p _).le.trans (hDn i)))
        ((Matrix.l2_opNorm_conjTranspose F).trans_le hFn)
  have hDH (i : SquareLatticeSiteOrEdge L L) :
      (Matrix.doubledHamiltonian (h.hermitianPart.term i)).IsHermitian := by
    simp only [Matrix.IsHermitian, Matrix.doubledHamiltonian, Matrix.conjTranspose_add,
      Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      (h.isHermitian_hermitianPart_term i).eq]
  have hBH (i : SquareLatticeSiteOrEdge L L) : (B i).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose F ((hDH i).reindex p)
  -- The doubled map is additive in its argument, so summing the doubled Hermitian
  -- parts recovers the doubled total.
  let D : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (Matrix.kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
      Matrix.kroneckerBilinear (R := ℂ)
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ)
  have hDsum : (∑ i : SquareLatticeSiteOrEdge L L,
      Matrix.doubledHamiltonian (h.hermitianPart.term i)) =
      Matrix.doubledHamiltonian h.hamiltonian := by
    change (∑ i : SquareLatticeSiteOrEdge L L, D (h.hermitianPart.term i)) = D h.hamiltonian
    rw [← map_sum D, ← h.hamiltonian_hermitianPart hh]; rfl
  -- The actual interaction family sums exactly to the swapped doubled total, since
  -- the conjugation and the bond reindexing are additive.
  have key : (∑ i : SquareLatticeSiteOrEdge L L, B i) = F * K * Fᴴ := by
    have hreindex : (∑ i : SquareLatticeSiteOrEdge L L,
        Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i))) = K := by
      change (∑ i : SquareLatticeSiteOrEdge L L,
        (Matrix.reindexAlgEquiv ℂ ℂ p) (Matrix.doubledHamiltonian (h.hermitianPart.term i))) = K
      rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ p), hDsum]
      rfl
    calc (∑ i : SquareLatticeSiteOrEdge L L, B i)
        = F * (∑ i : SquareLatticeSiteOrEdge L L,
            Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianPart.term i))) * Fᴴ := by
          simp only [B, Finset.mul_sum, Finset.sum_mul]
      _ = F * K * Fᴴ := by rw [hreindex]
  refine ⟨{ term := Function.extend (AreaLaw.rectangleAreaLawSupport L L)
              (fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)) 0
            mem := ?_ }, ?_, ?_, rfl, ?_⟩
  · intro X
    by_cases hx : ∃ i, AreaLaw.rectangleAreaLawSupport L L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(AreaLaw.rectangleAreaLawSupport_injective L L).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (AreaLaw.rectangleSiteEquiv L L).injective (hBsupport i)
      rw [AreaLaw.embedOp_rectangular_eq_reindex] at hs
      simpa only [AreaLaw.rectangleAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      exact zero_mem _
  · intro X
    dsimp only
    by_cases hx : ∃ i, AreaLaw.rectangleAreaLawSupport L L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(AreaLaw.rectangleAreaLawSupport_injective L L).extend_apply]
      exact (hBH i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    dsimp only
    by_cases hx : ∃ i, AreaLaw.rectangleAreaLawSupport L L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(AreaLaw.rectangleAreaLawSupport_injective L L).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (B i)).le.trans (hBn i)
    · rw [Function.extend_apply' _ _ _ hx]
      simpa only [Pi.zero_apply, norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ
  · let T := fun i : SquareLatticeSiteOrEdge L L => Matrix.reindex e e (B i)
    have hsum : (∑ i : SquareLatticeSiteOrEdge L L, T i) =
        ∑ X : ManyBody.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1,
          Function.extend (AreaLaw.rectangleAreaLawSupport L L) T 0 X := by
      apply Finset.sum_of_injOn (AreaLaw.rectangleAreaLawSupport L L)
        (AreaLaw.rectangleAreaLawSupport_injective L L).injOn (fun _ _ => Finset.mem_univ _)
      · intro X _ hX
        exact Function.extend_apply' _ _ _ (by simpa using hX)
      · intro i _
        exact ((AreaLaw.rectangleAreaLawSupport_injective L L).extend_apply T 0 i).symm
    change (∑ X, Function.extend (AreaLaw.rectangleAreaLawSupport L L) T 0 X) = _
    rw [← hsum]
    change (∑ i : SquareLatticeSiteOrEdge L L, (Matrix.reindexAlgEquiv ℂ ℂ e) (B i)) = _
    rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), key]
    rfl

end TNLean.PEPS.Approximation
