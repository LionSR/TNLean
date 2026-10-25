/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SquareAreaLawHamiltonian
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
theorem SquareHamiltonian.exists_swapped_doubled_localHamiltonian
    {L q : ℕ} {J : ℝ} (h : SquareHamiltonian L q J) (hJ : 0 ≤ J)
    (R : Finset (SquareLatticeVertex L L)) :
    let p := QuantumCircuit.sitePairConfigurationEquiv (SquareLatticeVertex L L) q q
    let e := AreaLaw.rectangleConfigurationEquiv L L (q * q)
    let F := Matrix.reindex p p (TNLean.Lattice.sheetSwapOp q R)
    let K := Matrix.reindex p p (Matrix.doubledHamiltonian h.operator)
    ∃ g : Lattice.LocalHamiltonian (AreaLaw.rectangularDomain L L) (q * q) 1 (2 * J),
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
    TNLean.Lattice.reindex_sheetSwapOp_conj_doubledHamiltonian_mem_supportedOperators R
      (squareInteractionSupport i) (h.hermitianTerm_mem_supportedOperators i)
  have hFn : ‖F‖ ≤ 1 :=
    (Matrix.l2_opNorm_reindex_equiv p (TNLean.Lattice.sheetSwapOp q R)).le.trans
      (TNLean.Lattice.norm_sheetSwapOp_le_one R)
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
  -- The doubled map is additive in its argument, so summing the doubled Hermitian
  -- parts recovers the doubled total.
  let D : Matrix (Configuration L q) (Configuration L q) ℂ →ₗ[ℂ]
      Matrix (Configuration L q × Configuration L q)
        (Configuration L q × Configuration L q) ℂ :=
    (Matrix.kroneckerBilinear (R := ℂ)).flip
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ) +
      Matrix.kroneckerBilinear (R := ℂ)
        (1 : Matrix (Configuration L q) (Configuration L q) ℂ)
  have hDsum : (∑ i : SquareInteraction L,
      Matrix.doubledHamiltonian (h.hermitianTerm i)) =
      Matrix.doubledHamiltonian h.operator := by
    change (∑ i : SquareInteraction L, D (h.hermitianTerm i)) = D h.operator
    rw [← map_sum D, h.sum_hermitianTerm]
  -- The actual interaction family sums exactly to the swapped doubled total, since
  -- the conjugation and the bond reindexing are additive.
  have key : (∑ i : SquareInteraction L, B i) = F * K * Fᴴ := by
    have hreindex : (∑ i : SquareInteraction L,
        Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i))) = K := by
      change (∑ i : SquareInteraction L,
        (Matrix.reindexAlgEquiv ℂ ℂ p) (Matrix.doubledHamiltonian (h.hermitianTerm i))) = K
      rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ p), hDsum]
      rfl
    calc (∑ i : SquareInteraction L, B i)
        = F * (∑ i : SquareInteraction L,
            Matrix.reindex p p (Matrix.doubledHamiltonian (h.hermitianTerm i))) * Fᴴ := by
          simp only [B, Finset.mul_sum, Finset.sum_mul]
      _ = F * K * Fᴴ := by rw [hreindex]
  refine ⟨{ term := Function.extend (squareAreaLawSupport L)
              (fun i : SquareInteraction L => Matrix.reindex e e (B i)) 0
            supported := ?_
            hermitian := ?_
            norm_le := ?_ }, rfl, ?_⟩
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      have hs := QuantumCircuit.embedOp_mem_supportedOperators_image
        (AreaLaw.rectangleSiteEquiv L L).injective (hBsupport i)
      rw [embedOp_rectangle_eq_reindex] at hs
      simpa only [squareAreaLawSupport, Finset.coe_image] using hs
    · rw [Function.extend_apply' _ _ _ hx]
      exact Submodule.zero_mem _
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      exact (hBH i).submatrix e.symm
    · rw [Function.extend_apply' _ _ _ hx]
      exact Matrix.isHermitian_zero
  · intro X
    by_cases hx : ∃ i, squareAreaLawSupport L i = X
    · obtain ⟨i, rfl⟩ := hx
      rw [(squareAreaLawSupport_injective L).extend_apply]
      exact (Matrix.l2_opNorm_reindex_equiv e (B i)).le.trans (hBn i)
    · rw [Function.extend_apply' _ _ _ hx]
      simpa only [Pi.zero_apply, norm_zero] using mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hJ
  · let T := fun i : SquareInteraction L => Matrix.reindex e e (B i)
    have hsum : (∑ i : SquareInteraction L, T i) =
        ∑ X : Lattice.AdmissibleSupport (AreaLaw.rectangularDomain L L) 1,
          Function.extend (squareAreaLawSupport L) T 0 X := by
      apply Finset.sum_of_injOn (squareAreaLawSupport L)
        (squareAreaLawSupport_injective L).injOn (fun _ _ => Finset.mem_univ _)
      · intro X _ hX
        exact Function.extend_apply' _ _ _ (by simpa using hX)
      · intro i _
        exact ((squareAreaLawSupport_injective L).extend_apply T 0 i).symm
    change (∑ X, Function.extend (squareAreaLawSupport L) T 0 X) = _
    rw [← hsum]
    change (∑ i : SquareInteraction L, (Matrix.reindexAlgEquiv ℂ ℂ e) (B i)) = _
    rw [← map_sum (Matrix.reindexAlgEquiv ℂ ℂ e), key]
    rfl

end TNLean.PEPS.Approximation
