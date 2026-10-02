/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Star.StarProjection

/-!
# Spectral gap of a sum of commuting projections

A finite sum `H` of commuting orthogonal projections satisfies `H² ≥ H`.
Its eigenvalues therefore belong to `{0} ∪ [1, ∞)`, independently of the
number of projections. This is the gap estimate for the commuting parent
Hamiltonian in Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F.2,
following equation `eq:sym:omega-gamma` (source lines 904–906).
-/

open scoped Matrix MatrixOrder ComplexOrder
namespace Matrix

/-- The square of a sum of commuting orthogonal projections dominates the sum.
Source: arXiv:1010.3732, Section II.F.2, the commuting parent Hamiltonian
following `eq:sym:omega-gamma`. -/
theorem sum_square_sub_posSemidef_of_isStarProjection
    {ι n : Type*} [Fintype n]
    (P : ι → Matrix n n ℂ) (s : Finset ι)
    (hP : ∀ i, IsStarProjection (P i))
    (hcomm : ∀ i j, Commute (P i) (P j)) :
    ((∑ i ∈ s, P i) * (∑ i ∈ s, P i) - ∑ i ∈ s, P i).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (PosSemidef.zero : (0 : Matrix n n ℂ).PosSemidef)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hprod : (P a * ∑ i ∈ s, P i).PosSemidef := by
        rw [Finset.mul_sum]
        exact posSemidef_sum s fun i _ =>
          nonneg_iff_posSemidef.mp ((hP a).mul (hP i) (hcomm a i)).nonneg
      have hc : Commute (P a) (∑ i ∈ s, P i) :=
        Commute.sum_right s P (P a) fun i _ => hcomm a i
      have heq : (P a + ∑ i ∈ s, P i) * (P a + ∑ i ∈ s, P i) -
          (P a + ∑ i ∈ s, P i) =
          ((∑ i ∈ s, P i) * (∑ i ∈ s, P i) - ∑ i ∈ s, P i) +
          (P a * (∑ i ∈ s, P i) + P a * (∑ i ∈ s, P i)) := by
        rw [add_mul, mul_add, mul_add, (hP a).isIdempotentElem.eq, ← hc.eq]
        abel
      rw [heq]
      exact ih.add (hprod.add hprod)

/-- If `H ≥ 0` and `H² ≥ H`, every nonzero spectral value is at least one.
This is the spectral estimate used for the commuting parent Hamiltonian in
arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
theorem spectrum_separated_of_square_sub_posSemidef
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Matrix n n ℂ} (hH : H.PosSemidef)
    (hSquare : (H * H - H).PosSemidef) :
    ∀ z ∈ spectrum ℂ H, 0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  intro z hz
  rw [hH.isHermitian.spectrum_eq_image_range] at hz
  obtain ⟨r, ⟨i, rfl⟩, rfl⟩ := hz
  change 0 ≤ hH.isHermitian.eigenvalues i ∧
    (hH.isHermitian.eigenvalues i = 0 ∨ 1 ≤ hH.isHermitian.eigenvalues i)
  have hnonneg := hH.eigenvalues_nonneg i
  have hdot : star ⇑(hH.isHermitian.eigenvectorBasis i) ⬝ᵥ
      ⇑(hH.isHermitian.eigenvectorBasis i) = (1 : ℂ) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    simpa only [ite_true] using
      (orthonormal_iff_ite.mp hH.isHermitian.eigenvectorBasis.orthonormal i i)
  have h := hSquare.re_dotProduct_nonneg ⇑(hH.isHermitian.eigenvectorBasis i)
  rw [sub_mulVec, ← mulVec_mulVec, hH.isHermitian.mulVec_eigenvectorBasis,
    mulVec_smul, hH.isHermitian.mulVec_eigenvectorBasis, smul_smul,
    ← sub_smul, dotProduct_smul, hdot] at h
  simp only [RCLike.smul_re, RCLike.one_re, mul_one] at h
  refine ⟨hnonneg, ?_⟩
  by_cases hz : hH.isHermitian.eigenvalues i = 0
  · exact Or.inl hz
  · right
    have hpos := lt_of_le_of_ne hnonneg (Ne.symm hz)
    nlinarith

/-- A finite sum of commuting orthogonal projections has a gap of at least
one above zero, with no dependence on the number of summands.
Source: arXiv:1010.3732, Section II.F.2, source lines 904–906. -/
theorem spectrum_sum_separated_of_isStarProjection
    {ι n : Type*} [Fintype ι] [Fintype n] [DecidableEq n]
    (P : ι → Matrix n n ℂ) (hP : ∀ i, IsStarProjection (P i))
    (hcomm : ∀ i j, Commute (P i) (P j)) :
    ∀ z ∈ spectrum ℂ (∑ i, P i), 0 ≤ z.re ∧ (z.re = 0 ∨ 1 ≤ z.re) := by
  exact spectrum_separated_of_square_sub_posSemidef
    (posSemidef_sum Finset.univ fun i _ => nonneg_iff_posSemidef.mp (hP i).nonneg)
    (sum_square_sub_posSemidef_of_isStarProjection P Finset.univ hP hcomm)

end Matrix
