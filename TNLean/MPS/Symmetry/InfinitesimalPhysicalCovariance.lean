/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.StringOrderDefs
import QICLean.Analysis.HermitianIntertwiner
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# Coordinates for infinitesimal physical covariance

The explicit row-vectorization convention below
matches the source E = ∑ Aᵢ ⊗ conjugate(Aᵢ). The existing generic transferMatrix
uses the opposite pair order, and must be reindexed before substitution.
Source: arXiv:0802.0447, lines 331–359.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-- Column i is the row-vectorization of Aᵢ. This rectangular coefficient
matrix is the input to the support-general Hermitian lift.
Source: arXiv:0802.0447, lines 343–350. -/
def krausRowMatrix (A : MPSTensor d D) : Matrix (Fin D × Fin D) (Fin d) ℂ :=
  fun p i => A i p.1 p.2

/-- The source doubled transfer matrix, in row-vectorization order.
Source: arXiv:0802.0447, lines 331–342. -/
noncomputable def rowTransferMatrix (A : MPSTensor d D) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  ∑ i, A i ⊗ₖ (A i).map (starRingEnd ℂ)

/-- Hermitian generator of conjugation in row-vectorization order.
Source: arXiv:0802.0447, lines 352–359. -/
def rowAdjointGenerator (H : Matrix (Fin D) (Fin D) ℂ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  H ⊗ₖ 1 - 1 ⊗ₖ H.map (starRingEnd ℂ)

/-- The physical row-index convention transposes the generic right lift.
Source: arXiv:0802.0447, lines 343–350. -/
theorem krausRowMatrix_mul_apply
    (A : MPSTensor d D) (K : Matrix (Fin d) (Fin d) ℂ)
    (a b : Fin D) (i : Fin d) :
    (krausRowMatrix A * K) (a, b) i = (∑ j, Kᵀ i j • A j) a b := by
  simp only [Matrix.mul_apply, krausRowMatrix, Matrix.sum_apply,
    Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

/-- Choi Gram and source transfer matrix are distinct realignments.
Source: arXiv:0802.0447, lines 340–350. -/
theorem krausRowMatrix_gram_apply
    (A : MPSTensor d D) (a b c e : Fin D) :
    (krausRowMatrix A * (krausRowMatrix A)ᴴ) (a, b) (c, e) =
      rowTransferMatrix A (a, c) (b, e) := by
  simp [Matrix.mul_apply, krausRowMatrix, rowTransferMatrix, Matrix.sum_apply,
    Matrix.conjTranspose_apply]

/-- Entry expansion of the left infinitesimal action. Supporting calculation
for arXiv:0802.0447, lines 352–359. -/
theorem rowAdjointGenerator_mul_apply
    (H : Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (a b : Fin D) (q : Fin D × Fin D) :
    (rowAdjointGenerator H * X) (a, b) q =
      (∑ r, H a r * X (r, b) q) -
        ∑ r, starRingEnd ℂ (H b r) * X (a, r) q := by
  simp [rowAdjointGenerator, sub_mul, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_sub_distrib]

/-- Entry expansion of the right infinitesimal action. Supporting calculation
for arXiv:0802.0447, lines 352–359. -/
theorem mul_rowAdjointGenerator_apply
    (H : Matrix (Fin D) (Fin D) ℂ)
    (X : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (p : Fin D × Fin D) (c e : Fin D) :
    (X * rowAdjointGenerator H) p (c, e) =
      (∑ r, X p (r, e) * H r c) -
        ∑ r, X p (c, r) * starRingEnd ℂ (H r e) := by
  simp [rowAdjointGenerator, mul_sub, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_sub_distrib]

/-- The commutator of the Choi Gram is the realignment of the commutator
of the source transfer matrix. The matrices themselves are not equal.
Source: arXiv:0802.0447, lines 340–359. -/
theorem krausRowMatrix_gram_commutator_apply
    (A : MPSTensor d D) (H : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (a b c e : Fin D) :
    (rowAdjointGenerator H * (krausRowMatrix A * (krausRowMatrix A)ᴴ) -
      (krausRowMatrix A * (krausRowMatrix A)ᴴ) * rowAdjointGenerator H)
        (a, b) (c, e) =
    (rowAdjointGenerator H * rowTransferMatrix A -
      rowTransferMatrix A * rowAdjointGenerator H) (a, c) (b, e) := by
  have hstar (r s : Fin D) : starRingEnd ℂ (H r s) = H s r := by
    simpa only [Matrix.conjTranspose_apply, starRingEnd_apply] using
      congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M s r) hH.eq
  simp only [Matrix.sub_apply, rowAdjointGenerator_mul_apply,
    mul_rowAdjointGenerator_apply, krausRowMatrix_gram_apply, hstar]
  simp only [rowTransferMatrix, Matrix.sum_apply,
    Finset.mul_sum, Finset.sum_mul]
  simp only [mul_comm]
  ring

/-- The source infinitesimal transfer criterion is equivalent to the Gram
commutation required by the supported Hermitian lift.
Source: arXiv:0802.0447, lines 352–359. -/
theorem commute_rowTransferMatrix_iff_commute_krausGram
    (A : MPSTensor d D) (H : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) :
    Commute (rowAdjointGenerator H) (rowTransferMatrix A) ↔
      Commute (rowAdjointGenerator H)
        (krausRowMatrix A * (krausRowMatrix A)ᴴ) := by
  change _ = _ ↔ _ = _
  constructor
  · intro h
    apply sub_eq_zero.mp
    ext ⟨a, b⟩ ⟨c, e⟩
    rw [krausRowMatrix_gram_commutator_apply A H hH, h, sub_self]
    rfl
  · intro h
    apply sub_eq_zero.mp
    ext ⟨a, c⟩ ⟨b, e⟩
    rw [← krausRowMatrix_gram_commutator_apply A H hH, h, sub_self]
    rfl

/-- The doubled generator acts on each Kraus column by the virtual
commutator. Source: arXiv:0802.0447, lines 352–359. -/
theorem rowAdjointGenerator_mul_krausRowMatrix_apply
    (A : MPSTensor d D) (H : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (a b : Fin D) (i : Fin d) :
    (rowAdjointGenerator H * krausRowMatrix A) (a, b) i =
      (H * A i - A i * H) a b := by
  have hstar (r s : Fin D) : starRingEnd ℂ (H r s) = H s r := by
    simpa only [Matrix.conjTranspose_apply, starRingEnd_apply] using
      congrArg (fun M : Matrix (Fin D) (Fin D) ℂ => M s r) hH.eq
  simp [rowAdjointGenerator, krausRowMatrix, mul_sub, Matrix.mul_apply,
    Fintype.sum_prod_type, Matrix.one_apply,
    Finset.sum_sub_distrib, hstar, mul_comm]

/-- A generic Hermitian lift gives the physical row-index generator after
transposition. Source: arXiv:0802.0447, lines 343–359. -/
theorem infinitesimal_physical_covariance_of_intertwiner
    (A : MPSTensor d D) (H : Matrix (Fin D) (Fin D) ℂ)
    (hH : H.IsHermitian) (K₀ : Matrix (Fin d) (Fin d) ℂ)
    (hFK : krausRowMatrix A * K₀ = rowAdjointGenerator H * krausRowMatrix A)
    (i : Fin d) :
    ∑ j, K₀ᵀ i j • A j = H * A i - A i * H := by
  ext a b
  rw [← krausRowMatrix_mul_apply, hFK,
    rowAdjointGenerator_mul_krausRowMatrix_apply A H hH]

end MPSTensor
