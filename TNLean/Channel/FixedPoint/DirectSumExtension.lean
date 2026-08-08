/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.TracePairing
import TNLean.Analysis.MatrixSqrt
import TNLean.Channel.Schwarz.AbstractMultiplicativeDomain
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Extension of maps on finite sums of matrix algebras

A linear map on a finite direct sum of full matrix algebras has a canonical
extension to the full matrix algebra on the direct sum of the underlying
spaces: first retain the diagonal blocks, apply the original map, and then
embed the resulting family as a block-diagonal matrix.

This file proves that the construction preserves positivity and the total
trace, identifies its fixed points in both directions, and computes its
trace-pairing adjoint. These are the algebraic ingredients of the
block-diagonal-embedding route from Wolf's Theorem 6.14 to the sector algebras
in arXiv:1606.00608, Appendix C.4, lines 1980--1995.

## Main definitions

* `Matrix.directSumDiagonalEmbedding`: block-diagonal embedding of a finite
  family of matrices.
* `Matrix.directSumDiagonalCompression`: family of diagonal blocks of a matrix.
* `Matrix.directSumExtension`: canonical full-matrix extension of a map on the
  finite direct sum.
* `Matrix.directSumTraceAdjointMap`: adjoint for the sum of the block traces.

## References

* M. Wolf, *Quantum Channels & Operations: Guided Tour*, Theorem 6.14.
* arXiv:1606.00608, Appendix C.4, lines 1980--1995.
-/

open scoped Matrix MatrixOrder ComplexOrder BigOperators

noncomputable section

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {n : ι → Type*} [∀ k, Fintype (n k)] [∀ k, DecidableEq (n k)]

/-- Embed a finite dependent family of square matrices as a block-diagonal
matrix on the direct sum of their index spaces. -/
noncomputable def directSumDiagonalEmbedding :
    (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ where
  toFun := Matrix.blockDiagonal'
  map_add' A B := Matrix.blockDiagonal'_add A B
  map_smul' c A := Matrix.blockDiagonal'_smul c A

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
@[simp]
theorem directSumDiagonalEmbedding_apply
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumDiagonalEmbedding A = Matrix.blockDiagonal' A :=
  rfl

/-- Retain the diagonal blocks of a matrix on a finite dependent direct sum. -/
noncomputable def directSumDiagonalCompression :
    Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ) where
  toFun A k := A.submatrix (Sigma.mk k) (Sigma.mk k)
  map_add' A B := by
    funext k i j
    rfl
  map_smul' c A := by
    funext k i j
    rfl

omit [Fintype ι] [DecidableEq ι] [(k : ι) → Fintype (n k)]
    [(k : ι) → DecidableEq (n k)] in
@[simp]
theorem directSumDiagonalCompression_apply
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) (k : ι) :
    directSumDiagonalCompression A k = A.submatrix (Sigma.mk k) (Sigma.mk k) :=
  rfl

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- Diagonal compression is a left inverse of block-diagonal embedding. -/
@[simp]
theorem directSumDiagonalCompression_embedding
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumDiagonalCompression (directSumDiagonalEmbedding A) = A := by
  funext k i j
  simp [directSumDiagonalCompression, directSumDiagonalEmbedding,
    Matrix.blockDiagonal'_apply_eq]

omit [(k : ι) → DecidableEq (n k)] in
/-- The trace of a finite block-diagonal matrix is the sum of the block traces. -/
theorem trace_directSumDiagonalEmbedding
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    (directSumDiagonalEmbedding A).trace = ∑ k, (A k).trace := by
  exact Matrix.trace_blockDiagonal' A

omit [DecidableEq ι] [(k : ι) → DecidableEq (n k)] in
/-- The sum of the traces of all diagonal compressions is the full trace. -/
theorem sum_trace_directSumDiagonalCompression
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) :
    ∑ k, (directSumDiagonalCompression A k).trace = A.trace := by
  simp only [directSumDiagonalCompression_apply, Matrix.trace, Matrix.diag,
    Matrix.submatrix_apply]
  exact (Fintype.sum_sigma' fun k i ↦ A ⟨k, i⟩ ⟨k, i⟩).symm

omit [(k : ι) → DecidableEq (n k)] in
/-- The trace pairing of block-diagonal matrices is the sum of the trace
pairings of their blocks. -/
theorem trace_directSumDiagonalEmbedding_mul
    (A B : ∀ k, Matrix (n k) (n k) ℂ) :
    (directSumDiagonalEmbedding A * directSumDiagonalEmbedding B).trace =
      ∑ k, (A k * B k).trace := by
  change (Matrix.blockDiagonal' A * Matrix.blockDiagonal' B).trace = _
  rw [← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']

omit [(k : ι) → DecidableEq (n k)] in
/-- Compressing after left multiplication by a block-diagonal matrix gives
left multiplication by the corresponding block. -/
theorem directSumDiagonalCompression_embedding_mul
    (B : ∀ k, Matrix (n k) (n k) ℂ)
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) (k : ι) :
    directSumDiagonalCompression (directSumDiagonalEmbedding B * A) k =
      B k * directSumDiagonalCompression A k := by
  ext i j
  simp only [directSumDiagonalCompression_apply, Matrix.submatrix_apply,
    Matrix.mul_apply, directSumDiagonalEmbedding_apply]
  rw [Fintype.sum_sigma fun q : (l : ι) × n l ↦
    Matrix.blockDiagonal' B ⟨k, i⟩ q * A q ⟨k, j⟩]
  rw [Finset.sum_eq_single k]
  · simp only [Matrix.blockDiagonal'_apply_eq]
  · intro l _ hl
    apply Finset.sum_eq_zero
    intro y _
    rw [Matrix.blockDiagonal'_apply_ne _ _ _ (Ne.symm hl)]
    simp
  · simp

omit [(k : ι) → DecidableEq (n k)] in
/-- In a trace pairing against a block-diagonal matrix, only the diagonal
blocks of the other matrix contribute. -/
theorem trace_embedding_compression_mul_embedding
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ)
    (B : ∀ k, Matrix (n k) (n k) ℂ) :
    (directSumDiagonalEmbedding (directSumDiagonalCompression A) *
        directSumDiagonalEmbedding B).trace =
      (A * directSumDiagonalEmbedding B).trace := by
  calc
    (directSumDiagonalEmbedding (directSumDiagonalCompression A) *
          directSumDiagonalEmbedding B).trace =
        ∑ k, (directSumDiagonalCompression A k * B k).trace :=
      trace_directSumDiagonalEmbedding_mul _ _
    _ = ∑ k, (B k * directSumDiagonalCompression A k).trace := by
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.trace_mul_comm _ _
    _ = ∑ k, (directSumDiagonalCompression
          (directSumDiagonalEmbedding B * A) k).trace := by
      apply Finset.sum_congr rfl
      intro k _
      rw [directSumDiagonalCompression_embedding_mul]
    _ = (directSumDiagonalEmbedding B * A).trace :=
      sum_trace_directSumDiagonalCompression _
    _ = (A * directSumDiagonalEmbedding B).trace :=
      Matrix.trace_mul_comm _ _

omit [(k : ι) → DecidableEq (n k)] in
/-- Block-diagonal embedding preserves multiplication. -/
theorem directSumDiagonalEmbedding_mul
    (A B : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumDiagonalEmbedding (A * B) =
      directSumDiagonalEmbedding A * directSumDiagonalEmbedding B := by
  change Matrix.blockDiagonal' (fun k ↦ A k * B k) =
    Matrix.blockDiagonal' A * Matrix.blockDiagonal' B
  exact Matrix.blockDiagonal'_mul A B

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- Block-diagonal embedding preserves conjugate transpose. -/
theorem directSumDiagonalEmbedding_conjTranspose
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumDiagonalEmbedding (fun k ↦ (A k)ᴴ) =
      (directSumDiagonalEmbedding A)ᴴ := by
  exact (Matrix.blockDiagonal'_conjTranspose A).symm

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- Block-diagonal embedding preserves positive semidefiniteness. -/
theorem directSumDiagonalEmbedding_posSemidef
    [Finite ι] [∀ k, Finite (n k)]
    {A : ∀ k, Matrix (n k) (n k) ℂ} (hA : ∀ k, (A k).PosSemidef) :
    (directSumDiagonalEmbedding A).PosSemidef := by
  exact Matrix.PosSemidef.blockDiagonal' A hA

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- Block-diagonal embedding preserves positive definiteness. -/
theorem directSumDiagonalEmbedding_posDef
    [Finite ι] [∀ k, Finite (n k)]
    {A : ∀ k, Matrix (n k) (n k) ℂ} (hA : ∀ k, (A k).PosDef) :
    (directSumDiagonalEmbedding A).PosDef := by
  classical
  letI := Fintype.ofFinite ι
  letI (k : ι) := Fintype.ofFinite (n k)
  have hpsd : (directSumDiagonalEmbedding A).PosSemidef :=
    directSumDiagonalEmbedding_posSemidef fun k ↦ (hA k).posSemidef
  apply hpsd.posDef_iff_isUnit.mpr
  rw [isUnit_iff_exists_inv]
  choose B hAB using fun k ↦ isUnit_iff_exists_inv.mp (hA k).isUnit
  refine ⟨directSumDiagonalEmbedding B, ?_⟩
  rw [← directSumDiagonalEmbedding_mul]
  have hAB' : A * B = (1 : ∀ k, Matrix (n k) (n k) ℂ) := by
    funext k
    exact hAB k
  rw [hAB']
  exact Matrix.blockDiagonal'_one

omit [Fintype ι] [DecidableEq ι] [(k : ι) → Fintype (n k)]
    [(k : ι) → DecidableEq (n k)] in
/-- Diagonal compression preserves positive semidefiniteness in every summand. -/
theorem directSumDiagonalCompression_posSemidef
    {A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ} (hA : A.PosSemidef)
    (k : ι) :
    (directSumDiagonalCompression A k).PosSemidef := by
  exact hA.submatrix (Sigma.mk k)

-- The finite instances construct the sigma index used by `PosSemidef`; the unused-instance
-- linter does not detect this use through the block-diagonal embedding. The per-summand
-- `DecidableEq` instance is genuinely unused and is omitted.
set_option linter.unusedFintypeInType false in
omit [(k : ι) → DecidableEq (n k)] in
/-- A block-diagonal matrix is positive semidefinite iff each of its diagonal blocks is: the
canonical order on a finite direct sum of matrix algebras is entrywise, and this is the fact
that realizes it inside the ambient block-diagonal embedding. -/
theorem blockDiagonal'_posSemidef_iff (M : ∀ i, Matrix (n i) (n i) ℂ) :
    (Matrix.blockDiagonal' M).PosSemidef ↔ ∀ i, (M i).PosSemidef := by
  constructor
  · intro h k
    have hcomp := directSumDiagonalCompression_posSemidef
      (A := directSumDiagonalEmbedding M) (directSumDiagonalEmbedding_apply M ▸ h) k
    rwa [directSumDiagonalCompression_embedding] at hcomp
  · intro h
    rw [← directSumDiagonalEmbedding_apply M]
    exact directSumDiagonalEmbedding_posSemidef h

omit [Fintype ι] [DecidableEq ι] [(k : ι) → Fintype (n k)]
    [(k : ι) → DecidableEq (n k)] in
/-- Diagonal compression commutes with conjugate transpose. -/
theorem directSumDiagonalCompression_conjTranspose
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) (k : ι) :
    directSumDiagonalCompression Aᴴ k =
      (directSumDiagonalCompression A k)ᴴ := by
  ext i j
  rfl

omit [DecidableEq ι] [(k : ι) → DecidableEq (n k)] in
/-- The defect in the Schwarz inequality for diagonal compression is the Gram
matrix of the column blocks lying outside the retained summand. -/
theorem directSumDiagonalCompression_schwarz
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) (k : ι) :
    (directSumDiagonalCompression (Aᴴ * A) k -
      (directSumDiagonalCompression A k)ᴴ *
        directSumDiagonalCompression A k).PosSemidef := by
  classical
  let R : Matrix ((l : ι) × n l) (n k) ℂ := fun q i ↦
    if q.1 = k then 0 else A q ⟨k, i⟩
  have hgap : directSumDiagonalCompression (Aᴴ * A) k -
      (directSumDiagonalCompression A k)ᴴ *
        directSumDiagonalCompression A k = Rᴴ * R := by
    ext i j
    simp only [directSumDiagonalCompression_apply, Matrix.submatrix_apply,
      Matrix.sub_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
    rw [Fintype.sum_sigma fun q : (l : ι) × n l ↦
      star (A q ⟨k, i⟩) * A q ⟨k, j⟩]
    rw [Fintype.sum_sigma fun q : (l : ι) × n l ↦ star (R q i) * R q j]
    let f : ι → ℂ := fun l ↦
      ∑ q : n l, star (A ⟨l, q⟩ ⟨k, i⟩) * A ⟨l, q⟩ ⟨k, j⟩
    change (∑ l, f l) - f k =
      ∑ l, ∑ q : n l, star (R ⟨l, q⟩ i) * R ⟨l, q⟩ j
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ k)]
    ring_nf
    let g : ι → ℂ := fun l ↦
      ∑ q : n l, star (R ⟨l, q⟩ i) * R ⟨l, q⟩ j
    change ∑ l ∈ Finset.univ.erase k, f l = ∑ l, g l
    rw [← Finset.sum_erase_add Finset.univ g (Finset.mem_univ k)]
    have hgk : g k = 0 := by
      simp [g, R]
    rw [hgk, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    have hlk : l ≠ k := Finset.ne_of_mem_erase hl
    simp [g, R, f, hlk]
  rw [hgap]
  exact Matrix.posSemidef_conjTranspose_mul_self R

/-- A linear map of a finite direct sum is positive when it sends a family of
positive-semidefinite matrices to such a family. -/
def IsPositiveDirectSumMap
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) : Prop :=
  ∀ A, (∀ k, (A k).PosSemidef) → ∀ k, (T A k).PosSemidef

/-- A map on a finite direct sum satisfies the Schwarz inequality when the
inequality holds in every summand. -/
def IsSchwarzDirectSumMap
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) : Prop :=
  ∀ A k,
    (T (fun l ↦ (A l)ᴴ * A l) k - T (fun l ↦ (A l)ᴴ) k * T A k).PosSemidef

/-- A linear map of a finite direct sum preserves the total trace when it
preserves the sum of the ordinary traces on its summands. -/
def IsTracePreservingDirectSumMap
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) : Prop :=
  ∀ A, ∑ k, (T A k).trace = ∑ k, (A k).trace

/-- Extend a map on a finite direct sum to the full matrix algebra by diagonal
compression followed by block-diagonal embedding. -/
noncomputable def directSumExtension
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) :
    Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ →ₗ[ℂ]
      Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ :=
  directSumDiagonalEmbedding.comp (T.comp directSumDiagonalCompression)

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
@[simp]
theorem directSumExtension_apply
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ))
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) :
    directSumExtension T A =
      directSumDiagonalEmbedding (T (directSumDiagonalCompression A)) :=
  rfl

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- Positivity of a map on the finite direct sum implies positivity of its
canonical full-matrix extension. -/
theorem IsPositiveDirectSumMap.directSumExtension_isPositiveMap
    [Finite ι] [∀ k, Finite (n k)]
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T) :
    IsPositiveMap (directSumExtension T) := by
  intro A hA
  exact directSumDiagonalEmbedding_posSemidef
    (hT (directSumDiagonalCompression A) fun k ↦
      directSumDiagonalCompression_posSemidef hA k)

omit [(k : ι) → DecidableEq (n k)] in
/-- Positivity and the summandwise Schwarz inequality imply the Schwarz
inequality for the canonical full-matrix extension. -/
theorem IsSchwarzDirectSumMap.directSumExtension_isSchwarzMap
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hTpos : IsPositiveDirectSumMap T) (hT : IsSchwarzDirectSumMap T) :
    IsSchwarzMap (directSumExtension T) := by
  intro A
  let X := directSumDiagonalCompression A
  let Y := directSumDiagonalCompression (Aᴴ * A)
  let Xstar : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦ (X k)ᴴ
  let XstarX : ∀ k, Matrix (n k) (n k) ℂ := fun k ↦ (X k)ᴴ * X k
  have hinput (k : ι) : (Y k - XstarX k).PosSemidef := by
    exact directSumDiagonalCompression_schwarz A k
  have hmonotone (k : ι) : (T Y k - T XstarX k).PosSemidef := by
    have hpos := hTpos (Y - XstarX) fun l ↦ hinput l
    have hk := hpos k
    simpa only [map_sub, Pi.sub_apply] using hk
  have hblock (k : ι) :
      (T Y k - T Xstar k * T X k).PosSemidef := by
    have hschwarz :
        (T XstarX k - T Xstar k * T X k).PosSemidef := by
      simpa only [XstarX, Xstar] using hT X k
    have hadd := (hmonotone k).add hschwarz
    rw [show T Y k - T Xstar k * T X k =
      (T Y k - T XstarX k) +
        (T XstarX k - T Xstar k * T X k) by abel]
    exact hadd
  have hXstar : directSumDiagonalCompression Aᴴ = Xstar := by
    funext k
    exact directSumDiagonalCompression_conjTranspose A k
  have hgap : directSumExtension T (Aᴴ * A) -
      directSumExtension T Aᴴ * directSumExtension T A =
        directSumDiagonalEmbedding
          (fun k ↦ T Y k - T Xstar k * T X k) := by
    rw [directSumExtension_apply, directSumExtension_apply,
      directSumExtension_apply]
    change directSumDiagonalEmbedding (T Y) -
      directSumDiagonalEmbedding (T (directSumDiagonalCompression Aᴴ)) *
        directSumDiagonalEmbedding (T X) = _
    rw [hXstar, ← directSumDiagonalEmbedding_mul, ← map_sub]
    congr 1
  rw [hgap]
  exact directSumDiagonalEmbedding_posSemidef hblock

omit [(k : ι) → DecidableEq (n k)] in
/-- Preservation of the total block trace implies ordinary trace preservation
for the canonical full-matrix extension. -/
theorem IsTracePreservingDirectSumMap.directSumExtension_isTracePreservingMap
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsTracePreservingDirectSumMap T) :
    IsTracePreservingMap (directSumExtension T) := by
  intro A
  rw [directSumExtension_apply, trace_directSumDiagonalEmbedding, hT,
    sum_trace_directSumDiagonalCompression]

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- A fixed family gives a fixed block-diagonal matrix under the extension. -/
theorem directSumExtension_embedding_eq_self_iff
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ))
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumExtension T (directSumDiagonalEmbedding A) =
        directSumDiagonalEmbedding A ↔
      T A = A := by
  rw [directSumExtension_apply, directSumDiagonalCompression_embedding]
  constructor
  · intro h
    have := congrArg directSumDiagonalCompression h
    rw [directSumDiagonalCompression_embedding,
      directSumDiagonalCompression_embedding] at this
    exact this
  · intro h
    rw [h]

omit [Fintype ι] [(k : ι) → Fintype (n k)] [(k : ι) → DecidableEq (n k)] in
/-- The fixed points of the extension are exactly the embedded fixed families.
This includes both directions of the fixed-point identification required in
the block-diagonal-embedding argument. -/
theorem directSumExtension_apply_eq_self_iff
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ))
    (A : Matrix ((k : ι) × n k) ((k : ι) × n k) ℂ) :
    directSumExtension T A = A ↔
      ∃ B : ∀ k, Matrix (n k) (n k) ℂ,
        T B = B ∧ A = directSumDiagonalEmbedding B := by
  constructor
  · intro hA
    have hfixed : T (directSumDiagonalCompression A) =
        directSumDiagonalCompression A := by
      have h := congrArg directSumDiagonalCompression hA
      simpa only [directSumExtension_apply,
        directSumDiagonalCompression_embedding] using h
    refine ⟨directSumDiagonalCompression A, hfixed, ?_⟩
    calc
      A = directSumDiagonalEmbedding (T (directSumDiagonalCompression A)) :=
        hA.symm
      _ = directSumDiagonalEmbedding (directSumDiagonalCompression A) := by
        rw [hfixed]
  · rintro ⟨B, hB, rfl⟩
    exact (directSumExtension_embedding_eq_self_iff T B).2 hB

/-! ## Trace-pairing adjoints -/

/-- The adjoint of a map on a finite direct sum for the bilinear pairing

\[
  \langle A,B\rangle=\sum_k\operatorname{tr}(A_kB_k).
\]

It is obtained by taking the full-matrix trace adjoint of the canonical
extension and then restricting it to diagonal input and output blocks. -/
noncomputable def directSumTraceAdjointMap
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) :
    (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ) :=
  directSumDiagonalCompression.comp
    ((Matrix.traceAdjointMap (directSumExtension T)).comp
      directSumDiagonalEmbedding)

omit [(k : ι) → DecidableEq (n k)] in
@[simp]
theorem directSumTraceAdjointMap_apply
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ))
    (A : ∀ k, Matrix (n k) (n k) ℂ) :
    directSumTraceAdjointMap T A =
      directSumDiagonalCompression
        (Matrix.traceAdjointMap (directSumExtension T)
          (directSumDiagonalEmbedding A)) :=
  rfl

omit [(k : ι) → DecidableEq (n k)] in
/-- The direct-sum trace adjoint satisfies its defining trace-pairing
identity. -/
theorem sum_trace_directSumTraceAdjointMap_mul
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ))
    (A B : ∀ k, Matrix (n k) (n k) ℂ) :
    ∑ k, (directSumTraceAdjointMap T A k * B k).trace =
      ∑ k, (A k * T B k).trace := by
  calc
    ∑ k, (directSumTraceAdjointMap T A k * B k).trace =
        (directSumDiagonalEmbedding (directSumTraceAdjointMap T A) *
          directSumDiagonalEmbedding B).trace :=
      (trace_directSumDiagonalEmbedding_mul _ _).symm
    _ = (Matrix.traceAdjointMap (directSumExtension T)
          (directSumDiagonalEmbedding A) * directSumDiagonalEmbedding B).trace := by
      rw [directSumTraceAdjointMap_apply]
      exact trace_embedding_compression_mul_embedding _ _
    _ = (directSumDiagonalEmbedding A *
          directSumExtension T (directSumDiagonalEmbedding B)).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = (directSumDiagonalEmbedding A *
          directSumDiagonalEmbedding (T B)).trace := by
      rw [directSumExtension_apply, directSumDiagonalCompression_embedding]
    _ = ∑ k, (A k * T B k).trace :=
      trace_directSumDiagonalEmbedding_mul _ _

omit [(k : ι) → DecidableEq (n k)] in
/-- Taking the full-matrix trace adjoint commutes with canonical extension.
Equivalently, block-diagonal embedding and diagonal compression are adjoint
to one another for the trace pairing. -/
theorem traceAdjointMap_directSumExtension
    (T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)) :
    Matrix.traceAdjointMap (directSumExtension T) =
      directSumExtension (directSumTraceAdjointMap T) := by
  apply LinearMap.ext
  intro A
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro B
  calc
    (Matrix.traceAdjointMap (directSumExtension T) A * B).trace =
        (A * directSumExtension T B).trace :=
      Matrix.trace_traceAdjointMap_mul _ _ _
    _ = (A * directSumDiagonalEmbedding
          (T (directSumDiagonalCompression B))).trace := rfl
    _ = (directSumDiagonalEmbedding (directSumDiagonalCompression A) *
          directSumDiagonalEmbedding
            (T (directSumDiagonalCompression B))).trace :=
      (trace_embedding_compression_mul_embedding _ _).symm
    _ = ∑ k, (directSumDiagonalCompression A k *
          T (directSumDiagonalCompression B) k).trace :=
      trace_directSumDiagonalEmbedding_mul _ _
    _ = ∑ k, (directSumTraceAdjointMap T
          (directSumDiagonalCompression A) k *
            directSumDiagonalCompression B k).trace :=
      (sum_trace_directSumTraceAdjointMap_mul T _ _).symm
    _ = ∑ k, (directSumDiagonalCompression B k *
          directSumTraceAdjointMap T
            (directSumDiagonalCompression A) k).trace := by
      apply Finset.sum_congr rfl
      intro k _
      exact Matrix.trace_mul_comm _ _
    _ = (directSumDiagonalEmbedding (directSumDiagonalCompression B) *
          directSumDiagonalEmbedding
            (directSumTraceAdjointMap T
              (directSumDiagonalCompression A))).trace :=
      (trace_directSumDiagonalEmbedding_mul _ _).symm
    _ = (B * directSumDiagonalEmbedding
          (directSumTraceAdjointMap T
            (directSumDiagonalCompression A))).trace :=
      trace_embedding_compression_mul_embedding _ _
    _ = (directSumDiagonalEmbedding
          (directSumTraceAdjointMap T
            (directSumDiagonalCompression A)) * B).trace :=
      Matrix.trace_mul_comm _ _
    _ = (directSumExtension (directSumTraceAdjointMap T) A * B).trace := rfl

omit [(k : ι) → DecidableEq (n k)] in
/-- The trace adjoint of a positive direct-sum map is positive. -/
theorem IsPositiveDirectSumMap.directSumTraceAdjointMap
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hT : IsPositiveDirectSumMap T) :
    IsPositiveDirectSumMap (directSumTraceAdjointMap T) := by
  intro A hA k
  apply directSumDiagonalCompression_posSemidef
  exact IsPositiveMap.traceAdjointMap hT.directSumExtension_isPositiveMap _
    (directSumDiagonalEmbedding_posSemidef hA)

omit [(k : ι) → DecidableEq (n k)] in
/-- A summandwise Schwarz trace adjoint yields the Schwarz trace adjoint of
the canonical full-matrix extension. -/
theorem IsSchwarzDirectSumMap.traceAdjointMap_directSumExtension_isSchwarzMap
    {T : (∀ k, Matrix (n k) (n k) ℂ) →ₗ[ℂ]
      (∀ k, Matrix (n k) (n k) ℂ)}
    (hTpos : IsPositiveDirectSumMap T)
    (hTstar : IsSchwarzDirectSumMap (directSumTraceAdjointMap T)) :
    IsSchwarzMap (Matrix.traceAdjointMap (directSumExtension T)) := by
  rw [traceAdjointMap_directSumExtension]
  exact hTstar.directSumExtension_isSchwarzMap hTpos.directSumTraceAdjointMap

end Matrix
