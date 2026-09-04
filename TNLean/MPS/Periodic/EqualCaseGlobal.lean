/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Multi
import TNLean.MPS.Periodic.EqualCase
import TNLean.MPS.Periodic.ProportionalOverlap

/-!
# Global assembly of the equal-case multiplicity gauge

The equal-case fundamental theorem closes by collecting the blockwise data into
two global matrices on the bond space of the assembled tensor: the
multiplicity gauge, which is the scalar acting by a root of unity on each
multiplicity copy, and the similarity, which permutes the matched copies and
applies the blockwise similarity inside each of them.

This module supplies the linear algebra of that assembly.

## Main declarations

* `MPSTensor.blockScalarMatrix`
* `MPSTensor.permMatrixOfEquiv`
* `MPSTensor.toTensorFromBlocks_conj_of_matched_blocks`

## References

* De las Cuevas, Cirac, Schuch, Perez-Garcia,
  *Irreducible forms of Matrix Product States: Theory and Applications*,
  arXiv:1708.00029, theorem `thm:bdequal`, lines 689--690.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-! ## Block-scalar matrices on flattened bond coordinates -/

section BlockScalar

variable {r : ℕ}

/-- The matrix acting on the flattened bond space of a block-diagonal tensor by
the scalar `z k` on the bond space of the `k`-th block.

In the notation of arXiv:1708.00029, line 653, this is the matrix
`⊕_k z_k 1_{D_k}`. -/
noncomputable def blockScalarMatrix (dim : Fin r → ℕ) (z : Fin r → ℂ) :
    Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ :=
  Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
    (Matrix.blockDiagonal' fun k => z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))

variable {dim : Fin r → ℕ}

theorem blockScalarMatrix_mul (z w : Fin r → ℂ) :
    blockScalarMatrix dim z * blockScalarMatrix dim w =
      blockScalarMatrix dim (fun k => z k * w k) := by
  classical
  have hmul := map_mul (Matrix.reindexAlgEquiv ℂ ℂ
      (finSigmaFinEquiv (m := r) (n := dim)))
    (Matrix.blockDiagonal' fun k => z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
    (Matrix.blockDiagonal' fun k => w k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
  simp only [Matrix.coe_reindexAlgEquiv] at hmul
  have hfun : (fun k : Fin r =>
      (z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) *
        (w k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))) =
      fun k : Fin r => (z k * w k) • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
    funext k
    simp [smul_smul, mul_comm]
  rw [blockScalarMatrix, blockScalarMatrix, blockScalarMatrix, ← hmul,
    ← Matrix.blockDiagonal'_mul, hfun]

@[simp] theorem blockScalarMatrix_one :
    blockScalarMatrix dim (fun _ => (1 : ℂ)) = 1 := by
  classical
  have h := map_one (Matrix.reindexAlgEquiv ℂ ℂ
    (finSigmaFinEquiv (m := r) (n := dim)))
  simp only [Matrix.coe_reindexAlgEquiv] at h
  rw [blockScalarMatrix, ← h]
  congr 1
  have hfun : (fun k : Fin r => (1 : ℂ) • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) =
      fun k : Fin r => (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ) := by
    funext k; simp
  rw [hfun]
  exact Matrix.blockDiagonal'_one

theorem blockScalarMatrix_pow (z : Fin r → ℂ) (n : ℕ) :
    blockScalarMatrix dim z ^ n = blockScalarMatrix dim (fun k => z k ^ n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, blockScalarMatrix_mul]
    simp [pow_succ]

/-- Multiplying a block-diagonal tensor on the left by a block-scalar matrix
rescales the block weights. -/
theorem blockScalarMatrix_mul_toTensorFromBlocks
    (z μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) (i : Fin d) :
    blockScalarMatrix dim z * toTensorFromBlocks (d := d) (μ := μ) A i =
      toTensorFromBlocks (d := d) (μ := fun k => z k * μ k) A i := by
  classical
  have hmul := map_mul (Matrix.reindexAlgEquiv ℂ ℂ
      (finSigmaFinEquiv (m := r) (n := dim)))
    (Matrix.blockDiagonal' fun k => z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
    (Matrix.blockDiagonal' fun k => μ k • A k i)
  simp only [Matrix.coe_reindexAlgEquiv] at hmul
  change blockScalarMatrix dim z *
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k => μ k • A k i) = _
  have hfun : (fun k : Fin r =>
      (z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ)) * (μ k • A k i)) =
      fun k : Fin r => (z k * μ k) • A k i := by
    funext k
    simp [smul_smul, mul_comm]
  rw [blockScalarMatrix, ← hmul, ← Matrix.blockDiagonal'_mul, hfun]
  rfl

/-- Multiplying a block-diagonal tensor on the right by a block-scalar matrix
rescales the block weights in the same way. -/
theorem toTensorFromBlocks_mul_blockScalarMatrix
    (z μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k)) (i : Fin d) :
    toTensorFromBlocks (d := d) (μ := μ) A i * blockScalarMatrix dim z =
      toTensorFromBlocks (d := d) (μ := fun k => z k * μ k) A i := by
  classical
  have hmul := map_mul (Matrix.reindexAlgEquiv ℂ ℂ
      (finSigmaFinEquiv (m := r) (n := dim)))
    (Matrix.blockDiagonal' fun k => μ k • A k i)
    (Matrix.blockDiagonal' fun k => z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))
  simp only [Matrix.coe_reindexAlgEquiv] at hmul
  change Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k => μ k • A k i) * blockScalarMatrix dim z = _
  have hfun : (fun k : Fin r =>
      (μ k • A k i) * (z k • (1 : Matrix (Fin (dim k)) (Fin (dim k)) ℂ))) =
      fun k : Fin r => (z k * μ k) • A k i := by
    funext k
    simp [smul_smul]
  rw [blockScalarMatrix, ← hmul, ← Matrix.blockDiagonal'_mul, hfun]
  rfl

end BlockScalar

/-! ## Permutation matrices of index equivalences -/

section PermMatrix

variable {m n : Type*} [DecidableEq m]

/-- The matrix of an index equivalence `E : n ≃ m`, sending the `t`-th basis
vector to the `E t`-th one. -/
def permMatrixOfEquiv (E : n ≃ m) : Matrix m n ℂ :=
  fun x t => if x = E t then 1 else 0

theorem permMatrixOfEquiv_mul [Fintype n] {p : Type*} (E : n ≃ m) (M : Matrix n p ℂ) :
    permMatrixOfEquiv E * M = M.submatrix E.symm id := by
  ext x u
  rw [Matrix.mul_apply]
  simp only [permMatrixOfEquiv, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (E.symm x)]
  · simp
  · intro t _ ht
    have : ¬ x = E t := fun h => ht (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem mul_permMatrixOfEquiv_transpose [Fintype n] {p : Type*} (E : n ≃ m)
    (M : Matrix p n ℂ) :
    M * (permMatrixOfEquiv E)ᵀ = M.submatrix id E.symm := by
  ext u y
  rw [Matrix.mul_apply]
  simp only [permMatrixOfEquiv, Matrix.transpose_apply, Matrix.submatrix_apply, id]
  rw [Finset.sum_eq_single (E.symm y)]
  · simp
  · intro t _ ht
    have : ¬ y = E t := fun h => ht (by rw [h, Equiv.symm_apply_apply])
    simp [this]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem permMatrixOfEquiv_mul_transpose [Fintype n] (E : n ≃ m) :
    permMatrixOfEquiv E * (permMatrixOfEquiv E)ᵀ = 1 := by
  rw [permMatrixOfEquiv_mul]
  ext x y
  simp only [Matrix.submatrix_apply, id, Matrix.transpose_apply, permMatrixOfEquiv,
    Matrix.one_apply]
  by_cases h : x = y
  · subst h; simp
  · have h' : ¬ y = x := fun hh => h hh.symm
    have h1 : (if y = E (E.symm x) then (1 : ℂ) else 0) = 0 := by simp [h']
    have h2 : (if x = y then (1 : ℂ) else 0) = 0 := by simp [h]
    rw [h1, h2]

theorem permMatrixOfEquiv_transpose_mul [Fintype m] [DecidableEq n] (E : n ≃ m) :
    (permMatrixOfEquiv E)ᵀ * permMatrixOfEquiv E = 1 := by
  ext t u
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, permMatrixOfEquiv, Matrix.one_apply]
  rw [Finset.sum_eq_single (E t)]
  · by_cases h : t = u
    · subst h; simp
    · have : ¬ E t = E u := fun hh => h (E.injective hh)
      simp [this, h]
  · intro x _ hx
    simp [hx]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- Reindexing a square matrix along an equivalence is conjugation by the
corresponding permutation matrix. -/
theorem reindex_eq_permMatrixOfEquiv_conj [Fintype n] (E : n ≃ m) (M : Matrix n n ℂ) :
    Matrix.reindex E E M =
      permMatrixOfEquiv E * M * (permMatrixOfEquiv E)ᵀ := by
  rw [permMatrixOfEquiv_mul, mul_permMatrixOfEquiv_transpose]
  ext x y
  simp [Matrix.submatrix_apply]

end PermMatrix

/-! ## Conjugation between matched block-diagonal tensors -/

/-- **Global similarity between matched block-diagonal tensors.**

If the blocks of two block-diagonal tensors are matched by an equivalence of
their index sets, with matching bond dimensions, and every matched pair of
weighted blocks is related by a similarity, then the two assembled tensors are
related by a single invertible matrix between their bond spaces.

The matrix is the composition of the permutation of the matched blocks with the
direct sum of the blockwise similarities, which is the matrix
`Y = ⊕_j T_j ⊗ Y_j` of arXiv:1708.00029, line 690. -/
theorem toTensorFromBlocks_conj_of_matched_blocks
    {r r' : ℕ} {dim : Fin r → ℕ} {dim' : Fin r' → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (μ' : Fin r' → ℂ) (B : (t : Fin r') → MPSTensor d (dim' t))
    (e : Fin r ≃ Fin r') (hd : ∀ k, dim k = dim' (e k))
    (X : (t : Fin r') → GL (Fin (dim' t)) ℂ)
    (hrel : ∀ (k : Fin r) (i : Fin d),
      Matrix.reindex (finCongr (hd k)) (finCongr (hd k)) (μ k • A k i) =
        μ' (e k) • ((X (e k) : Matrix (Fin (dim' (e k))) (Fin (dim' (e k))) ℂ) *
          B (e k) i *
          (((X (e k))⁻¹ : GL (Fin (dim' (e k))) ℂ) :
            Matrix (Fin (dim' (e k))) (Fin (dim' (e k))) ℂ))) :
    ∃ (Y : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ t : Fin r', dim' t)) ℂ)
      (Y' : Matrix (Fin (∑ t : Fin r', dim' t)) (Fin (∑ k : Fin r, dim k)) ℂ),
      Y * Y' = 1 ∧ Y' * Y = 1 ∧
      ∀ i : Fin d,
        toTensorFromBlocks (d := d) (μ := μ) A i =
          Y * toTensorFromBlocks (d := d) (μ := μ') B i * Y' := by
  classical
  -- The conjugated `B`-family, still indexed by the `B`-side blocks.
  set B' : (t : Fin r') → MPSTensor d (dim' t) := fun t i =>
    (X t : Matrix (Fin (dim' t)) (Fin (dim' t)) ℂ) * B t i *
      (((X t)⁻¹ : GL (Fin (dim' t)) ℂ) : Matrix (Fin (dim' t)) (Fin (dim' t)) ℂ)
    with hB'
  have hconj := toTensorFromBlocks_eq_globalGaugeOfBlocks_conj (d := d)
    (μ := μ') (A := B) (B := B') X (fun t i => rfl)
  -- The index permutation between the two flattened bond spaces.
  have hblocks : ∀ (k : Fin r) (i : Fin d),
      μ k • A k i =
        Matrix.reindex (finCongr (hd k)).symm (finCongr (hd k)).symm
          (μ' (e k) • B' (e k) i) := by
    intro k i
    have h := hrel k i
    rw [hB']
    rw [← h]
    ext x y
    simp
  have hreindex := toTensorFromBlocks_eq_reindex_of_equiv (d := d)
    μ A μ' B' e hd hblocks
  set E : Fin (∑ t : Fin r', dim' t) ≃ Fin (∑ k : Fin r, dim k) :=
    blockDimEquiv e hd with hE
  set G : Matrix (Fin (∑ t : Fin r', dim' t)) (Fin (∑ t : Fin r', dim' t)) ℂ :=
    (globalGaugeOfBlocks X : Matrix (Fin (∑ t : Fin r', dim' t))
      (Fin (∑ t : Fin r', dim' t)) ℂ) with hG
  set G' : Matrix (Fin (∑ t : Fin r', dim' t)) (Fin (∑ t : Fin r', dim' t)) ℂ :=
    (((globalGaugeOfBlocks X)⁻¹ : GL (Fin (∑ t : Fin r', dim' t)) ℂ) :
      Matrix (Fin (∑ t : Fin r', dim' t)) (Fin (∑ t : Fin r', dim' t)) ℂ) with hG'
  have hGG' : G * G' = 1 := by
    rw [hG, hG']
    simp
  have hG'G : G' * G = 1 := by
    rw [hG, hG']
    simp
  refine ⟨permMatrixOfEquiv E * G, G' * (permMatrixOfEquiv E)ᵀ, ?_, ?_, ?_⟩
  · calc permMatrixOfEquiv E * G * (G' * (permMatrixOfEquiv E)ᵀ)
        = permMatrixOfEquiv E * (G * G') * (permMatrixOfEquiv E)ᵀ := by
          simp [Matrix.mul_assoc]
    _ = 1 := by rw [hGG']; simp [permMatrixOfEquiv_mul_transpose]
  · calc G' * (permMatrixOfEquiv E)ᵀ * (permMatrixOfEquiv E * G)
        = G' * ((permMatrixOfEquiv E)ᵀ * permMatrixOfEquiv E) * G := by
          simp [Matrix.mul_assoc]
    _ = 1 := by rw [permMatrixOfEquiv_transpose_mul]; simp [hG'G]
  · intro i
    rw [hreindex i, hconj i, reindex_eq_permMatrixOfEquiv_conj]
    simp only [Matrix.mul_assoc]

/-! ## Transport of blockwise data along equal bond dimensions -/

section Transport

/-- Reindexing the matrices of a tensor along an equality of bond dimensions is
the transport of the tensor itself. -/
theorem reindex_finCongr_apply_eq_cast {n m : ℕ} (h : n = m) (A : MPSTensor d n) (i : Fin d) :
    Matrix.reindex (finCongr h) (finCongr h) (A i) =
      (cast (congr_arg (MPSTensor d) h) A) i := by
  subst h
  ext x y
  simp

/-- A weighted conjugated block is transported along an equality of bond
dimensions by reindexing. -/
theorem reindex_smul_conj_eq {n m : ℕ} (h : n = m)
    (c c' : ℂ) (A : MPSTensor d n) (A' : MPSTensor d m)
    (Xg : GL (Fin n) ℂ) (Xg' : GL (Fin m) ℂ)
    (hc : c = c') (hA : A ≍ A') (hX : Xg ≍ Xg') (i : Fin d) :
    Matrix.reindex (finCongr h) (finCongr h)
        (c • ((Xg : Matrix (Fin n) (Fin n) ℂ) * A i *
          ((Xg⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))) =
      c' • ((Xg' : Matrix (Fin m) (Fin m) ℂ) * A' i *
        ((Xg'⁻¹ : GL (Fin m) ℂ) : Matrix (Fin m) (Fin m) ℂ)) := by
  subst h
  subst hc
  rw [eq_of_heq hA, eq_of_heq hX]
  ext x y
  simp

theorem reindex_trans_finCongr {n m k : ℕ} (h₁ : n = m) (h₂ : m = k)
    (M : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.reindex (finCongr h₂) (finCongr h₂)
        (Matrix.reindex (finCongr h₁) (finCongr h₁) M) =
      Matrix.reindex (finCongr (h₁.trans h₂)) (finCongr (h₁.trans h₂)) M := by
  subst h₁
  subst h₂
  rfl

@[simp] theorem matched_block_gauge_apply {Q : SectorDecomposition d}
    (Xblock : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
    (t : Fin Q.totalCopies) :
    matched_block_gauge (Q := Q) Xblock t = Xblock (Q.flatIndexEquiv.symm t).1 := rfl

end Transport

/-! ## The global multiplicity gauge in the equal case -/

/-- **Global multiplicity gauge and similarity in the equal case.**

Given the blockwise data of the equal-case fundamental theorem — a bijection of
the two bases of periodic tensors, matched bond dimensions, blockwise
similarities carrying unit-modulus scalars, a reordering of the multiplicity
copies, and multiplicity ratios that are roots of unity of a common order —
this assembles the two global matrices of arXiv:1708.00029, line 653: the
multiplicity gauge `Z = ⊕_j Z_j ⊗ 1_{D_j}`, which commutes with every matrix of
the first assembled tensor, and the similarity `Y = ⊕_j T_j ⊗ Y_j` carrying the
gauged first tensor to the second.

The unit-modulus scalar of each matched pair is carried explicitly by the
hypothesis relating the multiplicity entries: the ratio that becomes a root of
unity is the one between the multiplicity entries of the second tensor and the
*rescaled* multiplicity entries of the first, exactly as at
arXiv:1708.00029, lines 667--671 and 681--688. -/
theorem equalCase_global_zgauge_of_blockwise
    {P Q : SectorDecomposition d}
    (perm : Fin P.basisCount ≃ Fin Q.basisCount)
    (hDim : ∀ j, P.basisDim j = Q.basisDim (perm j))
    (τ : (j : Fin P.basisCount) → Fin (P.copies j) ≃ Fin (Q.copies (perm j)))
    (ξ : Fin P.basisCount → ℂ)
    (Yb : (k : Fin Q.basisCount) → GL (Fin (Q.basisDim k)) ℂ)
    (hConj : ∀ (j : Fin P.basisCount) (i : Fin d),
      (cast (congr_arg (MPSTensor d) (hDim j)) (P.basis j)) i =
        ξ j • ((Yb (perm j) :
            Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ) *
          Q.basis (perm j) i *
          (((Yb (perm j))⁻¹ : GL (Fin (Q.basisDim (perm j))) ℂ) :
            Matrix (Fin (Q.basisDim (perm j))) (Fin (Q.basisDim (perm j))) ℂ)))
    (z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ)
    (hz : ∀ j q, z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ j q))
    (period : Fin P.basisCount → ℕ)
    (hPer : ∀ j, IsPeriodic (period j) (P.basis j))
    (hzm : ∀ j q, z j q ^ period j = 1)
    (L : ℕ) (hLdvd : ∀ j, period j ∣ L) :
    ∃ (Z : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ)
      (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
      (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
      Z ^ L = 1 ∧ Y * Y' = 1 ∧ Y' * Y = 1 ∧
      (∀ i : Fin d, Z * P.toTensor i = P.toTensor i * Z) ∧
      (∀ i : Fin d, Z * P.toTensor i = Y * Q.toTensor i * Y') ∧
      SameMPV₂Pos P.toTensor (fun i => Z * P.toTensor i) := by
  classical
  have hzL : ∀ j q, z j q ^ L = 1 := by
    intro j q
    obtain ⟨c, hc⟩ := hLdvd j
    rw [hc, pow_mul, hzm, one_pow]
  set zflat : Fin P.totalCopies → ℂ := fun s =>
    z (P.flatIndexEquiv.symm s).1 (P.flatIndexEquiv.symm s).2 with hzflat
  set Z : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ :=
    blockScalarMatrix P.flatDim zflat with hZ
  -- The gauged first tensor is the first tensor with rescaled multiplicities.
  have hZmul : ∀ i : Fin d, Z * P.toTensor i =
      toTensorFromBlocks (d := d)
        (μ := fun s => zflat s * P.flatWeight s) P.flatBasis i := fun i =>
    blockScalarMatrix_mul_toTensorFromBlocks zflat P.flatWeight P.flatBasis i
  have hZmulr : ∀ i : Fin d, P.toTensor i * Z =
      toTensorFromBlocks (d := d)
        (μ := fun s => zflat s * P.flatWeight s) P.flatBasis i := fun i =>
    toTensorFromBlocks_mul_blockScalarMatrix zflat P.flatWeight P.flatBasis i
  -- The matched flattened copy indices.
  set e : Fin P.totalCopies ≃ Fin Q.totalCopies :=
    SectorDecomposition.sectorFlatEquiv (P := Q) (Q := P) perm τ with he
  have hd : ∀ s, P.flatDim s = Q.flatDim (e s) := fun s =>
    (SectorDecomposition.flatDim_sectorFlatEquiv (P := Q) (Q := P) perm
      (fun j => (hDim j).symm) τ s).symm
  have hrel : ∀ (s : Fin P.totalCopies) (i : Fin d),
      Matrix.reindex (finCongr (hd s)) (finCongr (hd s))
          ((zflat s * P.flatWeight s) • P.flatBasis s i) =
        Q.flatWeight (e s) •
          ((matched_block_gauge (Q := Q) Yb (e s) :
              Matrix (Fin (Q.flatDim (e s))) (Fin (Q.flatDim (e s))) ℂ) *
            Q.flatBasis (e s) i *
            (((matched_block_gauge (Q := Q) Yb (e s))⁻¹ :
                GL (Fin (Q.flatDim (e s))) ℂ) :
              Matrix (Fin (Q.flatDim (e s))) (Fin (Q.flatDim (e s))) ℂ)) := by
    intro s i
    set j : Fin P.basisCount := (P.flatIndexEquiv.symm s).1 with hj
    set q : Fin (P.copies j) := (P.flatIndexEquiv.symm s).2 with hq
    have ht : Q.flatIndexEquiv.symm (e s) = ⟨perm j, τ j q⟩ := by
      rw [he, SectorDecomposition.sectorFlatEquiv_apply, Equiv.symm_apply_apply]
    have hQd : Q.flatDim (e s) = Q.basisDim (perm j) :=
      congrArg (fun x : (k : Fin Q.basisCount) × Fin (Q.copies k) =>
        Q.basisDim x.1) ht
    have hQw : Q.flatWeight (e s) = Q.weight (perm j) (τ j q) :=
      congrArg (fun x : (k : Fin Q.basisCount) × Fin (Q.copies k) =>
        Q.weight x.1 x.2) ht
    have hQb : Q.flatBasis (e s) ≍ Q.basis (perm j) :=
      congr_arg_heq (fun x : (k : Fin Q.basisCount) × Fin (Q.copies k) =>
        Q.basis x.1) ht
    have hQx : matched_block_gauge (Q := Q) Yb (e s) ≍ Yb (perm j) :=
      congr_arg_heq (fun x : (k : Fin Q.basisCount) × Fin (Q.copies k) =>
        Yb x.1) ht
    refine (Matrix.reindex (finCongr hQd) (finCongr hQd)).injective ?_
    rw [reindex_trans_finCongr,
      reindex_smul_conj_eq hQd (Q.flatWeight (e s)) (Q.weight (perm j) (τ j q))
        (Q.flatBasis (e s)) (Q.basis (perm j))
        (matched_block_gauge (Q := Q) Yb (e s)) (Yb (perm j)) hQw hQb hQx i]
    have hsmul : Matrix.reindex (finCongr ((hd s).trans hQd))
          (finCongr ((hd s).trans hQd))
          ((zflat s * P.flatWeight s) • P.flatBasis s i) =
        (z j q * P.weight j q) •
          Matrix.reindex (finCongr (hDim j)) (finCongr (hDim j)) (P.basis j i) := by
      have hcong : (hd s).trans hQd = hDim j := rfl
      rw [hcong]
      rfl
    rw [hsmul, reindex_finCongr_apply_eq_cast, hConj j i, smul_smul]
    congr 1
    rw [← hz j q]
    ring
  obtain ⟨Y, Y', hYY', hY'Y, hconj⟩ :=
    toTensorFromBlocks_conj_of_matched_blocks (d := d)
      (fun s => zflat s * P.flatWeight s) P.flatBasis
      Q.flatWeight Q.flatBasis e hd (matched_block_gauge (Q := Q) Yb) hrel
  refine ⟨Z, Y, Y', ?_, hYY', hY'Y, ?_, ?_, ?_⟩
  · rw [hZ, blockScalarMatrix_pow]
    have hone : (fun s : Fin P.totalCopies => zflat s ^ L) = fun _ => (1 : ℂ) := by
      funext s
      exact hzL _ _
    rw [hone, blockScalarMatrix_one]
  · intro i; rw [hZmul i, hZmulr i]
  · intro i; rw [hZmul i]; exact hconj i
  · -- the gauged tensor generates the same matrix-product vectors
    intro N _hN σ
    have hfun : (fun i => Z * P.toTensor i) =
        toTensorFromBlocks (d := d)
          (μ := fun s => zflat s * P.flatWeight s) P.flatBasis := funext hZmul
    rw [hfun]
    change mpv (toTensorFromBlocks (d := d) (μ := P.flatWeight) P.flatBasis) σ = _
    rw [mpv_toTensorFromBlocks_eq_sum, mpv_toTensorFromBlocks_eq_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hdvd : period (P.flatIndexEquiv.symm s).1 ∣ N
    · obtain ⟨c, hc⟩ := hdvd
      have hz1 : zflat s ^ N = 1 := by
        rw [hzflat, hc, pow_mul, hzm, one_pow]
      rw [mul_pow, hz1, one_mul]
    · have hzero : mpv (P.flatBasis s) σ = 0 :=
        pgvwc07_stateVector_eq_zero_of_not_dvd (P.flatBasis s)
          (hPer (P.flatIndexEquiv.symm s).1) hdvd σ
      rw [hzero]
      simp

/-! ## The equal-case fundamental theorem over multiplicity-bearing decompositions -/

/-- Repeated periodic blocks in left-canonical form have equal periods. -/
theorem IsPeriodic.period_eq_of_hetRepeatedBlocks
    {D₁ D₂ m n : ℕ} {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hA : IsPeriodic m A) (hB : IsPeriodic n B)
    (h : HetRepeatedBlocks A B) : m = n := by
  obtain ⟨hDim, hRep⟩ := h
  subst hDim
  exact IsPeriodic.period_eq_of_repeatedBlocks hA hB hRep
    hRep.peripheralEigenvalues_transferMap_eq

/-- **Fundamental theorem for matrix product states, equal case.**

Let two tensors carry the multiplicity-bearing irreducible forms
`A^i = ⊕_{j ∈ J} (R_j ⊗ A_j^i)` and `B^i = ⊕_{k ∈ K} (S_k ⊗ B_k^i)`, with
`R_j` and `S_k` diagonal with nonzero entries and with pairwise non-repeated
bases of periodic tensors. If the two tensors generate the same matrix-product
vector at every positive length, then the two bases have the same size and
there is a bijection `π : J → K` matching each `A_j` with the single `B_{π(j)}`
of the same period, with `A_j` and `B_{π(j)}` repeated blocks.

Moreover, for every `j` of period `m_j` the multiplicity matrices `R_j` and
`S_{π(j)}` have the same size, and after a reordering of the diagonal entries
of `S_{π(j)}` there is a diagonal matrix `Z_j` whose entries are `m_j`-th roots
of unity with `Z_j (ξ_j R_j) = S_{π(j)}`, where `ξ_j` is the unit-modulus scalar
of the repeated-block relation. Collecting the `Z_j` gives a matrix `Z` on the
bond space of the first tensor that commutes with every one of its matrices,
whose order divides the least common multiple of the periods, that satisfies
`Z A^i = Y B^i Y^{-1}` for an invertible `Y`, and that leaves the generated
matrix-product vectors unchanged.

Source: arXiv:1708.00029, theorem `thm:bdequal`, lines 643--693, over the
irreducible forms `eq:bdnr`, line 294, and `eq:Bbdnr`, line 582.

The unit-modulus scalar of each matched pair is displayed rather than
suppressed: the entries of `Z_j` are roots of unity against the *rescaled*
multiplicity matrix `ξ_j R_j`, which is what the source means at lines
667--671 by absorbing the phase into `S_j`. The scalar is genuinely present:
for period one and `B_j = e^{iθ} A_j` it is not a root of unity.

**Scope restriction (irreducible form II):** the blocks are assumed
left-canonical, that is, in irreducible form II. The source theorem assumes
only irreducible form, and asserts at lines 330--332 that one passes between
the two forms by a block-diagonal similarity, so that a proof in either form
applies to the other; that passage is not carried out here. The restriction is
recorded in `docs/paper-gaps/dccsp17_periodic_overlap_route_alignment.tex`,
section "Scope restriction: the equal case in irreducible form II". -/
theorem fundamentalTheorem_periodic_equalCase_sectorDecomposition
    (P Q : SectorDecomposition d)
    (periodP : Fin P.basisCount → ℕ) (periodQ : Fin Q.basisCount → ℕ)
    (hPerP : ∀ j, IsPeriodic (periodP j) (P.basis j))
    (hPerQ : ∀ k, IsPeriodic (periodQ k) (Q.basis k))
    (hNonRepP : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (P.basis i) (P.basis j))
    (hNonRepQ : ∀ i j, i ≠ j → ¬ HetRepeatedBlocks (Q.basis i) (Q.basis j))
    (hSame : SameMPV₂Pos P.toTensor Q.toTensor) :
    ∃ (perm : Fin P.basisCount ≃ Fin Q.basisCount) (ξ : Fin P.basisCount → ℂ),
      (∀ j, ‖ξ j‖ = 1) ∧
      (∀ j, periodP j = periodQ (perm j)) ∧
      (∀ j, HetRepeatedBlocks (P.basis j) (Q.basis (perm j))) ∧
      (∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
              (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j)))
              (Zj : Matrix (Fin (P.copies j)) (Fin (P.copies j)) ℂ),
            Zj ^ periodP j = 1 ∧
            Zj * Matrix.diagonal (fun q => ξ j * P.weight j q) =
              Matrix.diagonal (fun q => Q.weight (perm j) (τ q))) ∧
      ∃ (Z : Matrix (Fin P.totalDim) (Fin P.totalDim) ℂ)
        (Y : Matrix (Fin P.totalDim) (Fin Q.totalDim) ℂ)
        (Y' : Matrix (Fin Q.totalDim) (Fin P.totalDim) ℂ),
        Z ^ (Finset.univ.lcm periodP) = 1 ∧ Y * Y' = 1 ∧ Y' * Y = 1 ∧
        (∀ i : Fin d, Z * P.toTensor i = P.toTensor i * Z) ∧
        (∀ i : Fin d, Z * P.toTensor i = Y * Q.toTensor i * Y') ∧
        SameMPV₂Pos P.toTensor (fun i => Z * P.toTensor i) := by
  classical
  -- Theorem 3.4 supplies the matching of the two bases of periodic tensors.
  obtain ⟨_hCount, perm, hMatch⟩ :=
    fundamentalTheorem_periodic_proportional P.basis Q.basis hNonRepP hNonRepQ
      (PeriodicOverlapHypothesis.ofSectorDecompositions P Q periodP periodQ
        hPerP hPerQ hNonRepP hNonRepQ hSame.toNonzeroProportionalMPV₂)
  choose hDimJ ξ Yb' hξ hConj' using hMatch
  have hξ0 : ∀ j, ξ j ≠ 0 := fun j => Complex.ne_zero_of_norm_eq_one (hξ j)
  have hMatch' : ∀ j, HetRepeatedBlocks (P.basis j) (Q.basis (perm j)) :=
    fun j => ⟨hDimJ j, ξ j, Yb' j, hξ j, hConj' j⟩
  have hPeriodEq : ∀ j, periodP j = periodQ (perm j) := fun j =>
    IsPeriodic.period_eq_of_hetRepeatedBlocks (hPerP j) (hPerQ (perm j)) (hMatch' j)
  -- the matched matrix-product vectors differ by a power of the matched scalar
  have hBasis : ∀ (j : Fin P.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (P.basis j) σ = ξ j ^ N * mpv (Q.basis (perm j)) σ := by
    intro j N σ
    rw [← mpv_cast_dim (hDimJ j) (P.basis j) N σ]
    exact mpv_eq_pow_mul_of_gaugePhase (Q.basis (perm j))
      (cast (congr_arg (MPSTensor d) (hDimJ j)) (P.basis j)) (Yb' j) (ξ j)
      (hConj' j) N σ
  -- coefficient extraction along the period progression
  obtain ⟨N₀, hN₀⟩ :=
    SectorDecomposition.coeff_eq_of_sameMPV_of_matched_basis
      periodP hPerP hNonRepP perm ξ hξ0 hBasis hSame
  have hpowdata : ∀ j, ∃ (_hCopies : P.copies j = Q.copies (perm j))
      (τ : Fin (P.copies j) ≃ Fin (Q.copies (perm j))),
      ∀ q, Q.weight (perm j) (τ q) ^ periodP j =
        (ξ j * P.weight j q) ^ periodP j := by
    intro j
    have hm : 0 < periodP j := (hPerP j).period_pos
    have hCoeff : ∀ n > N₀,
        P.coeff (periodP j * n) j =
          (ξ j)⁻¹ ^ (periodP j * n) * Q.coeff (periodP j * n) (perm j) := by
      intro n hn
      exact hN₀ (periodP j * n)
        (le_trans (le_of_lt hn) (Nat.le_mul_of_pos_left n hm)) j ⟨n, rfl⟩
    obtain ⟨hc, τ, hτ⟩ :=
      matched_sector_weight_pow_equiv_of_period_multiple j (perm j) (periodP j)
        (ξ j)⁻¹ (inv_ne_zero (hξ0 j)) hCoeff
    exact ⟨hc, τ, fun q => by simpa [inv_inv] using hτ q⟩
  choose hCopies τ hτpow using hpowdata
  -- the multiplicity ratios are roots of unity of the block period
  have hden : ∀ j q, ξ j * P.weight j q ≠ 0 := fun j q =>
    mul_ne_zero (hξ0 j) (P.weight_ne_zero j q)
  set z : (j : Fin P.basisCount) → Fin (P.copies j) → ℂ := fun j q =>
    Q.weight (perm j) (τ j q) / (ξ j * P.weight j q) with hzdef
  have hz : ∀ j q, z j q * (ξ j * P.weight j q) = Q.weight (perm j) (τ j q) :=
    fun j q => div_mul_cancel₀ _ (hden j q)
  have hzm : ∀ j q, z j q ^ periodP j = 1 := by
    intro j q
    rw [hzdef, div_pow, hτpow j q, div_self (pow_ne_zero _ (hden j q))]
  refine ⟨perm, ξ, hξ, hPeriodEq, hMatch', ?_, ?_⟩
  · -- blockwise multiplicity gauge
    intro j
    obtain ⟨Zj, hZjpow, hZjmul⟩ :=
      zgauge_construction (periodP j)
        (fun q => Q.weight (perm j) (τ j q)) (fun q => ξ j * P.weight j q)
        (fun q => hτpow j q) (fun q => hden j q)
    exact ⟨hCopies j, τ j, Zj, hZjpow, hZjmul⟩
  · -- global multiplicity gauge and similarity
    obtain ⟨Z, Y, Y', hZpow, hYY', hY'Y, hcomm, hgauge, hmpv⟩ :=
      equalCase_global_zgauge_of_blockwise perm hDimJ τ ξ
        (Equiv.piCongrLeft (fun k => GL (Fin (Q.basisDim k)) ℂ) perm Yb')
        (by
          intro j i
          rw [Equiv.piCongrLeft_apply_apply]
          exact hConj' j i)
        z hz periodP hPerP hzm (Finset.univ.lcm periodP)
        (fun j => Finset.dvd_lcm (Finset.mem_univ j))
    exact ⟨Z, Y, Y', hZpow, hYY', hY'Y, hcomm, hgauge, hmpv⟩

end MPSTensor
