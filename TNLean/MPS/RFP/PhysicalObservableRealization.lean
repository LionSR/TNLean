/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BiCFDerivation.BNTDirectSum
import TNLean.MPS.RFP.BNTOrthogonality
import TNLean.MPS.RFP.ZeroCorrelationLength

/-!
# Physical observables from simultaneous block injectivity

This file proves the multiplicity-one, unit-weight specialization of the
physical-observable realization used in the converse zero-correlation-length
argument of arXiv:1606.00608, lines 1250--1258. A simultaneous word span allows
one physical observable to select one BNT basis sector and one virtual matrix
unit on both sides of the inserted transfer map.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- A simultaneous length-`L` word span has a coefficient family which selects
one block label and one matrix entry.

This is the length-`L` form of the simultaneous inverse supplied by the
block-injective proposition at arXiv:1606.00608, lines 340--345. -/
theorem WordTupleSpanTop.exists_simultaneous_left_inverse
    {A : (k : Fin r) → MPSTensor d (dim k)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L) :
    ∃ C : Matrix (BlockEntryIndex dim) (Fin L → Fin d) ℂ,
      ∀ (k j : Fin r) (x y : Fin (dim k))
        (x' y' : Fin (dim j)),
        (∑ w : Fin L → Fin d,
          C ⟨k, x, y⟩ w * evalWord (A j) (List.ofFn w) x' y') =
            if h : k = j then
              if _ : h ▸ x = x' then if _ : h ▸ y = y' then 1 else 0 else 0
            else 0 := by
  classical
  let target (k : Fin r) (x y : Fin (dim k)) :
      (j : Fin r) → Matrix (Fin (dim j)) (Fin (dim j)) ℂ :=
    fun j x' y' =>
      if h : k = j then
        if _ : h ▸ x = x' then if _ : h ▸ y = y' then 1 else 0 else 0
      else 0
  have htarget (k : Fin r) (x y : Fin (dim k)) :
      target k x y ∈ Submodule.span ℂ (Set.range (wordTuple A L)) := by
    rw [hSpan]
    exact Submodule.mem_top
  have hcoeff (k : Fin r) (x y : Fin (dim k)) :
      ∃ c : (Fin L → Fin d) → ℂ,
        ∑ w, c w • wordTuple A L w = target k x y :=
    (Submodule.mem_span_range_iff_exists_fun ℂ).mp (htarget k x y)
  choose C hC using hcoeff
  refine ⟨fun z w ↦ C z.1 z.2.1 z.2.2 w, ?_⟩
  intro k j x y x' y'
  have hentry := congrArg (fun M ↦ M j x' y') (hC k x y)
  simpa [wordTuple, target, Fintype.linearCombination_apply,
    Matrix.sum_apply, Matrix.smul_apply] using hentry

/-- The physical observable transfer as a double sum of word insertions. -/
private theorem physicalObservableTransfer_apply
    (A : MPSTensor d D) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    physicalObservableTransfer A L O X =
      ∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
        O τ σ • (evalWord A (List.ofFn σ) * X *
          (evalWord A (List.ofFn τ))ᴴ) := by
  classical
  simp only [physicalObservableTransfer, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  simp only [Matrix.mul_assoc]

/-- Inserted transfer maps preserve finite linear combinations of physical
observables. -/
private theorem physicalObservableTransfer_sum_smul
    {ι : Type*} [Fintype ι] (A : MPSTensor d D) (L : ℕ)
    (q : ι → ℂ)
    (O : ι → Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    physicalObservableTransfer A L (∑ i, q i • O i) =
      ∑ i, q i • physicalObservableTransfer A L (O i) := by
  classical
  apply LinearMap.ext
  intro X
  rw [physicalObservableTransfer_apply]
  simp only [Matrix.sum_apply, Matrix.smul_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, Finset.sum_smul]
  conv_lhs =>
    rw [Finset.sum_comm]
    enter [2, σ]
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalObservableTransfer_apply]
  conv_rhs => rw [Finset.sum_comm]
  simp [Finset.smul_sum, smul_smul]

/-- A word of a direct-sum tensor is the direct sum of the corresponding block
words. -/
private theorem evalWord_directSumTensor
    (A : (k : Fin r) → MPSTensor d (dim k)) (w : List (Fin d)) :
    evalWord (directSumTensor A) w =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k ↦ evalWord (A k) w) := by
  have hDirect : directSumTensor A = toTensorFromBlocks (fun _ ↦ 1) A := by
    funext i
    simp [directSumTensor, toTensorFromBlocks]
  rw [hDirect, evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal]
  simp

/-- Submatrices commute with finite sums. -/
private theorem submatrix_sum {ι l m p q : Type*}
    (s : Finset ι) (M : ι → Matrix m p ℂ) (f : l → m) (g : q → p) :
    (∑ i ∈ s, M i).submatrix f g = ∑ i ∈ s, (M i).submatrix f g := by
  ext a b
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

/-- The inserted transfer map of a direct sum is the reindexing of the
corresponding block-diagonal word sum. -/
private theorem physicalObservableTransfer_directSum_reindex
    (A : (k : Fin r) → MPSTensor d (dim k)) (L : ℕ)
    (O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ)
    (Y : Matrix ((k : Fin r) × Fin (dim k))
      ((k : Fin r) × Fin (dim k)) ℂ) :
    physicalObservableTransfer (directSumTensor A) L O
        (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv Y) =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
          O τ σ •
            (Matrix.blockDiagonal' (fun k ↦ evalWord (A k) (List.ofFn σ)) * Y *
              (Matrix.blockDiagonal' (fun k ↦
                evalWord (A k) (List.ofFn τ)))ᴴ)) := by
  classical
  rw [physicalObservableTransfer_apply]
  simp only [evalWord_directSumTensor, Matrix.reindex_apply]
  rw [submatrix_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [submatrix_sum]
  apply Finset.sum_congr rfl
  intro τ _
  rw [Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv _ _ _ finSigmaFinEquiv.symm _,
    Matrix.submatrix_mul_equiv _ _ _ finSigmaFinEquiv.symm _]
  rfl

/-- A simultaneous length-`L` word span realizes a sector-supported virtual
matrix-unit map by a physical observable on `L` sites.

For the direct-sum tensor, the inserted transfer map sends the chosen input
entry in sector `j` to the chosen output entry in the same sector and vanishes
on every other sector pair. By linearity, these matrix-unit realizations give
the rank-one maps $|R_j)(l_j|$ and $|r_j)(L_j|$ in equations (1252) and (1256)
of arXiv:1606.00608.
-/
theorem WordTupleSpanTop.exists_physicalObservableTransfer_directSum_matrixUnit
    {A : (k : Fin r) → MPSTensor d (dim k)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L)
    (j : Fin r) (a b c e : Fin (dim j)) :
    ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ,
        physicalObservableTransfer (directSumTensor A) L O X =
          Matrix.single
            (finSigmaFinEquiv ⟨j, a⟩) (finSigmaFinEquiv ⟨j, c⟩)
            (X (finSigmaFinEquiv ⟨j, b⟩) (finSigmaFinEquiv ⟨j, e⟩)) := by
  classical
  obtain ⟨C, hC⟩ := hSpan.exists_simultaneous_left_inverse
  let W : (Fin L → Fin d) →
      Matrix ((k : Fin r) × Fin (dim k)) ((k : Fin r) × Fin (dim k)) ℂ :=
    fun σ ↦ Matrix.blockDiagonal' (fun k ↦ evalWord (A k) (List.ofFn σ))
  let M₁ := ∑ σ : Fin L → Fin d, C ⟨j, a, b⟩ σ • W σ
  let M₂ := ∑ τ : Fin L → Fin d, C ⟨j, c, e⟩ τ • W τ
  have hM₁ : M₁ = Matrix.single ⟨j, a⟩ ⟨j, b⟩ 1 := by
    ext ⟨k, x⟩ ⟨l, y⟩
    by_cases hkl : k = l
    · subst l
      simp only [M₁, Matrix.sum_apply, Matrix.smul_apply, W,
        Matrix.blockDiagonal'_apply_eq, smul_eq_mul]
      rw [hC]
      by_cases hjk : j = k
      · subst k
        by_cases hx : a = x <;> by_cases hy : b = y <;>
          simp [hx, hy]
      · simp [hjk]
    · have hnot : ¬ ((j = k ∧ HEq a x) ∧ j = l ∧ HEq b y) := by
        rintro ⟨⟨hjk, _⟩, hjl, _⟩
        exact hkl (hjk.symm.trans hjl)
      simp only [M₁, Matrix.sum_apply, Matrix.smul_apply, W]
      rw [Finset.sum_eq_zero]
      · simp [hnot]
      · intro σ _
        simp [Matrix.blockDiagonal'_apply_ne _ _ _ hkl]
  have hM₂ : M₂ = Matrix.single ⟨j, c⟩ ⟨j, e⟩ 1 := by
    ext ⟨k, x⟩ ⟨l, y⟩
    by_cases hkl : k = l
    · subst l
      simp only [M₂, Matrix.sum_apply, Matrix.smul_apply, W,
        Matrix.blockDiagonal'_apply_eq, smul_eq_mul]
      rw [hC]
      by_cases hjk : j = k
      · subst k
        by_cases hx : c = x <;> by_cases hy : e = y <;>
          simp [hx, hy]
      · simp [hjk]
    · have hnot : ¬ ((j = k ∧ HEq c x) ∧ j = l ∧ HEq e y) := by
        rintro ⟨⟨hjk, _⟩, hjl, _⟩
        exact hkl (hjk.symm.trans hjl)
      simp only [M₂, Matrix.sum_apply, Matrix.smul_apply, W]
      rw [Finset.sum_eq_zero]
      · simp [hnot]
      · intro τ _
        simp [Matrix.blockDiagonal'_apply_ne _ _ _ hkl]
  let O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ := fun τ σ ↦
    C ⟨j, a, b⟩ σ * starRingEnd ℂ (C ⟨j, c, e⟩ τ)
  refine ⟨O, ?_⟩
  intro X
  let Y := Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm X
  have hX : X = Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv Y := by
    ext u v
    simp [Y, Matrix.reindex_apply]
  have hSum :
      (∑ σ : Fin L → Fin d, ∑ τ : Fin L → Fin d,
        O τ σ • (W σ * Y * (W τ)ᴴ)) = M₁ * Y * M₂ᴴ := by
    simp only [mul_assoc, Matrix.sum_mul, Algebra.smul_mul_assoc,
      Matrix.conjTranspose_sum, Matrix.conjTranspose_smul, RCLike.star_def,
      Matrix.mul_sum, Algebra.mul_smul_comm, Finset.smul_sum, smul_smul,
      mul_comm, O, M₁, M₂]
    rw [Finset.sum_comm]
  rw [hX, physicalObservableTransfer_directSum_reindex]
  change Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
      (∑ σ, ∑ τ, O τ σ • (W σ * Y * (W τ)ᴴ)) = _
  rw [hSum, hM₁, hM₂]
  ext u v
  simp only [Matrix.reindex_apply]
  simp [Matrix.single_apply, Equiv.eq_symm_apply]

/-- A physical observable can realize an arbitrary linear combination of
virtual matrix-unit maps supported on one BNT sector.

This is the linear extension of
`WordTupleSpanTop.exists_physicalObservableTransfer_directSum_matrixUnit`.
It is the sector-selection content of arXiv:1606.00608, lines 1250--1258. -/
theorem WordTupleSpanTop.exists_physicalObservableTransfer_directSum_sectorSupported
    {A : (k : Fin r) → MPSTensor d (dim k)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L) (j : Fin r)
    (q : Fin (dim j) × Fin (dim j) × Fin (dim j) × Fin (dim j) → ℂ) :
    ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ,
        physicalObservableTransfer (directSumTensor A) L O X =
          ∑ z, q z • Matrix.single
            (finSigmaFinEquiv ⟨j, z.1⟩)
            (finSigmaFinEquiv ⟨j, z.2.2.1⟩)
            (X (finSigmaFinEquiv ⟨j, z.2.1⟩)
              (finSigmaFinEquiv ⟨j, z.2.2.2⟩)) := by
  classical
  have hUnit : ∀ z : Fin (dim j) × Fin (dim j) × Fin (dim j) × Fin (dim j),
      ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
        ∀ X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ,
          physicalObservableTransfer (directSumTensor A) L O X =
            Matrix.single
              (finSigmaFinEquiv ⟨j, z.1⟩)
              (finSigmaFinEquiv ⟨j, z.2.2.1⟩)
              (X (finSigmaFinEquiv ⟨j, z.2.1⟩)
                (finSigmaFinEquiv ⟨j, z.2.2.2⟩)) := by
    rintro ⟨a, b, c, e⟩
    exact hSpan.exists_physicalObservableTransfer_directSum_matrixUnit j a b c e
  choose O hO using hUnit
  refine ⟨∑ z, q z • O z, ?_⟩
  intro X
  rw [physicalObservableTransfer_sum_smul]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro z _
  rw [hO z X]

/-- In the multiplicity-one, unit-weight direct sum, the two virtual rank-one
insertions corresponding to equations (1252) and (1256) of arXiv:1606.00608
are physical observables supported on the common block-injective length.

The coefficient `R a c * l e b` is the matrix-entry expansion of
$|R)(l|$: it sends an input matrix `X` to
$\operatorname{tr}(lX)R$. The conclusion is supported only on the selected
sector `j`; all other diagonal and off-diagonal sector pairs vanish. -/
theorem WordTupleSpanTop.exists_physicalObservableTransfer_directSum_rankOne
    {A : (k : Fin r) → MPSTensor d (dim k)} {L : ℕ}
    (hSpan : WordTupleSpanTop A L) (j : Fin r)
    (R l : Matrix (Fin (dim j)) (Fin (dim j)) ℂ) :
    ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
      ∀ X : Matrix (Fin (∑ k, dim k)) (Fin (∑ k, dim k)) ℂ,
        physicalObservableTransfer (directSumTensor A) L O X =
          ∑ z : Fin (dim j) × Fin (dim j) × Fin (dim j) × Fin (dim j),
            (R z.1 z.2.2.1 * l z.2.2.2 z.2.1) • Matrix.single
              (finSigmaFinEquiv ⟨j, z.1⟩)
              (finSigmaFinEquiv ⟨j, z.2.2.1⟩)
              (X (finSigmaFinEquiv ⟨j, z.2.1⟩)
                (finSigmaFinEquiv ⟨j, z.2.2.2⟩)) :=
  hSpan.exists_physicalObservableTransfer_directSum_sectorSupported j
    (fun z ↦ R z.1 z.2.2.1 * l z.2.2.2 z.2.1)

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- The multiplicity-one, unit-weight direct sum of a BNT basis admits
sector-supported rank-one physical observables on a common region of size at
most $3D^5$, where $D$ is the total bond dimension.

This is the multiplicity-one specialization of the physical-observable
consequence of Proposition `propblockinj` used at arXiv:1606.00608, lines
1250--1258. It selects one BNT basis sector and realizes an arbitrary virtual
rank-one insertion there, while all other sector pairs vanish. The raw-weight
repeated-copy tensor `P.toTensor` is not the tensor in this conclusion. -/
theorem exists_basis_physicalObservableTransfer_rankOne_le_three_totalDim_pow_five
    (hCF : IsBNTCanonicalForm P) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 3 * P.totalDim ^ 5 ∧
      ∀ (j : Fin P.basisCount)
        (R l : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ),
        ∃ O : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ,
          ∀ X : Matrix (Fin (∑ k : Fin P.basisCount, P.basisDim k))
              (Fin (∑ k : Fin P.basisCount, P.basisDim k)) ℂ,
            physicalObservableTransfer (directSumTensor P.basis) L O X =
              ∑ z : Fin (P.basisDim j) × Fin (P.basisDim j) ×
                  Fin (P.basisDim j) × Fin (P.basisDim j),
                (R z.1 z.2.2.1 * l z.2.2.2 z.2.1) • Matrix.single
                  (finSigmaFinEquiv ⟨j, z.1⟩)
                  (finSigmaFinEquiv ⟨j, z.2.2.1⟩)
                  (X (finSigmaFinEquiv ⟨j, z.2.1⟩)
                    (finSigmaFinEquiv ⟨j, z.2.2.2⟩)) := by
  obtain ⟨L, hL, hLbound, hSpan⟩ :=
    hCF.exists_basis_wordTupleSpanTop_le_three_totalDim_pow_five
  refine ⟨L, hL, hLbound, ?_⟩
  intro j R l
  exact hSpan.exists_physicalObservableTransfer_directSum_rankOne j R l

end IsBNTCanonicalForm

end MPSTensor
