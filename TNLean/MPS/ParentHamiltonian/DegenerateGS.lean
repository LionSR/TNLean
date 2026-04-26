/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.Assembly
import TNLean.MPS.CanonicalForm.BlockDiagonalCommutant
import TNLean.MPS.FundamentalTheorem.Multi

/-!
# Degenerate ground space = BNT span (block-injective parent Hamiltonians)

This file states the block-injective ground-space result:
for a canonical-form/BNT decomposition, the periodic parent-Hamiltonian ground
space equals the span of the BNT states.

The detailed proof is split conceptually into two inclusions:

* `⊇`: each BNT block-state is in the parent-Hamiltonian ground space;
* `⊆`: every ground state decomposes into block components, and injective-block
  uniqueness (from `UniqueGroundState`) forces each component to be proportional
  to the block MPV state.
-/

namespace MPSTensor

open scoped Matrix BigOperators

variable {d r : ℕ} {dim : Fin r → ℕ} {μ : Fin r → ℂ}

/-- Parent-Hamiltonian ground space for a CF/BNT block family, represented via
`chainGroundSpace` of the assembled tensor `toTensorFromBlocks μ A`.

Note: this definition depends on the implicit BNT phase/eigenvalue data
`μ : Fin r → ℂ` via `toTensorFromBlocks`. -/
noncomputable def parentHamiltonianGroundSpace
    (A : (j : Fin r) → MPSTensor d (dim j)) (L N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  chainGroundSpace (toTensorFromBlocks μ A) L N

@[simp] lemma parentHamiltonianGroundSpace_eq
    (A : (j : Fin r) → MPSTensor d (dim j)) (L N : ℕ) :
    parentHamiltonianGroundSpace (μ := μ) A L N =
      chainGroundSpace (toTensorFromBlocks μ A) L N := rfl

/-- Span of BNT block MPV states (as `N`-site coefficient functions). -/
noncomputable def bntSpan
    (A : (j : Fin r) → MPSTensor d (dim j)) (N : ℕ) :
    Submodule ℂ (NSiteSpace d N) :=
  Submodule.span ℂ (Set.range fun j : Fin r => (mpv (A j) : NSiteSpace d N))

/-- Ground space of any block `A j` is contained in the ground space of the
assembled tensor `toTensorFromBlocks μ A`, provided `μ j ≠ 0`.

The witness embeds `(μ j)⁻¹ ^ L • Y` into the `j`-th diagonal block of the
assembled matrix. -/
private lemma groundSpace_block_le_assembled
    (μ' : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (j : Fin r) (hμj : μ' j ≠ 0) (L : ℕ) :
    groundSpace (A j) L ≤ groundSpace (toTensorFromBlocks μ' A) L := by
  classical
  intro ψ hψ
  rw [groundSpace, LinearMap.mem_range] at hψ ⊢
  obtain ⟨Y, rfl⟩ := hψ
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k, dim k) := finSigmaFinEquiv
  let Xblock : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ :=
    fun k => if h : k = j then h ▸ ((μ' j)⁻¹ ^ L • Y) else 0
  refine ⟨(Matrix.reindex e e) (Matrix.blockDiagonal' Xblock), ?_⟩
  ext σ
  simp only [groundSpaceMap_apply]
  set w := List.ofFn σ with hw
  have hwlen : w.length = L := by simp [w]
  -- Rewrite evalWord of assembled tensor as reindexed block-diagonal
  let BD := fun i : Fin d =>
    Matrix.blockDiagonal' (fun k => μ' k • A k i)
  have hEval : MPSTensor.evalWord (toTensorFromBlocks μ' A) w =
      (Matrix.reindex e e) (_root_.evalWord BD w) := by
    simpa [toTensorFromBlocks, BD, e,
      show (fun i : Fin d => toTensorFromBlocks μ' A i) =
        fun i => (Matrix.reindex e e) (BD i) from by funext i; rfl]
      using evalWord_reindex (e := e) (A := BD) w
  rw [hEval,
    show Matrix.reindex e e (_root_.evalWord BD w) *
        Matrix.reindex e e (Matrix.blockDiagonal' Xblock) =
      Matrix.reindex e e (_root_.evalWord BD w * Matrix.blockDiagonal' Xblock) from by
      simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv],
    Matrix.trace_reindex,
    show _root_.evalWord BD w = Matrix.blockDiagonal'
        (fun k => (μ' k) ^ w.length • _root_.evalWord (A k) w) from by
      simpa [BD] using evalWord_blockDiagonal'_smul μ' A w,
    ← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
  rw [Finset.sum_eq_single j]
  · -- j-th term: scalar cancellation μ^L · μ⁻¹^L = 1
    simp only [Xblock, dif_pos rfl, hwlen]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_smul,
      show (μ' j) ^ L * (μ' j)⁻¹ ^ L = 1 from by
        rw [← mul_pow, mul_inv_cancel₀ hμj, one_pow],
      one_smul, evalWord_aux_eq]
  · -- k ≠ j: block is zero
    intro k _ hkj
    simp [Xblock, hkj]
  · -- j ∈ Finset.univ
    intro h; exact absurd (Finset.mem_univ j) h

/-- Periodic-chain block lift: each block `A j`'s chain ground space embeds into
the assembled tensor's chain ground space, provided `μ j ≠ 0`.

The two chain ground spaces live in the same ambient `NSiteSpace d N`, so the
lift is an inclusion of submodules; the witness for each cyclic window is
delivered by `groundSpace_block_le_assembled`. -/
theorem chainGroundSpace_block_le_toTensorFromBlocks
    (μ' : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (j : Fin r) (hμj : μ' j ≠ 0) (L N : ℕ) :
    chainGroundSpace (A j) L N ≤ chainGroundSpace (toTensorFromBlocks μ' A) L N := by
  intro ψ hψ
  by_cases h : 0 < N ∧ L ≤ N
  · rw [chainGroundSpace, dif_pos h] at hψ ⊢
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hψ ⊢
    intro i τ
    exact groundSpace_block_le_assembled μ' A j hμj L (hψ i τ)
  · rw [chainGroundSpace, dif_neg h]; exact Submodule.mem_top

/-- **Periodic block decomposition (forward inclusion)**: the supremum of the
blockwise periodic-chain ground spaces is contained in the assembled tensor's
periodic-chain ground space, provided every weight `μ j` is nonzero.

This is the `≥` half of the structural decomposition
`chainGroundSpace (toTensorFromBlocks μ A) L N = ⨆ j, chainGroundSpace (A j) L N`
referenced at the parent-Hamiltonian docstring (see `parentHamiltonian_gs_eq_bnt_span`).

The reverse inclusion — that every periodic-chain ground state of the assembled
tensor decomposes blockwise — is now reduced algebraically to the block-diagonal
boundary-matrix commutant step. The lemma
`isBlockDiagonal'_of_commutes_reindexed_wordSpan` shows that, once the virtual
sector projections are known to lie in the finite span of assembled long-word
matrices, any boundary matrix commuting with those long words has no off-block
entries. The remaining structural input is the CF/BNT finite-span statement for
those sector projections; after that, the blockwise injective endgame isolated
below applies `chainGroundSpace_eq_mpvSubmodule` to reach the BNT span. -/
theorem iSup_chainGroundSpace_block_le_toTensorFromBlocks
    (μ' : Fin r → ℂ) (hμ : ∀ j, μ' j ≠ 0)
    (A : (k : Fin r) → MPSTensor d (dim k)) (L N : ℕ) :
    (⨆ j, chainGroundSpace (A j) L N) ≤
      chainGroundSpace (toTensorFromBlocks μ' A) L N :=
  iSup_le fun j => chainGroundSpace_block_le_toTensorFromBlocks μ' A j (hμ j) L N

/-- CF-BNT specialization of `iSup_chainGroundSpace_block_le_toTensorFromBlocks`:
for a canonical-form/BNT block decomposition, the parent-Hamiltonian ground
space contains the supremum of the blockwise periodic-chain ground spaces. -/
theorem iSup_chainGroundSpace_block_le_parentHamiltonianGroundSpace
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) (L N : ℕ) :
    (⨆ j, chainGroundSpace (A j) L N) ≤
      parentHamiltonianGroundSpace (μ := μ) A L N :=
  iSup_chainGroundSpace_block_le_toTensorFromBlocks
    μ (fun j => hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero j) A L N

/-- `⊇` direction: each BNT block MPV lies in the parent-Hamiltonian ground
space of the assembled tensor.

The proof lifts `mpv_mem_chainGroundSpace` from the block level to the
assembled tensor using `chainGroundSpace_block_le_toTensorFromBlocks`. -/
theorem bnt_mem_groundSpace
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1)
    (j : Fin r) :
    (mpv (A j) : NSiteSpace d N) ∈ parentHamiltonianGroundSpace (μ := μ) A L N := by
  simp only [parentHamiltonianGroundSpace_eq]
  have hLN : L ≤ N := by omega
  have hN' : 0 < N := by omega
  have hμj : μ j ≠ 0 := hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero j
  exact chainGroundSpace_block_le_toTensorFromBlocks μ A j hμj L N
    (mpv_mem_chainGroundSpace (A j) L N hN' hLN)

/-- Boundary-map expansion for block-diagonal assembled boundaries.

If the boundary matrix for `toTensorFromBlocks μ A` is itself the reindexed
block diagonal with diagonal blocks `Xb k`, then the corresponding `N`-site
open-chain vector is the sum of the blockwise open-chain vectors, with the
expected weight factor `(μ k) ^ N`. -/
private lemma groundSpaceMap_toTensorFromBlocks_blockDiagonal
    (μ' : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (Xb : (k : Fin r) → Matrix (Fin (dim k)) (Fin (dim k)) ℂ) (N : ℕ) :
    groundSpaceMap (toTensorFromBlocks μ' A) N
        ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv) (Matrix.blockDiagonal' Xb)) =
      ∑ k : Fin r, (μ' k) ^ N • groundSpaceMap (A k) N (Xb k) := by
  classical
  ext σ
  simp only [groundSpaceMap_apply]
  have hwlen : (List.ofFn σ).length = N := by simp
  rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal μ' A (List.ofFn σ)]
  rw [show Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
          (Matrix.blockDiagonal' fun k =>
            (μ' k) ^ (List.ofFn σ).length • evalWord (A k) (List.ofFn σ)) *
        Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv (Matrix.blockDiagonal' Xb) =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        ((Matrix.blockDiagonal' fun k =>
            (μ' k) ^ (List.ofFn σ).length • evalWord (A k) (List.ofFn σ)) *
          Matrix.blockDiagonal' Xb) from by
        simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]]
  rw [Matrix.trace_reindex, ← Matrix.blockDiagonal'_mul, Matrix.trace_blockDiagonal']
  simp [groundSpaceMap_apply, hwlen, Matrix.trace_smul, Algebra.smul_mul_assoc]

/-- Applying `groundSpaceMap` to a scalar boundary matrix gives a scalar multiple
of the periodic MPV coefficient vector. -/
private lemma groundSpaceMap_matrix_scalar
    (A : MPSTensor d D) (N : ℕ) (c : ℂ) :
    groundSpaceMap A N (Matrix.scalar (Fin D) c) = c • (mpv A : NSiteSpace d N) := by
  ext σ
  simp only [groundSpaceMap_apply, Pi.smul_apply, smul_eq_mul, mpv, coeff]
  have hscalar : Matrix.scalar (Fin D) c = c • (1 : Matrix (Fin D) (Fin D) ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar, hij]
  rw [hscalar, Matrix.mul_smul, mul_one, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- Boundary-matrix block split from the projection-span input.

This is the algebraic endgame for the block-decomposition argument. Assume the
#911 finite-span input that every virtual sector projection lies in the
pulled-back span of length-`m` assembled word products. If a boundary matrix `X`
for the assembled tensor commutes with those length-`m` words (the output
expected from the wrapping-window comparison), then the open-chain vector
`groundSpaceMap (toTensorFromBlocks μ A) N X` lies in the supremum of the
blockwise periodic chain ground spaces.

The proof first applies
`MPSTensor.isBlockDiagonal'_of_commutes_reindexed_wordSpan` to make the pulled-back
boundary matrix block diagonal. Then the same length-`m` commutation, restricted
to each diagonal block, and blockwise injectivity from `IsCanonicalFormBNT` force
each diagonal block to be scalar. The boundary-map expansion above rewrites the
state as a finite sum of scalar multiples of the block MPV states; each block MPV
is in its own `chainGroundSpace`. -/
theorem groundSpaceMap_toTensorFromBlocks_mem_iSup_chainGroundSpace_of_reindexed_projectionSpan
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω))))
    {X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ}
    (hComm : ∀ ω : Fin m → Fin d,
      X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
        evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    groundSpaceMap (toTensorFromBlocks μ A) N X ∈
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  classical
  let e : ((k : Fin r) × Fin (dim k)) ≃ Fin (∑ k : Fin r, dim k) := finSigmaFinEquiv
  rcases isBlockDiagonal'_of_commutes_reindexed_wordSpan
      (B := toTensorFromBlocks μ A) (m := m) hProj hComm with
    ⟨Xb, hXb⟩
  have hCommRe : ∀ ω : Fin m → Fin d,
      Matrix.blockDiagonal' Xb *
          Matrix.blockDiagonal' (fun k : Fin r =>
            (μ k) ^ m • evalWord (A k) (List.ofFn ω)) =
        Matrix.blockDiagonal' (fun k : Fin r =>
            (μ k) ^ m • evalWord (A k) (List.ofFn ω)) *
          Matrix.blockDiagonal' Xb := by
    intro ω
    have h := congrArg (Matrix.reindex e.symm e.symm) (hComm ω)
    have hEval :
        Matrix.reindex e.symm e.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) =
          Matrix.blockDiagonal' (fun k : Fin r =>
            (μ k) ^ m • evalWord (A k) (List.ofFn ω)) := by
      rw [evalWord_toTensorFromBlocks_eq_reindex_blockDiagonal μ A (List.ofFn ω)]
      ext a b
      simp [e]
    have hLeft :
        Matrix.reindex e.symm e.symm
            (X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) =
          Matrix.reindex e.symm e.symm X *
            Matrix.reindex e.symm e.symm
              (evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
      exact (Matrix.submatrix_mul_equiv X
        (evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) e e e).symm
    have hRight :
        Matrix.reindex e.symm e.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) =
          Matrix.reindex e.symm e.symm
              (evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) *
            Matrix.reindex e.symm e.symm X := by
      rw [Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply]
      exact (Matrix.submatrix_mul_equiv
        (evalWord (toTensorFromBlocks μ A) (List.ofFn ω)) X e e e).symm
    rw [hLeft, hRight, hXb, hEval] at h
    exact h
  have hCommBlock : ∀ (k : Fin r) (ω : Fin m → Fin d),
      Xb k * evalWord (A k) (List.ofFn ω) = evalWord (A k) (List.ofFn ω) * Xb k := by
    intro k ω
    have hblock_smul :
        (μ k) ^ m • (Xb k * evalWord (A k) (List.ofFn ω)) =
          (μ k) ^ m • (evalWord (A k) (List.ofFn ω) * Xb k) := by
      have hblockEq :
          Matrix.blockDiagonal' (fun k : Fin r =>
              Xb k * ((μ k) ^ m • evalWord (A k) (List.ofFn ω))) =
            Matrix.blockDiagonal' (fun k : Fin r =>
              ((μ k) ^ m • evalWord (A k) (List.ofFn ω)) * Xb k) := by
        rw [Matrix.blockDiagonal'_mul, Matrix.blockDiagonal'_mul]
        exact hCommRe ω
      ext a b
      have hentry := congrFun (congrFun hblockEq ⟨k, a⟩) ⟨k, b⟩
      simpa [Algebra.mul_smul_comm, Algebra.smul_mul_assoc] using hentry
    have hμpow : (μ k) ^ m ≠ 0 :=
      pow_ne_zero m (hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero k)
    have hcancel := congrArg (fun M => ((μ k) ^ m)⁻¹ • M) hblock_smul
    simpa [smul_smul, hμpow] using hcancel
  have hScalar : ∀ k : Fin r, ∃ c : ℂ, Xb k = Matrix.scalar (Fin (dim k)) c := by
    intro k
    refine Matrix.isScalar_of_commute_span_eq_top
      (S := Set.range fun ω : Fin m → Fin d => evalWord (A k) (List.ofFn ω))
      (Xb k) ?_ ?_
    · simpa [wordSpan] using
        wordSpan_eq_top_of_isInjective (hCF.toHasInjectiveBlocks.block_injective k) hm
    · intro M hM
      rcases hM with ⟨ω, rfl⟩
      exact hCommBlock k ω
  choose c hc using hScalar
  have hX : X = Matrix.reindex e e (Matrix.blockDiagonal' Xb) := by
    rw [← hXb]
    ext a b
    simp [e]
  rw [hX, groundSpaceMap_toTensorFromBlocks_blockDiagonal]
  refine Submodule.sum_mem _ ?_
  intro k _
  rw [hc k, groundSpaceMap_matrix_scalar, smul_smul]
  exact Submodule.smul_mem _ _
    ((le_iSup (fun j : Fin r => chainGroundSpace (A j) L N) k)
      (mpv_mem_chainGroundSpace (A k) L N (by omega) (by omega)))

/-- Conditional reverse block split from the finite projection-span input.

Besides the #911 projection-span hypothesis, this theorem assumes the
boundary-matrix output of the wrapping/open-chain layer: every vector in the
assembled periodic ground space can be represented as `groundSpaceMap` applied to
a boundary matrix that commutes with all length-`m` assembled word products. Under
these inputs, the assembled periodic ground space is contained in the supremum of
the blockwise periodic ground spaces. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω))))
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    chainGroundSpace (toTensorFromBlocks μ A) L N ≤
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  intro ψ hψ
  rcases hBoundary hψ with ⟨X, hψX, hComm⟩
  rw [hψX]
  exact groundSpaceMap_toTensorFromBlocks_mem_iSup_chainGroundSpace_of_reindexed_projectionSpan
    (μ := μ) A hCF hL hN hm hProj hComm

/-- Conditional periodic block-decomposition equality for the assembled tensor.

This combines the already-proved forward inclusion with
`chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan`. The
only CF/BNT-specific finite-span assumption here is the #911 projection-span
input; the remaining boundary-matrix representation/commutation hypothesis is
the wrapping-window output that supplies the boundary matrix to which the
commutant reduction applies. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_reindexed_projectionSpan
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω))))
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    chainGroundSpace (toTensorFromBlocks μ A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N := by
  apply le_antisymm
  · exact chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan
      (μ := μ) A hCF hL hN hm hProj hBoundary
  · exact iSup_chainGroundSpace_block_le_toTensorFromBlocks μ
      (fun j => hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero j) A L N

/-- If the assembled periodic ground space splits blockwise into the block chain
ground spaces, then blockwise injective uniqueness already yields membership in
`bntSpan`. This isolates the endgame so the only missing ingredient is the
block-splitting theorem itself. -/
private theorem parentHamiltonianGroundSpace_le_bntSpan_of_block_chain_split
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1)
    (hSplit :
      parentHamiltonianGroundSpace (μ := μ) A L N ≤
        ⨆ j : Fin r, chainGroundSpace (A j) L N) :
    parentHamiltonianGroundSpace (μ := μ) A L N ≤ bntSpan A N := by
  refine hSplit.trans ?_
  refine iSup_le ?_
  intro j
  have hdim_ne : dim j ≠ 0 := by
    intro hdim0
    have hzero : ∀ N : ℕ, mpvOverlap (d := d) (A j) (A j) N = 0 := by
      intro N
      classical
      haveI : IsEmpty (Fin (dim j)) := by rw [hdim0]; infer_instance
      simp [mpvOverlap, mpv, coeff, Matrix.trace_eq_zero_of_isEmpty]
    have hconst : Filter.Tendsto (fun _ : ℕ => (0 : ℂ)) Filter.atTop (nhds (1 : ℂ)) :=
      (hCF.overlap_tendsto_one j).congr' (Filter.Eventually.of_forall hzero)
    exact zero_ne_one (tendsto_const_nhds_iff.mp hconst)
  haveI : NeZero (dim j) := ⟨hdim_ne⟩
  have hInj : IsInjective (A j) := hCF.toHasInjectiveBlocks.block_injective j
  have hEq : chainGroundSpace (A j) L N = mpvSubmodule (A j) N :=
    chainGroundSpace_eq_mpvSubmodule hInj (by omega) hL (by omega)
  rw [hEq]
  intro ψ hψ
  rw [mpvSubmodule, Submodule.mem_span_singleton] at hψ
  rcases hψ with ⟨c, rfl⟩
  exact Submodule.smul_mem _ c (Submodule.subset_span ⟨j, rfl⟩)

/-- Conditional containment in the BNT span from projection-span and boundary data.

This is the parent-Hamiltonian endgame after a block split has been produced by
`chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan`. The
projection-span hypothesis is the #911 finite CF/BNT input still tracked
separately; the boundary hypothesis is the wrapping/open-chain output that
supplies the commuting boundary matrix. The proof then delegates to
`parentHamiltonianGroundSpace_le_bntSpan_of_block_chain_split`, so the final step
uses the existing blockwise injective uniqueness theorem. -/
theorem parentHamiltonianGroundSpace_le_bntSpan_of_reindexed_projectionSpan
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hProj : ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω))))
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ parentHamiltonianGroundSpace (μ := μ) A L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    parentHamiltonianGroundSpace (μ := μ) A L N ≤ bntSpan A N := by
  refine parentHamiltonianGroundSpace_le_bntSpan_of_block_chain_split
    (μ := μ) A hCF hL hN ?_
  have hBoundary' : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X := by
    intro ψ hψ
    exact hBoundary (by simpa [parentHamiltonianGroundSpace_eq] using hψ)
  simpa [parentHamiltonianGroundSpace_eq] using
    chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan
      (μ := μ) A hCF hL hN hm hProj hBoundary'

private lemma reindexed_projectionSpan_of_wordTupleSpanTop
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {m : ℕ}
    (hSpan : WordTupleSpanTop A m) :
    ∀ k : Fin r,
      Matrix.blockProjection (n := fun k : Fin r => Fin (dim k)) (R := ℂ) k ∈
        Submodule.span ℂ (Set.range fun ω : Fin m → Fin d =>
          Matrix.reindex finSigmaFinEquiv.symm finSigmaFinEquiv.symm
            (evalWord (toTensorFromBlocks μ A) (List.ofFn ω))) :=
  blockProjection_mem_span_reindexed_toTensorFromBlocks_of_wordTupleSpanTop
    (d := d) (dim := dim) μ A
    (fun k => hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero k) hSpan

/-- Conditional reverse block split from a product-word span witness.

This is the Route B composition of the #927 product-word-span reduction with the
#929 projection-span block-split endgame. The finite product-word span hypothesis
`WordTupleSpanTop A m` is the #934 witness; the boundary hypothesis keeps the
wrapping/open-chain step explicit by requiring each assembled chain-ground vector
to come with a length-`m` commuting boundary-matrix representation. -/
theorem chainGroundSpace_toTensorFromBlocks_le_iSup_of_wordTuple_span_eq_top
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hSpan : WordTupleSpanTop A m)
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    chainGroundSpace (toTensorFromBlocks μ A) L N ≤
      ⨆ j : Fin r, chainGroundSpace (A j) L N :=
  chainGroundSpace_toTensorFromBlocks_le_iSup_of_reindexed_projectionSpan
    (μ := μ) A hCF hL hN hm
    (reindexed_projectionSpan_of_wordTupleSpanTop (μ := μ) A hCF hSpan)
    hBoundary

/-- Conditional periodic block-decomposition equality from a product-word span witness.

This records the exact equality obtained once #934 supplies the finite
product-word span and the wrapping/open-chain layer supplies the compatible
commuting boundary matrix.  It is still conditional on those two paper-level
inputs, and is therefore not a restatement of the final unconditional theorem. -/
theorem chainGroundSpace_toTensorFromBlocks_eq_iSup_of_wordTuple_span_eq_top
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hSpan : WordTupleSpanTop A m)
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ chainGroundSpace (toTensorFromBlocks μ A) L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    chainGroundSpace (toTensorFromBlocks μ A) L N =
      ⨆ j : Fin r, chainGroundSpace (A j) L N :=
  chainGroundSpace_toTensorFromBlocks_eq_iSup_of_reindexed_projectionSpan
    (μ := μ) A hCF hL hN hm
    (reindexed_projectionSpan_of_wordTupleSpanTop (μ := μ) A hCF hSpan)
    hBoundary

/-- Conditional BNT-span containment from a product-word span witness.

This is the final Route B composition used in the proof of the reverse inclusion:
#927 converts the product-word span witness into the sector-projection span, #929
turns that projection span plus the boundary representation into a block split,
and the existing blockwise uniqueness endgame places the result in `bntSpan`. -/
theorem parentHamiltonianGroundSpace_le_bntSpan_of_wordTuple_span_eq_top
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N m : ℕ}
    (hL : 1 < L) (hN : N ≥ L + 1) (hm : 0 < m)
    (hSpan : WordTupleSpanTop A m)
    (hBoundary : ∀ ⦃ψ : NSiteSpace d N⦄,
      ψ ∈ parentHamiltonianGroundSpace (μ := μ) A L N →
        ∃ X : Matrix (Fin (∑ k : Fin r, dim k)) (Fin (∑ k : Fin r, dim k)) ℂ,
          ψ = groundSpaceMap (toTensorFromBlocks μ A) N X ∧
          ∀ ω : Fin m → Fin d,
            X * evalWord (toTensorFromBlocks μ A) (List.ofFn ω) =
              evalWord (toTensorFromBlocks μ A) (List.ofFn ω) * X) :
    parentHamiltonianGroundSpace (μ := μ) A L N ≤ bntSpan A N :=
  parentHamiltonianGroundSpace_le_bntSpan_of_reindexed_projectionSpan
    (μ := μ) A hCF hL hN hm
    (reindexed_projectionSpan_of_wordTupleSpanTop (μ := μ) A hCF hSpan)
    hBoundary

/-- Reverse-inclusion step for the BNT ground-space theorem.

This is the remaining block-decomposition step: every periodic-chain ground state
of the assembled BNT tensor should split into blockwise chain ground states.
Once such a split is available, blockwise injective uniqueness
`chainGroundSpace_eq_mpvSubmodule` places those components in the BNT span. -/
theorem parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1) :
    parentHamiltonianGroundSpace (μ := μ) A L N ≤ bntSpan A N := by
  refine parentHamiltonianGroundSpace_le_bntSpan_of_block_chain_split
    (μ := μ) A hCF hL hN ?_
  -- Remaining step: periodic-chain block decomposition for the assembled tensor,
  -- i.e. a theorem identifying every assembled chain-ground-state with a sum of
  -- block chain-ground-state components.
  sorry

/-- **Degenerate ground space = span of BNT states** for block-injective parent
Hamiltonians.

The periodic parent-Hamiltonian ground space of a canonical-form/BNT tensor
equals the span of the individual BNT block MPV states.

TODO(#195): prove by combining `bnt_mem_groundSpace` (⊇ direction) with a
block-splitting theorem for the assembled tensor (⊆ direction).

The single-block endgame is already available on `main`: for each block `A j`,
`IsCanonicalFormBNT` supplies `IsInjective (A j)`, so
`chainGroundSpace_eq_mpvSubmodule` identifies
`chainGroundSpace (A j) L N` with `mpvSubmodule (A j) N` whenever `1 < L ≤ N`.

The remaining missing ingredient is therefore a **periodic-chain block
splitting theorem** of the form
`parentHamiltonianGroundSpace (μ := μ) A L N ≤ ⨆ j, chainGroundSpace (A j) L N`,
saying that a state whose cyclic windows all lie in the block-diagonal local
ground space decomposes into a sum of block chain-ground-state components. The
conditional Route B endgame in this file composes two still-explicit inputs: a
finite product-word span witness for #934 (which gives the virtual-sector
projection span) and a wrapping/open-chain boundary representation commuting
with the same length words. It does not replace either paper-level input, so it
does not close the unconditional block-splitting theorem by itself.

Given that block-splitting theorem, the ⊆ direction becomes:
```
parentHamiltonianGroundSpace (μ := μ) A L N
  ≤ ⨆ j, chainGroundSpace (A j) L N        -- block splitting
  = ⨆ j, mpvSubmodule (A j) N              -- blockwise injective uniqueness
  ≤ Submodule.span ℂ (Set.range fun j => (mpv (A j) : NSiteSpace d N))
    = bntSpan A N
```
where the final inclusion is immediate because `mpvSubmodule (A j) N` is the
span of the single vector `mpv (A j)`. -/
theorem parentHamiltonian_gs_eq_bnt_span
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1) :
    parentHamiltonianGroundSpace (μ := μ) A L N = bntSpan A N := by
  apply le_antisymm
  · exact
      parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition
        (μ := μ) A hCF hL hN
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact bnt_mem_groundSpace (μ := μ) A hCF hL hN j

end MPSTensor
