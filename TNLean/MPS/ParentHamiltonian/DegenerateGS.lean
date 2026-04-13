/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.ParentHamiltonian.UniqueGroundState
import TNLean.MPS.BNT.Construction
import TNLean.MPS.CanonicalForm.Assembly
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

open scoped Matrix

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

/-- `⊇` direction: each BNT block MPV lies in the parent-Hamiltonian ground
space of the assembled tensor.

The proof lifts `mpv_mem_chainGroundSpace` from the block level to the
assembled tensor using `groundSpace_block_le_assembled`. -/
theorem bnt_mem_groundSpace
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1)
    (j : Fin r) :
    (mpv (A j) : NSiteSpace d N) ∈ parentHamiltonianGroundSpace (μ := μ) A L N := by
  simp only [parentHamiltonianGroundSpace_eq]
  have hLN : L ≤ N := by omega
  have hN' : 0 < N := by omega
  have hμj : μ j ≠ 0 := hCF.toHasStrictOrderedNonzeroWeights.mu_ne_zero j
  -- mpv (A j) ∈ chainGroundSpace (A j) L N by trace cyclicity
  have hmem := mpv_mem_chainGroundSpace (A j) L N hN' hLN
  -- Lift: chainGroundSpace (A j) ≤ chainGroundSpace (toTensorFromBlocks μ A)
  rw [chainGroundSpace, dif_pos ⟨hN', hLN⟩] at hmem ⊢
  simp only [Submodule.mem_iInf, Submodule.mem_comap] at hmem ⊢
  intro i τ
  exact groundSpace_block_le_assembled μ A j hμj L (hmem i τ)

/-- **Degenerate ground space = span of BNT states** for block-injective parent
Hamiltonians.

The periodic parent-Hamiltonian ground space of a canonical-form/BNT tensor
equals the span of the individual BNT block MPV states.

TODO(#195): prove by combining `bnt_mem_groundSpace` (⊇ direction) with
blockwise decomposition / uniqueness for the assembled tensor (⊆ direction).

The ⊆ direction requires *two* upstream dependencies, neither currently
available:

1. **Block-diagonal periodic-chain ground-space decomposition.** A structural
   theorem of the form
   `chainGroundSpace (toTensorFromBlocks μ A) L N = ⨆ j, (embed_j) (chainGroundSpace (A j) L N)`,
   saying that a state whose cyclic windows all lie in the block-diagonal
   local ground space decomposes (via projectors onto the virtual-space irrep
   sectors) into a sum of block components. This is the "projectors commute
   through the tensor" idea from the proof sketch. No periodic-chain block
   decomposition infrastructure is available in `MPS/Chain/` or
   `MPS/Structure/` at present.

2. **Blockwise MPV uniqueness** via `chainGroundSpace_eq_mpvSubmodule_normal`
   in `UniqueGroundState.lean`, which is itself still a `sorry` pending the
   normal-form range reduction from `2 L₀` to `L₀ + 1`. Each block of a
   CF-BNT decomposition is normal and `L₀`-block-injective, so this theorem
   (once proved) identifies each block's chain ground space with its MPV
   submodule, i.e. exactly one component of `bntSpan`.

Given dependency (1) and (2), the ⊆ direction becomes:
```
chainGroundSpace (toTensorFromBlocks μ A) L N
  = ⨆ j, (embed_j) (chainGroundSpace (A j) L N)         -- by (1)
  = ⨆ j, (embed_j) (mpvSubmodule (A j) N)               -- by (2)
  = Submodule.span ℂ (Set.range fun j => mpv (A j))     -- = bntSpan A N
```
where the final step uses that the embedding of a block's MPV into the
assembled tensor is (up to the μ_j^N scalar) the corresponding BNT MPV. -/
theorem parentHamiltonian_gs_eq_bnt_span
    (A : (j : Fin r) → MPSTensor d (dim j))
    (hCF : IsCanonicalFormBNT μ A) {L N : ℕ} (hL : 1 < L) (hN : N ≥ L + 1) :
    parentHamiltonianGroundSpace (μ := μ) A L N = bntSpan A N := by
  apply le_antisymm
  · -- TODO(#195): reverse inclusion.
    -- Requires:
    --  (1) a periodic-chain block-decomposition theorem identifying
    --      `chainGroundSpace (toTensorFromBlocks μ A) L N` with the supremum
    --      of embedded blockwise chain ground spaces (not yet formalized);
    --  (2) `chainGroundSpace_eq_mpvSubmodule_normal` (currently `sorry`) to
    --      reduce each block's chain ground space to its MPV submodule.
    -- See the docstring above for the proof outline.
    sorry
  · rw [bntSpan, Submodule.span_le]
    intro ψ hψ
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hψ
    exact bnt_mem_groundSpace A hCF hL hN j

end MPSTensor
