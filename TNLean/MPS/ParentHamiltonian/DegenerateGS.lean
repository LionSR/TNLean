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
tensor decomposes blockwise — is the structural projector argument from
[CPGSV21] arXiv:2011.12127 §IV.C: the abelian-symmetry projectors
`P_α = ∑ χ̄_k(g) U_g` onto the virtual-space irrep sectors commute with the
assembled tensor and split a chain ground state into block components. That
inclusion is not yet formalized; together with the blockwise normal-form
uniqueness `chainGroundSpace_eq_mpvSubmodule_normal` (issue #588) it would
discharge `parentHamiltonianGroundSpace_le_bntSpan_of_block_decomposition`. -/
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
ground space decomposes into a sum of block chain-ground-state components.
This is the "projectors commute through the tensor" step from the proof sketch.
No such periodic-chain block-splitting infrastructure is currently available in
`MPS/ParentHamiltonian`, and the repository does not yet expose the analogous
finite-length block-separation theorem used elsewhere in biCF-style arguments.

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
