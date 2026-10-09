/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.SwapSymmetryTransport

/-!
# Swap symmetry transport after common blocking

The one-sided swap transformation commutes with blocking. Consequently it
identifies the three symmetry-preserving path comparisons after an arbitrary
common positive blocking length.

**Scope restriction:** the ambient bond dimension is fixed, and no identity
ancillas are introduced. These statements are distinct from unrestricted
stabilized equivalence. See `docs/paper-gaps/mpu_equivalence_fixed_bond.tex`
and `docs/paper-gaps/mpu_symmetry_ancilla_transport.tex`.

**Local fix (one-sided swap):** equation `threeMPU2` uses one-sided
multiplication \(\widetilde U_N=S_NU_N\), while the conjugation paragraph in
the printed proof of `lemma:sym-trafo-swap` displays two-sided multiplication.
The blocked comparisons here use the one-sided transformation of the defining
equation. See `docs/paper-gaps/mpu_swap_symmetry_one_sided.tex`.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085.
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

private theorem reindex_sitewisePhysicalMatrix_blockKron
    (Q : Matrix (Fin d) (Fin d) ℂ) (N k : ℕ) :
    Matrix.reindex (MPSTensor.blockedConfigEquiv d N k).symm
        (MPSTensor.blockedConfigEquiv d N k).symm (sitewisePhysicalMatrix Q (N * k)) =
      sitewisePhysicalMatrix (MPSTensor.blockKron k Q) N := by
  classical
  symm
  exact Matrix.ext fun σ τ => by
    simpa [sitewisePhysicalMatrix, MPSTensor.blockKron, Matrix.reindex_apply,
      MPSTensor.blockedConfigEquiv, Equiv.arrowCongr, Equiv.curry, Function.comp,
      Fintype.prod_prod_type] using
      (finProdFinEquiv.prod_comp (fun v : Fin (N * k) =>
        Q (MPSTensor.blockedConfigEquiv d N k σ v)
          (MPSTensor.blockedConfigEquiv d N k τ v)))

private theorem reindex_mul {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (X Y : Matrix α α ℂ) :
    Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
  (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e X Y).symm

private theorem block_dagger_action (k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d k))
      (Fin N → Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    ((daggerSymmetry d).block k).action X = Xᴴ := by
  simp only [FiniteChainOperatorSymmetry.block, daggerSymmetry,
    Matrix.conjTranspose_reindex]
  ext σ τ
  simp [Matrix.reindex_apply]

private theorem block_transpose_action (k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d k))
      (Fin N → Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    ((transposeSymmetry d).block k).action X = Xᵀ := by
  ext σ τ
  simp [FiniteChainOperatorSymmetry.block, transposeSymmetry,
    Matrix.reindex_apply, Matrix.transpose_apply]

private theorem block_conjugation_action (k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim d k))
      (Fin N → Fin (MPSTensor.blockPhysDim d k)) ℂ) :
    ((conjugationSymmetry d).block k).action X = X.map (starRingEnd ℂ) := by
  ext σ τ
  simp [FiniteChainOperatorSymmetry.block, conjugationSymmetry,
    Matrix.reindex_apply, Matrix.map_apply]

private theorem block_swap_dagger_action (d k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim (d * d) k))
      (Fin N → Fin (MPSTensor.blockPhysDim (d * d) k)) ℂ) :
    ((shiftSwapDaggerSymmetry d).block k).action X =
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N * Xᴴ *
        sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N := by
  simp only [FiniteChainOperatorSymmetry.block, shiftSwapDaggerSymmetry,
    reindex_mul, reindex_sitewisePhysicalMatrix_blockKron, Matrix.conjTranspose_reindex]
  congr 2
  ext σ τ
  simp [Matrix.reindex_apply]

private theorem block_swap_transpose_action (d k N : ℕ)
    (X : Matrix (Fin N → Fin (MPSTensor.blockPhysDim (d * d) k))
      (Fin N → Fin (MPSTensor.blockPhysDim (d * d) k)) ℂ) :
    ((shiftSwapTransposeSymmetry d).block k).action X =
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N * Xᵀ *
        sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N := by
  simp only [FiniteChainOperatorSymmetry.block, shiftSwapTransposeSymmetry,
    reindex_mul, reindex_sitewisePhysicalMatrix_blockKron]
  congr 2
  ext σ τ
  simp [Matrix.reindex_apply, Matrix.transpose_apply]

private theorem blocked_chainSwap_mul_self (d k N : ℕ) :
    sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N *
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N = 1 := by
  rw [sitewisePhysicalMatrix_mul, ← MPSTensor.blockKron_mul, shiftPhysicalSwap_mul_self,
    MPSTensor.blockKron_one, sitewisePhysicalMatrix_one]

private theorem blocked_chainSwap_conjTranspose (d k N : ℕ) :
    (sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N)ᴴ =
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N := by
  simp only [sitewisePhysicalMatrix_conjTranspose, MPSTensor.blockKron_conjTranspose,
    shiftPhysicalSwap, Matrix.conjTranspose_permMatrix, Equiv.Perm.inv_def,
    bondPairSwapEquiv_symm]

private theorem blocked_chainSwap_transpose (d k N : ℕ) :
    (sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N)ᵀ =
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N := by
  have hQ : (shiftPhysicalSwap d)ᵀ = shiftPhysicalSwap d := by
    simp only [shiftPhysicalSwap, Matrix.transpose_permMatrix,
      Equiv.Perm.inv_def, bondPairSwapEquiv_symm]
  ext σ τ
  change (∏ n, ∏ i, shiftPhysicalSwap d
    (MPSTensor.decodeBlock (d * d) k (τ n) i)
    (MPSTensor.decodeBlock (d * d) k (σ n) i)) = _
  refine Finset.prod_congr rfl fun n _ => ?_
  refine Finset.prod_congr rfl fun i _ => ?_
  exact congrFun (congrFun hQ _) _

private theorem blocked_chainSwap_map_star (d k N : ℕ) :
    (sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N).map
        (starRingEnd ℂ) =
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N := by
  ext σ τ
  simp [sitewisePhysicalMatrix, MPSTensor.blockKron, shiftPhysicalSwap,
    Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]

private theorem block_swap_dagger_invariance_iff (d k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d) k) E) :
    IsInvariantUnderSymmetry ((shiftSwapDaggerSymmetry d).block k) W ↔
      IsInvariantUnderSymmetry ((daggerSymmetry (d * d)).block k)
        (W.ketLeftMul (MPSTensor.blockKron k (shiftPhysicalSwap d))) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    ((shiftSwapDaggerSymmetry d).block k) ((daggerSymmetry (d * d)).block k) _ _ rfl
  intro N
  rw [block_swap_dagger_action, block_dagger_action, mpo_ketLeftMul]
  apply swapCombined_fixed_iff_leftMul _ _ (blocked_chainSwap_mul_self d k N)
  rw [Matrix.conjTranspose_mul, blocked_chainSwap_conjTranspose]

private theorem block_swap_transpose_invariance_iff (d k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d) k) E) :
    IsInvariantUnderSymmetry ((shiftSwapTransposeSymmetry d).block k) W ↔
      IsInvariantUnderSymmetry ((transposeSymmetry (d * d)).block k)
        (W.ketLeftMul (MPSTensor.blockKron k (shiftPhysicalSwap d))) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise
    ((shiftSwapTransposeSymmetry d).block k) ((transposeSymmetry (d * d)).block k) _ _ rfl
  intro N
  rw [block_swap_transpose_action, block_transpose_action, mpo_ketLeftMul]
  apply swapCombined_fixed_iff_leftMul _ _ (blocked_chainSwap_mul_self d k N)
  rw [Matrix.transpose_mul, blocked_chainSwap_transpose]

private theorem block_conjugation_invariance_iff (d k : ℕ) {E : ℕ}
    (W : MPOTensor (MPSTensor.blockPhysDim (d * d) k) E) :
    IsInvariantUnderSymmetry ((conjugationSymmetry (d * d)).block k) W ↔
      IsInvariantUnderSymmetry ((conjugationSymmetry (d * d)).block k)
        (W.ketLeftMul (MPSTensor.blockKron k (shiftPhysicalSwap d))) := by
  apply isInvariantUnderSymmetry_iff_of_pointwise _ _ _ _ rfl
  intro N
  rw [block_conjugation_action, block_conjugation_action, mpo_ketLeftMul,
    Matrix.map_mul, blocked_chainSwap_map_star]
  constructor
  · exact congrArg (fun X ↦
      sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N * X)
  · intro h
    simpa only [← Matrix.mul_assoc, blocked_chainSwap_mul_self, Matrix.one_mul] using
      congrArg (fun X ↦
        sitewisePhysicalMatrix (MPSTensor.blockKron k (shiftPhysicalSwap d)) N * X) h

/-- After some common positive blocking length, swap multiplication identifies
strict equivalence under swap-combined adjunction with that under adjunction.
The same blocking length works in both directions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem exists_strictlyEquivalentUnderSymmetry_blockTensor_shiftSwapDagger_iff
    (U V : MPOTensor (d * d) D) :
    (∃ k > 0, StrictlyEquivalentUnderSymmetry ((shiftSwapDaggerSymmetry d).block k)
      (blockTensor U k) (blockTensor V k) rfl) ↔
      (∃ k > 0, StrictlyEquivalentUnderSymmetry ((daggerSymmetry (d * d)).block k)
        (blockTensor (U.ketLeftMul (shiftPhysicalSwap d)) k)
        (blockTensor (V.ketLeftMul (shiftPhysicalSwap d)) k) rfl) :=
  exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    (fun k _ ↦ block_swap_dagger_invariance_iff d k) U V

/-- After some common positive blocking length, swap multiplication identifies
strict equivalence under swap-combined transposition with that under transposition.
The same blocking length works in both directions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem exists_strictlyEquivalentUnderSymmetry_blockTensor_shiftSwapTranspose_iff
    (U V : MPOTensor (d * d) D) :
    (∃ k > 0, StrictlyEquivalentUnderSymmetry ((shiftSwapTransposeSymmetry d).block k)
      (blockTensor U k) (blockTensor V k) rfl) ↔
      (∃ k > 0, StrictlyEquivalentUnderSymmetry ((transposeSymmetry (d * d)).block k)
        (blockTensor (U.ketLeftMul (shiftPhysicalSwap d)) k)
        (blockTensor (V.ketLeftMul (shiftPhysicalSwap d)) k) rfl) :=
  exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    (fun k _ ↦ block_swap_transpose_invariance_iff d k) U V

/-- After some common positive blocking length, swap multiplication preserves
strict equivalence under entrywise conjugation. The same blocking length works
in both directions.
Source: arXiv:1703.09188, Lemma `lemma:sym-trafo-swap`, lines 2065--2085. -/
theorem exists_strictlyEquivalentUnderSymmetry_blockTensor_conjugation_swap_iff
    (U V : MPOTensor (d * d) D) :
    (∃ k > 0, StrictlyEquivalentUnderSymmetry ((conjugationSymmetry (d * d)).block k)
      (blockTensor U k) (blockTensor V k) rfl) ↔
      (∃ k > 0, StrictlyEquivalentUnderSymmetry ((conjugationSymmetry (d * d)).block k)
        (blockTensor (U.ketLeftMul (shiftPhysicalSwap d)) k)
        (blockTensor (V.ketLeftMul (shiftPhysicalSwap d)) k) rfl) :=
  exists_strictlyEquivalentUnderSymmetry_blockTensor_iff_ketLeftMul _ _ _
    (shiftPhysicalSwap_mem_unitaryGroup d) (shiftPhysicalSwap_mul_self d)
    (fun k _ ↦ block_conjugation_invariance_iff d k) U V

end MPOTensor
