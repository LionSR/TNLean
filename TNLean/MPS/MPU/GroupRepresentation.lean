/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Matrix product unitary group representations

This file formalizes the tensor family used in the discussion of matrix product
unitary group representations in arXiv:2502.20257.  Bond dimensions may depend
on the group element.  All operator identities and unitarity statements use
positive chain lengths, matching the paper's convention that the represented
operators act on nonempty chains.

## Main definitions

* `MPOTensor.IsMPUPos`: unitarity on every positive chain length.
* `MPOTensor.GroupFamily`: a group-indexed family of positive-bond-dimension MPO tensors.
* `MPOTensor.GroupFamily.IsRepresentation`: an exact positive-length operator
  representation whose tensors are simple and injective.
* `MPOTensor.GroupFamily.block`: simultaneous positive physical blocking.

## Main results

* `MPOTensor.IsMPUPos.isMPU`: the positive-length convention implies the
  established `IsMPU` predicate.
* `MPOTensor.GroupFamily.IsRepresentation.sameMPV₂Pos_mulTensor`: the tensor
  product representing multiplication generates exactly the same positive-length
  MPV family as the tensor indexed by the product.
* `MPOTensor.GroupFamily.IsRepresentation.block`: positive blocking preserves
  the representation, simplicity, and injectivity.
* `MPOTensor.GroupFamily.IsRawRepresentation.block_common`: for a finite group,
  one explicit positive block makes every tensor in an injective raw
  representation simple.

Source: arXiv:2502.20257, Section "MPU group representations", beginning at
lines 1403--1407.
-/

open scoped Matrix

namespace MPOTensor

universe u

variable {d D : ℕ}

/-- The paper-facing MPU convention: the periodic MPO is unitary on every
nonempty chain.

Source: arXiv:2502.20257, lines 198--209. -/
def IsMPUPos (U : MPOTensor d D) : Prop :=
  ∀ N : ℕ, 0 < N → mpo U N ∈ Matrix.unitaryGroup (Fin N → Fin d) ℂ

namespace IsMPUPos

/-- Positive-length MPU unitarity implies the established all-`N > 1`
predicate. -/
theorem isMPU {U : MPOTensor d D} (hU : IsMPUPos U) : IsMPU U :=
  fun N hN ↦ hU N (by omega)

/-- Positive physical blocking preserves unitarity on every nonempty chain. -/
theorem blockTensor {U : MPOTensor d D} (hU : IsMPUPos U)
    (L : ℕ) (hL : 0 < L) : IsMPUPos (MPOTensor.blockTensor U L) := by
  intro N hN
  rw [mpo_blockTensor_eq_reindex U L N]
  apply Matrix.reindex_mem_unitaryGroup
    (MPSTensor.blockedConfigEquiv d N L).symm (mpo U (N * L))
  exact hU (N * L) (Nat.mul_pos hN hL)

end IsMPUPos

/-- A group-indexed MPO tensor family with a positive, element-dependent bond
dimension. -/
structure GroupFamily (G : Type u) (d : ℕ) where
  bondDim : G → ℕ
  bondDim_pos : ∀ g, 0 < bondDim g
  tensor : (g : G) → MPOTensor d (bondDim g)

namespace GroupFamily

variable {G : Type u} {d : ℕ}

/-- Every bond dimension in a group family is nonzero. -/
instance (F : GroupFamily G d) (g : G) : NeZero (F.bondDim g) :=
  ⟨Nat.ne_of_gt (F.bondDim_pos g)⟩

/-- An exact positive-length MPU representation by simple injective tensors.
The operator identities are literal matrix equalities, with no scalar freedom.

Source: arXiv:2502.20257, lines 1403--1407. -/
structure IsRepresentation [Group G] (F : GroupFamily G d) : Prop where
  isMPUPos : ∀ g, IsMPUPos (F.tensor g)
  isSimple : ∀ g, IsMPUSimple (F.tensor g)
  isInjective : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor
  operator_one : ∀ N, 0 < N → mpo (F.tensor 1) N = 1
  operator_mul : ∀ g h N, 0 < N →
    mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N

/-- The multiplication law as exact positive-length equality of doubled-index
matrix product vectors. The chosen injective tensor for `g * h` is placed first,
matching the orientation used by the later rectangular reduction interface.

Source: arXiv:2502.20257, lines 1403--1407. -/
theorem IsRepresentation.sameMPV₂Pos_mulTensor [Group G]
    (F : GroupFamily G d) (hF : F.IsRepresentation) (g h : G) :
    MPSTensor.SameMPV₂Pos
      (F.tensor (g * h)).toMPSTensor
      (MPOTensor.mulTensor (F.tensor g) (F.tensor h)).toMPSTensor := by
  apply MPSTensor.SameMPV₂Pos.symm
  intro N hN ρ
  let σ : Fin N → Fin d := fun n ↦ (ρ n).divNat
  let τ : Fin N → Fin d := fun n ↦ (ρ n).modNat
  have hρ : (fun n ↦ finProdFinEquiv (σ n, τ n)) = ρ := by
    funext n
    exact finProdFinEquiv.apply_symm_apply (ρ n)
  rw [← hρ, MPSTensor.mpv_toMPSTensor_pairConfig,
    MPSTensor.mpv_toMPSTensor_pairConfig, mpo_mulTensor,
    hF.operator_mul g h N hN]

/-- Simultaneously block every tensor in a group family by `L` physical sites. -/
noncomputable def block (F : GroupFamily G d) (L : ℕ) :
    GroupFamily G (MPSTensor.blockPhysDim d L) where
  bondDim := F.bondDim
  bondDim_pos := F.bondDim_pos
  tensor g := MPOTensor.blockTensor (F.tensor g) L

private theorem injective_blockTensor (F : GroupFamily G d) (g : G)
    {L : ℕ} (hL : 0 < L) (h : Kraus.IsInjective (F.tensor g).toMPSTensor) :
    Kraus.IsInjective ((F.block L).tensor g).toMPSTensor := by
  rw [block, isInjective_toMPSTensor_blockTensor_iff]
  have hOne : Kraus.IsNBlkInjective (F.tensor g).toMPSTensor 1 :=
    Kraus.isNBlkInjective_one_of_isInjective h
  have hMul : Kraus.IsNBlkInjective (F.tensor g).toMPSTensor (L * 1) :=
    MPSTensor.isNBlkInjective_mul_of_isNBlkInjective
      (F.tensor g).toMPSTensor hL hOne
  exact (MPSTensor.isNBlkInjective_iff_blockTensor_isInjective
    (F.tensor g).toMPSTensor L).1 (by simpa using hMul)

private theorem operator_one_block [Group G] (F : GroupFamily G d)
    (hOne : ∀ N, 0 < N → mpo (F.tensor 1) N = 1)
    {L : ℕ} (hL : 0 < L) (N : ℕ) (hN : 0 < N) :
    mpo ((F.block L).tensor 1) N = 1 := by
  simp only [block]
  rw [mpo_blockTensor_eq_reindex,
    hOne (N * L) (Nat.mul_pos hN hL)]
  change (Matrix.reindexLinearEquiv ℂ ℂ
    (MPSTensor.blockedConfigEquiv d N L).symm
    (MPSTensor.blockedConfigEquiv d N L).symm) 1 = 1
  exact Matrix.reindexLinearEquiv_one ℂ ℂ _

private theorem operator_mul_block [Group G] (F : GroupFamily G d)
    (hMul : ∀ g h N, 0 < N →
      mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N)
    {L : ℕ} (hL : 0 < L) (g h : G) (N : ℕ) (hN : 0 < N) :
    mpo ((F.block L).tensor g) N * mpo ((F.block L).tensor h) N =
      mpo ((F.block L).tensor (g * h)) N := by
  simp only [block]
  rw [mpo_blockTensor_eq_reindex, mpo_blockTensor_eq_reindex,
    mpo_blockTensor_eq_reindex]
  change
    (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv d N L).symm)
          (mpo (F.tensor g) (N * L)) *
        (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv d N L).symm)
          (mpo (F.tensor h) (N * L)) =
      (Matrix.reindexAlgEquiv ℂ ℂ (MPSTensor.blockedConfigEquiv d N L).symm)
        (mpo (F.tensor (g * h)) (N * L))
  rw [← map_mul, hMul g h (N * L) (Nat.mul_pos hN hL)]

/-- Positive physical blocking preserves exact representation laws, unitarity,
simplicity, and injectivity. -/
theorem IsRepresentation.block [Group G] (F : GroupFamily G d)
    (hF : F.IsRepresentation) (L : ℕ) (hL : 0 < L) :
    (F.block L).IsRepresentation where
  isMPUPos g := (hF.isMPUPos g).blockTensor L hL
  isSimple g := (hF.isSimple g).blockTensor L hL
  isInjective g := injective_blockTensor F g hL (hF.isInjective g)
  operator_one N hN := operator_one_block F hF.operator_one hL N hN
  operator_mul g h N hN := operator_mul_block F hF.operator_mul hL g h N hN

/-- An exact positive-length MPU representation before simplicity is imposed. -/
structure IsRawRepresentation [Group G] (F : GroupFamily G d) : Prop where
  isMPUPos : ∀ g, IsMPUPos (F.tensor g)
  isInjective : ∀ g, Kraus.IsInjective (F.tensor g).toMPSTensor
  operator_one : ∀ N, 0 < N → mpo (F.tensor 1) N = 1
  operator_mul : ∀ g h N, 0 < N →
    mpo (F.tensor g) N * mpo (F.tensor h) N = mpo (F.tensor (g * h)) N

/-- An explicit common blocking length for a finite group-indexed family. -/
noncomputable def commonSimpleLength [Fintype G] (F : GroupFamily G d) : ℕ :=
  ∑ g : G, F.bondDim g ^ 4

private theorem bond_pow_le_commonSimpleLength [Fintype G]
    (F : GroupFamily G d) (g : G) :
    F.bondDim g ^ 4 ≤ F.commonSimpleLength := by
  classical
  simpa only [commonSimpleLength] using
    (Finset.single_le_sum (s := Finset.univ)
      (f := fun x : G ↦ F.bondDim x ^ 4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ g))

/-- The explicit common simplicity length is positive for a finite group. -/
theorem commonSimpleLength_pos [Group G] [Fintype G] (F : GroupFamily G d) :
    0 < F.commonSimpleLength := by
  classical
  apply Finset.sum_pos'
  · exact fun _ _ ↦ Nat.zero_le _
  · exact ⟨1, Finset.mem_univ _, pow_pos (F.bondDim_pos 1) 4⟩

/-- For a finite group, blocking an injective raw representation at the explicit
positive length `∑ g, (bondDim g)^4` makes every representing tensor simple. -/
theorem IsRawRepresentation.block_common [Group G] [Fintype G] [NeZero d]
    (F : GroupFamily G d) (hF : F.IsRawRepresentation) :
    (F.block F.commonSimpleLength).IsRepresentation where
  isMPUPos g := (hF.isMPUPos g).blockTensor _ F.commonSimpleLength_pos
  isSimple g :=
    (hF.isMPUPos g).isMPU.blockTensor_isMPUSimple_of_le
      (pow_pos (F.bondDim_pos g) 4) (F.bond_pow_le_commonSimpleLength g)
      ((hF.isMPUPos g).isMPU.blockTensor_pow_four_isMPUSimple)
  isInjective g :=
    injective_blockTensor F g F.commonSimpleLength_pos (hF.isInjective g)
  operator_one N hN :=
    operator_one_block F hF.operator_one F.commonSimpleLength_pos N hN
  operator_mul g h N hN :=
    operator_mul_block F hF.operator_mul F.commonSimpleLength_pos g h N hN

/-- After the explicit common simplicity block, every further positive physical
blocking remains an exact simple injective MPU representation. -/
theorem IsRawRepresentation.block_common_then_block
    [Group G] [Fintype G] [NeZero d]
    (F : GroupFamily G d) (hF : F.IsRawRepresentation)
    (L : ℕ) (hL : 0 < L) :
    ((F.block F.commonSimpleLength).block L).IsRepresentation :=
  (hF.block_common F).block (F.block F.commonSimpleLength) L hL

end GroupFamily

end MPOTensor
