/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.MPS.Core.CyclicTrace
import TNLean.MPS.Core.PhysicalReindexTransport
import TNLean.MPS.MPDO.OperatorProduct
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Physical blocking of MPO tensors

This file defines arbitrary physical blocking of an MPO tensor, together with
the two-site specialization used in the renormalization maps.  Ket words and
bra words are grouped separately, as in the operator notation of
arXiv:1606.00608.

## Main definitions

* `MPOTensor.blockTensor`: the tensor obtained by blocking an arbitrary number
  of adjacent sites.
* `MPOTensor.blockTwo`: the tensor obtained by blocking two adjacent sites.
* `MPOTensor.physClose4`: the right-associated four-site physical closure.
* `MPOTensor.physClose1_blockTwo_eq_physClose2`: one blocked site is two original sites.
* `MPOTensor.physClose2_blockTwo_eq_physClose4`: two blocked sites are four original sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, lines 851--856
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Arbitrary physical blocking -/

/-- The MPO tensor obtained by blocking `L` adjacent physical sites.  A ket
index and a bra index each encode a word of length `L`; the corresponding
letter is the ordered product of the original MPO matrices along those two
words.

This is the MPO counterpart of the blocking used to make the basis of normal
tensors block injective in arXiv:1606.00608, lines 317--345.  The ket and bra
indices remain separate.  This local tensor should not be confused with the
closed-chain operator `O_L(M)` defined at lines 962--967. -/
noncomputable def blockTensor (M : MPOTensor d D) (L : ℕ) :
    MPOTensor (MPSTensor.blockPhysDim d L) D :=
  fun i j => evalWord M (MPSTensor.wordOfBlock d L i) (MPSTensor.wordOfBlock d L j)

@[simp]
lemma blockTensor_apply (M : MPOTensor d D) (L : ℕ)
    (i j : Fin (MPSTensor.blockPhysDim d L)) :
    blockTensor M L i j =
      evalWord M (MPSTensor.wordOfBlock d L i) (MPSTensor.wordOfBlock d L j) :=
  rfl

/-- Canonical identification between the doubled physical index of an
`L`-site MPO block and the `L`-site block of the doubled MPS index.

The map decodes the blocked ket and bra words, pairs their letters site by
site, and then encodes the resulting word in `Fin (d * d)`.  This is the
index identification implicit in the blocking argument of
arXiv:1606.00608, lines 317--345. -/
noncomputable def blockedDoubledIndexEquiv (d L : ℕ) :
    Fin (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L) ≃
      Fin (MPSTensor.blockPhysDim (d * d) L) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr (MPSTensor.decodeBlockEquiv d L)
      (MPSTensor.decodeBlockEquiv d L)) |>.trans
    (Equiv.arrowProdEquivProdArrow (Fin L) (fun _ ↦ Fin d) (fun _ ↦ Fin d)).symm |>.trans
    (Equiv.arrowCongr (Equiv.refl (Fin L)) finProdFinEquiv) |>.trans
    (MPSTensor.decodeBlockEquiv (d * d) L).symm

@[simp]
lemma decodeBlock_blockedDoubledIndexEquiv (d L : ℕ)
    (ij : Fin (MPSTensor.blockPhysDim d L * MPSTensor.blockPhysDim d L))
    (k : Fin L) :
    MPSTensor.decodeBlock (d * d) L (blockedDoubledIndexEquiv d L ij) k =
      finProdFinEquiv
        (MPSTensor.decodeBlock d L ij.divNat k,
          MPSTensor.decodeBlock d L ij.modNat k) := by
  simp [blockedDoubledIndexEquiv, Equiv.arrowCongr,
    MPSTensor.decodeBlockEquiv_apply]

/-- Physical blocking commutes with passing from an MPO tensor to its
doubled-index MPS tensor, up to the canonical pairing of the blocked ket and
bra words. -/
theorem toMPSTensor_blockTensor (M : MPOTensor d D) {L : ℕ} :
    (blockTensor M L).toMPSTensor =
      MPSTensor.reindexPhysical (blockedDoubledIndexEquiv d L)
        (MPSTensor.blockTensor M.toMPSTensor L) := by
  funext ij
  simp only [toMPSTensor, blockTensor_apply, MPSTensor.reindexPhysical,
    MPSTensor.blockTensor]
  simp only [MPSTensor.wordOfBlock, MPOTensor.evalWord_ofFn,
    MPSTensor.evalWord_ofFn_eq_prod]
  simp only [toMPSTensor, decodeBlock_blockedDoubledIndexEquiv,
    MPSTensor.finProdFinEquiv_divNat, MPSTensor.finProdFinEquiv_modNat]

/-- Injectivity of an MPO block is the injectivity of the corresponding block
of its doubled-index MPS tensor. -/
theorem isInjective_toMPSTensor_blockTensor_iff
    (M : MPOTensor d D) {L : ℕ} :
    MPSTensor.IsInjective (blockTensor M L).toMPSTensor ↔
      MPSTensor.IsInjective (MPSTensor.blockTensor M.toMPSTensor L) := by
  rw [toMPSTensor_blockTensor M,
    MPSTensor.isInjective_reindexPhysical_equiv]

/-- Physical blocking commutes with the product of MPO tensors.  The
intermediate physical word is merely reindexed from a function `Fin L → Fin d`
to one blocked physical index. -/
theorem blockTensor_mulTensor {D₁ D₂ : ℕ}
    (M : MPOTensor d D₁) (N : MPOTensor d D₂) {L : ℕ} :
    blockTensor (mulTensor M N) L =
      mulTensor (blockTensor M L) (blockTensor N L) := by
  funext I K
  rw [blockTensor_apply, mulTensor_apply]
  change evalWord (mulTensor M N)
      (List.ofFn (MPSTensor.decodeBlock d L I))
      (List.ofFn (MPSTensor.decodeBlock d L K)) = _
  rw [evalWord_mulTensor]
  rw [← (MPSTensor.decodeBlockEquiv d L).sum_comp]
  simp only [MPSTensor.decodeBlockEquiv_apply, blockTensor_apply,
    MPSTensor.wordOfBlock]

/-! ### Two-site blocking -/

/-- The MPO tensor obtained by blocking two adjacent physical sites. The two
ket indices, and separately the two bra indices, are encoded through the
standard equivalence `Fin d × Fin d ≃ Fin (d * d)`. This is the blocking used
in arXiv:1606.00608, Theorem 4.9, lines 851--856. -/
noncomputable def blockTwo (M : MPOTensor d D) : MPOTensor (d * d) D :=
  fun i j =>
    M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

@[simp] lemma blockTwo_apply (M : MPOTensor d D) (i j : Fin (d * d)) :
    blockTwo M i j =
      M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
        M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2 :=
  rfl

/-! ### The four-site physical closure -/

/-- The four-site physical closure, with the physical indices associated as
`Fin d × (Fin d × (Fin d × Fin d))`. Its coefficient is the virtual trace of
four consecutive tensor matrices followed by the inserted virtual operator.
This is the four-site instance of the open physical contraction used in
arXiv:1606.00608, Definition 4.1, lines 638--657. -/
noncomputable def physClose4 (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin d × (Fin d × (Fin d × Fin d)))
        (Fin d × (Fin d × (Fin d × Fin d))) ℂ where
  toFun X := Matrix.of fun i j =>
    Matrix.trace
      (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2.1 j.2.2.1 *
        M i.2.2.2 j.2.2.2 * X)
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]

@[simp] lemma physClose4_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin d × (Fin d × (Fin d × Fin d))) :
    physClose4 M X i j =
      Matrix.trace
        (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2.1 j.2.2.1 *
          M i.2.2.2 j.2.2.2 * X) :=
  rfl

/-- Under the canonical right-associated identification of four-site
configurations with quadruples of physical indices, the general length-four
closure is `physClose4`. -/
theorem physCloseN_four_eq_physClose4 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (_root_.finFourArrowEquiv (Fin d))
        (_root_.finFourArrowEquiv (Fin d))).toLinearMap ∘ₗ physCloseN M 4 =
      physClose4 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, Matrix.mul_assoc]

/-! ### Blocking identities -/

/-- Decode one blocked physical index into its two constituent indices. -/
def blockedIndexEquiv (d : ℕ) : Fin (d * d) ≃ Fin d × Fin d :=
  finProdFinEquiv.symm

/-- Decode a pair of blocked physical indices into four right-associated
original physical indices. -/
def blockedPairEquiv (d : ℕ) :
    Fin (d * d) × Fin (d * d) ≃ Fin d × (Fin d × (Fin d × Fin d)) :=
  (Equiv.prodCongr (blockedIndexEquiv d) (blockedIndexEquiv d)).trans
    (Equiv.prodAssoc (Fin d) (Fin d) (Fin d × Fin d))

/-- After decoding the blocked physical index, the one-site closure of the
two-site blocked tensor is the two-site closure of the original tensor. -/
theorem physClose1_blockTwo_eq_physClose2 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedIndexEquiv d)
        (blockedIndexEquiv d)).toLinearMap ∘ₗ physClose1 (blockTwo M) =
      physClose2 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, blockedIndexEquiv, blockTwo]

/-- After decoding both blocked physical indices, the two-site closure of the
two-site blocked tensor is the right-associated four-site closure of the
original tensor. -/
theorem physClose2_blockTwo_eq_physClose4 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (blockedPairEquiv d) (blockedPairEquiv d)).toLinearMap ∘ₗ
        physClose2 (blockTwo M) =
      physClose4 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, blockedPairEquiv, blockedIndexEquiv,
    blockTwo, Matrix.mul_assoc]

@[deprecated _root_.finFourArrowEquiv (since := "2026-07-13")]
alias finFourArrowEquiv := _root_.finFourArrowEquiv

end MPOTensor
