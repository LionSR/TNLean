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
* `MPOTensor.mpo_blockTensor_eq_reindex`: closing a blocked chain gives the
  corresponding longer unblocked chain.
* `MPOTensor.IsMPDO.blockTensor`: physical blocking preserves the MPDO property.
* `MPOTensor.blockTwo`: the tensor obtained by blocking two adjacent sites.
* `MPOTensor.physClose4`: the right-associated four-site physical closure.
* `MPOTensor.physClose1_blockTwo_eq_physClose2`: one blocked site is two original sites.
* `MPOTensor.physClose2_blockTwo_eq_physClose4`: two blocked sites are four original sites.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Theorem 4.9, lines 851--856
* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 1952--2017
-/

open scoped Matrix ComplexOrder

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

/-- Evaluating a blocked tensor gives the corresponding pair of blocked words. -/
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

/-- Decoding the doubled blocked index pairs the ket and bra letters pointwise. -/
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

private theorem evalWord_blockTensor_ofFn (M : MPOTensor d D) (L : ℕ) {N : ℕ}
    (s t : Fin N → Fin (MPSTensor.blockPhysDim d L)) :
    evalWord (blockTensor M L) (List.ofFn s) (List.ofFn t) =
      evalWord M (MPSTensor.flattenBlockedWord d L (List.ofFn s))
        (MPSTensor.flattenBlockedWord d L (List.ofFn t)) := by
  induction N with
  | zero =>
      simp [MPSTensor.flattenBlockedWord]
  | succ N ih =>
      simp only [List.ofFn_succ, evalWord_cons, blockTensor_apply,
        MPSTensor.flattenBlockedWord_cons]
      rw [ih]
      rw [evalWord_append M _ _ _ _ (by simp)]

/-- Closing a chain of `N` tensors after blocking `L` consecutive physical
sites gives the original closed chain of length `N * L`, after the canonical
identification of blocked configurations with unblocked configurations.

The algebraic identity holds for every natural `L`; its interpretation as
blocking adjacent physical sites requires `L > 0`.

This is the finite-index form of the physical blocking used when placing the
one-site tensor and its two-site blocking in vertical canonical form in
arXiv:1606.00608, Appendix C.4, lines 1952--2017. -/
theorem mpo_blockTensor_eq_reindex (M : MPOTensor d D) (L N : ℕ) :
    mpo (blockTensor M L) N =
      Matrix.reindex (MPSTensor.blockedConfigEquiv d N L).symm
        (MPSTensor.blockedConfigEquiv d N L).symm (mpo M (N * L)) := by
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, mpo_apply, mpoMatrixEntry]
  rw [evalWord_blockTensor_ofFn]
  simp only [Equiv.symm_symm, MPSTensor.ofFn_blockedConfigEquiv]

/-- Positive-length physical blocking preserves positivity of the closed MPO
family.

This is the blocking operation used throughout the vertical canonical-form
comparison of arXiv:1606.00608, Appendix C.4, lines 1952--2017. -/
theorem IsMPDO.blockTensor {M : MPOTensor d D} (hM : IsMPDO M) (L : ℕ)
    (hL : 0 < L) :
    IsMPDO (blockTensor M L) := by
  intro N hN
  rw [mpo_blockTensor_eq_reindex]
  rw [Matrix.reindex_apply]
  exact (hM (N * L) (Nat.mul_pos hN hL)).submatrix _

/-! ### Two-site blocking -/

/-- The MPO tensor obtained by blocking two adjacent physical sites. The two
ket indices, and separately the two bra indices, are encoded through the
standard equivalence `Fin d × Fin d ≃ Fin (d * d)`. This is the blocking used
in arXiv:1606.00608, Theorem 4.9, lines 851--856. -/
noncomputable def blockTwo (M : MPOTensor d D) : MPOTensor (d * d) D :=
  fun i j =>
    M (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm j).1 *
      M (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2

/-- The physical-trace transfer of a two-site block is the square of the
original physical-trace transfer. -/
theorem physTraceTransfer_blockTwo (M : MPOTensor d D) :
    physTraceTransfer (blockTwo M) =
      physTraceTransfer M * physTraceTransfer M := by
  rw [physTraceTransfer, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type,
    physTraceTransfer, Finset.sum_mul_sum]
  simp [blockTwo]

/-- Identify the standard two-site index `Fin (d * d)` with the general
length-two blocked alphabet.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
noncomputable def twoSiteBlockEquiv (d : ℕ) :
    Fin (d * d) ≃ Fin (MPSTensor.blockPhysDim d 2) :=
  finProdFinEquiv.symm |>.trans
    (finTwoArrowEquiv (Fin d)).symm |>.trans
    (MPSTensor.decodeBlockEquiv d 2).symm

/-- Identify the doubled physical index of `blockTwo` with the general
length-two block of the doubled MPS alphabet. -/
noncomputable def twoSiteDoubledIndexEquiv (d : ℕ) :
    Fin ((d * d) * (d * d)) ≃
      Fin (MPSTensor.blockPhysDim (d * d) 2) :=
  finProdFinEquiv.symm |>.trans
    (Equiv.prodCongr (twoSiteBlockEquiv d) (twoSiteBlockEquiv d)) |>.trans
    finProdFinEquiv |>.trans
    (blockedDoubledIndexEquiv d 2)

/-- Passing `blockTwo` to its doubled-index MPS tensor is general two-site
blocking followed by the canonical ket--bra reindexing.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem toMPSTensor_blockTwo (M : MPOTensor d D) :
    (blockTwo M).toMPSTensor =
      MPSTensor.reindexPhysical (twoSiteDoubledIndexEquiv d)
        (MPSTensor.blockTensor M.toMPSTensor 2) := by
  funext ij
  simp [toMPSTensor, blockTwo, MPSTensor.reindexPhysical,
    MPSTensor.blockTensor, twoSiteDoubledIndexEquiv, twoSiteBlockEquiv,
    blockedDoubledIndexEquiv, MPSTensor.wordOfBlock, Equiv.arrowCongr]

/-- The concrete two-site blocking is the general length-two blocking after
the canonical relabeling of each physical index.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem blockTwo_eq_blockTensor_reindex (M : MPOTensor d D) :
    blockTwo M = fun i j ↦
      blockTensor M 2 (twoSiteBlockEquiv d i) (twoSiteBlockEquiv d j) := by
  funext i j
  simp [blockTwo, blockTensor, twoSiteBlockEquiv, MPSTensor.wordOfBlock]

/-- Closing a chain of concrete two-site blocks is the same as closing a
chain of general length-two blocks, after relabeling every physical index.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem mpo_blockTwo_eq_reindex_blockTensor (M : MPOTensor d D) (N : ℕ) :
    mpo (blockTwo M) N =
      Matrix.reindex
        (Equiv.arrowCongr (Equiv.refl (Fin N)) (twoSiteBlockEquiv d)).symm
        (Equiv.arrowCongr (Equiv.refl (Fin N)) (twoSiteBlockEquiv d)).symm
        (mpo (blockTensor M 2) N) := by
  ext σ τ
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, mpo_apply,
    mpoMatrixEntry, evalWord_ofFn]
  rw [blockTwo_eq_blockTensor_reindex]
  rfl

/-- Concrete two-site blocking preserves positivity of every closed MPO.

Source: arXiv:1606.00608, Appendix C.4, lines 1951--1956. -/
theorem IsMPDO.blockTwo {M : MPOTensor d D} (hM : IsMPDO M) :
    IsMPDO (blockTwo M) := by
  intro N hN
  rw [mpo_blockTwo_eq_reindex_blockTensor, Matrix.reindex_apply]
  exact (hM.blockTensor 2 (by omega) N hN).submatrix _

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

/-- Evaluating the one-site closure of the two-site blocking at a virtual
matrix gives the two-site closure after decoding the blocked physical index.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1979. -/
theorem physClose1_blockTwo_eq_physClose2_apply
    (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.equivReindexMap (blockedIndexEquiv d)
        (physClose1 (blockTwo M) X) = physClose2 M X := by
  simpa [Matrix.equivReindexMap] using
    LinearMap.congr_fun (physClose1_blockTwo_eq_physClose2 M) X

/-- Relabelling the two-site closure by one blocked physical index gives the
one-site closure of the two-site blocking.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1979. -/
theorem physClose2_eq_physClose1_blockTwo_apply
    (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.equivReindexMap (blockedIndexEquiv d).symm (physClose2 M X) =
      physClose1 (blockTwo M) X := by
  have h := congrArg (Matrix.equivReindexMap (blockedIndexEquiv d).symm)
    (physClose1_blockTwo_eq_physClose2_apply M X)
  simpa [Matrix.equivReindexMap] using h.symm

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
