/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.CanonicalForm.Periodic.CyclicSectors.CommonBlockedCyclicSectorConstruction
import TNLean.MPS.CanonicalForm.BNTPresentation.Refinement
import QICLean.Channel.Irreducible.Ergodicity
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT

/-!
# CPSV canonical-form representative after blocking

This module constructs the canonical-form representative stated after the
canonical-form definition in Cirac--Pérez-García--Schuch--Verstraete,
arXiv:1606.00608, lines 249--251.

## Main statements

* `exists_leftCanonical_cpsvCanonicalFormData_after_blocking` retains the
  displayed blocks and their left-canonical identities.
* `exists_cpsvCanonicalForm_representative_after_blocking` gives, after a
  positive blocking length, a tensor in literal CPSV canonical form with the same
  positive-length MPV family as the blocked input tensor.
* `MPSTensor.exists_blockTensor_normal_sectors`,
  `MPSTensor.exists_blockTensor_normal_sectors_fixedPoints`: normal sectors of an arbitrary tensor
  after fixed blocking.

## References

* [Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608, Section 2.3]

## Tags

matrix product states, canonical form, blocking, normal tensor
-/

open MPTensor

section RepresentativeAfterBlocking

open scoped BigOperators
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-- After a positive blocking length, every tensor has a possibly different
representative in literal CPSV canonical form which generates the same
positive-length MPV family, with left-canonical displayed normal blocks.

The representative is the weighted direct sum of the primitive irreducible
left-canonical blocks. It need not equal the blocked input tensor in the
input tensor's original bond coordinates.

Source: arXiv:1606.00608, lines 214--251, especially eqs. `II_Aiplusk1` and
`II_CF1` and the proposition at lines 249--251. -/
theorem exists_leftCanonical_cpsvCanonicalFormData_after_blocking
    (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ D' : ℕ, ∃ B : MPSTensor (blockPhysDim d p) D',
        ∃ data : CPSVCanonicalFormData B,
          (∀ j, IsLeftCanonical (data.blocks j)) ∧
          SameMPV₂Pos (blockTensor A p) B := by
  have hRefl : SameMPV₂Pos A A := by
    intro N _hN σ
    rfl
  obtain ⟨p, hp, rA, dimA, μA, blocksA, rB, dimB, μB, blocksB,
      hABlocks, _hBBlocks, _hBlocksAgree, hμA, _hμB, hLeftA, _hLeftB,
      hPrimitiveA, _hPrimitiveB, hIrreducibleA, _hIrreducibleB,
      hDimA, _hDimB⟩ :=
    unconditional_commonPrimitiveIrreducibleBlocks A A hRefl
  let B : MPSTensor (blockPhysDim d p) (∑ k : Fin rA, dimA k) :=
    toTensorFromBlocks (d := blockPhysDim d p) μA blocksA
  have hNormalA : ∀ k, IsNormalTensor (blocksA k) := by
    intro k
    let : NeZero (dimA k) := ⟨Nat.ne_of_gt (hDimA k)⟩
    exact isNormalTensor_of_isNormal_leftCanonical (blocksA k)
      (isNormal_of_tp_primitive_irreducible (blocksA k)
        (hLeftA k) (hPrimitiveA k) (hIrreducibleA k))
      (hLeftA k)
  exact ⟨p, hp, ∑ k : Fin rA, dimA k, B,
    CPSVCanonicalFormData.ofBlocks hDimA μA hμA blocksA hNormalA, hLeftA, hABlocks⟩

/-- After a positive blocking length, every tensor has a possibly different
representative in literal CPSV canonical form which generates the same
positive-length MPV family.

The representative is the weighted direct sum of the primitive irreducible
left-canonical blocks. It need not equal the blocked input tensor in the
input tensor's original bond coordinates.

Source: arXiv:1606.00608, lines 214--251, especially eqs. `II_Aiplusk1` and
`II_CF1` and the proposition at lines 249--251. -/
theorem exists_cpsvCanonicalForm_representative_after_blocking
    (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧
      ∃ D' : ℕ, ∃ B : MPSTensor (blockPhysDim d p) D',
        IsCPSVCanonicalForm B ∧
        SameMPV₂Pos (blockTensor A p) B := by
  obtain ⟨p, hp, D', B, data, _, heq⟩ :=
    exists_leftCanonical_cpsvCanonicalFormData_after_blocking A
  exact ⟨p, hp, D', B, data.isCPSVCanonicalForm, heq⟩

end MPSTensor

end RepresentativeAfterBlocking

section BlockedNormalSectors

/-!
## Normal sectors of an arbitrary tensor after fixed blocking

Every tensor admits one positive blocking length and a sector decomposition with
left-canonical, inequivalent normal representatives. Copy multiplicities and complex
weights are retained exactly, including cancellations at particular lengths. The normalized
faithful stationary matrices and strict mixed-transfer bounds are derived from the blocks.
No nonzero-state or canonical-form hypothesis is imposed on the input tensor; an empty
family represents the identically zero positive-length family.

This supplies the canonical reduction needed by arXiv:2307.01696, eq. (S2), on chains
whose physical length is a multiple of the fixed blocking length. It does not treat
other physical lengths or transport circuits from grouped sites to physical sites.

### References

* arXiv:1606.00608, Section II.C and Appendix A.
* arXiv:2307.01696, "Long-range MPS using measurements", eqs. (S2)--(S4).
-/

open scoped BigOperators ComplexOrder
open Kraus (blockPhysDim blockTensor)

namespace MPSTensor

variable {d D : ℕ}

/-- An arbitrary tensor has, after a fixed positive blocking, an exact expansion in
inequivalent left-canonical normal sectors. The coefficients are the actual copy power sums
`P.coeff N j`; no coefficient is required to survive at every length.
Source: arXiv:1606.00608, Section II.C; arXiv:2307.01696, eqs. (S2)--(S4). -/
theorem exists_blockTensor_normal_sectors (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ P : SectorDecomposition (blockPhysDim d p),
      SameMPV₂Pos (blockTensor A p) P.toTensor ∧
      (∀ j, IsNormalTensor (P.basis j)) ∧
      (∀ j, IsLeftCanonical (P.basis j)) ∧
      BlocksNotGaugePhaseEquiv P.basis := by
  classical
  obtain ⟨p, hp, D', B, data, hleft, hAB⟩ :=
    exists_leftCanonical_cpsvCanonicalFormData_after_blocking A
  let ref := data.bntRefinement
  refine ⟨p, hp, ref.representativeSectorDecomposition,
    hAB.trans (ref.source_sameMPV₂Pos_groupedTensor.trans
      ref.groupedTensor_sameMPV₂Pos_representativeSectorDecomposition),
    ref.representativeNormal, ?_, ref.representativesNotEquiv⟩
  intro j
  exact hleft (data.representativeIndex j)

/-- The sectors of an arbitrary blocked tensor have faithful trace-one stationary matrices
and a strict mixed-transfer gap. All the analytic hypotheses used by overlapping-block
measurement preparation follow from the canonical reduction.
Source: arXiv:2307.01696, eq. (5), eq. (S2), and the proof of Lemma 1'(ii). -/
theorem exists_blockTensor_normal_sectors_fixedPoints (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ P : SectorDecomposition (blockPhysDim d p),
      ∃ σ : (j : Fin P.basisCount) → Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ,
        SameMPV₂Pos (blockTensor A p) P.toTensor ∧
        (∀ j, Kraus.IsNormal (P.basis j)) ∧
        (∀ j, IsLeftCanonical (P.basis j)) ∧
        (∀ j, (σ j).PosDef) ∧ (∀ j, (σ j).trace = 1) ∧
        (∀ j, Kraus.transferMap (P.basis j) (σ j) = σ j) ∧
        (∀ j k, j ≠ k → ∀ z,
          Module.End.HasEigenvalue (Kraus.mixedMapLM (P.basis j) (P.basis k)) z → ‖z‖ < 1) := by
  classical
  obtain ⟨p, hp, P, heq, hnormal, hleft, hneq⟩ := exists_blockTensor_normal_sectors A
  have hdim : ∀ j, 0 < P.basisDim j := fun j =>
    Nat.pos_of_ne_zero (hnormal j).bondDim_ne_zero
  let : ∀ j, NeZero (P.basisDim j) := fun j => ⟨(hdim j).ne'⟩
  have hfixed : ∀ j, ∃ σ : Matrix (Fin (P.basisDim j)) (Fin (P.basisDim j)) ℂ,
      σ.PosDef ∧ σ.trace = 1 ∧ Kraus.transferMap (P.basis j) σ = σ := by
    intro j
    obtain ⟨σ, hmem, hpos, hfix, _⟩ :=
      IsChannel.exists_unique_density_fixedPoint_of_irreducible
        (Kraus.transferMap (P.basis j))
        (Kraus.isChannel_mapLM (P.basis j) (hleft j))
        (Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily (P.basis j)
          (hnormal j).no_invariant_proj) (hdim j)
    exact ⟨σ, hpos, hmem.2, hfix⟩
  choose σ hpos htr hfix using hfixed
  refine ⟨p, hp, P, σ, heq, fun j => (hnormal j).isNormal, hleft, hpos, htr, hfix, ?_⟩
  intro j k hjk z hz
  apply mixedMap_eigenvalue_norm_lt_one_of_normal_inequivalent
    (P.basis j) (P.basis k) (hnormal j).isNormal (hnormal k).isNormal
    (hleft j) (hleft k) ?_ hz
  intro h
  simpa only [eqRec_eq_cast] using hneq j k hjk h

end MPSTensor

end BlockedNormalSectors
