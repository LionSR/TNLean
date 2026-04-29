/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingForm
import TNLean.MPS.MPDO.FusionIsometries
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Blocked-RFP construction for simple MPDOs

This file records the current blocked-RFP theorem interface for the simple-MPDO
branch of arXiv:1606.00608, Appendix C.2 / Theorem 4.9.

At the present repository state, the local entropy side and the commuting-form
side live in separate modules:

* `SimpleLocalStructure.lean` isolates the local SAL/SSA and rank-one-`T`
  consequences of Lemmas C.3--C.4.
* `CommutingForm.lean` records the GSNNCH / commuting-form target side of
  Proposition C.6 and Theorem 4.9(iii).

What is still missing as a preceding is the theorem turning the local simple-MPDO data
into the global commuting-form property. Because of that gap, the present file
is formulated around the explicit record `SimpleMPDOBlockedRFPData`. The local
Appendix C.2 data are retained there, together with a provisional compatibility
relation to the ambient MPO tensor, so that the eventual local-to-global
implication has a canonical target.

The current consequences recorded here are:

* a **blocked fusion-isometry witness** at size `2`, formalized as
  `Nonempty (FusionIsometryData K 2)`;
* the GSNNCH-with-ZCL branch of Theorem 4.9;
* the transfer-map fusion formulation of MPDO RFP.

Thus this file supplies the paper-facing conclusion that later work can use
once the remaining local-to-global implication has been formalized.

## Main declarations

* `MPOTensor.SimpleMPDOLocalStructureData`
* `MPOTensor.SimpleMPDOBlockedRFPData`
* `MPOTensor.structural_implies_rfp_blocked`
* `MPOTensor.simple_mpdo_rfp_chain`

## References

* [CPGSV17] arXiv:1606.00608, Appendix C.2, Proposition C.5 and Theorem 4.9
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The local simple-MPDO structure isolated by Appendix C.2, Lemmas C.3--C.4.

This records exactly the information exposed by `SimpleLocalStructure.lean`:

a normalized three-site reduced state satisfying equality in strong
subadditivity, the resulting local `η`-structure, and a primitive real matrix
`T` together with the rank-one conclusion extracted from the constant-trace
condition.

The record is intentionally independent of a particular MPO tensor. The missing
preceding theorem is the map from a concrete simple MPDO satisfying SAL/ZCL to
such a record and then onward to `HasCommutingForm`. -/
structure SimpleMPDOLocalStructureData where
  /-- Dimensions of the three contiguous local regions. -/
  dA : ℕ
  dB : ℕ
  dC : ℕ
  /-- The normalized three-site reduced state entering Lemma C.3. -/
  rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ
  /-- Density-matrix normalization for the local state. -/
  hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1
  /-- Equality in strong subadditivity for `rhoABC`. -/
  hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian
  /-- The local `η`-structure extracted from SSA equality. -/
  eta : Nonempty (EtaStructure rhoABC)
  /-- The auxiliary real matrix `T` from Lemma C.4. -/
  Tdim : ℕ
  T : Matrix (Fin Tdim) (Fin Tdim) ℝ
  /-- Primitivity of `T`. -/
  hPrimitive : Matrix.IsPrimitive T
  /-- Trace normalization of `T`. -/
  hTrace : Matrix.trace T = 1
  /-- Constancy of the traces of positive powers of `T`. -/
  hTraceConst : Matrix.TracePowersConstant T
  /-- Rank-one conclusion for `T`. -/
  rankOne : ∃ a b : Fin Tdim → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1

namespace SimpleMPDOLocalStructureData

/-- Construct the local simple-MPDO data record from the scoped Lemma C.3/C.4
inputs already available in `SimpleLocalStructure.lean`. -/
def ofSALZCL
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T) :
    SimpleMPDOLocalStructureData where
  dA := dA
  dB := dB
  dC := dC
  rhoABC := rhoABC
  hRhoDM := hRhoDM
  hSSA := hSSA
  eta := sal_implies_eta_structure rhoABC hRhoDM hSSA
  Tdim := n
  T := T
  hPrimitive := hPrimitive
  hTrace := hTrace
  hTraceConst := hTraceConst
  rankOne := sal_zcl_implies_rank_one_T T hPrimitive hTrace hTraceConst hPF

end SimpleMPDOLocalStructureData

/-- Provisional relation expressing that local simple-MPDO structure data are
attached to a specific MPO tensor.

The current development does not yet formalize the local-to-global map from the
Appendix-C.2 entropy input to a commuting-form witness for `K`, so this
compatibility relation is temporarily the trivial proposition. It is included
already so that `SimpleMPDOBlockedRFPData` carries a type-level field linking
its local data to the ambient tensor. -/
def SimpleMPDOLocalStructureData.CompatibleWith
    (_data : SimpleMPDOLocalStructureData) (_K : MPOTensor d D) : Prop :=
  True

/-- Auxiliary record for the simple-MPDO blocked-RFP argument.

The field `localData` records the Appendix C.2 local structure from issue #781,
the field `compatible` records its provisional attachment to `K`, and the
fields `commutingForm` and `zcl` record the issue-#782 target side and the MPO
zero-correlation-length input. This is the current point where the two sibling
branches meet: the missing theorem is the derivation of `commutingForm` from
the entropy-side hypotheses attached to `K`.

The present blocked-RFP consequences only use `commutingForm` and `zcl`; the
pair `localData` / `compatible` is retained so that the eventual local-to-global
implication already has a type-level target. -/
structure SimpleMPDOBlockedRFPData (K : MPOTensor d D) where
  /-- Local SAL/SSA/rank-one data from Appendix C.2. -/
  localData : SimpleMPDOLocalStructureData
  /-- Provisional attachment of the local data to the ambient MPO tensor. -/
  compatible : localData.CompatibleWith K
  /-- Global commuting-form / GSNNCH data. -/
  commutingForm : HasCommutingForm K
  /-- Zero correlation length, hence the current provisional RFP predicate. -/
  zcl : IsZCL K

namespace SimpleMPDOBlockedRFPData

variable {K : MPOTensor d D}

/-- Construct this record directly from the scoped local lemmas of
`SimpleLocalStructure.lean`, the commuting-form hypothesis, and MPO ZCL.

At present, the subsequent consequences in this file use only `hCommuting` and
`hZCL`. The local-data inputs are retained so that the eventual local-to-global
implication from Appendix C.2 already has a canonical type-level target. -/
def ofSALZCLAndCommutingForm
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T)
    (hCommuting : HasCommutingForm K) (hZCL : IsZCL K) :
    SimpleMPDOBlockedRFPData K where
  localData := SimpleMPDOLocalStructureData.ofSALZCL
    rhoABC hRhoDM hSSA T hPrimitive hTrace hTraceConst hPF
  compatible := trivial
  commutingForm := hCommuting
  zcl := hZCL

/-- The issue-#782 commuting-form data together with MPO ZCL yield the
GSNNCH-with-ZCL branch of Theorem 4.9. -/
theorem isGSNNCHWithZCL (data : SimpleMPDOBlockedRFPData K) :
    IsGSNNCHWithZCL K := by
  exact (isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL K).2
    ⟨data.commutingForm, data.zcl⟩

/-- The data record implies the current provisional MPDO RFP predicate. -/
theorem isRFP (data : SimpleMPDOBlockedRFPData K) : IsRFP K :=
  data.zcl

/-- The data record implies the transfer-map fusion formulation of MPDO RFP. -/
theorem isRFPViaFusion (data : SimpleMPDOBlockedRFPData K) :
    IsRFP_MPDO_via_fusion K := by
  exact isRFP_MPDO_via_fusion_of_isRFP (M := K) data.isRFP

end SimpleMPDOBlockedRFPData

/-- Under the current convention `IsRFP = IsZCL`, zero correlation length yields
a blocked fusion-isometry witness at size `2`. -/
theorem structural_implies_rfp_blocked {K : MPOTensor d D}
    (hZCL : IsZCL K) :
    Nonempty (FusionIsometryData K 2) :=
  (isRFP_MPDO_via_fusion_of_isRFP
    (M := K)
    (show IsRFP K from hZCL)) 2 (show 0 < 2 by decide)

/-- Data-parameterized blocked fusion-isometry witness.

Relative to the current convention `IsRFP = IsZCL`, the present conclusion uses
only `data.zcl`. The fields `localData`, `compatible`, and `commutingForm` are
retained for the larger simple-MPDO interface and for the future local-to-global
implication. -/
theorem structural_implies_rfp_blocked_of_data {K : MPOTensor d D}
    (data : SimpleMPDOBlockedRFPData K) :
    Nonempty (FusionIsometryData K 2) :=
  structural_implies_rfp_blocked (K := K) data.zcl

/-- **Theorem 4.9 conclusion, data-parameterized form**.

From the explicit simple-MPDO inputs one simultaneously recovers:

* the GSNNCH-with-ZCL branch of Theorem 4.9(iii),
* the blocked fusion-isometry witness at size `2`, and
* the transfer-map fusion formulation of MPDO RFP.

Relative to the current repository state, this is the final construction layer
on top of issues #781 and #782. -/
theorem simple_mpdo_rfp_chain_of_data {K : MPOTensor d D}
    (data : SimpleMPDOBlockedRFPData K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K := by
  refine ⟨data.isGSNNCHWithZCL, structural_implies_rfp_blocked_of_data data,
    data.isRFPViaFusion⟩

/-- Direct-argument form of Theorem 4.9 using only the hypotheses that enter the
current conclusion. -/
theorem simple_mpdo_rfp_chain {K : MPOTensor d D}
    (hCommuting : HasCommutingForm K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K := by
  refine ⟨?_, structural_implies_rfp_blocked (K := K) hZCL, ?_⟩
  · exact (isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL K).2 ⟨hCommuting, hZCL⟩
  · exact isRFP_MPDO_via_fusion_of_isRFP (M := K) (show IsRFP K from hZCL)

end MPOTensor
