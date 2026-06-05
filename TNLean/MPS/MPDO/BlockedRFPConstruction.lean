/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.CommutingFormBridge
import TNLean.MPS.MPDO.FusionIsometries
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Blocked-RFP construction for simple MPDOs

This file states the current blocked-RFP theorem for the simple-MPDO case of
arXiv:1606.00608, Appendix C.2 / Theorem 4.9.

At the present repository state, the local entropy side and the commuting-form
side live in separate modules:

* `SimpleLocalStructure.lean` isolates the local SAL/SSA and rank-one-`T`
  consequences of Lemmas C.2, C.4, and C.5.
* `CommutingFormBridge.lean` isolates the `η`-local structure that carries the
  commuting-form witness of arXiv:1606.00608, Appendix C.2, Proposition C.8,
  after the sector-local neighboring operators have been assembled.
* `CommutingForm.lean` states the GSNNCH / commuting-form target side of
  arXiv:1606.00608, Appendix C.2, Proposition C.8 and Theorem 4.9(iii).

What is still missing is the preceding theorem turning the local simple-MPDO data
into the global commuting-form property. Because of that gap, the present file
is formulated around the explicit structure `SimpleMPDOBlockedRFPData`, which
records the local Appendix C.2 hypotheses and the global commuting-form and
zero-correlation-length conclusions.

The current consequences are:

* a **blocked fusion-isometry witness** at size `2`, formalized as
  `Nonempty (FusionIsometryData K 2)`;
* the GSNNCH-with-ZCL case of Theorem 4.9;
* the transfer-map fusion formulation of MPDO RFP.

Thus this file supplies the Appendix C conclusion that later work can use
once the remaining local-to-global implication has been formalized.

## Main declarations

* `MPOTensor.SimpleMPDOLocalStructureData`
* `MPOTensor.SimpleMPDOBlockedRFPData`
* `MPOTensor.SimpleMPDOBlockedRFPData.ofEtaLocalStructure`
* `MPOTensor.SimpleMPDOBlockedRFPData.ofSALZCLAndEtaLocalStructure`
* `MPOTensor.SimpleMPDOBlockedRFPData.ofSALZCLAndEtaLocalStructureOfPosSemidef`
* `MPOTensor.structural_implies_rfp_blocked`
* `MPOTensor.simple_mpdo_rfp_chain_of_etaLocalStructure`
* `MPOTensor.simple_mpdo_rfp_chain_of_sal_zcl_and_etaLocalStructure`
* `MPOTensor.simple_mpdo_rfp_chain_of_sal_zcl_and_etaLocalStructure_of_posSemidef`
* `MPOTensor.simple_mpdo_rfp_chain`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Corollary C.6 and Theorem 4.9
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The local simple-MPDO structure isolated by Appendix C.2, Lemmas C.2, C.4,
and C.5.

This structure contains exactly the information proved in `SimpleLocalStructure.lean`:

a normalized three-site reduced state satisfying equality in strong
subadditivity, the resulting local `η`-structure, and a primitive real matrix
`T` together with the rank-one conclusion extracted from the constant-trace
condition.

The structure is intentionally independent of a particular MPO tensor. The missing
preceding theorem is the map from a concrete simple MPDO to this structure and
then onward to `HasCommutingForm`: Lemma C.2 supplies the local `η`-structure
(the Markov decomposition), Lemma C.4 supplies the trace matrix `T` and its
primitivity, while ZCL and Lemma C.5 supply trace-power constancy and the
rank-one factorization of `T`. -/
structure SimpleMPDOLocalStructureData where
  /-- Dimensions of the three contiguous local regions. -/
  dA : ℕ
  dB : ℕ
  dC : ℕ
  /-- The normalized three-site reduced state entering Lemma C.2. -/
  rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ
  /-- Density-matrix normalization for the local state. -/
  hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1
  /-- Equality in strong subadditivity for `rhoABC`. -/
  hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian
  /-- The quantum-Markov decomposition (`EtaStructure`) from Lemma C.2. -/
  eta : Nonempty (EtaStructure rhoABC)
  /-- The auxiliary trace matrix `T` from Lemma C.4. -/
  Tdim : ℕ
  T : Matrix (Fin Tdim) (Fin Tdim) ℝ
  /-- Primitivity of `T`, supplied by Lemma C.4. -/
  hPrimitive : Matrix.IsPrimitive T
  /-- Trace normalization of `T`. -/
  hTrace : Matrix.trace T = 1
  /-- Constancy of the traces of positive powers of `T`. -/
  hTraceConst : Matrix.TracePowersConstant T
  /-- Rank-one conclusion for `T`. -/
  rankOne : ∃ a b : Fin Tdim → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1

namespace SimpleMPDOLocalStructureData

/-- Construct the local simple-MPDO structure from the Lemma C.2, C.4, and C.5
hypotheses already available in `SimpleLocalStructure.lean`.

**Unfaithful:** This constructor currently relies on
`sal_zcl_implies_rank_one_T`, whose `hPF` hypothesis is not supplied by
arXiv:1606.00608, Lemma C.5, lines 1484--1502. Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. Elimination: use
`ofSALZCLOfPosSemidef` and `sal_zcl_implies_rank_one_T_of_posSemidef`; tracked
in issue #1041. -/
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

/-- Construct the local simple-MPDO structure from the Lemma C.2 and C.4
hypotheses and the PSD-corrected Lemma C.5 rank-one criterion.

Source: arXiv:1606.00608, Appendix C.2, Lemmas C.4 and C.5 and the corollary
after them, lines 1406--1505.

**Local fix (PSD rank-one criterion):** the source's primitive
nonnegative-matrix inference at lines 1490--1498 is not valid as stated. This
constructor uses the positive-semidefinite sufficient condition documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
def ofSALZCLOfPosSemidef
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T) :
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
  rankOne :=
    sal_zcl_implies_rank_one_T_of_posSemidef T hPrimitive hPSD hTrace hTraceConst

end SimpleMPDOLocalStructureData

/-- Auxiliary structure for the simple-MPDO blocked-RFP argument.

It consists of the Appendix C.2 local structure, the commuting-form conclusion,
and the MPO zero-correlation-length hypothesis. The missing theorem is the
derivation of the commuting-form conclusion from the entropy-side hypotheses
attached to `K`. -/
structure SimpleMPDOBlockedRFPData (K : MPOTensor d D) where
  /-- Local SAL/SSA/rank-one data from Appendix C.2. -/
  localData : SimpleMPDOLocalStructureData
  /-- Global commuting-form / GSNNCH data. -/
  commutingForm : HasCommutingForm K
  /-- Zero correlation length, hence the current RFP predicate. -/
  zcl : IsZCL K

namespace SimpleMPDOBlockedRFPData

variable {K : MPOTensor d D}

/-- Construct this structure directly from the local lemmas of
`SimpleLocalStructure.lean`, the commuting-form hypothesis, and MPO ZCL.

**Unfaithful:** This constructor uses `SimpleMPDOLocalStructureData.ofSALZCL`,
and hence relies on the conditional `hPF` shortcut absent from arXiv:1606.00608,
Lemma C.5, lines 1484--1502. Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. Elimination: use
`ofSALZCLAndCommutingFormOfPosSemidef`; tracked in issue #1041. -/
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
  commutingForm := hCommuting
  zcl := hZCL

/-- Construct this structure from the local SAL--ZCL hypotheses, the
PSD-corrected rank-one criterion for `T`, a commuting-form hypothesis, and MPO
ZCL.

Source: arXiv:1606.00608, Appendix C.2, Lemmas C.4 and C.5 and Proposition 3to4,
lines 1406--1505 and 1569--1593.

**Local fix (PSD rank-one criterion):** this is the blocked-RFP version of
`SimpleMPDOLocalStructureData.ofSALZCLOfPosSemidef`; the correction is recorded
in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
def ofSALZCLAndCommutingFormOfPosSemidef
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hCommuting : HasCommutingForm K) (hZCL : IsZCL K) :
    SimpleMPDOBlockedRFPData K where
  localData := SimpleMPDOLocalStructureData.ofSALZCLOfPosSemidef
    rhoABC hRhoDM hSSA T hPrimitive hPSD hTrace hTraceConst
  commutingForm := hCommuting
  zcl := hZCL

/-- Construct the blocked-RFP data from the assembled `η`-local structure.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
once the local neighboring operators `η_{k,h}` have been assembled into a
positive nearest-neighbor bond product, the translated bond operators commute
and realize the finite-chain MPDO. This eta-local structure gives the
commuting-form property required in the blocked-RFP argument. -/
def ofEtaLocalStructure
    (localData : SimpleMPDOLocalStructureData)
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    SimpleMPDOBlockedRFPData K where
  localData := localData
  commutingForm := hEta.hasCommutingForm
  zcl := hZCL

/-- Construct the blocked-RFP data from the local SAL--ZCL hypotheses and the
assembled `η`-local structure.

References: arXiv:1606.00608, Appendix C.2, Corollary to Proposition 3.3,
lines 1501--1505, and Proposition 3to4, lines 1571--1593. This declaration is
the post-assembly step: the local hypotheses record the Lemmas C.2, C.4, and
C.5 consequences, while the eta-local structure records the already assembled
positive nearest-neighbor product
`σ^{(N)}(K) ∝ ∏ n, B_{n,n+1}` with commuting bonds.

**Scope restriction:** this constructor still assumes `EtaLocalStructureData K`;
it does not construct the translated bond operators from SAL. It also assumes
the conditional primitive trace-power rank-one input `hPF`. Documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex` and
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`; the remaining constructions are
tracked by issue #823.

**Unfaithful:** The local-data field is constructed through
`SimpleMPDOLocalStructureData.ofSALZCL`, whose `hPF` shortcut is absent from
arXiv:1606.00608, Lemma C.5, lines 1484--1502. Documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. Elimination: use
`ofSALZCLAndEtaLocalStructureOfPosSemidef`; tracked in issue #1041. -/
def ofSALZCLAndEtaLocalStructure
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T)
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    SimpleMPDOBlockedRFPData K :=
  ofEtaLocalStructure
    (SimpleMPDOLocalStructureData.ofSALZCL
      rhoABC hRhoDM hSSA T hPrimitive hTrace hTraceConst hPF)
    hEta hZCL

/-- Construct the blocked-RFP data from the local SAL--ZCL hypotheses, the
PSD-corrected rank-one criterion for `T`, and the assembled `η`-local
structure.

References: arXiv:1606.00608, Appendix C.2, Corollary to Proposition 3.3,
lines 1501--1505, and Proposition 3to4, lines 1571--1593.

**Scope restriction:** this constructor still assumes `EtaLocalStructureData K`;
it does not construct the translated bond operators from SAL. Documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`; that
construction is tracked by issue #823.

**Local fix (PSD rank-one criterion):** it uses the positive-semidefinite
replacement for the matrix step in Lemma C.5, documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
def ofSALZCLAndEtaLocalStructureOfPosSemidef
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    SimpleMPDOBlockedRFPData K :=
  ofEtaLocalStructure
    (SimpleMPDOLocalStructureData.ofSALZCLOfPosSemidef
      rhoABC hRhoDM hSSA T hPrimitive hPSD hTrace hTraceConst)
    hEta hZCL

/-- Commuting-form data together with MPO ZCL yield the GSNNCH-with-ZCL case of
Theorem 4.9. -/
theorem isGSNNCHWithZCL (data : SimpleMPDOBlockedRFPData K) : IsGSNNCHWithZCL K :=
  (isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL K).2 ⟨data.commutingForm, data.zcl⟩

/-- The structure implies the current MPDO RFP predicate. -/
theorem isRFP (data : SimpleMPDOBlockedRFPData K) : IsRFP K :=
  data.zcl

/-- The structure implies the transfer-map fusion formulation of MPDO RFP. -/
theorem isRFP_via_fusion (data : SimpleMPDOBlockedRFPData K) : IsRFP_MPDO_via_fusion K :=
  isRFP_MPDO_via_fusion_of_isRFP (M := K) data.isRFP

end SimpleMPDOBlockedRFPData

/-- Under the current convention `IsRFP = IsZCL`, zero correlation length yields
a blocked fusion-isometry witness at size `2`. -/
theorem structural_implies_rfp_blocked {K : MPOTensor d D}
    (hZCL : IsZCL K) :
    Nonempty (FusionIsometryData K 2) :=
  (isRFP_MPDO_via_fusion_of_isRFP
    (M := K)
    (show IsRFP K from hZCL)) 2 (show 0 < 2 by decide)

/-- Hypothesis-parameterized blocked fusion-isometry witness.

Relative to the current convention `IsRFP = IsZCL`, the present conclusion uses
only `data.zcl`. The components `localData` and `commutingForm` record the local
Appendix C structure and the global commuting-form conclusion used in the
larger simple-MPDO statement. -/
theorem structural_implies_rfp_blocked_of_data {K : MPOTensor d D}
    (data : SimpleMPDOBlockedRFPData K) :
    Nonempty (FusionIsometryData K 2) :=
  structural_implies_rfp_blocked (K := K) data.zcl

namespace EtaLocalStructureData

variable {K : MPOTensor d D}

/-- An η-local structure, together with ZCL, gives the blocked
fusion-isometry witness at size `2`.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593,
followed by the ZCL/RFP implication in Theorem 4.9. -/
theorem fusion_isometry_data_two (_data : EtaLocalStructureData K) (hZCL : IsZCL K) :
    Nonempty (FusionIsometryData K 2) :=
  structural_implies_rfp_blocked (K := K) hZCL

/-- An η-local structure, together with ZCL, gives the transfer-map
fusion formulation of MPDO RFP.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593,
followed by the ZCL/RFP implication in Theorem 4.9. -/
theorem isRFP_via_fusion (_data : EtaLocalStructureData K) (hZCL : IsZCL K) :
    IsRFP_MPDO_via_fusion K :=
  isRFP_MPDO_via_fusion_of_isRFP (M := K) (show IsRFP K from hZCL)

/-- The complete RFP chain carried by an η-local structure and ZCL.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
the η-local nearest-neighbor product gives the commuting-form side; adding ZCL
gives the GSNNCH--ZCL and RFP consequences of Theorem 4.9. -/
theorem simple_mpdo_rfp_chain (data : EtaLocalStructureData K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K :=
  ⟨data.isGSNNCHWithZCL hZCL, data.fusion_isometry_data_two hZCL,
    data.isRFP_via_fusion hZCL⟩

end EtaLocalStructureData

/-- **Theorem 4.9 conclusion, hypothesis-parameterized form**.

From the explicit simple-MPDO hypotheses one simultaneously recovers:

* the GSNNCH-with-ZCL case of Theorem 4.9(iii),
* the blocked fusion-isometry witness at size `2`, and
* the transfer-map fusion formulation of MPDO RFP.

Relative to the current formalization, this is the construction layer after the
local simple-MPDO structure, commuting form, and zero-correlation-length
hypotheses have been supplied explicitly. -/
theorem simple_mpdo_rfp_chain_of_data {K : MPOTensor d D}
    (data : SimpleMPDOBlockedRFPData K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K := by
  exact ⟨data.isGSNNCHWithZCL, structural_implies_rfp_blocked_of_data data,
    data.isRFP_via_fusion⟩

/-- Direct-argument form of Theorem 4.9 using only the hypotheses that enter the
current theorem. -/
theorem simple_mpdo_rfp_chain {K : MPOTensor d D}
    (hCommuting : HasCommutingForm K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K := by
  refine ⟨?_, structural_implies_rfp_blocked (K := K) hZCL, ?_⟩
  · exact (isGSNNCHWithZCL_iff_hasCommutingForm_and_isZCL K).2 ⟨hCommuting, hZCL⟩
  · exact isRFP_MPDO_via_fusion_of_isRFP (M := K) (show IsRFP K from hZCL)

/-- Direct form of the simple-MPDO construction once the assembled `η`-local
structure has been constructed.

Source: arXiv:1606.00608, Appendix C.2, Proposition 3to4, lines 1571--1593:
the neighboring `η_{k,h}` operators assemble into commuting two-site bonds
whose product realizes the MPDO. The eta-local structure is precisely this
assembled positive commuting-bond form. -/
theorem simple_mpdo_rfp_chain_of_etaLocalStructure {K : MPOTensor d D}
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K :=
  hEta.simple_mpdo_rfp_chain hZCL

/-- The simple-MPDO RFP chain from local SAL--ZCL hypotheses once the eta-local
nearest-neighbor product has been assembled.

References: arXiv:1606.00608, Appendix C.2, Corollary to Proposition 3.3,
lines 1501--1505, and Proposition 3to4, lines 1571--1593. This declaration is
the post-assembly step combining those outputs.

**Scope restriction:** this theorem assumes the assembled eta-local structure
instead of deriving it from SAL, and it assumes the conditional primitive
trace-power rank-one input `hPF`. It records the final assembly step after the
nearest-neighbor bonds $B_{n,n+1}$ and their commutation have been constructed.
Documented in `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`
and `docs/paper-gaps/cpgsv17_pf_rank_one.tex`; the source-faithful
constructions are tracked by issue #823.

**Unfaithful:** The proof uses the non-PSD constructor
`SimpleMPDOBlockedRFPData.ofSALZCLAndEtaLocalStructure`, which relies on the
conditional `hPF` shortcut absent from arXiv:1606.00608, Lemma C.5,
lines 1484--1502. Documented in `docs/paper-gaps/cpgsv17_pf_rank_one.tex`.
Elimination: use the PSD-corrected theorem
`simple_mpdo_rfp_chain_of_sal_zcl_and_etaLocalStructure_of_posSemidef`; tracked
in issue #1041. -/
theorem simple_mpdo_rfp_chain_of_sal_zcl_and_etaLocalStructure {K : MPOTensor d D}
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hPF : Matrix.PrimitiveTracePowersConstantImpliesRankOne T)
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K :=
  simple_mpdo_rfp_chain_of_data
    (SimpleMPDOBlockedRFPData.ofSALZCLAndEtaLocalStructure
      rhoABC hRhoDM hSSA T hPrimitive hTrace hTraceConst hPF hEta hZCL)

/-- The simple-MPDO RFP chain from local SAL--ZCL hypotheses, the
PSD-corrected rank-one criterion for `T`, and the assembled eta-local
nearest-neighbor product.

References: arXiv:1606.00608, Appendix C.2, Corollary to Proposition 3.3,
lines 1501--1505, and Proposition 3to4, lines 1571--1593.

**Scope restriction:** this theorem assumes the assembled eta-local structure
instead of deriving it from SAL. Documented in
`docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`; the missing
construction is tracked by issue #823.

**Local fix (PSD rank-one criterion):** it uses the positive-semidefinite
replacement for the matrix step in Lemma C.5, documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`. -/
theorem simple_mpdo_rfp_chain_of_sal_zcl_and_etaLocalStructure_of_posSemidef
    {K : MPOTensor d D} {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hPSD : T.PosSemidef)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (hEta : EtaLocalStructureData K) (hZCL : IsZCL K) :
    IsGSNNCHWithZCL K ∧ Nonempty (FusionIsometryData K 2) ∧
      IsRFP_MPDO_via_fusion K :=
  simple_mpdo_rfp_chain_of_data
    (SimpleMPDOBlockedRFPData.ofSALZCLAndEtaLocalStructureOfPosSemidef
      rhoABC hRhoDM hSSA T hPrimitive hPSD hTrace hTraceConst hEta hZCL)

end MPOTensor
