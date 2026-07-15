/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.SimpleLocalStructure

/-!
# Local structure for simple MPDOs

This file records the local consequences of arXiv:1606.00608, Appendix C.2,
Lemmas C.2, C.4, and C.5.  The structure consists of a normalized three-site
state satisfying equality in strong subadditivity, its quantum-Markov
decomposition, and a primitive trace matrix with a rank-one factorization.

The source's rank-one argument for the trace matrix is not valid without a
further hypothesis.  Accordingly, the constructors retained here use either
positive semidefiniteness of the trace matrix or linear independence in the
sector-pairing construction.

## Main declarations

* `MPOTensor.SimpleMPDOLocalStructureData`
* `MPOTensor.SimpleMPDOLocalStructureData.ofSALZCLOfPosSemidef`
* `MPOTensor.SimpleMPDOLocalStructureData.ofSALZCLOfPairingIdempotent`

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, Lemmas C.2, C.4, and C.5
-/

open scoped Matrix ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The local simple-MPDO structure isolated by Appendix C.2, Lemmas C.2, C.4,
and C.5.

It consists of a normalized three-site reduced state satisfying equality in
strong subadditivity, the resulting local `η`-structure, and a primitive real
matrix `T` satisfying trace normalization, constancy of positive-power traces,
and a rank-one factorization.

The structure is independent of a particular MPO tensor. Lemma C.2 supplies
the Markov decomposition and Lemma C.4 supplies the primitive trace matrix.
The two constructors below obtain the rank-one conclusion from corrected
sufficient hypotheses for the matrix step in Lemma C.5. -/
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

private def ofData
    {dA dB dC n : ℕ}
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (hPrimitive : Matrix.IsPrimitive T)
    (hTrace : Matrix.trace T = 1)
    (hTraceConst : Matrix.TracePowersConstant T)
    (rankOne : ∃ a b : Fin n → ℝ, T = Matrix.vecMulVec a b ∧ a ⬝ᵥ b = 1) :
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
  rankOne := rankOne

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
    SimpleMPDOLocalStructureData :=
  ofData rhoABC hRhoDM hSSA T hPrimitive hTrace hTraceConst
    (sal_zcl_implies_rank_one_T_of_posSemidef T hPrimitive hPSD hTrace hTraceConst)

/-- Construct the local simple-MPDO structure from the Lemma C.2 and C.4
hypotheses and the pairing-idempotence Lemma C.5 rank-one criterion: the
sector tensors of arXiv:1606.00608, Appendix C.2, satisfy the displayed
zero-correlation-length identity (lines 1490--1493), giving the constant
trace powers of the sector trace matrix unconditionally; linear independence
of the closed sector tensors additionally turns the identity into idempotence
of that matrix, from which the rank-one factorization follows.

Source: arXiv:1606.00608, Appendix C.2, Lemmas C.4 and C.5, lines 1406--1499.

**Scope restriction (linear independence):** the source lemma neither assumes
nor derives linear independence of the sector tensors; documented in
`docs/paper-gaps/cpgsv17_pf_rank_one.tex`.  The hypothesis `hl` is discharged
by `SectorPairingData.linearIndependent_l` once each sector tensor lies in the
corresponding member of an independent family of subspaces. -/
def ofSALZCLOfPairingIdempotent
    {dA dB dC n : ℕ} {V : Type*} [AddCommGroup V] [Module ℝ V]
    (rhoABC : Matrix (Fin dA × Fin dB × Fin dC) (Fin dA × Fin dB × Fin dC) ℂ)
    (hRhoDM : rhoABC.PosSemidef ∧ rhoABC.trace = 1)
    (hSSA : IsSSAEquality rhoABC hRhoDM.1.isHermitian)
    (T : Matrix (Fin n) (Fin n) ℝ)
    (data : SectorPairingData T V)
    (hPrimitive : Matrix.IsPrimitive T)
    (hl : LinearIndependent ℝ data.l)
    (hTrace : Matrix.trace T = 1) :
    SimpleMPDOLocalStructureData :=
  ofData rhoABC hRhoDM hSSA T hPrimitive hTrace data.tracePowersConstant
    (sal_zcl_implies_rank_one_T_of_pairing_idempotent T data hl hTrace)

end SimpleMPDOLocalStructureData
end MPOTensor
