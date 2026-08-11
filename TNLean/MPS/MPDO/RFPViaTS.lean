/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.Algebra.TracePairing
import TNLean.Channel.KrausCPTP
import TNLean.MPS.MPDO.PhysicalClosure
import TNLean.MPS.MPDO.ZCL

/-!
# MPDO renormalization fixed point via trace-preserving CP maps (Definition 4.1)

This file states the source-faithful renormalization-fixed-point notion for
matrix product density operators, following
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Definition 4.1
(paper label RFPMixedTS, line 657, figures MPDO_XM, MPDO_XMM,
MPDO_TandS).

In the paper, a tensor `M` in canonical form generating MPDOs is a renormalization
fixed point when there exist two trace-preserving completely positive maps `T` and
`S` on the physical indices intertwining the one-site and two-site physical
operators obtained by contracting an arbitrary virtual operator into the tensor
ring:

* `S[M₂(X)] = M₁(X)`  (paper label eq:Smap);
* `T[M₁(X)] = M₂(X)`  (paper label eq:Tmap),

for all virtual operators `X`. Here, with the physical legs left open,

* `(M₁ X) i j = tr(M^{ij} X)` is the one-site physical operator (figure
  MPDO_XM), and
* `(M₂ X) (i₁,i₂) (j₁,j₂) = tr(M^{i₁j₁} M^{i₂j₂} X)` is the two-site physical
  operator (figure MPDO_XMM).

Following the convention used for `MPOTensor.IsZCL`,
`IsRFPViaTS` is stated on a bare `MPOTensor`; the source's standing hypotheses
(canonical form, generating an MPDO) are carried at theorem level rather than in
the predicate.

## Main definitions

* `IsKrausCPTP`: the rectangular Kraus-form predicate for trace-preserving
  completely positive maps used in Definition 4.1.
* `MPOTensor.IsRFPViaTS`: Definition 4.1, the tp-CP-map renormalization
  fixed point.
* `MPOTensor.physTraceTransfer_sq_of_isRFPViaTS`: Definition 4.1 implies
  idempotence of the physical-trace transfer.
* `MPOTensor.isSourceZCL_of_isRFPViaTS`: the resulting source
  zero-correlation-length statement when the physical-trace transfer is nonzero.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Definition 4.1
  (line 657)
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-! ### MPDO renormalization fixed point (Definition 4.1) -/

/-- `IsRFPViaTS M` is the source's MPDO **renormalization fixed point** of
arXiv:1606.00608 Definition 4.1 (paper label RFPMixedTS, line 657): there exist
two trace-preserving completely positive maps `S` and `T` on the physical indices
intertwining the one-site and two-site physical operators, namely

* `S[M₂(X)] = M₁(X)` for all `X`  (paper label eq:Smap), and
* `T[M₁(X)] = M₂(X)` for all `X`  (paper label eq:Tmap).

This is the source's tp-CP-map renormalization fixed point. It is *distinct* from
`MPOTensor.IsZCL`, the doubled-index transfer-map idempotence
condition on the doubled-index completely positive map. Theorem
`physTraceTransfer_sq_of_isRFPViaTS` proves the source zero-correlation-length
identity for the physical-trace transfer. It does not identify this identity
with doubled-index transfer-map idempotence. -/
def IsRFPViaTS (M : MPOTensor d D) : Prop :=
  ∃ (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
    IsKrausCPTP S ∧ IsKrausCPTP T ∧
    (∀ X, S (physClose2 M X) = physClose1 M X) ∧
    (∀ X, T (physClose1 M X) = physClose2 M X)

/-- Definition 4.1 implies literal idempotence of the physical-trace transfer.

This is the zero-correlation-length part of arXiv:1606.00608, lines 1333--1340:
trace preservation of the map from one site to
two sites identifies the traces of the one-site and two-site physical closures
for every virtual boundary matrix. -/
theorem physTraceTransfer_sq_of_isRFPViaTS (M : MPOTensor d D) (h : IsRFPViaTS M) :
    physTraceTransfer M * physTraceTransfer M = physTraceTransfer M := by
  obtain ⟨_, T, _, hT, _, hT_close⟩ := h
  apply sub_eq_zero.mp
  apply (Matrix.trace_mul_right_eq_zero_iff _).mp
  intro X
  rw [Matrix.sub_mul, Matrix.trace_sub, ← trace_physClose2_eq M X,
    ← trace_physClose1_eq M X, ← hT_close X, hT.trace_map, sub_self]

/-- Definition 4.1 gives source zero correlation length when the physical-trace
transfer is nonzero.

**Scope restriction (nonzero transfer):** The source assumes that the tensor is
in canonical form and generates normalized density operators. The bare
predicate `IsRFPViaTS` does not include these standing hypotheses, so the
nonzero transfer is stated explicitly. This restriction is documented in
`docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.

Source: arXiv:1606.00608, lines 1333--1340. -/
theorem isSourceZCL_of_isRFPViaTS (M : MPOTensor d D) (h : IsRFPViaTS M)
    (h0 : physTraceTransfer M ≠ 0) : IsSourceZCL M :=
  isSourceZCL_of_physTraceTransfer_sq M h0 (physTraceTransfer_sq_of_isRFPViaTS M h)

@[deprecated _root_.finThreeArrowEquiv (since := "2026-07-13")]
alias finThreeArrowEquiv := _root_.finThreeArrowEquiv

end MPOTensor
