/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.Algebra.TracePairing
import TNLean.Channel.KrausCPTP
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
* `MPOTensor.physCloseN`: the length-$N$ physical operator as a linear map in
  the virtual operator $X$.
* `MPOTensor.physClose1`, `MPOTensor.physClose2`, `MPOTensor.physClose3`: the
  one-site, two-site, and three-site specializations.
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

/-! ### Physical operators of arbitrary length -/

/-- The length-$N$ physical operator obtained by contracting an arbitrary
virtual operator $X$ into a chain of $N$ copies of an MPO tensor while leaving
the physical legs open:

For configurations $\sigma$ and $\tau$, its coefficient is
$\operatorname{tr}(M^{\sigma_0\tau_0}\cdots
M^{\sigma_{N-1}\tau_{N-1}}X)$.

The displayed order chooses the cut of the cyclic virtual contraction just
before the first site, so that $X$ follows the last site. For $N=1,2$, this is
the physical closure constructed in arXiv:1606.00608, lines 638--654 and used
in Definition 4.1, line 657. When $M=\mathcal K$, the cases $N=2,3$ are the
operators $\mathcal K_2(X)$ and $\mathcal K_3(X)$ in Proposition C.7,
lines 1510--1516. -/
noncomputable def physCloseN (M : MPOTensor d D) (N : ℕ) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ where
  toFun X := Matrix.of fun σ τ =>
    Matrix.trace (evalWord M (List.ofFn σ) (List.ofFn τ) * X)
  map_add' X Y := by
    ext σ τ
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext σ τ
    simp [Matrix.trace_smul]

@[simp] lemma physCloseN_apply (M : MPOTensor d D) (N : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (σ τ : Fin N → Fin d) :
    physCloseN M N X σ τ =
      Matrix.trace (evalWord M (List.ofFn σ) (List.ofFn τ) * X) :=
  rfl

/-- Closing the virtual boundary by the identity matrix gives the periodic MPO
operator.

Source: arXiv:1606.00608, lines 638--654 and Definition 4.1. -/
theorem physCloseN_identity_eq_mpo (M : MPOTensor d D) (N : ℕ) :
    physCloseN M N (1 : Matrix (Fin D) (Fin D) ℂ) = mpo M N := by
  ext σ τ
  simp [mpoMatrixEntry]

/-- The general length-three physical closure has the coefficient formula for
$M_3(X)$. When $M=\mathcal K$, it is the operator $\mathcal K_3(X)$ in
arXiv:1606.00608, Proposition C.7, lines 1510--1516. -/
lemma physCloseN_three_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) (σ τ : Fin 3 → Fin d) :
    physCloseN M 3 X σ τ =
      Matrix.trace
        (M (σ 0) (τ 0) * M (σ 1) (τ 1) * M (σ 2) (τ 2) * X) := by
  simp [physCloseN, List.ofFn_succ, evalWord_cons, Matrix.mul_assoc]

/-! ### The one-site physical operator -/

/-- The **one-site physical operator** as a linear map in the virtual operator
`X`: contract `X : D × D` into a single copy of the tensor with the physical legs
open, giving `(physClose1 M X) i j = tr(M^{ij} X)` (figure MPDO_XM of
arXiv:1606.00608). -/
noncomputable def physClose1 (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := Matrix.of fun i j => Matrix.trace (M i j * X)
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]

@[simp] lemma physClose1_apply (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin d) : physClose1 M X i j = Matrix.trace (M i j * X) := rfl

/-- The trace of the one-site physical closure is the trace pairing with the
physical-trace transfer.

Source: arXiv:1606.00608, Definition 4.1, line 657, and lines 1333--1340. -/
theorem trace_physClose1_eq (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (physClose1 M X) = Matrix.trace (physTraceTransfer M * X) := by
  rw [physTraceTransfer, Finset.sum_mul, Matrix.trace_sum]
  rfl

/-- Under the canonical equivalence between one-site configurations and
physical indices, the length-one closure is `physClose1`. This is the one-site
operator in arXiv:1606.00608, Definition 4.1, line 657 and figure MPDO_XM. -/
theorem physCloseN_one_eq_physClose1 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (Equiv.funUnique (Fin 1) (Fin d))
        (Equiv.funUnique (Fin 1) (Fin d))).toLinearMap ∘ₗ physCloseN M 1 =
      physClose1 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv]

/-! ### The two-site physical operator -/

/-- The **two-site physical operator** as a linear map in the virtual operator
`X`: contract `X : D × D` into two copies of the tensor with all four physical
legs open, giving `(physClose2 M X) (i₁,i₂) (j₁,j₂) = tr(M^{i₁j₁} M^{i₂j₂} X)`
(figure MPDO_XMM of arXiv:1606.00608). -/
noncomputable def physClose2 (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ where
  toFun X := Matrix.of fun i j => Matrix.trace (M i.1 j.1 * M i.2 j.2 * X)
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]

@[simp] lemma physClose2_apply (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin d × Fin d) :
    physClose2 M X i j = Matrix.trace (M i.1 j.1 * M i.2 j.2 * X) := rfl

/-- The trace of the two-site physical closure is the trace pairing with the
square of the physical-trace transfer.

Source: arXiv:1606.00608, Definition 4.1, line 657, and lines 1333--1340. -/
theorem trace_physClose2_eq (M : MPOTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    Matrix.trace (physClose2 M X) =
      Matrix.trace (physTraceTransfer M * physTraceTransfer M * X) := by
  change (∑ p : Fin d × Fin d, Matrix.trace (M p.1 p.1 * M p.2 p.2 * X)) = _
  rw [Fintype.sum_prod_type]
  simp only [physTraceTransfer, Finset.sum_mul, Matrix.mul_sum, Matrix.trace_sum]

/-- Under the canonical equivalence between two-site configurations and pairs
of physical indices, the length-two closure is `physClose2`. This is the
two-site operator constructed in arXiv:1606.00608, lines 638--654 and used in
Definition 4.1, line 657. When $M=\mathcal K$, it is $\mathcal K_2(X)$ in
Proposition C.7, lines 1510--1516. -/
theorem physCloseN_two_eq_physClose2 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d))).toLinearMap ∘ₗ physCloseN M 2 =
      physClose2 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, finTwoArrowEquiv_symm_apply]

/-! ### The three-site physical operator -/

/-- The **three-site physical operator** as a linear map in the virtual operator
$X$. Its physical indices are right-associated as
$\operatorname{Fin}(d) \times (\operatorname{Fin}(d) \times \operatorname{Fin}(d))$,
and its coefficients are
\[
  M_3(X)_{(i_0,(i_1,i_2)),(j_0,(j_1,j_2))}
  = \operatorname{tr}(M^{i_0j_0}M^{i_1j_1}M^{i_2j_2}X).
\]

When $M=\mathcal K$, this is the operator $\mathcal K_3(X)$ of
arXiv:1606.00608, Proposition C.7, lines 1510--1516. -/
noncomputable def physClose3 (M : MPOTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ]
      Matrix (Fin d × (Fin d × Fin d)) (Fin d × (Fin d × Fin d)) ℂ where
  toFun X := Matrix.of fun i j =>
    Matrix.trace (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2 j.2.2 * X)
  map_add' X Y := by
    ext i j
    simp [Matrix.mul_add, Matrix.trace_add]
  map_smul' c X := by
    ext i j
    simp [Matrix.trace_smul]

/-- Coefficient formula for the right-associated three-site physical closure.
For $M=\mathcal K$, this is $\mathcal K_3(X)$ in arXiv:1606.00608,
Proposition C.7, lines 1510--1516. -/
@[simp] lemma physClose3_apply (M : MPOTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ)
    (i j : Fin d × (Fin d × Fin d)) :
    physClose3 M X i j =
      Matrix.trace (M i.1 j.1 * M i.2.1 j.2.1 * M i.2.2 j.2.2 * X) :=
  rfl

/-- Under the canonical right-associated identification of three-site
configurations with triples of physical indices, the general length-three
closure is `physClose3`. For $M=\mathcal K$, this identifies the two forms of
$\mathcal K_3(X)$ in arXiv:1606.00608, Proposition C.7, lines 1510--1516. -/
theorem physCloseN_three_eq_physClose3 (M : MPOTensor d D) :
    (Matrix.reindexLinearEquiv ℂ ℂ (_root_.finThreeArrowEquiv (Fin d))
        (_root_.finThreeArrowEquiv (Fin d))).toLinearMap ∘ₗ physCloseN M 3 =
      physClose3 M := by
  ext X i j
  simp [Matrix.coe_reindexLinearEquiv, Matrix.mul_assoc]

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
