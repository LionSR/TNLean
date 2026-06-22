/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.MPDO.KrausCPTP

/-!
# MPDO renormalization fixed point via trace-preserving CP maps (Definition 4.1)

This file states the source-faithful renormalization-fixed-point notion for
matrix product density operators, following
arXiv:1606.00608 (Cirac–Pérez-García–Schuch–Verstraete), Definition 4.1
(paper label `RFPMixedTS`, line 657, figures `MPDO_XM`, `MPDO_XMM`,
`MPDO_TandS`).

In the paper, a tensor `M` in canonical form generating MPDOs is a renormalization
fixed point when there exist two trace-preserving completely positive maps `T` and
`S` on the physical indices intertwining the one-site and two-site physical
operators obtained by contracting an arbitrary virtual operator into the tensor
ring:

* `S[M₂(X)] = M₁(X)`  (paper label `eq:Smap`);
* `T[M₁(X)] = M₂(X)`  (paper label `eq:Tmap`),

for all virtual operators `X`. Here, with the physical legs left open,

* `(M₁ X) i j = tr(M^{ij} X)` is the one-site physical operator (figure
  `MPDO_XM`), and
* `(M₂ X) (i₁,i₂) (j₁,j₂) = tr(M^{i₁j₁} M^{i₂j₂} X)` is the two-site physical
  operator (figure `MPDO_XMM`).

Following the codebase convention (as for `MPOTensor.IsRFP` and `MPOTensor.IsZCL`),
`IsRFPViaTS` is stated on a bare `MPOTensor`; the source's standing hypotheses
(canonical form, generating an MPDO) are carried at theorem level rather than in
the predicate.

## Main definitions

* `IsKrausCPTP`: the rectangular Kraus-form predicate for trace-preserving
  completely positive maps used in Definition 4.1.
* `MPOTensor.physClose1`, `MPOTensor.physClose2`: the one-site and two-site
  physical operators as linear maps in the virtual operator `X`.
* `MPOTensor.IsRFPViaTS`: Definition 4.1, the tp-CP-map renormalization
  fixed point.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608, Definition 4.1
  (line 657)
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-! ### The one-site physical operator -/

/-- The **one-site physical operator** as a linear map in the virtual operator
`X`: contract `X : D × D` into a single copy of the tensor with the physical legs
open, giving `(physClose1 M X) i j = tr(M^{ij} X)` (figure `MPDO_XM` of
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

/-! ### The two-site physical operator -/

/-- The **two-site physical operator** as a linear map in the virtual operator
`X`: contract `X : D × D` into two copies of the tensor with all four physical
legs open, giving `(physClose2 M X) (i₁,i₂) (j₁,j₂) = tr(M^{i₁j₁} M^{i₂j₂} X)`
(figure `MPDO_XMM` of arXiv:1606.00608). -/
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

/-! ### MPDO renormalization fixed point (Definition 4.1) -/

/-- `IsRFPViaTS M` is the source's MPDO **renormalization fixed point** of
arXiv:1606.00608 Definition 4.1 (paper label `RFPMixedTS`, line 657): there exist
two trace-preserving completely positive maps `S` and `T` on the physical indices
intertwining the one-site and two-site physical operators, namely

* `S[M₂(X)] = M₁(X)` for all `X`  (paper label `eq:Smap`), and
* `T[M₁(X)] = M₂(X)` for all `X`  (paper label `eq:Tmap`).

This is the source's tp-CP-map renormalization fixed point. It is *distinct* from
`MPOTensor.IsRFP`, the transfer-map idempotence (zero-correlation-length)
condition: Definition 4.1 is strictly stronger for general MPDO. The implication
`IsRFPViaTS M → IsRFP M` (Theorem 4.9, direction i ⟹ ii) is deferred future
work (#2382, #826). -/
def IsRFPViaTS (M : MPOTensor d D) : Prop :=
  ∃ (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
    IsKrausCPTP S ∧ IsKrausCPTP T ∧
    (∀ X, S (physClose2 M X) = physClose1 M X) ∧
    (∀ X, T (physClose1 M X) = physClose2 M X)

end MPOTensor
