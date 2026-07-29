/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.TransferMatrix
import TNLean.MPS.RFP.Defs

/-!
# Limits of the pure-state renormalization flow

Blocking two sites squares the transfer map of a matrix product tensor. The
corresponding dyadic renormalization orbit is therefore represented by the
matrices \(\widehat E_B^{2^n}\). This file defines when a tensor appears as a
limit of such an orbit and proves the limit characterization in CPSV16
Theorem 3.1.

The initial physical dimension is allowed to vary, while the bond dimension
stays fixed. The neighboring source sentence asserting convergence for all
canonical forms is separate and is not claimed here.

## Main results

* `isIdempotentElem_of_tendsto_pow_two_pow`: a limit of dyadic powers in a
  Hausdorff topological monoid is idempotent.
* `MPSTensor.AppearsAsRenormalizationFlowLimit`: appearance as a limit of a
  dyadic transfer-matrix orbit.
* `MPSTensor.appearsAsRenormalizationFlowLimit_iff_hasPhysicalBlockingIsometry`:
  the flow-limit form of CPSV16 Theorem 3.1.

## References

* [Cirac--Pérez-García--Schuch--Verstraete 2017], arXiv:1606.00608,
  Theorem 3.1, lines 382--405, and its proof at lines 1205--1209.
-/

open Filter
open scoped Topology

noncomputable section

/-- A limit of the dyadic powers \(x^{2^n}\) is idempotent.

Indeed, the shifted sequence has the same limit, while
\(x^{2^{n+1}} = x^{2^n}x^{2^n}\). Continuity of multiplication and uniqueness
of limits give the result.

Source: arXiv:1606.00608, proof of Theorem 3.1, lines 1205--1209. -/
theorem isIdempotentElem_of_tendsto_pow_two_pow
    {R : Type*} [TopologicalSpace R] [Monoid R] [ContinuousMul R] [T2Space R]
    (x p : R)
    (h : Tendsto (fun n : ℕ ↦ x ^ (2 ^ n : ℕ)) atTop (𝓝 p)) :
    IsIdempotentElem p := by
  have hmul :
      Tendsto (fun n : ℕ ↦ x ^ (2 ^ n : ℕ) * x ^ (2 ^ n : ℕ))
        atTop (𝓝 (p * p)) :=
    h.mul h
  have hshift :
      Tendsto (fun n : ℕ ↦ x ^ (2 ^ (n + 1) : ℕ)) atTop (𝓝 p) :=
    (tendsto_add_atTop_iff_nat 1).2 h
  have heq : (fun n : ℕ ↦ x ^ (2 ^ (n + 1) : ℕ)) =
      fun n : ℕ ↦ x ^ (2 ^ n : ℕ) * x ^ (2 ^ n : ℕ) := by
    funext n
    rw [pow_succ, Nat.mul_two, pow_add]
  rw [heq] at hshift
  exact tendsto_nhds_unique hmul hshift

namespace MPSTensor

variable {d D : ℕ}

/-- A tensor appears as a limit of the renormalization flow if its transfer
matrix is the limit of the dyadic transfer-matrix powers of a tensor with the
same bond dimension.

The initial physical dimension is existentially quantified because blocking
changes the physical dimension. The fixed bond dimension puts the entire orbit
in one finite-dimensional matrix space.

Source: arXiv:1606.00608, Theorem 3.1, lines 382--405, and its proof at
lines 1205--1209. -/
def AppearsAsRenormalizationFlowLimit (A : MPSTensor d D) : Prop :=
  ∃ d₀ : ℕ, ∃ B : MPSTensor d₀ D,
    Tendsto (fun n : ℕ ↦ (transferMatrix (transferMap B)) ^ (2 ^ n : ℕ))
      atTop (𝓝 (transferMatrix (transferMap A)))

/-- A tensor which appears as a renormalization-flow limit has an idempotent
transfer map.

Source: arXiv:1606.00608, proof of Theorem 3.1, lines 1205--1209. -/
theorem IsTransferIdempotent.of_appearsAsRenormalizationFlowLimit
    {A : MPSTensor d D} (hA : AppearsAsRenormalizationFlowLimit A) :
    IsTransferIdempotent A := by
  obtain ⟨d₀, B, hlim⟩ := hA
  have hIdem : IsIdempotentElem (transferMatrix (transferMap A)) :=
    isIdempotentElem_of_tendsto_pow_two_pow
      (transferMatrix (transferMap B)) (transferMatrix (transferMap A)) hlim
  change transferMatrix (transferMap A) * transferMatrix (transferMap A) =
    transferMatrix (transferMap A) at hIdem
  apply transferMatrix_injective
  simpa only [transferMatrix_comp] using hIdem

/-- An idempotent transfer map gives a constant dyadic renormalization orbit.

Source: arXiv:1606.00608, proof of Theorem 3.1, lines 1205--1209. -/
theorem IsTransferIdempotent.appearsAsRenormalizationFlowLimit
    {A : MPSTensor d D} (hA : IsTransferIdempotent A) :
    AppearsAsRenormalizationFlowLimit A := by
  refine ⟨d, A, ?_⟩
  have hIdem : IsIdempotentElem (transferMatrix (transferMap A)) := by
    change transferMatrix (transferMap A) * transferMatrix (transferMap A) =
      transferMatrix (transferMap A)
    rw [← transferMatrix_comp]
    exact congrArg transferMatrix hA
  apply tendsto_const_nhds.congr'
  filter_upwards [] with n
  exact (hIdem.pow_eq (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).symm

/-- Appearance as a dyadic renormalization-flow limit is equivalent to
transfer-map idempotence.

Source: arXiv:1606.00608, Theorem 3.1 and its proof, lines 398--405 and
1205--1209. -/
theorem appearsAsRenormalizationFlowLimit_iff_isTransferIdempotent
    (A : MPSTensor d D) :
    AppearsAsRenormalizationFlowLimit A ↔ IsTransferIdempotent A :=
  ⟨IsTransferIdempotent.of_appearsAsRenormalizationFlowLimit,
    IsTransferIdempotent.appearsAsRenormalizationFlowLimit⟩

/-- **CPSV16 Theorem 3.1.** A tensor appears as a limit of the renormalization
flow if and only if two physical sites can be blocked into one through a
physical isometry.

Source: arXiv:1606.00608, Theorem 3.1, equation `AA=A`, lines 398--405, and
the completely positive map argument at lines 1205--1209.

**Local fix (renormalization-flow indices):** The displayed source equation
sums the free indices `i₁, i₂` and writes an undefined output index `j₁`. The
renormalization equation at lines 389--394, the source diagrams, and the
Appendix argument give the well-formed equation used here. This correction
changes no hypothesis or conclusion; see
`docs/paper-gaps/cpsv16_renormalization_flow_index_typo.tex`. -/
theorem appearsAsRenormalizationFlowLimit_iff_hasPhysicalBlockingIsometry
    (A : MPSTensor d D) :
    AppearsAsRenormalizationFlowLimit A ↔ HasPhysicalBlockingIsometry A := by
  rw [appearsAsRenormalizationFlowLimit_iff_isTransferIdempotent,
    isTransferIdempotent_iff_hasPhysicalBlockingIsometry]

end MPSTensor
