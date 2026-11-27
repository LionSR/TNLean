/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BNT.Construction
import TNLean.MPS.Transfer.Spectrum.QuantitativeGap
import QICLean.Channel.TransferMatrix.Basic
import TNLean.MPS.Transfer.RenormalizationFixedPoint.Defs
import QICLean.Analysis.Topology.NewtonIdempotent

/-!
# Transfer-map convergence for primitive canonical-form blocks

This file proves convergence of the transfer-map powers for each primitive block
in an auxiliary canonical-form family. The proof follows the primitive-block
part of the transfer-map gap argument from arXiv:1606.00608, Appendix B,
lines 1211--1244; see also the transfer-matrix and RGFP discussion in
arXiv:2011.12127, lines 433--442 and 870--892.

For one primitive block, the transfer map has a unique peripheral eigenvalue
and its powers converge to the fixed-point projection. This does not imply
convergence for the full weighted repeated-copy assembly: relative phases can
oscillate under repeated squaring. That obstruction is formalized in
`cubePhaseTensor_not_tendsto_dyadic_transferMap`.

## Main result

* `rg_flow_converges_of_isInjective`: for an injective left-canonical tensor
  (one block of a canonical form), the dyadic transfer-map powers converge
  pointwise to an idempotent. The proof uses the exponential transfer-map gap bound to
  squeeze the difference `E^n X - P X` to zero, then composes with the
  subsequence `2^n → ∞`.

## References

* [CPGSV21] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
  Lines 433--442 (transfer matrix and correlations) and lines 870--892
  (renormalization fixed points for MPS).
  Source: `Papers/2011.12127/`
* [CPSV16] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product Density Operators: Renormalization Fixed Points
  and Boundary Theories*, arXiv:1606.00608.
  Appendix B, lines 1211--1244 (the printed canonical-form convergence
  argument) and lines 1264--1268 (finite power-sum nonvanishing estimate).
  Source: `Papers/1606.00608/`

## Limits of the pure-state renormalization flow

Blocking two sites squares the transfer map of a matrix product tensor. The
corresponding dyadic renormalization orbit is therefore represented by the
matrices \(\widehat E_B^{2^n}\). This file defines when a tensor appears as a
limit of such an orbit and proves the limit characterization in CPSV16
Theorem 3.1.

The initial physical dimension is allowed to vary, while the bond dimension
stays fixed. The neighboring source sentence asserting convergence for all
canonical forms is separate and is not claimed here.

### Main results

* `isIdempotentElem_of_tendsto_pow_two_pow`: a limit of dyadic powers in a
  Hausdorff topological monoid is idempotent.
* `MPSTensor.AppearsAsRenormalizationFlowLimit`: appearance as a limit of a
  dyadic transfer-matrix orbit.
* `MPSTensor.appearsAsRenormalizationFlowLimit_iff_hasPhysicalBlockingIsometry`:
  the flow-limit form of CPSV16 Theorem 3.1.

### References

* [Cirac--Pérez-García--Schuch--Verstraete 2017], arXiv:1606.00608,
  Theorem 3.1, lines 382--405, and its proof at lines 1205--1209.
-/

section

open scoped Matrix ComplexOrder Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- For an injective left-canonical tensor, the iterated transfer map `E^{2^n}` converges to an
idempotent.

The convergence is pointwise on the matrix space:
`∀ ρ, (E^{2^n}) ρ → E_∞ ρ` where `E_∞ ∘ E_∞ = E_∞`.

The proof uses the transfer-map gap: injectivity implies primitivity of the transfer map. The
exponential bound `‖E^n X - P X‖ ≤ C(1-δ)^n ‖X‖` from
`exponential_convergence_of_primitive` then gives pointwise convergence
`E^n X → P X`, and composing with `2^n → ∞` yields the result.

**Scope restriction (CPSV16 Appendix B):** This is the primitive single-block
part of the argument at arXiv:1606.00608, lines 1211--1244, applied to one block of a
canonical form, not the printed full weighted canonical-form convergence assertion. The latter
is refuted by relative-phase oscillation; see
`docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`. -/
theorem rg_flow_converges_of_isInjective [NeZero D] (A : MPSTensor d D)
    (hInj : Kraus.IsInjective A) (hNorm : ∑ i : Fin d, (A i)ᴴ * (A i) = 1) :
    ∃ (E_infty : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ),
      E_infty ∘ₗ E_infty = E_infty ∧
      ∀ ρ : Matrix (Fin D) (Fin D) ℂ,
        Filter.Tendsto
          (fun n : ℕ => ((Kraus.transferMap A ^ (2 ^ n : ℕ) : _) ρ))
          Filter.atTop
          (nhds (E_infty ρ)) := by
  -- Obtain the unique positive-definite fixed point (quantum Perron-Frobenius).
  obtain ⟨ρ₀, hufp⟩ := Kraus.injective_transfer_unique_fixed_point' A hInj hNorm
  have htr : Matrix.trace ρ₀ ≠ 0 := ne_of_gt hufp.pos_def.trace_pos
  -- The witness is the rank-one fixed-point projection P(X) = (tr X / tr ρ₀) • ρ₀.
  refine ⟨fixedPointProj ρ₀ htr,
    fixedPointProj_mul_self (ρ := ρ₀) (htr := htr), fun X => ?_⟩
  -- Exponential convergence bound from QuantitativeGap.
  obtain ⟨C, δ, hC, hδ, hδ1, hbound⟩ :=
    exponential_convergence_of_primitive A hNorm hInj ρ₀ hufp.pos_def hufp.fixed
  -- Step 1: E^n X → P X for all n (not just 2^n).
  have h_allN : Filter.Tendsto (fun n => (Kraus.transferMap A ^ n) X)
      Filter.atTop (nhds (fixedPointProj ρ₀ htr X)) := by
    -- Norm bound: ‖(E^n) X - P X‖ ≤ C · (1-δ)^n · ‖X‖.
    have h_norm_bound : ∀ n, ‖(Kraus.transferMap A ^ n) X - fixedPointProj ρ₀ htr X‖ ≤
        C * (1 - δ) ^ n * ‖X‖ := fun n => by
      simpa [Module.End.pow_apply] using hbound n X
    -- The bounding sequence C · (1-δ)^n · ‖X‖ → 0.
    have h_rate : Filter.Tendsto (fun n => C * (1 - δ) ^ n * ‖X‖)
        Filter.atTop (nhds 0) := by
      have h_pow := tendsto_pow_atTop_nhds_zero_of_lt_one
        (by linarith : (0 : ℝ) ≤ 1 - δ)
        (by linarith : 1 - δ < 1)
      have h_mul := h_pow.const_mul (C * ‖X‖)
      simp only [mul_zero] at h_mul
      exact h_mul.congr fun n => by ring
    -- Squeeze: difference → 0, hence E^n X → P X.
    have h_zero := squeeze_zero_norm h_norm_bound h_rate
    have h_add := h_zero.add (tendsto_const_nhds (x := fixedPointProj ρ₀ htr X))
    simp only [sub_add_cancel, zero_add] at h_add
    exact h_add
  -- Step 2: compose with the subsequence 2^n → ∞.
  exact h_allN.comp
    (tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℕ) < 2 by norm_num))

end MPSTensor

end

section

open Filter
open scoped Topology

noncomputable section

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
    Tendsto (fun n : ℕ ↦ (transferMatrix (Kraus.transferMap B)) ^ (2 ^ n : ℕ))
      atTop (𝓝 (transferMatrix (Kraus.transferMap A)))

/-- A tensor which appears as a renormalization-flow limit has an idempotent
transfer map.

Source: arXiv:1606.00608, proof of Theorem 3.1, lines 1205--1209. -/
theorem IsTransferIdempotent.of_appearsAsRenormalizationFlowLimit
    {A : MPSTensor d D} (hA : AppearsAsRenormalizationFlowLimit A) :
    IsTransferIdempotent A := by
  obtain ⟨d₀, B, hlim⟩ := hA
  have hIdem : IsIdempotentElem (transferMatrix (Kraus.transferMap A)) :=
    isIdempotentElem_of_tendsto_pow_two_pow
      (transferMatrix (Kraus.transferMap B)) (transferMatrix (Kraus.transferMap A)) hlim
  change transferMatrix (Kraus.transferMap A) * transferMatrix (Kraus.transferMap A) =
    transferMatrix (Kraus.transferMap A) at hIdem
  apply transferMatrix_injective
  simpa only [transferMatrix_comp] using hIdem

/-- An idempotent transfer map gives a constant dyadic renormalization orbit.

Source: arXiv:1606.00608, proof of Theorem 3.1, lines 1205--1209. -/
theorem IsTransferIdempotent.appearsAsRenormalizationFlowLimit
    {A : MPSTensor d D} (hA : IsTransferIdempotent A) :
    AppearsAsRenormalizationFlowLimit A := by
  refine ⟨d, A, ?_⟩
  have hIdem : IsIdempotentElem (transferMatrix (Kraus.transferMap A)) := by
    change transferMatrix (Kraus.transferMap A) * transferMatrix (Kraus.transferMap A) =
      transferMatrix (Kraus.transferMap A)
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
end

end
