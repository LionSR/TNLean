/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PiAlgebra.CanonicalFormSepAux
import TNLean.Spectral.QuantitativeGap

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

* `rg_flow_converges_of_cf`: for each primitive block in an auxiliary
  canonical-form family, the dyadic transfer-map powers converge pointwise to
  an idempotent. The proof uses the exponential transfer-map gap bound to
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
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- For each primitive block in an auxiliary canonical-form family, the
iterated transfer map `E^{2^n}` converges to an idempotent.

The convergence is pointwise on the block's matrix space:
`∀ ρ, (E^{2^n}) ρ → E_∞ ρ` where `E_∞ ∘ E_∞ = E_∞`.

The proof uses the transfer-map gap: injectivity of block `k` implies
primitivity of its transfer map. The exponential bound
`‖E^n X - P X‖ ≤ C(1-δ)^n ‖X‖` from
`exponential_convergence_of_primitive` then gives pointwise convergence
`E^n X → P X`, and composing with `2^n → ∞` yields the result.

**Scope restriction (CPSV16 Appendix B):** This is the primitive single-block
part of the argument at arXiv:1606.00608, lines 1211--1244, not the printed
full weighted canonical-form convergence assertion. The latter is refuted by
relative-phase oscillation; see
`docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`. -/
theorem rg_flow_converges_of_cf {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor d (dim k))
    (hCF : IsCanonicalForm μ A) (k : Fin r) :
    ∃ (E_infty : Matrix (Fin (dim k)) (Fin (dim k)) ℂ →ₗ[ℂ]
                 Matrix (Fin (dim k)) (Fin (dim k)) ℂ),
      E_infty ∘ₗ E_infty = E_infty ∧
      ∀ ρ : Matrix (Fin (dim k)) (Fin (dim k)) ℂ,
        Filter.Tendsto
          (fun n : ℕ => ((transferMap (A k) ^ (2 ^ n : ℕ) : _) ρ))
          Filter.atTop
          (nhds (E_infty ρ)) := by
  have hInj := hCF.block_injective k
  have hNorm := hCF.leftCanonical k
  letI : NeZero (dim k) := ⟨Nat.ne_of_gt (hCF.dim_pos k)⟩
  -- Obtain the unique positive-definite fixed point (quantum Perron-Frobenius).
  obtain ⟨ρ₀, hufp⟩ := injective_transfer_unique_fixed_point' (A k) hInj hNorm
  have htr : Matrix.trace ρ₀ ≠ 0 := ne_of_gt hufp.pos_def.trace_pos
  -- The witness is the rank-one fixed-point projection P(X) = (tr X / tr ρ₀) • ρ₀.
  refine ⟨fixedPointProj ρ₀ htr,
    fixedPointProj_mul_self (ρ := ρ₀) (htr := htr), fun X => ?_⟩
  -- Exponential convergence bound from QuantitativeGap.
  obtain ⟨C, δ, hC, hδ, hδ1, hbound⟩ :=
    exponential_convergence_of_primitive (A k) hNorm hInj ρ₀ hufp.pos_def hufp.fixed
  -- Step 1: E^n X → P X for all n (not just 2^n).
  have h_allN : Filter.Tendsto (fun n => (transferMap (A k) ^ n) X)
      Filter.atTop (nhds (fixedPointProj ρ₀ htr X)) := by
    -- Norm bound: ‖(E^n) X - P X‖ ≤ C · (1-δ)^n · ‖X‖.
    have h_norm_bound : ∀ n, ‖(transferMap (A k) ^ n) X - fixedPointProj ρ₀ htr X‖ ≤
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
