/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Core.Transfer
import TNLean.MPS.BNT.Construction
import TNLean.Spectral.SpectralGap
import TNLean.Spectral.QuantitativeGap
import TNLean.MPS.RFP.Defs

/-!
# RG flow convergence for canonical-form MPS tensors

This file proves the convergence result for the renormalization-group (RG) flow
applied to MPS tensors in canonical form. The proof follows the spectral-gap
argument from CPGSV21, Section 2.3 and Appendix B of arXiv:1606.00608
(Cirac–Pérez-García–Schuch–Verstraete).

For a CF tensor, the transfer matrix decomposes as
`E' = ⊕_{j,j'} μ_{j,q} μ̄_{j',q'} E_{j,j'}`.
Off-diagonal blocks `E_{j,j'}` (j ≠ j') have spectral radius < 1 and decay.
Diagonal blocks `E_{j,j}` have a unique magnitude-1 eigenvalue. So `E'^N`
converges to an idempotent (the RFP).

## Main result

* `rg_flow_converges_of_cf`: the sequence of blocked transfer maps converges
  pointwise to an idempotent for any canonical-form tensor. The proof uses the
  exponential convergence bound from `QuantitativeGap` to squeeze the difference
  `E^n X - P X` to zero, then composes with the subsequence `2^n → ∞`.

## References

* [CPGSV21] Cirac, Pérez-García, Schuch, Verstraete,
  *Matrix Product States and Projected Entangled Pair States*,
  Rev. Mod. Phys. 93 (2021), arXiv:2011.12127. Sec. 2.3 (correlations and transfer matrix).
* [CPSV17] Cirac, Pérez-García, Schuch, Verstraete,
  *Completeness of the set of Matrix Product States*,
  arXiv:1606.00608. Appendix B (RFP as idempotent limit).
  Source: `Papers/1606.00608/`
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- **Appendix B** (arXiv:1606.00608): For a tensor in canonical form, the
iterated blocking `E^{2^n}` converges to an idempotent transfer map.

The convergence is entry-wise on the `D² × D²` transfer matrix space:
`∀ ρ, (E^{2^n}) ρ → E_∞ ρ` where `E_∞ ∘ E_∞ = E_∞`.

The proof uses the spectral gap: for each block `k`, injectivity implies
primitivity of the transfer map, giving `E^n = P + N^n` where `P` is the
fixed-point projection (idempotent) and `N = E - P` has spectral radius `< 1`.
The exponential bound `‖E^n X - P X‖ ≤ C(1-δ)^n ‖X‖` from
`exponential_convergence_of_primitive` then gives pointwise convergence
`E^n X → P X`, and composing with `2^n → ∞` yields the result. -/
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
  -- Obtain the unique positive-definite fixed point (quantum Perron-Frobenius).
  obtain ⟨ρ₀, hufp⟩ := injective_transfer_unique_fixed_point' (A k) hInj hNorm
  -- Handle the degenerate dim k = 0 case (0×0 matrices are a subsingleton).
  by_cases hDk : dim k = 0
  · haveI : IsEmpty (Fin (dim k)) := by rw [hDk]; exact Fin.isEmpty
    refine ⟨0, LinearMap.ext fun x => Subsingleton.elim _ _, fun x => ?_⟩
    exact tendsto_const_nhds.congr fun _ => Subsingleton.elim _ _
  · -- Main case: dim k ≥ 1.
    haveI : NeZero (dim k) := ⟨hDk⟩
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
