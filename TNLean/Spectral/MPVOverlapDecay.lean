/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Spectral.MPVOverlapTrace
import TNLean.Spectral.SpectralGap

import Mathlib.Topology.Algebra.Star
import Mathlib.Analysis.Matrix.Normed
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

namespace MPSTensor

open scoped Matrix BigOperators ComplexOrder NNReal ENNReal Matrix.Norms.Operator
open Matrix Filter

/-!
# MPV overlap decay

This file proves a literature-standard decay statement for the *MPV overlap*
`mpvOverlap A B N` in the **square bond dimension** case
(cf. PerezGarcia2007 Lemma 5; Wolf Theorem 6.6 for the underlying
spectral-gap theory).

If `A` and `B` are injective, satisfy the trace-preserving normalization
`∑ i, (A i)ᴴ * A i = 1` and `∑ i, (B i)ᴴ * B i = 1`, and are **not** gauge-phase
equivalent, then the MPV overlaps decay to `0` as `N → ∞`.

## Proof idea (no operator topology)

1. Use `trace_mixedTransferMap_pow_eq_mpvOverlap` to rewrite the overlap as the
   operator trace of `((mixedTransferMap A B)^N)`.
2. Expand `LinearMap.trace` as a finite double sum over matrix units
   `Matrix.single p q 1` using `linearMap_trace_eq_sum_apply_single`.
3. For each fixed `(p,q)`, apply the spectral-gap lemma `mixedTransfer_pow_tendsto_zero`
   to get `((mixedTransferMap A B)^N) (Matrix.single p q 1) → 0`.
4. Extract the `(p,q)` entry using the continuous linear functional
   `Matrix.entryLinearMap ℂ ℂ p q`.
5. Reassemble the finite sum using `tendsto_finset_sum`.

## Rectangular (heterogeneous bond dimensions)

`mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one` handles the case where
`A : MPSTensor d D₁` and `B : MPSTensor d D₂` may have different bond dimensions,
*assuming* a spectral-radius gap `spectralRadius < 1` for the rectangular mixed transfer
operator.
-/

section

variable {d D : ℕ} [NeZero D]

/-- **Overlap decay** (square bond dimension case): if `A` and `B` are injective,
normalized, and not gauge-phase equivalent, then
`mpvOverlap (d := d) A B N → 0` as `N → ∞`.
-/
theorem mpvOverlap_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  -- The matrix-entry term appearing in the trace expansion.
  let term : Fin D → Fin D → ℕ → ℂ := fun p q N =>
    (((mixedTransferMap A B) ^ N) (Matrix.single p q (1 : ℂ))) p q
  -- For each fixed `(p,q)`, the entry converges to `0`.
  have hterm : ∀ p q : Fin D,
      Filter.Tendsto (fun N => term p q N) Filter.atTop (nhds 0) := by
    intro p q
    -- Matrix-level convergence from the spectral gap.
    have hmat :
        Filter.Tendsto
          (fun N => ((mixedTransferMap A B) ^ N) (Matrix.single p q (1 : ℂ)))
          Filter.atTop (nhds 0) :=
      mixedTransfer_pow_tendsto_zero (A := A) (B := B) hA hB hA_norm hB_norm hAB
        (Matrix.single p q (1 : ℂ))
    -- Entry evaluation is continuous (finite-dimensionality).
    have hcont : Continuous (Matrix.entryLinearMap ℂ ℂ p q) :=
      LinearMap.continuous_of_finiteDimensional _
    -- Compose the matrix convergence with the continuous entry functional.
    simpa [term, Matrix.entryLinearMap_apply] using
      (hcont.tendsto (0 : Matrix (Fin D) (Fin D) ℂ)).comp hmat
  -- For fixed `p`, the inner `q`-sum tends to `0`.
  have hinner : ∀ p : Fin D,
      Filter.Tendsto (fun N => ∑ q : Fin D, term p q N) Filter.atTop (nhds 0) := fun p => by
    simpa [Finset.sum_const_zero] using
      tendsto_finset_sum (s := Finset.univ) (fun q _ => hterm p q)
  -- The outer `p`-sum also tends to `0`.
  have hsum :
      Filter.Tendsto (fun N => ∑ p : Fin D, ∑ q : Fin D, term p q N)
        Filter.atTop (nhds 0) := by
    simpa [Finset.sum_const_zero] using
      tendsto_finset_sum (s := Finset.univ) (fun p _ => hinner p)
  -- Rewrite the finite sum as the operator trace.
  have htraceEq : ∀ N : ℕ,
      (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N)
        = ∑ p : Fin D, ∑ q : Fin D, term p q N := fun N => by
    simpa [term] using linearMap_trace_eq_sum_apply_single (T := ((mixedTransferMap A B) ^ N))
  -- Step 1: lift convergence from the sum-of-terms to the operator trace.
  have htrace :
      Filter.Tendsto
        (fun N => (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N))
        Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr (fun N => (htraceEq N).symm) hsum
  -- Step 2: rewrite the trace as the MPV overlap.
  exact Filter.Tendsto.congr
    (fun N => trace_mixedTransferMap_pow_eq_mpvOverlap (A := A) (B := B) N)
    htrace

/-- **Inner product decay**: the same overlap decay statement for Lean's Hilbert-space
inner product `mpvInner`, using `mpvOverlap_eq_star_mpvInner`.
-/
theorem mpvInner_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvInner (d := d) A B N) Filter.atTop (nhds 0) := by
  have hOverlap :=
    mpvOverlap_tendsto_zero (A := A) (B := B) hA hB hA_norm hB_norm hAB
  simpa [mpvOverlap_eq_star_mpvInner] using hOverlap.star

end

/-! ## Rectangular (heterogeneous bond dimensions) -/

section TraceDecay

variable {d D₁ D₂ : ℕ}

local notation "V" => Matrix (Fin D₁) (Fin D₂) ℂ

/-- Trace, viewed as a linear functional on the Banach algebra of continuous endomorphisms.

On finite-dimensional spaces this is automatically continuous. -/
noncomputable def traceCLMRect : (V →L[ℂ] V) →ₗ[ℂ] ℂ where
  toFun F := LinearMap.trace ℂ V (F : V →ₗ[ℂ] V)
  map_add' F G := by simp
  map_smul' c F := by simp

/-- If `F^n → 0` in operator norm, then `trace(F^n) → 0`. -/
lemma tendsto_trace_pow_of_tendsto_zero_rect
    (F : V →L[ℂ] V)
    (hF : Tendsto (fun n => F ^ n) atTop (nhds 0)) :
    Tendsto (fun n => LinearMap.trace ℂ V ((F ^ n : V →L[ℂ] V) : V →ₗ[ℂ] V))
      atTop (nhds (0 : ℂ)) := by
  -- continuity of trace on finite-dimensional spaces
  have hcont : Continuous (traceCLMRect (D₁ := D₁) (D₂ := D₂)) :=
    LinearMap.continuous_of_finiteDimensional (traceCLMRect (D₁ := D₁) (D₂ := D₂))
  have h := (hcont.tendsto (0 : V →L[ℂ] V)).comp hF
  have hzero : traceCLMRect (D₁ := D₁) (D₂ := D₂) (0 : V →L[ℂ] V) = 0 := by
    simp [traceCLMRect]
  change Tendsto
      ((fun G : V →L[ℂ] V => LinearMap.trace ℂ V ((G : V →ₗ[ℂ] V))) ∘ fun n => F ^ n)
      atTop (nhds (0 : ℂ))
  simpa [traceCLMRect, Function.comp_apply, hzero] using h

/-- If the rectangular mixed transfer map has spectral radius `< 1`, then `mpvOverlap → 0`. -/
theorem mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one
    [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSpect :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap V)
            (mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B)) < 1) :
    Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds (0 : ℂ)) := by
  classical
  let Φ : (V →ₗ[ℂ] V) ≃ₐ[ℂ] (V →L[ℂ] V) := Module.End.toContinuousLinearMap V
  let F' : V →L[ℂ] V := Φ (mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B)
  have hpow0 : Tendsto (fun n => F' ^ n) atTop (nhds 0) :=
    pow_tendsto_zero_of_spectralRadius_lt_one (a := F') (by simpa [F', Φ] using hSpect)
  have htr0 :
      Tendsto (fun n => LinearMap.trace ℂ V ((F' ^ n : V →L[ℂ] V) : V →ₗ[ℂ] V))
        atTop (nhds (0 : ℂ)) :=
    tendsto_trace_pow_of_tendsto_zero_rect (D₁ := D₁) (D₂ := D₂) (F := F') hpow0
  -- Identify `trace(F'^n)` with `trace((mixedTransferMap₂ A B)^n)`.
  have htr0' :
      Tendsto
        (fun n => LinearMap.trace ℂ V
          ((mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B) ^ n))
        atTop (nhds (0 : ℂ)) := by
    refine Tendsto.congr (fun n => ?_) htr0
    -- `Φ` preserves powers; `((Φ M : V →L[ℂ] V) : V →ₗ[ℂ] V) = M` by definition.
    have hpow : (F' ^ n) = Φ ((mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B) ^ n) := by
      simp [F', Φ]
    -- Pass to underlying linear maps.
    have hlin :
        ((F' ^ n : V →L[ℂ] V) : V →ₗ[ℂ] V) =
          (mixedTransferMap₂ (d := d) (D₁ := D₁) (D₂ := D₂) A B) ^ n :=
      (congrArg (fun F : V →L[ℂ] V => (F : V →ₗ[ℂ] V)) hpow).trans rfl
    exact congrArg (fun F : V →ₗ[ℂ] V => LinearMap.trace ℂ V F) hlin
  -- Convert trace to overlap using `trace_mixedTransferMap₂_pow_eq_mpvOverlap`.
  simpa [trace_mixedTransferMap₂_pow_eq_mpvOverlap (A := A) (B := B)] using htr0'

end TraceDecay

end MPSTensor
