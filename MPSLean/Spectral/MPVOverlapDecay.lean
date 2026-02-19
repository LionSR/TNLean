/-
Copyright (c) 2025 MPSLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import MPSLean.Spectral.MPVOverlapTrace
import MPSLean.Spectral.SpectralGap

import Mathlib.Topology.Algebra.Star

namespace MPSTensor

open scoped Matrix BigOperators

/-!
# MPV overlap decay

This file proves a literature-standard decay statement for the *MPV overlap*
`mpvOverlap A B N` in the **square bond dimension** case.

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
-/

section

variable {d D : ℕ} [NeZero D]

/-- **Overlap decay** (square bond dimension case): if `A` and `B` are injective,
normalized, and not gauge-phase equivalent, then
`mpvOverlap (d := d) A B N → 0` as `N → ∞`.

This is the literature-oriented overlap
`∑ σ, mpv A σ * star (mpv B σ)`.
-/
theorem mpvOverlap_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) := by
  classical
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
    have hentry :
        Filter.Tendsto (Matrix.entryLinearMap ℂ ℂ p q)
          (nhds (0 : Matrix (Fin D) (Fin D) ℂ)) (nhds 0) := by
      simpa using (hcont.tendsto (0 : Matrix (Fin D) (Fin D) ℂ))
    -- Compose the matrix convergence with the continuous entry functional.
    have ht :
        Filter.Tendsto
          (fun N =>
            (Matrix.entryLinearMap ℂ ℂ p q)
              (((mixedTransferMap A B) ^ N) (Matrix.single p q (1 : ℂ))))
          Filter.atTop (nhds 0) :=
      hentry.comp hmat
    simpa [term, Matrix.entryLinearMap_apply] using ht
  -- For fixed `p`, the inner `q`-sum tends to `0`.
  have hinner : ∀ p : Fin D,
      Filter.Tendsto (fun N => ∑ q : Fin D, term p q N) Filter.atTop (nhds 0) := by
    intro p
    have :=
      (tendsto_finset_sum (s := (Finset.univ : Finset (Fin D)))
        (f := fun q N => term p q N) (x := (Filter.atTop : Filter ℕ)) (a := fun _ => (0 : ℂ))
        (fun q _ => hterm p q))
    simpa [Finset.sum_const_zero] using this
  -- Now the outer `p`-sum tends to `0`.
  have hsum :
      Filter.Tendsto (fun N => ∑ p : Fin D, ∑ q : Fin D, term p q N)
        Filter.atTop (nhds 0) := by
    have :=
      (tendsto_finset_sum (s := (Finset.univ : Finset (Fin D)))
        (f := fun p N => ∑ q : Fin D, term p q N) (x := (Filter.atTop : Filter ℕ))
        (a := fun _ => (0 : ℂ)) (fun p _ => hinner p))
    simpa [Finset.sum_const_zero] using this
  -- Rewrite the finite sum as the operator trace.
  have htraceEq : ∀ N : ℕ,
      (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N)
        = ∑ p : Fin D, ∑ q : Fin D, term p q N := by
    intro N
    simpa [term] using (linearMap_trace_eq_sum_apply_single (T := ((mixedTransferMap A B) ^ N)))
  have htrace :
      Filter.Tendsto
        (fun N =>
          (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N))
        Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr (fun N => (htraceEq N).symm) hsum
  -- Final rewrite using the operator-trace / MPV overlap identity.
  have hmpvEq : ∀ N : ℕ,
      (LinearMap.trace ℂ (Matrix (Fin D) (Fin D) ℂ)) ((mixedTransferMap A B) ^ N)
        = mpvOverlap (d := d) A B N := by
    intro N
    simpa using (trace_mixedTransferMap_pow_eq_mpvOverlap (A := A) (B := B) N)
  exact Filter.Tendsto.congr hmpvEq htrace

/-- **Inner product decay**: the same overlap decay statement for Lean's Hilbert-space
inner product `mpvInner`, using `mpvOverlap_eq_star_mpvInner`.

This is optional but convenient in later applications.
-/
theorem mpvInner_tendsto_zero
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hAB : ¬ GaugePhaseEquiv A B) :
    Filter.Tendsto (fun N => mpvInner (d := d) A B N) Filter.atTop (nhds 0) := by
  have hOverlap :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) :=
    mpvOverlap_tendsto_zero (A := A) (B := B) hA hB hA_norm hB_norm hAB
  -- Apply `star` (continuous) and rewrite `star (mpvOverlap) = mpvInner`.
  have hStar :
      Filter.Tendsto (fun N => star (mpvOverlap (d := d) A B N)) Filter.atTop (nhds 0) := by
    simpa using hOverlap.star
  simpa [mpvOverlap_eq_star_mpvInner] using hStar

end

end MPSTensor
