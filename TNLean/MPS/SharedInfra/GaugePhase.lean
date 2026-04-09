/- 
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.Overlap.Basic
import TNLean.MPS.Overlap.PeripheralToSpectralGap
import TNLean.Spectral.MPVOverlapDecay
import TNLean.Spectral.SpectralGapNT
import TNLean.Topology.TendstoHelpers

import Mathlib.Data.Real.Sqrt

open scoped Matrix BigOperators

namespace MPSTensor

/-!
# Shared gauge-phase lemmas for MPS tensors

This module collects the generic gauge-phase identities used by both the
single-block proportional FT and the canonical-form equal-norm bridge.
-/

variable {d D : ℕ}

/-- If `B i = ζ • (X * A i * X⁻¹)` then `mpv B σ = ζ^N * mpv A σ`. -/
theorem mpv_eq_pow_mul_of_gaugePhase
    (A B : MPSTensor d D)
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX :
      ∀ i : Fin d,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ := by
  intro N σ
  classical
  set w : List (Fin d) := List.ofFn σ
  have hwlen : w.length = N := by
    simp [w]
  let C : MPSTensor d D := fun i =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun i => ζ • C i := by
    funext i
    simpa [C] using hX i
  have hGauge :
      evalWord C w =
        (X : Matrix (Fin D) (Fin D) ℂ) * evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using (evalWord_gauge (A := A) (B := C) X (by intro i; rfl) w)
  have htrace : Matrix.trace (evalWord C w) = Matrix.trace (evalWord A w) := by
    simpa [hGauge, Matrix.mul_assoc] using (trace_conj_eq (X := X) (M := evalWord A w))
  calc
    mpv B σ = Matrix.trace (evalWord B w) := by
      simp [mpv, coeff, w]
    _ = Matrix.trace (evalWord (fun i => ζ • C i) w) := by
      simp [hB]
    _ = Matrix.trace ((ζ ^ w.length) • evalWord C w) := by
          simpa using congrArg Matrix.trace (evalWord_smul (ζ := ζ) (A := C) w)
    _ = (ζ ^ w.length) * Matrix.trace (evalWord C w) := by
          simp [Matrix.trace_smul, smul_eq_mul]
    _ = (ζ ^ w.length) * Matrix.trace (evalWord A w) := by
          simp [htrace]
    _ = ζ ^ N * mpv A σ := by
          simp [mpv, coeff, w, hwlen]

/-- If `mpv B σ = ζ ^ N * mpv A σ` for every system size `N` and configuration `σ`, then the
self-overlap of `B` scales by `(ζ * conj ζ) ^ N` times the self-overlap of `A`. -/
theorem mpvOverlap_self_scale_of_mpv_eq_pow_mul
    {D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N := by
  intro N
  classical
  simp only [mpvOverlap]
  simp_rw [hmpv N, star_mul, star_pow]
  simp_rw [show star ζ = starRingEnd ℂ ζ from rfl]
  simp_rw [show ∀ x : Cfg d N,
      ζ ^ N * mpv A x * (star (mpv A x) * (starRingEnd ℂ ζ) ^ N) =
        ζ ^ N * (starRingEnd ℂ ζ) ^ N * (mpv A x * star (mpv A x)) from
      fun x => by ring]
  rw [← Finset.mul_sum, mul_pow]

/-- If two self-overlaps both have norm limit `1`, and one scales from the other by powers of
`ζ * conj ζ`, then `ζ` has unit norm. -/
theorem norm_eq_one_of_selfOverlap_scale
    {D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop (nhds 1))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N) :
    ‖ζ‖ = 1 := by
  have hAA_ne : ∀ᶠ N in Filter.atTop, ‖mpvOverlap (d := d) A A N‖ ≠ 0 :=
    hAA.eventually_ne one_ne_zero
  have hRatio : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖ /
      ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 / 1 from (one_div_one).symm]
    exact hBB.div hAA one_ne_zero
  have hRatioEq : ∀ᶠ N in Filter.atTop,
      ‖mpvOverlap (d := d) B B N‖ / ‖mpvOverlap (d := d) A A N‖ = (‖ζ‖ ^ 2) ^ N := by
    filter_upwards [hAA_ne] with N hN
    rw [hSelf N, norm_mul, norm_pow, show ‖ζ * starRingEnd ℂ ζ‖ = ‖ζ‖ ^ 2 from by
      rw [norm_mul, RCLike.norm_conj, sq]]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_div_cancel_of_imp (fun h => absurd h hN)
  have hPow : Filter.Tendsto (fun N => (‖ζ‖ ^ 2) ^ N) Filter.atTop (nhds 1) :=
    hRatio.congr' hRatioEq
  have h1 : ‖ζ‖ ^ 2 = 1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact (hPow.ne_nhds one_ne_zero)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h)
    · have hlt2 : ∀ᶠ n in Filter.atTop, (‖ζ‖ ^ 2) ^ n < 2 :=
        hPow.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
      rcases ((Filter.tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt h) 2).and hlt2).exists
        with ⟨n, hn1, hn2⟩
      exact not_lt_of_ge hn1 hn2
  nlinarith [norm_nonneg ζ]

/-- The gauge phase `ζ` in a gauge-phase equivalence between two TP-normalized irreducible
primitive blocks has unit norm. -/
theorem norm_gaugePhase_eq_one_of_irr_TP_primitive
    {D : ℕ} [NeZero D]
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A)
    (hB_irr : IsIrreducibleTensor B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) A))
    (hB_prim : _root_.IsPrimitive (transferMap (d := d) (D := D) B))
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX : ∀ i : Fin d,
      B i = ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
        ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ‖ζ‖ = 1 := by
  have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d), mpv B σ = ζ ^ N * mpv A σ :=
    mpv_eq_pow_mul_of_gaugePhase A B X ζ hX
  have hScale : ∀ N,
      mpvOverlap (d := d) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A) (B := B) (ζ := ζ) hmpv
  have hA_pf : HasPrimitiveFixedPoint A :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible A hA_irr hA_norm hA_prim
  have hB_pf : HasPrimitiveFixedPoint B :=
    hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible B hB_irr hB_norm hB_prim
  have hAA : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds 1) := by
    convert hA_pf.overlap_tendsto_one.norm using 1
    simp
  have hBB : Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop (nhds 1) := by
    convert hB_pf.overlap_tendsto_one.norm using 1
    simp
  exact norm_eq_one_of_selfOverlap_scale hAA hBB hScale

end MPSTensor
