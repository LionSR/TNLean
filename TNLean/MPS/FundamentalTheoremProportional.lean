/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs
import TNLean.MPS.MPVOverlap
import TNLean.Spectral.MPVOverlapDecay

import Mathlib.Data.Real.Sqrt

open scoped Matrix BigOperators

namespace MPSTensor

/-!
# Proportional single-block Fundamental Theorem (primitive case)

This file packages a lightweight “proportional” variant of the single-block Fundamental Theorem,
aligned with the **primitive/aperiodic** branch of Cirac et al., Rev. Mod. Phys. 93 (2021),
Theorem 4.4 (arXiv:2011.12127).

* If `A` and `B` are related by a gauge transform up to a scalar `ζ` (`GaugePhaseEquiv A B`), then
  their Matrix Product Vectors are proportional for each system size `N`.

* Conversely, if the MPV families are proportional (`ProportionalMPV₂ A B`) and both self-overlaps
  `mpvOverlap A A N` and `mpvOverlap B B N` converge to `1`, then `A` and `B` must be
  gauge-phase equivalent.

The key input for the converse is the overlap decay lemma
`MPSTensor.mpvOverlap_tendsto_zero` from `TNLean.Spectral.MPVOverlapDecay`.
-/

variable {d D : ℕ}

/-! ## Gauge-phase scaling of MPV coefficients -/

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
  have hwlen : w.length = N := by simp [w]
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
    mpv B σ = Matrix.trace (evalWord B w) := by simp [mpv, coeff, w]
    _ = Matrix.trace (evalWord (fun i => ζ • C i) w) := by simp [hB]
    _ = Matrix.trace ((ζ ^ w.length) • evalWord C w) := by
          simpa using congrArg Matrix.trace (evalWord_smul (ζ := ζ) (A := C) w)
    _ = (ζ ^ w.length) * Matrix.trace (evalWord C w) := by
          simp [Matrix.trace_smul, smul_eq_mul]
    _ = (ζ ^ w.length) * Matrix.trace (evalWord A w) := by simp [htrace]
    _ = ζ ^ N * mpv A σ := by simp [mpv, coeff, w, hwlen]

/-! ## Easy direction: gauge-phase ⇒ proportional MPV -/

section EasyDirection

variable [NeZero D]

/-- Gauge-phase equivalence implies proportionality of MPVs.

`GaugePhaseEquiv` allows the degenerate case `ζ = 0`, in which `B` is the zero tensor; to obtain
proportionality in the direction `A = c_N • B` we assume the standard trace-preserving/DS-gauge
normalization on `B`, which forces `ζ ≠ 0` when `D ≠ 0`. -/
theorem proportionalMPV₂_of_gaugePhaseEquiv
    (A B : MPSTensor d D)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1) :
    GaugePhaseEquiv A B → ProportionalMPV₂ (d := d) A B := by
  classical
  rintro ⟨X, ζ, hX⟩
  have hζ : ζ ≠ 0 := by
    intro hζ0
    have hBzero : ∀ i : Fin d, B i = 0 := by
      intro i
      simp [hX i, hζ0]
    have hsum0 : (∑ i : Fin d, (B i)ᴴ * B i) = (0 : Matrix (Fin D) (Fin D) ℂ) := by
      simp [hBzero]
    haveI : Nonempty (Fin D) := ⟨⟨0, NeZero.pos D⟩⟩
    haveI : Nontrivial (Matrix (Fin D) (Fin D) ℂ) := Matrix.nonempty
    exact zero_ne_one (hsum0 ▸ hB_norm)
  intro N
  refine ⟨(ζ ^ N)⁻¹, ?_⟩
  intro σ
  have hmpv := mpv_eq_pow_mul_of_gaugePhase (A := A) (B := B) X ζ hX N σ
  have hζN : ζ ^ N ≠ 0 := pow_ne_zero N hζ
  have h1 : (ζ ^ N)⁻¹ * mpv B σ = mpv A σ := by
    -- Rewrite `mpv B σ` using the gauge-phase relation and cancel `ζ ^ N`.
    simpa [hmpv] using (inv_mul_cancel_left₀ hζN (mpv A σ))
  exact h1.symm

end EasyDirection

/-! ## Main direction: proportional MPV + primitive overlap ⇒ gauge-phase -/

section Main

variable [NeZero D]

/-- **Proportional Fundamental Theorem (primitive case).**

If `A` and `B` are injective, trace-preserving/DS-gauged, both self-overlaps tend to `1`, and
`V_N(A)` is proportional to `V_N(B)` for every `N`, then `A` and `B` are gauge-phase equivalent.

The proof is by contradiction: proportionality forces `‖mpvOverlap A B N‖ → 1`, while
`¬ GaugePhaseEquiv A B` implies `mpvOverlap A B N → 0` by overlap decay.
-/
theorem gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one
    (A B : MPSTensor d D)
    (hA : IsInjective A) (hB : IsInjective B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp : ProportionalMPV₂ (d := d) A B) :
    GaugePhaseEquiv A B := by
  classical
  choose c hc using hProp
  have hOverlapAB :
      ∀ N : ℕ,
        mpvOverlap (d := d) A B N = c N * mpvOverlap (d := d) B B N := by
    intro N
    -- Expand the RHS as a sum and simplify termwise using the proportionality hypothesis.
    simp [mpvOverlap, hc N, Finset.mul_sum, mul_assoc]
  have hOverlapAA :
      ∀ N : ℕ,
        mpvOverlap (d := d) A A N = (c N * star (c N)) * mpvOverlap (d := d) B B N := by
    intro N
    -- Same as `hOverlapAB`, but with the additional conjugation in the overlap.
    simp [mpvOverlap, hc N, Finset.mul_sum, star_mul, mul_assoc, mul_left_comm, mul_comm]
  have hA_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using hA_self.norm
  have hB_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop (nhds (1 : ℝ)) := by
    simpa using hB_self.norm
  have hRatio :
      Filter.Tendsto
        (fun N => ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖)
        Filter.atTop (nhds (1 : ℝ)) := by
    simpa using hA_self_norm.div hB_self_norm one_ne_zero
  have hB_self_norm_ne :
      (∀ᶠ N in Filter.atTop, ‖mpvOverlap (d := d) B B N‖ ≠ (0 : ℝ)) :=
    hB_self_norm.eventually_ne one_ne_zero
  have hRatio_eq :
      (fun N => ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖)
        =ᶠ[Filter.atTop] fun N => ‖c N‖ ^ 2 := by
    filter_upwards [hB_self_norm_ne] with N hN
    calc
      ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖
          = ‖(c N * star (c N)) * mpvOverlap (d := d) B B N‖ /
              ‖mpvOverlap (d := d) B B N‖ := by
                simp [hOverlapAA N]
      _ = (‖c N * star (c N)‖ * ‖mpvOverlap (d := d) B B N‖) /
            ‖mpvOverlap (d := d) B B N‖ := by
                simp
      _ = ‖c N * star (c N)‖ := by
            simpa using
              (mul_div_cancel_right₀ (a := ‖c N * star (c N)‖)
                (b := ‖mpvOverlap (d := d) B B N‖) hN)
      _ = ‖c N‖ ^ 2 := by
            simp [pow_two]
  have hc_normsq :
      Filter.Tendsto (fun N => ‖c N‖ ^ 2) Filter.atTop (nhds (1 : ℝ)) :=
    Filter.Tendsto.congr' hRatio_eq hRatio
  have hc_norm :
      Filter.Tendsto (fun N => ‖c N‖) Filter.atTop (nhds (1 : ℝ)) := by
    simpa [Real.sqrt_sq (norm_nonneg _)] using hc_normsq.sqrt
  have hCrossNorm :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop (nhds (1 : ℝ)) := by
    have hmul : Filter.Tendsto (fun N => ‖c N‖ * ‖mpvOverlap (d := d) B B N‖)
        Filter.atTop (nhds (1 : ℝ)) := by simpa using hc_norm.mul hB_self_norm
    exact hmul.congr fun N => by simp [hOverlapAB N]
  by_contra hNot
  have hto0 :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) :=
    mpvOverlap_tendsto_zero (A := A) (B := B) hA hB hA_norm hB_norm hNot
  exact absurd
    (tendsto_nhds_unique (by simpa using hto0.norm) hCrossNorm)
    zero_ne_one

end Main

end MPSTensor
