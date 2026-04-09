/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.GaugePhase

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

/-! ## Easy direction: gauge-phase ⇒ proportional MPV -/

section EasyDirection

/-- Gauge-phase equivalence implies proportionality of MPVs.

`GaugePhaseEquiv` requires `ζ ≠ 0`, so `B` is a nondegenerate gauge-phase transform of `A`. -/
theorem proportionalMPV₂_of_gaugePhaseEquiv
    (A B : MPSTensor d D) :
    GaugePhaseEquiv A B → ProportionalMPV₂ (d := d) A B := by
  classical
  rintro ⟨X, ζ, hζ, hX⟩
  intro N
  refine ⟨(ζ ^ N)⁻¹, ?_⟩
  intro σ
  have hmpv := mpv_eq_pow_mul_of_gaugePhase (A := A) (B := B) X ζ hX N σ
  have hζN : ζ ^ N ≠ 0 := pow_ne_zero N hζ
  have h1 : (ζ ^ N)⁻¹ * mpv B σ = mpv A σ := by
    -- Rewrite `mpv B σ` using the gauge-phase relation and cancel `ζ ^ N`.
    rw [hmpv]
    exact inv_mul_cancel_left₀ hζN _
  exact h1.symm

end EasyDirection

/-! ## Main direction: proportional MPV + primitive overlap ⇒ gauge-phase -/

section Main

variable [NeZero D]

omit [NeZero D] in
private theorem gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_tendsto_zero
    (A B : MPSTensor d D)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp : ProportionalMPV₂ (d := d) A B)
    (hZero : ¬ GaugePhaseEquiv A B →
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0)) :
    GaugePhaseEquiv A B := by
  classical
  choose c hc using hProp
  have hOverlapAB :
      ∀ N : ℕ,
        mpvOverlap (d := d) A B N = c N * mpvOverlap (d := d) B B N := by
    intro N
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc N σ]; ring
  have hOverlapAA :
      ∀ N : ℕ,
        mpvOverlap (d := d) A A N = (c N * star (c N)) * mpvOverlap (d := d) B B N := by
    intro N
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc N σ]
    simp only [star_mul]
    ring
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
        Filter.atTop (nhds (1 : ℝ)) := by
      simpa using hc_norm.mul hB_self_norm
    exact hmul.congr fun N => by simp [hOverlapAB N]
  by_contra hNot
  have hto0 :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0) :=
    hZero hNot
  exact (hCrossNorm.ne_nhds one_ne_zero) (by simpa using hto0.norm)

/-- **Proportional Fundamental Theorem (primitive case).**

If `A` and `B` are injective, left-canonical / trace-preserving, both self-overlaps tend to `1`,
and `V_N(A)` is proportional to `V_N(B)` for every `N`, then `A` and `B` are gauge-phase
equivalent.

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
    GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_tendsto_zero
    A B hA_self hB_self hProp
    (fun hNot => mpvOverlap_tendsto_zero (A := A) (B := B) hA hB hA_norm hB_norm hNot)

/-- NT / irreducible version of
`gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one`.

The proof is identical, replacing the injective overlap-decay theorem by
`mpvOverlap_tendsto_zero_of_irreducible_TP`. -/
theorem gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp : ProportionalMPV₂ (d := d) A B) :
    GaugePhaseEquiv A B :=
  gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_tendsto_zero
    A B hA_self hB_self hProp
    (fun hNot =>
      mpvOverlap_tendsto_zero_of_irreducible_TP
        (A := A) (B := B) hA_irr hB_irr hA_norm hB_norm hNot)

end Main

end MPSTensor
