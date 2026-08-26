/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.SharedInfra.GaugePhase

/-!
# Proportional single-block Fundamental Theorem (primitive case)

This file contains a lightweight “proportional” variant of the single-block Fundamental Theorem,
aligned with the **primitive/aperiodic** branch of Cirac et al., Rev. Mod. Phys. 93 (2021),
Theorem IV.4 (arXiv:2011.12127).

* If `A` and `B` are related by a gauge transform up to a scalar `ζ` (`GaugePhaseEquiv A B`), then
  their Matrix Product Vectors are proportional for each system size `N`.

* Conversely, if the MPV families are eventually proportional by some scalar
  (`∀ᶠ N in atTop, ∃ c, ∀ σ, mpv A σ = c * mpv B σ`, with no nonvanishing condition
  imposed on `c`) and both self-overlaps `mpvOverlap A A N` and `mpvOverlap B B N`
  converge to `1`, then `A` and `B` must be gauge-phase equivalent. The eventual
  nonvanishing of the scalar is not assumed; it is derived from the self-overlap
  convergence hypotheses.

The key input for the converse is the overlap decay lemma
`MPSTensor.mpvOverlap_tendsto_zero` from `TNLean.Spectral.MPVOverlapDecay`.
-/
open scoped Matrix BigOperators Kraus

namespace MPSTensor

variable {d D : ℕ}

/-! ## Main direction: proportional MPV + primitive overlap ⇒ gauge-phase -/

section Main

variable [NeZero D]

/-- Eventual proportionality and normalized self-overlaps force the rectangular
cross-overlap to have asymptotic norm one.

This is the scalar-control argument used in the primitive single-block branch
of Cirac et al., arXiv:2011.12127, Theorem IV.4. No common bond dimension is
required. -/
theorem mpvOverlap_norm_tendsto_one_of_eventually_proportionalMPV₂
    {D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp :
      ∀ᶠ N in Filter.atTop, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv A σ = c * mpv B σ) :
    Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
      (nhds (1 : ℝ)) := by
  classical
  let proportionalAt : ℕ → Prop := fun N =>
    ∃ c : ℂ, ∀ σ : Fin N → Fin d,
      Matrix.trace (Kraus.evalWord A (List.ofFn σ)) =
        c * Matrix.trace (Kraus.evalWord B (List.ofFn σ))
  let c : ℕ → ℂ := fun N =>
    if h : proportionalAt N then
      Classical.choose h
    else 0
  have hc_event :
      ∀ᶠ N in Filter.atTop, ∀ σ : Fin N → Fin d, mpv A σ = c N * mpv B σ := by
    filter_upwards [hProp] with N hN σ
    have hN' : proportionalAt N := by
      simpa [proportionalAt, mpv, coeff] using hN
    dsimp [c]
    rw [dite_eq_left hN']
    simpa [mpv, coeff] using Classical.choose_spec hN' σ
  have hOverlapAB :
      (fun N => mpvOverlap (d := d) A B N) =ᶠ[Filter.atTop]
        fun N => c N * mpvOverlap (d := d) B B N := by
    filter_upwards [hc_event] with N hc
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc σ]
    ring
  have hOverlapAA :
      (fun N => mpvOverlap (d := d) A A N) =ᶠ[Filter.atTop]
        fun N => (c N * star (c N)) * mpvOverlap (d := d) B B N := by
    filter_upwards [hc_event] with N hc
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc σ]
    simp only [star_mul]
    ring
  have hA_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    simpa using hA_self.norm
  have hB_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    simpa using hB_self.norm
  have hRatio :
      Filter.Tendsto
        (fun N => ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖)
        Filter.atTop (nhds (1 : ℝ)) := by
    have hdiv := hA_self_norm.div hB_self_norm one_ne_zero
    have hfun :
        ((fun N => ‖mpvOverlap (d := d) A A N‖) /
          (fun N => ‖mpvOverlap (d := d) B B N‖)) =
            (fun N => ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖) := by
      funext N
      rfl
    simpa [hfun] using hdiv
  have hB_self_norm_ne :
      (∀ᶠ N in Filter.atTop, ‖mpvOverlap (d := d) B B N‖ ≠ (0 : ℝ)) :=
    hB_self_norm.eventually_ne one_ne_zero
  have hRatio_eq :
      (fun N => ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖)
        =ᶠ[Filter.atTop] fun N => ‖c N‖ ^ 2 := by
    filter_upwards [hOverlapAA, hB_self_norm_ne] with N hAA hN
    calc
      ‖mpvOverlap (d := d) A A N‖ / ‖mpvOverlap (d := d) B B N‖
          = ‖(c N * star (c N)) * mpvOverlap (d := d) B B N‖ /
              ‖mpvOverlap (d := d) B B N‖ := by
                simp [hAA]
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
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    have hmul :
        Filter.Tendsto (fun N => ‖c N‖ * ‖mpvOverlap (d := d) B B N‖)
          Filter.atTop (nhds (1 : ℝ)) := by
      simpa using hc_norm.mul hB_self_norm
    have hCross_eq :
        (fun N => ‖mpvOverlap (d := d) A B N‖) =ᶠ[Filter.atTop]
          fun N => ‖c N‖ * ‖mpvOverlap (d := d) B B N‖ := by
      filter_upwards [hOverlapAB] with N hAB
      simp [hAB]
    exact Filter.Tendsto.congr' hCross_eq.symm hmul
  exact hCrossNorm


/-! ## Consequences of gauge-phase recovery -/

/-- Non-gauge-phase-equivalent irreducible trace-preserving blocks cannot have
proportional MPV states at all sufficiently large lengths. -/
theorem exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily A) (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hNot : ¬ GaugePhaseEquiv A B) (Nmin : ℕ) :
    ∃ N : ℕ, Nmin ≤ N ∧
      ¬ ∃ c : ℂ, ∀ σ : Fin N → Fin d, mpv A σ = c * mpv B σ := by
  by_contra hNo
  have hProp :
      ∀ᶠ N in Filter.atTop, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv A σ = c * mpv B σ := by
    exact Filter.eventually_atTop.2 ⟨Nmin, fun N hN => by
      by_contra hNprop
      exact hNo ⟨N, hN, hNprop⟩⟩
  have hCrossNorm :=
    mpvOverlap_norm_tendsto_one_of_eventually_proportionalMPV₂
      A B hA_self hB_self hProp
  have hto0 := mpvOverlap_tendsto_zero_of_irreducible_TP
    (A := A) (B := B) hA_irr hB_irr hA_norm hB_norm hNot
  exact one_ne_zero (tendsto_nhds_unique hCrossNorm (by simpa using hto0.norm))

end Main

end MPSTensor
