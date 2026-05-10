/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.GaugePhase

open scoped Matrix BigOperators

namespace MPSTensor

/-!
# Proportional single-block Fundamental Theorem (primitive case)

This file contains a lightweight “proportional” variant of the single-block Fundamental Theorem,
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
private theorem gaugePhaseEquiv_of_eventually_proportionalMPV₂_of_overlap_decay
    (A B : MPSTensor d D)
    (hA_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (d := d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp :
      ∀ᶠ N in Filter.atTop, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv A σ = c * mpv B σ)
    (hZero : ¬ GaugePhaseEquiv A B →
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop (nhds 0)) :
    GaugePhaseEquiv A B := by
  classical
  let proportionalAt : ℕ → Prop := fun N =>
    ∃ c : ℂ, ∀ σ : Fin N → Fin d,
      Matrix.trace (evalWord A (List.ofFn σ)) =
        c * Matrix.trace (evalWord B (List.ofFn σ))
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
    rw [dif_pos hN']
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
    simpa using hA_self_norm.div hB_self_norm one_ne_zero
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
  gaugePhaseEquiv_of_eventually_proportionalMPV₂_of_overlap_decay
    A B hA_self hB_self
    (Filter.Eventually.of_forall fun N => hProp N)
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
  gaugePhaseEquiv_of_eventually_proportionalMPV₂_of_overlap_decay
    A B hA_self hB_self
    (Filter.Eventually.of_forall fun N => hProp N)
    (fun hNot =>
      mpvOverlap_tendsto_zero_of_irreducible_TP
        (A := A) (B := B) hA_irr hB_irr hA_norm hB_norm hNot)

/-! ## Source-faithful equalMPS: gauge-phase from `|overlap| → 1` alone -/

/-- **Spectral radius lower bound from unit-modulus overlap.**

Source: arXiv:1606.00608, proof of Lemma `equalMPS`, lines 1093-1117.
This is the spectral-radius step inside the proof: if the modulus of the
overlap tends to `1`, the cross-transfer spectral radius is at least `1`.

The proof is the contrapositive of
`mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one`: if the
spectral radius were strictly less than `1`, the overlap (and hence its
modulus) would tend to `0`, contradicting the hypothesis.

The proof uses the trace identity
`trace_mixedTransferMap_pow_eq_mpvOverlap` and is paper-faithful (no
proportionality hypothesis required). -/
theorem mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one
    (A B : MPSTensor d D)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    1 ≤ mixedTransferSpectralRadius A B := by
  by_contra hlt
  push Not at hlt
  -- Unpack mixedTransferSpectralRadius and pass to the rectangular form (D₁ = D₂ = D).
  have hlt' :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (mixedTransferMap₂ (d := d) (D₁ := D) (D₂ := D) A B)) < 1 := by
    have hsq :
        spectralRadius ℂ
            ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
              (mixedTransferMap (d := d) (D := D) A B)) < 1 := by
      simpa [mixedTransferSpectralRadius] using hlt
    -- `mixedTransferMap` and `mixedTransferMap₂` agree on `D × D` matrices.
    have hagree :
        mixedTransferMap (d := d) (D := D) A B =
          mixedTransferMap₂ (d := d) (D₁ := D) (D₂ := D) A B := by
      ext X
      simp
    rw [← hagree]; exact hsq
  have hzero :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop
        (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one
      (A := A) (B := B) hlt'
  have hnorm_zero :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (0 : ℝ)) := by
    simpa using hzero.norm
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hOverlap hnorm_zero
  exact one_ne_zero h01

/-- **Source-faithful equalMPS gauge recovery.**

Source: arXiv:1606.00608, Lemma `equalMPS`, statement lines 1080-1091 and
proof lines 1093-1117. If two
irreducible trace-preserving (left-canonical) blocks of the same bond
dimension have asymptotically unit-modulus overlap, then they are
gauge-phase equivalent.

This is the **proportionality-free** version of the gauge recovery — the
counterpart to `gaugePhaseEquiv_of_proportionalMPV₂_of_overlap_tendsto_one_of_irreducible_TP`
without the extra `ProportionalMPV₂` hypothesis. The proof uses the
cross-transfer-matrix spectral radius (computed via
`mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one`)
together with the rigidity theorem
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`.

Closes the same-bond-dimension component of the equalMPS gap
(arXiv:1606.00608, Lemma `equalMPS`); the rectangular bond-dimension conclusion
is separate. -/
theorem gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D) B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    GaugePhaseEquiv A B :=
  modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    A B hA_irr hB_irr hA_norm hB_norm
    (mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one
      (A := A) (B := B) hOverlap)

/-- Non-gauge-phase-equivalent irreducible trace-preserving blocks cannot have
proportional MPV states at all sufficiently large lengths. -/
theorem exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP
    (A B : MPSTensor d D)
    (hA_irr : IsIrreducibleTensor A) (hB_irr : IsIrreducibleTensor B)
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
  exact hNot
    (gaugePhaseEquiv_of_eventually_proportionalMPV₂_of_overlap_decay
      A B hA_self hB_self hProp
      (fun hNot' =>
        mpvOverlap_tendsto_zero_of_irreducible_TP
          (A := A) (B := B) hA_irr hB_irr hA_norm hB_norm hNot'))

end Main

end MPSTensor
