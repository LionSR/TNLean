/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.SharedInfra.GaugePhase

open scoped Matrix BigOperators

namespace MPSTensor

/-!
# Single-block overlap consequences for the Fundamental Theorem

This file contains overlap consequences used in the single-block and BNT parts
of the Fundamental Theorem of Matrix Product States.

The source-facing results are the `equalMPS` consequences from
arXiv:1606.00608, Lemma `equalMPS`, lines 1085-1117:

* asymptotically unit-modulus overlap gives a mixed-transfer spectral radius
  lower bound;
* in the rectangular case, it forces equality of bond dimensions;
* in the common-bond-dimension case, it gives gauge-phase equivalence.

The remaining proportionality lemma is auxiliary: it is the contrapositive
form needed for separated BNT blocks, saying that non-gauge-equivalent
left-canonical irreducible blocks cannot remain proportional at all sufficiently
large lengths.
-/

variable {d D : ℕ}

/-! ## Auxiliary proportionality exclusion -/

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

/-- **Rectangular equalMPS dimension recovery.**

Source: arXiv:1606.00608, Lemma `equalMPS`, lines 1085-1117, especially the
dimension conclusion in line 1090 and the final dimension argument in
lines 1115-1117.  If two irreducible trace-preserving (left-canonical) blocks
have asymptotically unit-modulus overlap, then their bond dimensions agree.

The proof is the contrapositive of the rectangular overlap-decay theorem
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP`: different bond
dimensions force the overlap to tend to `0`, contradicting the assumed limit
of its modulus to `1`. -/
theorem dim_eq_of_overlap_norm_tendsto_one_of_irreducible_TP
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : IsIrreducibleTensor (d := d) (D := D₁) A)
    (hB_irr : IsIrreducibleTensor (d := d) (D := D₂) B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    D₁ = D₂ := by
  by_contra hD
  have hzero :
      Filter.Tendsto (fun N => mpvOverlap (d := d) A B N) Filter.atTop
        (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      A B hA_irr hB_irr hA_norm hB_norm hD
  have hnorm_zero :
      Filter.Tendsto (fun N => ‖mpvOverlap (d := d) A B N‖) Filter.atTop
        (nhds (0 : ℝ)) := by
    simpa using hzero.norm
  have h10 : (1 : ℝ) = 0 := tendsto_nhds_unique hOverlap hnorm_zero
  exact one_ne_zero h10

/-- **Source-faithful equalMPS gauge recovery.**

Source: arXiv:1606.00608, Lemma `equalMPS`, statement lines 1080-1091 and
proof lines 1093-1117. If two
irreducible trace-preserving (left-canonical) blocks of the same bond
dimension have asymptotically unit-modulus overlap, then they are
gauge-phase equivalent.

This is the gauge recovery from the paper's asymptotic overlap hypothesis
itself; no proportionality of MPVs is assumed. The proof uses the
cross-transfer-matrix spectral radius, computed via
`mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one`
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
