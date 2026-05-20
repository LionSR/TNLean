/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.SectorBNT.StrongMatch
import TNLean.MPS.CanonicalForm.PhaseCover

/-!
# Coefficient identity for full BNT basis matching (CPSV16 §II.C lines 1187–1188)

This module contains the CPSV16 §II.C lines 1187–1188 coefficient
comparison in the full-basis bijection form.  The full basis bijection
`β : Fin Q.basisCount ≃ Fin P.basisCount` (from `StrongMatch`) together with
`IsBNTCanonicalForm`'s CPSV21 Section IV.A / Definition 4.2 BNT input and
per-block spectral-radius-one normalization ensure the substitution has no
residual unmatched terms.  BNT linear independence of the `P`-basis
(`hP.bnt_data`) then yields eventual **exact** coefficient identities.

Paper anchors:

* CPSV16 §II.C lines 1182–1188: match every BNT basis tensor, substitute the
  gauge-phase identities, and compare the coefficients of the BNT basis.
* CPSV21 Definition 4.2 lines 1846–1850 and the two-layer display at
  lines 1864–1884: per-block BNT normalization that makes every sector
  participate in the full-basis matching.

No `dropSector` recursion and no partial-union combined LI are used here.
-/

open scoped Matrix BigOperators
open Filter Topology

namespace MPSTensor

variable {d : ℕ}

/-- **Unit phase from matched normalized BNT blocks.**

If two normalized BNT basis tensors have MPV families related by a scalar
power `ζ^N`, then `ζ` has norm one. This is the self-overlap normalization
closure used after the equal-MPS lemma of CPSV16 (lines 1080–1097) in the
non-periodic BNT setting. -/
theorem IsBNTCanonicalForm.norm_phase_of_matched_mpv
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {j : Fin P.basisCount} {k : Fin Q.basisCount} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis j) σ) :
    ‖ζ‖ = 1 := by
  have hAA : Tendsto (fun N => ‖mpvOverlap (d := d) (P.basis j) (P.basis j) N‖)
      atTop (𝓝 (1 : ℝ)) := by
    have h1 := (hP.basis_normalized_self_overlap j).norm
    simpa using h1
  have hBB : Tendsto (fun N => ‖mpvOverlap (d := d) (Q.basis k) (Q.basis k) N‖)
      atTop (𝓝 (1 : ℝ)) := by
    have h1 := (hQ.basis_normalized_self_overlap k).norm
    simpa using h1
  have hScale :=
    mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := P.basis j) (B := Q.basis k)
      (ζ := ζ) hmpv
  exact norm_eq_one_of_selfOverlap_scale (ζ := ζ) hAA hBB hScale

/-- **Auxiliary lemma: gauge-phase data gives an MPV-level scalar-power identity with unit phase.**

Given a matched bond-dimension equality `h : P.basisDim j = Q.basisDim k`
and a cast-left gauge-phase equivalence between `P.basis j` and `Q.basis k`,
extract a phase `ζ` with `‖ζ‖ = 1` and
`mpv (Q.basis k) σ = ζ^N * mpv (P.basis j) σ` for all lengths and words.

This is CPSV16's Lemma `equalMPS` (lines 1080–1097) plus the normalized
self-overlap/unit-phase closure used in the non-periodic setting. -/
private lemma extract_unit_gauge_phase_mpv
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    {j : Fin P.basisCount} {k : Fin Q.basisCount}
    (h : P.basisDim j = Q.basisDim k)
    (hGPE : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis j)) (Q.basis k)) :
    ∃ ζ : ℂ, ‖ζ‖ = 1 ∧
      ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis j) σ := by
  classical
  obtain ⟨ζ, _hζne, hmpv⟩ :=
    MPVBlockPhaseEquiv.of_gaugePhaseEquiv_cast (P.basis j) (Q.basis k) h hGPE
  refine ⟨ζ, ?_, hmpv⟩
  exact hP.norm_phase_of_matched_mpv hQ hmpv

/-- **CPSV16 §II.C lines 1187–1188, coefficient identity from fixed MPV phases.**

This auxiliary lemma isolates the linear-independence part of the global-gauge
substitution.  If a full basis bijection `β` has already been equipped with
specific phases `ζ k` satisfying

`mpv (Q.basis k) σ = (ζ k)^N * mpv (P.basis (β k)) σ`,

then `SameMPV₂ P.toTensor Q.toTensor` and the BNT linear independence of the
`P`-basis force the eventual exact coefficient identities

`P.coeff N (β k) = (ζ k)^N * Q.coeff N k`.

Unlike `coeff_identity_via_global_gauge`, this statement keeps the phase
function explicit.  The coefficient/weight comparison is the line 1187--1188
part of the equal-MPV corollary; the per-block gauge matrices are combined
afterwards into `X = ⊕_k (𝟙_{r_k} ⊗ X_k)` in lines 1189--1192. -/
theorem coeff_identity_via_matched_mpv_phasePos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor)
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (ζ : Fin Q.basisCount → ℂ)
    (hζ_mpv : ∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ) :
    ∀ k : Fin Q.basisCount, ∃ N₀, ∀ N > N₀,
      P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k := by
  classical
  let a : ℕ → Fin P.basisCount → ℂ := fun N j => P.coeff N j
  let b : ℕ → Fin P.basisCount → ℂ := fun N j =>
    (ζ (β.symm j)) ^ N * Q.coeff N (β.symm j)
  have hLI : ∀ᶠ N in atTop,
      LinearIndependent ℂ (fun j : Fin P.basisCount => mpvState (d := d) (P.basis j) N) := by
    obtain ⟨N₀, hN₀⟩ := hP.bnt_data
    rw [Filter.eventually_atTop]
    refine ⟨N₀ + 1, ?_⟩
    intro N hN
    exact hN₀ N (Nat.lt_of_succ_le hN)
  have hEq : ∀ᶠ N in atTop,
      ∑ j : Fin P.basisCount, a N j • mpvState (d := d) (P.basis j) N =
        ∑ j : Fin P.basisCount, b N j • mpvState (d := d) (P.basis j) N := by
    -- Under `SameMPV₂Pos`, the per-`N` MPV state identity is established only
    -- for `N ≥ 1`; this eventual identity suffices for the downstream
    -- `coefficient_eventually_eq_of_eventually_linearIndependent` consumer.
    refine Filter.eventually_atTop.mpr ⟨1, ?_⟩
    intro N hN
    have hPstate :
        mpvState (d := d) P.toTensor N =
          ∑ j : Fin P.basisCount, P.coeff N j •
            mpvState (d := d) (P.basis j) N := by
      refine mpvState_eq_sum_of_decomp (d := d) P.toTensor P.basis
        (N := N) (fun j => P.coeff N j) ?_
      intro σ
      simpa [smul_eq_mul] using P.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hQstate :
        mpvState (d := d) Q.toTensor N =
          ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := by
      refine mpvState_eq_sum_of_decomp (d := d) Q.toTensor Q.basis
        (N := N) (fun k => Q.coeff N k) ?_
      intro σ
      simpa [smul_eq_mul] using Q.mpv_toTensor_eq_sum_coeff (N := N) σ
    have hStateEq : mpvState (d := d) P.toTensor N = mpvState (d := d) Q.toTensor N := by
      apply PiLp.ext
      intro σ
      simpa [mpvState_apply, mpv] using hEqual N hN σ
    have hQsubst :
        (∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N) =
          ∑ k : Fin Q.basisCount,
            ((ζ k) ^ N * Q.coeff N k) •
              mpvState (d := d) (P.basis (β k)) N := by
      refine Finset.sum_congr rfl ?_
      intro k _
      have hState_k : mpvState (d := d) (Q.basis k) N =
          ((ζ k) ^ N) • mpvState (d := d) (P.basis (β k)) N := by
        apply PiLp.ext
        intro σ
        simpa [mpvState_apply, smul_eq_mul] using hζ_mpv k N σ
      calc
        Q.coeff N k • mpvState (d := d) (Q.basis k) N
            = Q.coeff N k • (((ζ k) ^ N) •
                mpvState (d := d) (P.basis (β k)) N) := by rw [hState_k]
        _ = (Q.coeff N k * (ζ k) ^ N) •
              mpvState (d := d) (P.basis (β k)) N := by rw [smul_smul]
        _ = ((ζ k) ^ N * Q.coeff N k) •
              mpvState (d := d) (P.basis (β k)) N := by rw [mul_comm]
    have hReindex :
        (∑ k : Fin Q.basisCount,
            ((ζ k) ^ N * Q.coeff N k) •
              mpvState (d := d) (P.basis (β k)) N) =
          ∑ j : Fin P.basisCount,
            (((ζ (β.symm j)) ^ N * Q.coeff N (β.symm j)) •
              mpvState (d := d) (P.basis j) N) := by
      let f : Fin Q.basisCount → MPVSpace d N := fun k =>
        ((ζ k) ^ N * Q.coeff N k) • mpvState (d := d) (P.basis (β k)) N
      let g : Fin P.basisCount → MPVSpace d N := fun j =>
        ((ζ (β.symm j)) ^ N * Q.coeff N (β.symm j)) •
          mpvState (d := d) (P.basis j) N
      have hfg : ∀ k, f k = g (β k) := by
        intro k
        simp [f, g]
      simpa [f, g] using (Fintype.sum_equiv β f g hfg)
    calc
      ∑ j : Fin P.basisCount, a N j • mpvState (d := d) (P.basis j) N
          = mpvState (d := d) P.toTensor N := by
              simpa [a] using hPstate.symm
      _ = mpvState (d := d) Q.toTensor N := hStateEq
      _ = ∑ k : Fin Q.basisCount, Q.coeff N k •
            mpvState (d := d) (Q.basis k) N := hQstate
      _ = ∑ k : Fin Q.basisCount,
            ((ζ k) ^ N * Q.coeff N k) •
              mpvState (d := d) (P.basis (β k)) N := hQsubst
      _ = ∑ j : Fin P.basisCount, b N j •
            mpvState (d := d) (P.basis j) N := by
              simpa [b] using hReindex
  have hCoeff : ∀ᶠ N in atTop, ∀ j : Fin P.basisCount, a N j = b N j := by
    set_option maxRecDepth 1024 in
    exact coefficient_eventually_eq_of_eventually_linearIndependent
      (v := fun N j => mpvState (d := d) (P.basis j) N) (a := a) (b := b) hLI hEq
  rw [Filter.eventually_atTop] at hCoeff
  obtain ⟨N₀, hN₀⟩ := hCoeff
  intro k
  refine ⟨N₀, ?_⟩
  intro N hN
  have h := hN₀ N (le_of_lt hN) (β k)
  simpa [a, b] using h

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem coeff_identity_via_matched_mpv_phase
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (ζ : Fin Q.basisCount → ℂ)
    (hζ_mpv : ∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ) :
    ∀ k : Fin Q.basisCount, ∃ N₀, ∀ N > N₀,
      P.coeff N (β k) = (ζ k) ^ N * Q.coeff N k :=
  coeff_identity_via_matched_mpv_phasePos
    (P := P) (Q := Q) hP hEqual.toSameMPV₂Pos β ζ hζ_mpv

/-- **CPSV16 §II.C lines 1187–1188, full-basis coefficient identity.**

Assume a full matched-basis equivalence `β : Fin Q.basisCount ≃
Fin P.basisCount`, with every `Q`-block gauge-phase equivalent to the
corresponding `P`-block.  Substituting the MPV phase relation for each
matched pair into `SameMPV₂ P.toTensor Q.toTensor`, reindexing the `Q`-sum
by `β`, and applying A-only BNT linear independence (`hP.bnt_data`) gives
an eventual exact coefficient identity

`P.coeff N (β k) = ζ_k^N * Q.coeff N k`.

This is the formal counterpart of CPSV16 line 1188's exact power-sum
comparison; it deliberately avoids the unsound asymptotic-difference to
full-multiset route noted in the multiplicity-audit memo. -/
theorem coeff_identity_via_global_gaugePos
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂Pos P.toTensor Q.toTensor)
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hMatch : ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) :
    ∀ k : Fin Q.basisCount, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ N₀, ∀ N > N₀,
      P.coeff N (β k) = ζ ^ N * Q.coeff N k := by
  classical
  -- Extract a per-block unit-modulus phase ζ with the MPV scalar-power
  -- relation `mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis (β k)) σ`.
  let phaseData : (k : Fin Q.basisCount) →
      { ζ : ℂ // ‖ζ‖ = 1 ∧
        ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (Q.basis k) σ = ζ ^ N * mpv (P.basis (β k)) σ } := fun k =>
    let hm := hMatch k
    let hdim : P.basisDim (β k) = Q.basisDim k := hm.choose
    let hGPE : GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) hdim) (P.basis (β k))) (Q.basis k) :=
      hm.choose_spec
    let res := extract_unit_gauge_phase_mpv hP hQ hdim hGPE
    ⟨res.choose, res.choose_spec⟩
  let ζ : Fin Q.basisCount → ℂ := fun k => (phaseData k).val
  have hζ_norm : ∀ k : Fin Q.basisCount, ‖ζ k‖ = 1 := fun k =>
    (phaseData k).property.1
  have hζ_mpv : ∀ (k : Fin Q.basisCount) (N : ℕ) (σ : Fin N → Fin d),
      mpv (Q.basis k) σ = (ζ k) ^ N * mpv (P.basis (β k)) σ := fun k =>
    (phaseData k).property.2
  -- Feed the matched MPV phases into the fixed-phase identity.
  have hCoeff := coeff_identity_via_matched_mpv_phasePos
    (P := P) (Q := Q) hP hEqual β ζ hζ_mpv
  intro k
  obtain ⟨N₀, hN₀⟩ := hCoeff k
  exact ⟨ζ k, hζ_norm k, N₀, hN₀⟩

/-- Reformulation for the all-length `SameMPV₂` form. -/
theorem coeff_identity_via_global_gauge
    {P Q : SectorDecomposition d}
    (hP : IsBNTCanonicalForm P) (hQ : IsBNTCanonicalForm Q)
    (hEqual : SameMPV₂ P.toTensor Q.toTensor)
    (β : Fin Q.basisCount ≃ Fin P.basisCount)
    (hMatch : ∀ k : Fin Q.basisCount, ∃ h : P.basisDim (β k) = Q.basisDim k,
      GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) h) (P.basis (β k))) (Q.basis k)) :
    ∀ k : Fin Q.basisCount, ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ∃ N₀, ∀ N > N₀,
      P.coeff N (β k) = ζ ^ N * Q.coeff N k :=
  coeff_identity_via_global_gaugePos
    (P := P) (Q := Q) hP hQ hEqual.toSameMPV₂Pos β hMatch

end MPSTensor
