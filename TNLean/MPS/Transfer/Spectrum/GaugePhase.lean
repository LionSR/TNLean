/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Tensor.Defs
import TNLean.MPS.Tensor.Overlap
import TNLean.MPS.Transfer.Spectrum.PrimitiveOverlap
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapInjective
import TNLean.MPS.Transfer.Spectrum.TransferOperatorGapNT
import TNLean.MPS.Transfer.Irreducible.PhysicalReindexTransport
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Shared gauge-phase lemmas for MPS tensors

This module collects generic gauge-phase identities and overlap-to-gauge
recovery results used by both the single-block proportional FT and the
canonical-form equal-norm argument.

It also contains the following results.

* `MPSTensor.mpvOverlap_norm_tendsto_one_of_eventually_proportionalMPV₂`,
  `MPSTensor.exists_ge_not_forall_mpv_eq_mul_of_not_gaugePhaseEquiv_of_irreducible_TP`: proportional
  single-block Fundamental Theorem (primitive case).
-/

open MPTensor

open scoped Matrix BigOperators Kraus

namespace MPSTensor

section GaugePhase

variable {α : Type*} [Fintype α] {d D : ℕ}

omit [Fintype α] in
/-- If `B i = ζ • (X * A i * X⁻¹)` then `mpv B σ = ζ^N * mpv A σ`. -/
theorem mpv_eq_pow_mul_of_gaugePhase
    (A B : MPTensor α (Fin D))
    (X : GL (Fin D) ℂ) (ζ : ℂ)
    (hX :
      ∀ i : α,
        B i =
          ζ • ((X : Matrix (Fin D) (Fin D) ℂ) * A i *
            ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) :
    ∀ (N : ℕ) (σ : Fin N → α), mpv B σ = ζ ^ N * mpv A σ := by
  intro N σ
  classical
  set w : List α := List.ofFn σ
  have hwlen : w.length = N := by
    simp [w]
  let C : MPTensor α (Fin D) := fun i =>
    (X : Matrix (Fin D) (Fin D) ℂ) * A i *
      ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hB : B = fun i => ζ • C i := by
    funext i
    simpa [C] using hX i
  have hGauge :
      Kraus.evalWord C w =
        (X : Matrix (Fin D) (Fin D) ℂ) * Kraus.evalWord A w *
          ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [C] using (evalWord_gauge (A := A) (B := C) X (by intro i; rfl) w)
  have htrace : Matrix.trace (Kraus.evalWord C w) = Matrix.trace (Kraus.evalWord A w) := by
    simpa [hGauge, Matrix.mul_assoc] using (Kraus.trace_conj_eq (X := X) (M := Kraus.evalWord A w))
  calc
    mpv B σ = Matrix.trace (Kraus.evalWord B w) := by
      simp [mpv, coeff, w]
    _ = Matrix.trace (Kraus.evalWord (fun i => ζ • C i) w) := by
      simp [hB]
    _ = Matrix.trace ((ζ ^ w.length) • Kraus.evalWord C w) := by
          simpa using congrArg Matrix.trace (Kraus.evalWord_smul (ζ := ζ) (K := C) w)
    _ = (ζ ^ w.length) * Matrix.trace (Kraus.evalWord C w) := by
          simp [Matrix.trace_smul, smul_eq_mul]
    _ = (ζ ^ w.length) * Matrix.trace (Kraus.evalWord A w) := by
          simp [htrace]
    _ = ζ ^ N * mpv A σ := by
          simp [mpv, coeff, w, hwlen]

private theorem mpvOverlap_cross_scale_of_mpv_eq_pow_mul_at
    {D D1 D2 N : ℕ} {A : MPTensor α (Fin D)} {B1 : MPTensor α (Fin D1)} {B2 : MPTensor α (Fin D2)}
    {ζ1 ζ2 : ℂ}
    (hmpv1 : ∀ σ : Fin N → α, mpv B1 σ = ζ1 ^ N * mpv A σ)
    (hmpv2 : ∀ σ : Fin N → α, mpv B2 σ = ζ2 ^ N * mpv A σ) :
    mpvOverlap (α := α) B1 B2 N =
      (ζ1 * star ζ2) ^ N * mpvOverlap (α := α) A A N := by
  classical
  simp only [mpvOverlap]
  simp_rw [hmpv1, hmpv2, star_mul, star_pow]
  simp_rw [show ∀ x : Fin N → α,
      ζ1 ^ N * mpv A x * (star (mpv A x) * (star ζ2) ^ N) =
        ζ1 ^ N * (star ζ2) ^ N * (mpv A x * star (mpv A x)) from
      fun x => by ring]
  rw [← Finset.mul_sum, mul_pow]

/-- If two matrix-product vector families are obtained from a common family by
length-dependent phases `ζ1 ^ N` and `ζ2 ^ N`, then their mixed overlap is
`(ζ1 * conj ζ2) ^ N` times the self-overlap of the common family. -/
theorem mpvOverlap_cross_scale_of_mpv_eq_pow_mul
    {D D1 D2 : ℕ} {A : MPTensor α (Fin D)} {B1 : MPTensor α (Fin D1)} {B2 : MPTensor α (Fin D2)}
    {ζ1 ζ2 : ℂ}
    (hmpv1 : ∀ (N : ℕ) (σ : Fin N → α), mpv B1 σ = ζ1 ^ N * mpv A σ)
    (hmpv2 : ∀ (N : ℕ) (σ : Fin N → α), mpv B2 σ = ζ2 ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (α := α) B1 B2 N =
        (ζ1 * star ζ2) ^ N * mpvOverlap (α := α) A A N :=
  fun N => mpvOverlap_cross_scale_of_mpv_eq_pow_mul_at (hmpv1 N) (hmpv2 N)

/-- Positive-length overlap scaling for two MPV families with a common representative. -/
theorem mpvOverlap_cross_scale_of_mpv_eq_pow_mul_pos
    {D D1 D2 : ℕ} {A : MPTensor α (Fin D)} {B1 : MPTensor α (Fin D1)} {B2 : MPTensor α (Fin D2)}
    {ζ1 ζ2 : ℂ}
    (hmpv1 : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → α,
      mpv B1 σ = ζ1 ^ N * mpv A σ)
    (hmpv2 : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → α,
      mpv B2 σ = ζ2 ^ N * mpv A σ) :
    ∀ N : ℕ, 0 < N →
      mpvOverlap (α := α) B1 B2 N =
        (ζ1 * star ζ2) ^ N * mpvOverlap (α := α) A A N :=
  fun N hN => mpvOverlap_cross_scale_of_mpv_eq_pow_mul_at (hmpv1 N hN) (hmpv2 N hN)

/-- If `mpv B σ = ζ ^ N * mpv A σ` for every system size `N` and configuration `σ`, then the
self-overlap of `B` scales by `(ζ * conj ζ) ^ N` times the self-overlap of `A`. -/
theorem mpvOverlap_self_scale_of_mpv_eq_pow_mul
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ) (σ : Fin N → α), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N := by
  simpa using
    (mpvOverlap_cross_scale_of_mpv_eq_pow_mul
      (A := A) (B1 := B) (B2 := B) (ζ1 := ζ) (ζ2 := ζ) hmpv hmpv)

/-- Positive-length form of `mpvOverlap_self_scale_of_mpv_eq_pow_mul`. -/
theorem mpvOverlap_self_scale_of_mpv_eq_pow_mul_pos
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → α,
      mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ, 0 < N →
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N := by
  simpa using
    (mpvOverlap_cross_scale_of_mpv_eq_pow_mul_pos
      (A := A) (B1 := B) (B2 := B) (ζ1 := ζ) (ζ2 := ζ) hmpv hmpv)

private theorem mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_at
    {D D' N : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hmpv : ∀ σ : Fin N → α, mpv B σ = ζ ^ N * mpv A σ) :
    mpvOverlap (α := α) A B N =
      (star ζ) ^ N * mpvOverlap (α := α) A A N := by
  classical
  calc
    mpvOverlap (α := α) A B N =
        ∑ σ : Fin N → α, mpv A σ * star (ζ ^ N * mpv A σ) := by
          simp only [mpvOverlap]
          refine Finset.sum_congr rfl ?_
          intro σ _
          rw [hmpv σ]
    _ = ∑ σ : Fin N → α,
        (star ζ) ^ N * (mpv A σ * star (mpv A σ)) := by
          refine Finset.sum_congr rfl ?_
          intro σ _
          have hstar :
              star (ζ ^ N * mpv A σ) = star (mpv A σ) * (star ζ) ^ N := by
            rw [StarMul.star_mul, star_pow]
          rw [hstar]
          ring
    _ = (star ζ) ^ N * mpvOverlap (α := α) A A N := by
          simp [mpvOverlap, Finset.mul_sum]

/-- If all matrix-product amplitudes of `B` are obtained from those of `A` by the
length-dependent phase `ζ ^ N`, then the mixed overlap with `A` is
`(conj ζ) ^ N` times the self-overlap of `A`. -/
theorem mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ) (σ : Fin N → α), mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ,
      mpvOverlap (α := α) A B N =
        (star ζ) ^ N * mpvOverlap (α := α) A A N :=
  fun N => mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_at (hmpv N)

/-- Positive-length form of
`mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul`. -/
theorem mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_pos
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hmpv : ∀ (N : ℕ), 0 < N → ∀ σ : Fin N → α,
      mpv B σ = ζ ^ N * mpv A σ) :
    ∀ N : ℕ, 0 < N →
      mpvOverlap (α := α) A B N =
        (star ζ) ^ N * mpvOverlap (α := α) A A N :=
  fun N hN => mpvOverlap_eq_star_pow_mul_self_of_mpv_eq_pow_mul_at (hmpv N hN)

private theorem norm_eq_one_of_selfOverlap_scale_at_nonzero_limit_pos_aux
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    {r : ℝ} (hr : r ≠ 0)
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) A A N‖) Filter.atTop (nhds r))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) B B N‖) Filter.atTop (nhds r))
    (hSelf : ∀ N : ℕ, 0 < N →
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N) :
    ‖ζ‖ = 1 := by
  have hAA_ne : ∀ᶠ N in Filter.atTop, ‖mpvOverlap (α := α) A A N‖ ≠ 0 :=
    hAA.eventually_ne hr
  have hRatio : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) B B N‖ /
      ‖mpvOverlap (α := α) A A N‖) Filter.atTop (nhds 1) :=
    (tendsto_div_nhds_one_iff_eq₀ hBB hAA hr).2 rfl
  have hRatioEq : ∀ᶠ N in Filter.atTop,
      ‖mpvOverlap (α := α) B B N‖ / ‖mpvOverlap (α := α) A A N‖ = (‖ζ‖ ^ 2) ^ N := by
    filter_upwards [hAA_ne, Filter.eventually_ge_atTop 1] with N hN hNpos
    rw [hSelf N hNpos, norm_mul, norm_pow,
      show ‖ζ * starRingEnd ℂ ζ‖ = ‖ζ‖ ^ 2 from by
        rw [norm_mul, RCLike.norm_conj, sq]]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_div_cancel_of_imp (fun h => absurd h hN)
  have hPow : Filter.Tendsto (fun N => (‖ζ‖ ^ 2) ^ N) Filter.atTop (nhds 1) :=
    hRatio.congr' hRatioEq
  have h1 : ‖ζ‖ ^ 2 = 1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact one_ne_zero
        (tendsto_nhds_unique hPow (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h))
    · have hlt2 : ∀ᶠ n in Filter.atTop, (‖ζ‖ ^ 2) ^ n < 2 :=
        hPow.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
      rcases ((Filter.tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt h) 2).and hlt2).exists
        with ⟨n, hn1, hn2⟩
      exact not_lt_of_ge hn1 hn2
  nlinarith [norm_nonneg ζ]

/-- If two self-overlaps have the same nonzero norm limit, and one scales from
the other by powers of `ζ * conj ζ`, then `ζ` has unit norm. -/
theorem norm_eq_one_of_selfOverlap_scale_at_nonzero_limit
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    {r : ℝ} (hr : r ≠ 0)
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) A A N‖) Filter.atTop (nhds r))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) B B N‖) Filter.atTop (nhds r))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N) :
    ‖ζ‖ = 1 :=
  norm_eq_one_of_selfOverlap_scale_at_nonzero_limit_pos_aux hr hAA hBB
    (fun N _hN => hSelf N)

/-- If two self-overlaps both have norm limit `1`, and one scales from the other by powers of
`ζ * conj ζ`, then `ζ` has unit norm. -/
theorem norm_eq_one_of_selfOverlap_scale
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) A A N‖) Filter.atTop (nhds 1))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) B B N‖) Filter.atTop (nhds 1))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N) :
    ‖ζ‖ = 1 :=
  norm_eq_one_of_selfOverlap_scale_at_nonzero_limit one_ne_zero hAA hBB hSelf

/-- Positive-length form of `norm_eq_one_of_selfOverlap_scale`.  The proof only
uses the scaling identity eventually, so no value at length zero is required. -/
theorem norm_eq_one_of_selfOverlap_scale_pos
    {D D' : ℕ} {A : MPTensor α (Fin D)} {B : MPTensor α (Fin D')} {ζ : ℂ}
    (hAA : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) A A N‖) Filter.atTop (nhds 1))
    (hBB : Filter.Tendsto (fun N => ‖mpvOverlap (α := α) B B N‖) Filter.atTop (nhds 1))
    (hSelf : ∀ N : ℕ, 0 < N →
      mpvOverlap (α := α) B B N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (α := α) A A N) :
    ‖ζ‖ = 1 :=
  norm_eq_one_of_selfOverlap_scale_at_nonzero_limit_pos_aux one_ne_zero hAA hBB hSelf

section OverlapGauge

variable [NeZero D]

/-! ## Gauge-phase equivalence from unit-modulus overlap -/

private theorem dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP_fin
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hA_irr : Kraus.IsIrreducibleFamily A)
    (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    D₁ = D₂ := by
  by_contra hdim
  have hzero :
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) A B N) Filter.atTop
        (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP
      A B hA_irr hB_irr hA_norm hB_norm hdim
  have hnorm_zero :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (0 : ℝ)) := by
    simpa using hzero.norm
  exact one_ne_zero (tendsto_nhds_unique hOverlap hnorm_zero)

/-- **Bond-dimension equality from a non-decaying rectangular overlap.**

Source: arXiv:1606.00608, Lemma `equalMPS`, statement lines 1080--1091 and
proof lines 1093--1117.  Two irreducible trace-preserving tensors whose
rectangular MPV overlap has norm tending to one have equal bond dimensions.
Indeed, distinct bond dimensions would force the same overlap to tend to zero.

This is the bond-dimension part of the source lemma, separated from the
same-dimension gauge recovery below.  The relation to the full source statement
is recorded in `docs/paper-gaps/cpsv16_equalMPS_gauge_phase_gap.tex`. -/
theorem dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP
    {D₁ D₂ : ℕ} [NeZero D₁] [NeZero D₂]
    (A : MPTensor α (Fin D₁)) (B : MPTensor α (Fin D₂))
    (hA_irr : Kraus.IsIrreducibleFamily A)
    (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_norm : ∑ i : α, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : α, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap A B N‖) Filter.atTop (nhds (1 : ℝ))) :
    D₁ = D₂ := by
  -- The proof runs on the `Fin` alphabet obtained by relabelling along `Fintype.equivFin`.
  let e := (Fintype.equivFin α).symm
  exact dim_eq_of_mpvOverlap_norm_tendsto_one_of_irreducible_TP_fin
    (Kraus.reindexPhysical e A) (Kraus.reindexPhysical e B)
    ((Kraus.isIrreducibleFamily_reindexPhysical_equiv e A).2 hA_irr)
    ((Kraus.isIrreducibleFamily_reindexPhysical_equiv e B).2 hB_irr)
    ((e.sum_comp fun i ↦ (A i)ᴴ * A i).trans hA_norm)
    ((e.sum_comp fun i ↦ (B i)ᴴ * B i).trans hB_norm)
    (by simpa only [mpvOverlap_reindexPhysical_equiv] using hOverlap)

/-- **Spectral radius lower bound from unit-modulus overlap.**

Source: arXiv:1606.00608, proof of Lemma equalMPS, lines 1093-1117.
This is the spectral-radius step inside the proof: if the modulus of the
overlap tends to `1`, the cross-transfer spectral radius is at least `1`.

The proof is the contrapositive of
`mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one`: if the
spectral radius were strictly less than `1`, the overlap (and hence its
modulus) would tend to `0`, contradicting the hypothesis.

The proof uses the rectangular overlap-decay theorem
`mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one`, whose proof rests on the
mixed-transfer trace identity, with no proportionality hypothesis required. -/
theorem mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one
    (A B : MPSTensor d D)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    1 ≤ Kraus.mixedTransferSpectralRadius A B := by
  by_contra hlt
  push Not at hlt
  -- Unpack `Kraus.mixedTransferSpectralRadius` in the equal-dimension rectangular form.
  have hlt' :
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
            (Kraus.mixedMapLM (D₁ := D) (D₂ := D) A B)) < 1 := by
    simpa [Kraus.mixedTransferSpectralRadius] using hlt
  have hzero :
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) A B N) Filter.atTop
        (nhds (0 : ℂ)) :=
    mpvOverlap_tendsto_zero_of_mixedTransferSpectralRadius_lt_one
      (A := A) (B := B) hlt'
  have hnorm_zero :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (0 : ℝ)) := by
    simpa using hzero.norm
  have h01 : (1 : ℝ) = 0 := tendsto_nhds_unique hOverlap hnorm_zero
  exact one_ne_zero h01


private theorem gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP_fin
    (A B : MPSTensor d D)
    (hA_irr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) A)
    (hB_irr : Kraus.IsIrreducibleFamily (ι := Fin d) (n := Fin D) B)
    (hA_norm : ∑ i : Fin d, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : Fin d, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (1 : ℝ))) :
    GaugePhaseEquiv A B :=
  modulus_one_eigenvalue_implies_gauge_of_irreducible_TP
    A B hA_irr hB_irr hA_norm hB_norm
    (mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one
      (A := A) (B := B) hOverlap)

/-- **Gauge-phase equivalence from unit-modulus overlap.**

Source: arXiv:1606.00608, Lemma equalMPS, statement lines 1080-1091 and
proof lines 1093-1117. If two
irreducible trace-preserving (left-canonical) blocks of the same bond
dimension have asymptotically unit-modulus overlap, then they are
gauge-phase equivalent.

This is the **proportionality-free** version of the gauge recovery — the
counterpart to the proportionality-based gauge recovery
without the extra `NonzeroProportionalMPV₂` hypothesis. The proof uses the
cross-transfer-matrix spectral radius (computed via
`mixedTransferSpectralRadius_ge_one_of_mpvOverlap_norm_tendsto_one`)
together with the rigidity theorem
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`.

**Scope restriction (same bond dimension):** this theorem proves the gauge
recovery for two tensors of a common bond dimension `D`. The source Lemma
equalMPS additionally concludes `D_a = D_b` in the unit-overlap case; that
bond-dimension matching follows from the rectangular overlap-decay theorem
`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` (distinct bond dimensions
force the overlap to decay, so a non-decaying overlap forces equal dimensions),
which is applied directly where blocks of differing dimension arise. Documented
in `docs/paper-gaps/cpsv16_equalMPS_gauge_phase_gap.tex`. -/
theorem gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP
    (A B : MPTensor α (Fin D))
    (hA_irr : Kraus.IsIrreducibleFamily A)
    (hB_irr : Kraus.IsIrreducibleFamily B)
    (hA_norm : ∑ i : α, (A i)ᴴ * A i = 1)
    (hB_norm : ∑ i : α, (B i)ᴴ * B i = 1)
    (hOverlap :
      Filter.Tendsto (fun N => ‖mpvOverlap A B N‖) Filter.atTop (nhds (1 : ℝ))) :
    GaugePhaseEquiv A B := by
  -- The proof runs on the `Fin` alphabet obtained by relabelling along `Fintype.equivFin`.
  let e := (Fintype.equivFin α).symm
  exact (gaugePhaseEquiv_reindexPhysical_equiv e A B).1
    (gaugePhaseEquiv_of_overlap_norm_tendsto_one_of_irreducible_TP_fin
      (Kraus.reindexPhysical e A) (Kraus.reindexPhysical e B)
      ((Kraus.isIrreducibleFamily_reindexPhysical_equiv e A).2 hA_irr)
      ((Kraus.isIrreducibleFamily_reindexPhysical_equiv e B).2 hB_irr)
      ((e.sum_comp fun i ↦ (A i)ᴴ * A i).trans hA_norm)
      ((e.sum_comp fun i ↦ (B i)ᴴ * B i).trans hB_norm)
      (by simpa only [mpvOverlap_reindexPhysical_equiv] using hOverlap))

end OverlapGauge

/-! ### Symmetry, transitivity, and cast-composition of `GaugePhaseEquiv`

The following four lemmas record purely algebraic facts about the
`GaugePhaseEquiv` predicate (defined in `MPS.Defs`).  They were originally
local auxiliary lemmas in `MPS/FundamentalTheorem/SectorBNT/StrongMatch.lean` for the
bijective-matching argument, but are module-agnostic and so
live here, next to the existing gauge-phase shared infrastructure. -/

/-- Symmetry of `GaugePhaseEquiv` at a fixed bond dimension.

`GaugePhaseEquiv A B` says there exist a gauge `X ∈ GL` and a nonzero
scalar `ζ` such that `B i = ζ • (X * A i * X⁻¹)` for every physical
index `i`.  Conjugating by `X⁻¹` and scaling by `ζ⁻¹` gives the
reversed identity `A i = ζ⁻¹ • (X⁻¹ * B i * X)`, i.e.
`GaugePhaseEquiv B A`. -/
theorem gaugePhaseEquiv_symm_same_dim {α : Type*} {D : ℕ} {A B : MPTensor α (Fin D)}
    (h : GaugePhaseEquiv A B) : GaugePhaseEquiv B A := by
  classical
  obtain ⟨X, ζ, hζ, hrel⟩ := h
  refine ⟨X⁻¹, ζ⁻¹, inv_ne_zero hζ, ?_⟩
  intro i
  -- From `B i = ζ • (X * A i * X⁻¹)` derive `A i = ζ⁻¹ • (X⁻¹ * B i * X)`.
  have hBi := hrel i
  -- Abbreviations for the matrix coercions.
  set XM : Matrix (Fin D) (Fin D) ℂ := (X : Matrix (Fin D) (Fin D) ℂ)
  set XinvM : Matrix (Fin D) (Fin D) ℂ :=
    ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  have hXX : XinvM * XM = (1 : Matrix (Fin D) (Fin D) ℂ) := by
    have hU : (X⁻¹ * X : GL (Fin D) ℂ) = 1 := by simp
    have hUval :
        ((X⁻¹ * X : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
          = ((1 : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) :=
      congrArg Units.val hU
    simp only [Units.val_mul, Units.val_one] at hUval
    exact hUval
  -- Inverse-of-inverse: `(X⁻¹)⁻¹ = X` for units.
  have hInvInv : ((X⁻¹)⁻¹ : GL (Fin D) ℂ) = X := inv_inv X
  -- The desired identity: `A i = ζ⁻¹ • (X⁻¹ * B i * X)`.
  -- Multiply `hBi : B i = ζ • (X * A i * X⁻¹)` on the left by `X⁻¹` and on
  -- the right by `X`:
  --   X⁻¹ * B i * X = ζ • (X⁻¹ * X * A i * X⁻¹ * X) = ζ • (1 * A i * 1) = ζ • A i.
  have hSandwich :
      XinvM * B i * XM = ζ • A i := by
    calc
      XinvM * B i * XM
          = XinvM * (ζ • (XM * A i * XinvM)) * XM := by rw [hBi]
      _ = ζ • (XinvM * (XM * A i * XinvM) * XM) := by
            simp
      _ = ζ • ((XinvM * XM) * A i * (XinvM * XM)) := by
            simp [Matrix.mul_assoc]
      _ = ζ • A i := by rw [hXX]; simp
  -- Now divide by `ζ`.
  have hAi : A i = ζ⁻¹ • (XinvM * B i * XM) := by
    have := congrArg (fun M => (ζ⁻¹ : ℂ) • M) hSandwich
    simp only [smul_smul, inv_mul_cancel₀ hζ, one_smul] at this
    exact this.symm
  -- Use the inverse of `X⁻¹`, which is `X`.
  -- The goal expects `((X⁻¹)⁻¹ : GL).val = X.val`.
  change A i = ζ⁻¹ • (XinvM * B i *
    (((X⁻¹)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))
  simpa [hInvInv, XM, XinvM] using hAi

/-- Symmetry of `GaugePhaseEquiv` across a bond-dim cast: if the cast
maps the *right-hand* tensor into the *left-hand* space, then we may
flip both the cast direction and the equivalence direction.

The two forms are mathematically the same statement (after eliminating
the cast by `subst`), but the cast routing differs at the term level,
so we record this as an explicit auxiliary lemma. -/
theorem gaugePhaseEquiv_swap_cast {d D₁ D₂ : ℕ}
    (h : D₁ = D₂) {A : MPSTensor d D₁} {B : MPSTensor d D₂}
    (hGP : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h.symm) B) A) :
    GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h) A) B := by
  subst h
  -- After `subst`, both casts reduce to identity.
  simpa using gaugePhaseEquiv_symm_same_dim (by simpa using hGP)

/-- Transitivity of `GaugePhaseEquiv` at a fixed bond dimension.

If `B i = ζ₁ • (X₁ * A i * X₁⁻¹)` and `C i = ζ₂ • (X₂ * B i * X₂⁻¹)`,
then `C i = (ζ₂ ζ₁) • ((X₂ X₁) * A i * (X₂ X₁)⁻¹)`, giving
`GaugePhaseEquiv A C` with gauge `X₂ * X₁` and phase scalar `ζ₂ * ζ₁`. -/
theorem gaugePhaseEquiv_trans_same_dim {d D : ℕ} {A B C : MPSTensor d D}
    (h₁ : GaugePhaseEquiv A B) (h₂ : GaugePhaseEquiv B C) : GaugePhaseEquiv A C := by
  classical
  obtain ⟨X₁, ζ₁, hζ₁, hr₁⟩ := h₁
  obtain ⟨X₂, ζ₂, hζ₂, hr₂⟩ := h₂
  refine ⟨X₂ * X₁, ζ₂ * ζ₁, mul_ne_zero hζ₂ hζ₁, ?_⟩
  intro i
  -- Abbreviations for the matrix coercions of the four GL units in play.
  set X₁M : Matrix (Fin D) (Fin D) ℂ :=
    ((X₁ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₂M : Matrix (Fin D) (Fin D) ℂ :=
    ((X₂ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₁invM : Matrix (Fin D) (Fin D) ℂ :=
    ((X₁⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  set X₂invM : Matrix (Fin D) (Fin D) ℂ :=
    ((X₂⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)
  -- Coercion of the product `X₂ * X₁` to a matrix is the matrix product.
  have hMul_val :
      (((X₂ * X₁ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) = X₂M * X₁M := by
    simp [X₁M, X₂M]
  -- Coercion of the inverse of the product is the reversed product of inverses.
  have hMulInv_val :
      (((X₂ * X₁)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) = X₁invM * X₂invM := by
    simp [X₁invM, X₂invM]
  -- Compute `C i` by chaining the two equivalences.
  calc C i
      = ζ₂ • (X₂M * B i * X₂invM) := hr₂ i
    _ = ζ₂ • (X₂M * (ζ₁ • (X₁M * A i * X₁invM)) * X₂invM) := by rw [hr₁ i]
    _ = ζ₂ • (ζ₁ • (X₂M * (X₁M * A i * X₁invM) * X₂invM)) := by
          simp [smul_smul]
    _ = (ζ₂ * ζ₁) • (X₂M * X₁M * A i * X₁invM * X₂invM) := by
          simp [smul_smul, Matrix.mul_assoc]
    _ = (ζ₂ * ζ₁) • ((X₂M * X₁M) * A i * (X₁invM * X₂invM)) := by
          simp [Matrix.mul_assoc]
    _ = (ζ₂ * ζ₁) •
          ((((X₂ * X₁ : GL (Fin D) ℂ)) : Matrix (Fin D) (Fin D) ℂ) * A i *
            (((X₂ * X₁)⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) := by
          rw [hMul_val, hMulInv_val]

/-- Composition through a common centre `A`: if the cast `D = D₁` carries
`A : MPSTensor d D` into a gauge-phase equivalence with `B : MPSTensor d D₁`,
and similarly the cast `D = D₂` carries `A` into a gauge-phase equivalence
with `C : MPSTensor d D₂`, then `B` and `C` are gauge-phase equivalent
(after the dimension cast `D₁ = D₂`).

This cast-aware transitivity is used to compose two gauge-phase
equivalences through a shared centre tensor, eliminating the centre via
`gaugePhaseEquiv_symm_same_dim` and `gaugePhaseEquiv_trans_same_dim`. -/
theorem gaugePhaseEquiv_cast_compose_via_centre
    {d D D₁ D₂ : ℕ}
    (h₁ : D = D₁) (h₂ : D = D₂)
    {A : MPSTensor d D} {B : MPSTensor d D₁} {C : MPSTensor d D₂}
    (GE₁ : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h₁) A) B)
    (GE₂ : GaugePhaseEquiv (cast (congr_arg (MPSTensor d) h₂) A) C) :
    GaugePhaseEquiv
        (cast (congr_arg (MPSTensor d) (h₁.symm.trans h₂)) B) C := by
  subst h₁
  -- After `subst h₁`, `D₁` is replaced everywhere by `D`, the cast on
  -- `GE₁` reduces to identity, and `h₂.symm.trans h₂ = h₂`.
  subst h₂
  -- After `subst h₂`, all three tensors live in `MPSTensor d D`.
  simp only [cast_eq] at GE₁ GE₂ ⊢
  exact gaugePhaseEquiv_trans_same_dim (gaugePhaseEquiv_symm_same_dim GE₁) GE₂

end GaugePhase

section Proportional

/-!
## Proportional single-block Fundamental Theorem (primitive case)

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
`MPSTensor.mpvOverlap_tendsto_zero` from
`TNLean.Spectral.TransferOperatorGapInjective`.
-/

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
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) B B N) Filter.atTop (nhds (1 : ℂ)))
    (hProp :
      ∀ᶠ N in Filter.atTop, ∃ c : ℂ, ∀ σ : Fin N → Fin d,
        mpv A σ = c * mpv B σ) :
    Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
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
      (fun N => mpvOverlap (α := Fin d) A B N) =ᶠ[Filter.atTop]
        fun N => c N * mpvOverlap (α := Fin d) B B N := by
    filter_upwards [hc_event] with N hc
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc σ]
    ring
  have hOverlapAA :
      (fun N => mpvOverlap (α := Fin d) A A N) =ᶠ[Filter.atTop]
        fun N => (c N * star (c N)) * mpvOverlap (α := Fin d) B B N := by
    filter_upwards [hc_event] with N hc
    unfold mpvOverlap
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    rw [hc σ]
    simp only [star_mul]
    ring
  have hA_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A A N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    simpa using hA_self.norm
  have hB_self_norm :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) B B N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    simpa using hB_self.norm
  have hRatio :
      Filter.Tendsto
        (fun N => ‖mpvOverlap (α := Fin d) A A N‖ / ‖mpvOverlap (α := Fin d) B B N‖)
        Filter.atTop (nhds (1 : ℝ)) := by
    have hdiv := hA_self_norm.div hB_self_norm one_ne_zero
    have hfun :
        ((fun N => ‖mpvOverlap (α := Fin d) A A N‖) /
          (fun N => ‖mpvOverlap (α := Fin d) B B N‖)) =
            (fun N => ‖mpvOverlap (α := Fin d) A A N‖ / ‖mpvOverlap (α := Fin d) B B N‖) := by
      funext N
      rfl
    simpa [hfun] using hdiv
  have hB_self_norm_ne :
      (∀ᶠ N in Filter.atTop, ‖mpvOverlap (α := Fin d) B B N‖ ≠ (0 : ℝ)) :=
    hB_self_norm.eventually_ne one_ne_zero
  have hRatio_eq :
      (fun N => ‖mpvOverlap (α := Fin d) A A N‖ / ‖mpvOverlap (α := Fin d) B B N‖)
        =ᶠ[Filter.atTop] fun N => ‖c N‖ ^ 2 := by
    filter_upwards [hOverlapAA, hB_self_norm_ne] with N hAA hN
    calc
      ‖mpvOverlap (α := Fin d) A A N‖ / ‖mpvOverlap (α := Fin d) B B N‖
          = ‖(c N * star (c N)) * mpvOverlap (α := Fin d) B B N‖ /
              ‖mpvOverlap (α := Fin d) B B N‖ := by
                simp [hAA]
      _ = (‖c N * star (c N)‖ * ‖mpvOverlap (α := Fin d) B B N‖) /
            ‖mpvOverlap (α := Fin d) B B N‖ := by
                simp
      _ = ‖c N * star (c N)‖ := by
            simpa using
              (mul_div_cancel_right₀ (a := ‖c N * star (c N)‖)
                (b := ‖mpvOverlap (α := Fin d) B B N‖) hN)
      _ = ‖c N‖ ^ 2 := by
            simp [pow_two]
  have hc_normsq :
      Filter.Tendsto (fun N => ‖c N‖ ^ 2) Filter.atTop (nhds (1 : ℝ)) :=
    Filter.Tendsto.congr' hRatio_eq hRatio
  have hc_norm :
      Filter.Tendsto (fun N => ‖c N‖) Filter.atTop (nhds (1 : ℝ)) := by
    simpa [Real.sqrt_sq (norm_nonneg _)] using hc_normsq.sqrt
  have hCrossNorm :
      Filter.Tendsto (fun N => ‖mpvOverlap (α := Fin d) A B N‖) Filter.atTop
        (nhds (1 : ℝ)) := by
    have hmul :
        Filter.Tendsto (fun N => ‖c N‖ * ‖mpvOverlap (α := Fin d) B B N‖)
          Filter.atTop (nhds (1 : ℝ)) := by
      simpa using hc_norm.mul hB_self_norm
    have hCross_eq :
        (fun N => ‖mpvOverlap (α := Fin d) A B N‖) =ᶠ[Filter.atTop]
          fun N => ‖c N‖ * ‖mpvOverlap (α := Fin d) B B N‖ := by
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
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) A A N) Filter.atTop (nhds (1 : ℂ)))
    (hB_self :
      Filter.Tendsto (fun N => mpvOverlap (α := Fin d) B B N) Filter.atTop (nhds (1 : ℂ)))
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

end Proportional

end MPSTensor
