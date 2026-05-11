/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalDominant

/-!
# Uniqueness of non-decaying BNT overlap partners

This module isolates the uniqueness step for non-decaying partners in the
CPSV16 Fundamental Theorem proof.
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **Uniqueness of a non-decaying left partner for a BNT block.**

Source context: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. After the
proof finds a block whose overlap with a fixed block does not decay, Corollary
`eqV` and Lemma `equalMPS` identify the two blocks up to gauge and phase. Hence
a fixed block on one side cannot have two distinct non-decaying partners on the
other side, because that would force two distinct BNT blocks on the latter side
to have a non-decaying mutual overlap. -/
lemma unique_left_nondecaying_overlap_partner_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (k : Fin rB) (j₁ j₂ : Fin rA)
    (h1 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₁) (B k) N) atTop (nhds 0))
    (h2 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₂) (B k) N) atTop (nhds 0)) :
    j₁ = j₂ := by
  have hA_inj_local := hA.toHasInjectiveBlocks.block_injective
  have hB_inj_local := hB.toHasInjectiveBlocks.block_injective
  have hA_left_local := hA.toIsLeftCanonicalBlockFamily.leftCanonical
  have hB_left_local := hB.toIsLeftCanonicalBlockFamily.leftCanonical
  have hA_self := hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self := hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hA_cross := hA.cross_overlap_tendsto_zero
  by_contra hne
  have hdim1 : dimA j₁ = dimB k := by
    by_contra hd
    exact h1 (mpvOverlap_tendsto_zero_of_dim_ne _ _
      (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) hd)
  have hdim2 : dimA j₂ = dimB k := by
    by_contra hd
    exact h2 (mpvOverlap_tendsto_zero_of_dim_ne _ _
      (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) hd)
  have hgpe1 : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim1) (A j₁)) (B k) := by
    by_contra h
    exact h1 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim1 _ _ (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) h)
  have hgpe2 : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim2) (A j₂)) (B k) := by
    by_contra h
    exact h2 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim2 _ _ (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) h)
  obtain ⟨X1, ζ1, _, hX1⟩ := hgpe1
  obtain ⟨X2, ζ2, _, hX2⟩ := hgpe2
  have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k) σ = ζ1 ^ N * mpv (A j₁) σ := fun N σ => by
    rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ, mpv_cast_dim hdim1]
  have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B k) σ = ζ2 ^ N * mpv (A j₂) σ := fun N σ => by
    rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ, mpv_cast_dim hdim2]
  have hBB_norm :
      Tendsto (fun N => ‖mpvOverlap (d := d) (B k) (B k) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (B k) (hB_self k)
  have hAA1_norm :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₁) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A j₁) (hA_self j₁)
  have hAA2_norm :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A j₂) (A j₂) N‖) atTop (nhds 1) :=
    tendsto_norm_selfOverlap_one (d := d) (A j₂) (hA_self j₂)
  have hζ1_norm : ‖ζ1‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA1_norm hBB_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₁) (B := B k) (ζ := ζ1) hmpv1)
  have hζ2_norm : ‖ζ2‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale hAA2_norm hBB_norm
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₂) (B := B k) (ζ := ζ2) hmpv2)
  have hCross_eq : ∀ N : ℕ,
      mpvOverlap (d := d) (A j₁) (A j₂) N =
      (starRingEnd ℂ ζ1 * ζ2) ^ N * mpvOverlap (d := d) (B k) (B k) N := by
    intro N
    simp only [mpvOverlap]
    have hζ1_star_mul : starRingEnd ℂ ζ1 * ζ1 = 1 := by
      have := Complex.conj_mul' ζ1
      rw [this, hζ1_norm, Complex.ofReal_one, one_pow]
    have hζ2_star_mul : starRingEnd ℂ ζ2 * ζ2 = 1 := by
      have := Complex.conj_mul' ζ2
      rw [this, hζ2_norm, Complex.ofReal_one, one_pow]
    have hA1_eq : ∀ σ : Cfg d N, mpv (A j₁) σ =
        (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j₁) σ) := fun σ => by
      rw [← mul_assoc, ← mul_pow, hζ1_star_mul, one_pow, one_mul]
    have hA2_eq : ∀ σ : Cfg d N, mpv (A j₂) σ =
        (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j₂) σ) := fun σ => by
      rw [← mul_assoc, ← mul_pow, hζ2_star_mul, one_pow, one_mul]
    have hStep : ∀ σ : Cfg d N, mpv (A j₁) σ * star (mpv (A j₂) σ) =
        (starRingEnd ℂ ζ1) ^ N * mpv (B k) σ *
        star ((starRingEnd ℂ ζ2) ^ N * mpv (B k) σ) := by
      intro σ
      rw [hA1_eq σ, ← hmpv1 N σ, hA2_eq σ, ← hmpv2 N σ]
    simp_rw [hStep]
    simp only [star_mul, star_pow, RCLike.star_def, starRingEnd_self_apply]
    rw [mul_pow]
    rw [Finset.mul_sum]
    congr 1
    ext σ
    ring
  have hNormζ : ‖starRingEnd ℂ ζ1 * ζ2‖ = 1 := by
    rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
  have hCross_norm_one :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 1) := by
    have heq : (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) =
        fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
      ext N
      rw [hCross_eq, norm_mul]
    rw [heq]
    have : (fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
        ‖mpvOverlap (d := d) (B k) (B k) N‖) =
        fun N => 1 * ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
      ext N
      rw [norm_pow, hNormζ, one_pow]
    rw [this]
    simpa only [one_mul] using hBB_norm
  have hCross_norm_zero :
      Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 0) := by
    convert (hA_cross j₁ j₂ hne).norm using 1
    simp only [norm_zero]
  exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)

/-- **Uniqueness of a non-decaying right partner for a BNT block.**

This is the symmetric form of
`unique_left_nondecaying_overlap_partner_CFBNT`; it is the same CPSV16
Theorem `thm1`, lines 1170--1192, uniqueness step with the two tensor
families interchanged. -/
lemma unique_right_nondecaying_overlap_partner_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (j : Fin rA) (k₁ k₂ : Fin rB)
    (h1 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₁) N) atTop (nhds 0))
    (h2 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₂) N) atTop (nhds 0)) :
    k₁ = k₂ := by
  have h1' :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (B k₁) (A j) N) atTop (nhds 0) := by
    intro h
    exact h1 (tendsto_mpvOverlap_zero_swap (d := d) (B k₁) (A j) h)
  have h2' :
      ¬ Tendsto (fun N => mpvOverlap (d := d) (B k₂) (A j) N) atTop (nhds 0) := by
    intro h
    exact h2 (tendsto_mpvOverlap_zero_swap (d := d) (B k₂) (A j) h)
  exact unique_left_nondecaying_overlap_partner_CFBNT B A hB hA j k₁ k₂ h1' h2'

end HeteroEqualCase

end MPSTensor
