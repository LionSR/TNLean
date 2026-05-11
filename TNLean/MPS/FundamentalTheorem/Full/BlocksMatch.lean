/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.NondecayingOverlap
import TNLean.MPS.BNT.Construction

/-!
# Block matching for equal-MPV BNT families

`blocks_match_of_sameMPV₂_CFBNT`: from `SameMPV₂` on two assembled
`IsCanonicalFormBNT` families, obtain a `ProportionalDecompositionConclusion`:
equal block counts, a block permutation, and per-block gauge-phase equivalence.

## References

* Cirac, Pérez-García, Schuch, Verstraete, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
* Cirac, Pérez-García, Schuch, Verstraete, arXiv:1606.00608 Appendix A.
-/

open scoped Matrix BigOperators
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **Heterogeneous equal-case block matching**.

Given two `IsCanonicalFormBNT` families with `SameMPV₂` on their assembled
block-diagonal tensors, this produces equal block counts `rA = rB`, a block
permutation, and per-block gauge-phase equivalence.

The proof uses the overlap dichotomy: non-decaying cross-family overlap
forces equal block dimensions and gauge-phase equivalence; injectivity of
the matching follows from BNT separation.  The argument follows Cirac et al.
2021 (CPSV17) Appendix A. -/
lemma blocks_match_of_sameMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    ProportionalDecompositionConclusion A B := by
  have hμA_ne := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  have hμB_ne := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero
  obtain ⟨N0A, hLIA⟩ := hA.isBNT.eventually_li
  obtain ⟨N0B, hLIB⟩ := hB.isBNT.eventually_li
  -- Step 1: Weighted-sum identity in mpvState form.
  have hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N := by
    intro N
    have h_pointwise : ∀ σ : Cfg d N,
        ∑ j : Fin rA, μA j ^ N * mpv (A j) σ =
          ∑ k : Fin rB, μB k ^ N * mpv (B k) σ := by
      intro σ
      have hA_eq := mpv_toTensorFromBlocks_eq_sum μA A σ
      have hB_eq := mpv_toTensorFromBlocks_eq_sum μB B σ
      simp only [smul_eq_mul] at hA_eq hB_eq
      rw [← hA_eq, hEqual N σ, hB_eq]
    apply PiLp.ext; intro σ
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul]
    change ∑ x, μA x ^ N * (A x).mpvState N σ = ∑ x, μB x ^ N * (B x).mpvState N σ
    simp only [mpvState_apply]
    exact h_pointwise σ
  -- Step 2: Base cases rA = 0 or rB = 0.
  by_cases hrA : rA = 0
  · subst hrA
    have hrB : rB = 0 := by
      by_contra hrB_ne
      have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB_ne
      have hN := hLIB (N0B + 1) (by omega)
      have hzero :
          ∑ k : Fin rB, (μB k) ^ (N0B + 1) • mpvState (d := d) (B k) (N0B + 1) = 0 := by
        rw [← hSumState (N0B + 1)]
        simp [Finset.sum_empty]
      exact absurd
        (Fintype.linearIndependent_iff.mp hN _ hzero ⟨0, hrB_pos⟩)
        (pow_ne_zero (N0B + 1) (hμB_ne ⟨0, hrB_pos⟩))
    subst hrB
    exact ⟨rfl, Equiv.refl _, fun j => Fin.elim0 j⟩
  by_cases hrB : rB = 0
  · subst hrB
    exfalso
    have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
    have hN := hLIA (N0A + 1) (by omega)
    have hzero : ∑ j : Fin rA, (μA j) ^ (N0A + 1) • mpvState (d := d) (A j) (N0A + 1) = 0 := by
      rw [hSumState (N0A + 1)]
      simp [Finset.sum_empty]
    exact pow_ne_zero (N0A + 1) (hμA_ne ⟨0, hrA_pos⟩)
      (Fintype.linearIndependent_iff.mp hN _ hzero ⟨0, hrA_pos⟩)
  -- Step 3: Main case rA, rB ≥ 1 (overlap dichotomy + bijection construction).
  classical
  have hA_inj := hA.toHasInjectiveBlocks.block_injective
  have hB_inj := hB.toHasInjectiveBlocks.block_injective
  have hA_left := hA.toIsLeftCanonicalBlockFamily.leftCanonical
  have hB_left := hB.toIsLeftCanonicalBlockFamily.leftCanonical
  have hA_self := hA.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hB_self := hB.toHasNormalizedSelfOverlap.overlap_tendsto_one
  have hA_cross : ∀ j k : Fin rA, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0) :=
    fun j k hjk => hA.cross_overlap_tendsto_zero j k hjk
  have hB_cross : ∀ j k : Fin rB, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0) :=
    fun j k hjk => hB.cross_overlap_tendsto_zero j k hjk
  -- ===========================================================================
  -- 3b. KEY STEP: For each A-block, there exists a B-block with non-decaying
  -- overlap (and vice versa).  Proved via strong induction on rA + rB by
  -- `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`; see its docstring for the
  -- dominant-weight projection argument (CPSV17 Appendix A).
  -- ===========================================================================
  have h_nondecaying := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
    A B hA hB hEqual hrA hrB hSumState hA_self hB_self hA_cross hB_cross
  have exists_nondecaying_A : ∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0) :=
    h_nondecaying.1
  have exists_nondecaying_B : ∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0) :=
    h_nondecaying.2
  -- Non-decaying overlap → dim equality + GaugePhaseEquiv (overlap dichotomy).
  -- Matching function from A-blocks to B-blocks.
  let fA : Fin rA → Fin rB := fun j => (exists_nondecaying_A j).choose
  have hfA_nd : ∀ j,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B (fA j)) N) atTop (nhds 0) :=
    fun j => (exists_nondecaying_A j).choose_spec
  -- Dimension equality by contrapositive of mpvOverlap_tendsto_zero_of_dim_ne.
  have hfA_dim : ∀ j, dimA j = dimB (fA j) := by
    intro j
    by_contra hne
    exact hfA_nd j (mpvOverlap_tendsto_zero_of_dim_ne (A j) (B (fA j))
      (hA_inj j) (hB_inj (fA j)) (hA_left j) (hB_left (fA j)) hne)
  -- GaugePhaseEquiv by contrapositive of mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv.
  have hfA_gpe : ∀ j,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hfA_dim j)) (A j))
        (B (fA j)) := by
    intro j
    by_contra hNotGPE
    have hdim := hfA_dim j
    exact hfA_nd j
      (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim (A j) (B (fA j))
        (hA_inj j) (hB_inj (fA j))
        (hA_left j) (hB_left (fA j)) hNotGPE)
  -- ===========================================================================
  -- 3d. fA is injective (from A-BNT separation).
  -- If fA(j₁) = fA(j₂) for j₁ ≠ j₂, then both A j₁ and A j₂ are GPE with
  -- B(fA j₁). From the MPV scaling formulas, the cross-overlap
  -- mpvOverlap(A j₁, A j₂) has norm → 1, contradicting A-BNT cross-overlap → 0.
  -- ===========================================================================
  have hfA_inj : Function.Injective fA := by
    intro j1 j2 hfj
    by_contra hne
    obtain ⟨X1, ζ1, _, hX1⟩ := hfA_gpe j1
    obtain ⟨X2, ζ2, _, hX2⟩ := hfA_gpe j2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B (fA j1)) σ = ζ1 ^ N * mpv (A j1) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ,
          mpv_cast_dim (hfA_dim j1)]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B (fA j1)) σ = ζ2 ^ N * mpv (A j2) σ := by
      intro N σ
      rw [hfj]
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ,
          mpv_cast_dim (hfA_dim j2)]
    have hBB_norm_tendsto :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖)
          atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (B (fA j1)) (hB_self (fA j1))
    have hAA1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j1) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (A j1) (hA_self j1)
    have hAA2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j2) (A j2) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (A j2) (hA_self j2)
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA1_norm hBB_norm_tendsto
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A j1) (B := B (fA j1)) (ζ := ζ1) hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA2_norm hBB_norm_tendsto
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A j2) (B := B (fA j1)) (ζ := ζ2) hmpv2)
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (A j1) (A j2) N =
        (starRingEnd ℂ ζ1 * ζ2) ^ N *
          mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N := by
      intro N
      simp only [mpvOverlap]
      have hζ1_star_mul : starRingEnd ℂ ζ1 * ζ1 = 1 := by
        have := Complex.conj_mul' ζ1
        rw [this, hζ1_norm, Complex.ofReal_one, one_pow]
      have hζ2_star_mul : starRingEnd ℂ ζ2 * ζ2 = 1 := by
        have := Complex.conj_mul' ζ2
        rw [this, hζ2_norm, Complex.ofReal_one, one_pow]
      have hA1_eq : ∀ σ : Cfg d N, mpv (A j1) σ =
          (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j1) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ1_star_mul, one_pow, one_mul]
      have hA2_eq : ∀ σ : Cfg d N, mpv (A j2) σ =
          (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j2) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ2_star_mul, one_pow, one_mul]
      have hStep1 : ∀ σ : Cfg d N, mpv (A j1) σ * star (mpv (A j2) σ) =
          (starRingEnd ℂ ζ1) ^ N * mpv (B (fA j1)) σ *
          star ((starRingEnd ℂ ζ2) ^ N * mpv (B (fA j1)) σ) := by
        intro σ; rw [hA1_eq σ, ← hmpv1 N σ, hA2_eq σ, ← hmpv2 N σ]
      simp_rw [hStep1]
      simp only [star_mul, star_pow, RCLike.star_def, starRingEnd_self_apply]
      rw [mul_pow]
      rw [Finset.mul_sum]
      congr 1; ext σ; ring
    -- Norm of phase factor is 1.
    have hNormζ : ‖starRingEnd ℂ ζ1 * ζ2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
    -- So ‖mpvOverlap(A j1, A j2, N)‖ → 1.
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) =
          fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
            ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]
      have : (fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (B (fA j1)) (B (fA j1)) N‖ := by
        ext N; rw [norm_pow, hNormζ, one_pow]
      rw [this]
      simpa only [one_mul] using hBB_norm_tendsto
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j1) (A j2) N‖) atTop (nhds 0) := by
      convert (hA_cross j1 j2 hne).norm using 1; simp only [norm_zero]
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- Matching function from B-blocks to A-blocks, also injective.
  let gB : Fin rB → Fin rA := fun k => (exists_nondecaying_B k).choose
  have hgB_nd : ∀ k,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A (gB k)) (B k) N) atTop (nhds 0) :=
    fun k => (exists_nondecaying_B k).choose_spec
  have hgB_dim : ∀ k, dimA (gB k) = dimB k := by
    intro k
    by_contra hne
    exact hgB_nd k (mpvOverlap_tendsto_zero_of_dim_ne (A (gB k)) (B k)
      (hA_inj (gB k)) (hB_inj k) (hA_left (gB k)) (hB_left k) hne)
  have hgB_gpe : ∀ k,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hgB_dim k)) (A (gB k)))
        (B k) := by
    intro k
    by_contra hNotGPE
    exact hgB_nd k
      (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        (hgB_dim k) (A (gB k)) (B k)
        (hA_inj (gB k)) (hB_inj k)
        (hA_left (gB k)) (hB_left k) hNotGPE)
  have hgB_inj : Function.Injective gB := by
    intro k1 k2 hgk
    by_contra hne
    obtain ⟨Y1, ω1, _, hY1⟩ := hgB_gpe k1
    obtain ⟨Y2, ω2, _, hY2⟩ := hgB_gpe k2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k1) σ = ω1 ^ N * mpv (A (gB k1)) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y1 ω1 hY1 N σ,
          mpv_cast_dim (hgB_dim k1)]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k2) σ = ω2 ^ N * mpv (A (gB k1)) σ := by
      intro N σ
      rw [hgk] at hmpv1 ⊢
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y2 ω2 hY2 N σ,
          mpv_cast_dim (hgB_dim k2)]
    have hAA_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖)
          atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (A (gB k1)) (hA_self (gB k1))
    have hBB1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k1) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (B k1) (hB_self k1)
    have hBB2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k2) (B k2) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (B k2) (hB_self k2)
    have hω1_norm : ‖ω1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB1_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A (gB k1)) (B := B k1) (ζ := ω1) hmpv1)
    have hω2_norm : ‖ω2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB2_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul
          (A := A (gB k1)) (B := B k2) (ζ := ω2) hmpv2)
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B k1) (B k2) N =
        (ω1 * starRingEnd ℂ ω2) ^ N *
          mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N := by
      intro N
      simp only [mpvOverlap]
      simp_rw [hmpv1 N, hmpv2 N, star_mul, star_pow]
      simp_rw [show star ω2 = starRingEnd ℂ ω2 from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ω1 ^ N * mpv (A (gB k1)) x *
          (star (mpv (A (gB k1)) x) * (starRingEnd ℂ ω2) ^ N) =
        ω1 ^ N * (starRingEnd ℂ ω2) ^ N *
          (mpv (A (gB k1)) x * star (mpv (A (gB k1)) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hNormω : ‖ω1 * starRingEnd ℂ ω2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hω1_norm, hω2_norm, mul_one]
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) =
          fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
            ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]
      have : (fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
          ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A (gB k1)) (A (gB k1)) N‖ := by
        ext N; rw [norm_pow, hNormω, one_pow]
      rw [this]
      simpa only [one_mul] using hAA_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k1) (B k2) N‖) atTop (nhds 0) := by
      convert (hB_cross k1 k2 hne).norm using 1; simp only [norm_zero]
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- rA = rB from injective maps between finite types.
  have hrA_le_rB : Fintype.card (Fin rA) ≤ Fintype.card (Fin rB) :=
    Fintype.card_le_of_injective fA hfA_inj
  have hrB_le_rA : Fintype.card (Fin rB) ≤ Fintype.card (Fin rA) :=
    Fintype.card_le_of_injective gB hgB_inj
  simp only [Fintype.card_fin] at hrA_le_rB hrB_le_rA
  have hrAB : rA = rB := le_antisymm hrA_le_rB hrB_le_rA
  refine ⟨hrAB, ?_⟩
  subst hrAB
  -- fA is injective on Fin rA, hence bijective; build the permutation.
  have hfA_bij : Function.Bijective fA :=
    ⟨hfA_inj, (Finite.injective_iff_surjective.mp hfA_inj)⟩
  let perm : Fin rA ≃ Fin rA := Equiv.ofBijective fA hfA_bij
  refine ⟨perm, fun j => ?_⟩
  have hpj : perm j = fA j := Equiv.ofBijective_apply fA hfA_bij j
  refine ⟨?_, ?_⟩
  · simpa [hpj] using hfA_dim j
  · simpa [hpj] using hfA_gpe j

end HeteroEqualCase

end MPSTensor
