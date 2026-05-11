/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.FundamentalTheorem.Full.ProportionalDominant

/-!
# Non-decaying overlap existence for BNT families

This module proves `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`, the existence of
non-decaying cross-overlaps between blocks of two `IsCanonicalFormBNT` families with
equal total matrix product vectors (`SameMPV₂`). This is **Layer 1a** of the
heterogeneous equal-case fundamental theorem — the block matching stage that feeds
`blocks_match_of_sameMPV₂_CFBNT` in `TNLean.MPS.FundamentalTheorem.Full.BlocksMatch`.

It also states the corresponding proportional-MPV paper-realignment step
`exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`, using the
nonzero projective proportionality hypothesis from arXiv:1606.00608,
Theorem `thm1`.
That proportional statement currently carries the intentional proof obligation
for issue #1563.

## Main statements

* `exists_nondecaying_overlap_of_sameMPV₂_CFBNT`: For every block of one family there
  exists a block of the other family whose cross-overlap does not decay to zero.
* `exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT`: The analogous
  block-selection statement from nonzero proportionality of the assembled MPV
  families, stated without external coefficient-array hypotheses.

## Implementation notes

The proof proceeds by strong induction on `rA + rB` combined with a dominant-weight
projection argument. Convergence auxiliary lemmas live in
`TNLean.MPS.FundamentalTheorem.OverlapConvergenceAux`; the dominant-weight comparison
and small overlap/inner-product auxiliary lemmas live in
`TNLean.MPS.FundamentalTheorem.Full.DominantWeight`.

## References

* Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled
  pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. 93 (2021), arXiv:2011.12127.
* Cirac, Pérez-García, Schuch, Verstraete, *Fundamental Theorems for PEPS*,
  arXiv:1606.00608 (2017).

## Tags

matrix product states, fundamental theorem, BNT, overlap, induction
-/

open scoped Matrix BigOperators InnerProductSpace
open Filter

namespace MPSTensor

section HeteroEqualCase

/-- **Non-decaying overlap existence for equal-MPV BNT families.**

For two `IsCanonicalFormBNT` families with equal total MPVs (`SameMPV₂`), every block in
one family has non-decaying cross-overlap with some block in the other.

The proof proceeds by strong induction on `rA + rB`:

* **Dominant blocks** (`j = 0` or `k = 0`): The normalized overlap identity and the
  equality `‖μA 0‖ = ‖μB 0‖` (derived from the total self-overlap) give a non-vanishing
  overlap norm, contradicting the hypothesis that all cross-overlaps decay to zero.

* **Non-dominant blocks** (`j > 0` or `k > 0`): After matching dominant blocks via the
  overlap dichotomy and extracting the weight relation `μA 0 = ζ · μB π(0)` from the
  gauge-phase equivalence, the matched dominant pair is subtracted from the weighted-sum
  identity.  The reduced identity involves `rA − 1` and `rB − 1` blocks that still satisfy
  `IsCanonicalFormBNT` (all per-block properties are inherited, and the strict weight
  ordering restricts to the sub-range).  The strong induction hypothesis then closes the
  remaining cases. -/
lemma exists_nondecaying_overlap_of_sameMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hEqual : SameMPV₂ (toTensorFromBlocks μA A) (toTensorFromBlocks μB B))
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hSumState : ∀ N : ℕ,
      ∑ j : Fin rA, (μA j) ^ N • mpvState (d := d) (A j) N =
        ∑ k : Fin rB, (μB k) ^ N • mpvState (d := d) (B k) N)
    (hA_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (A k) (A k) N) atTop (nhds 1))
    (hB_self : ∀ k, Tendsto (fun N => mpvOverlap (d := d) (B k) (B k) N) atTop (nhds 1))
    (hA_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (A j) (A k) N) atTop (nhds 0))
    (hB_cross : ∀ j k, j ≠ k →
      Tendsto (fun N => mpvOverlap (d := d) (B j) (B k) N) atTop (nhds 0)) :
    (∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) ∧
    (∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) := by
  -- ── Proof structure (see also the lemma docstring for the full description) ──
  -- Step A: ‖μA 0‖ = ‖μB 0‖ via normalized inner-product identity (both cases).
  -- Step B: Dominant match existence via contradiction (inner product → 1 vs → 0).
  -- Step C: Non-dominant blocks by strong induction on rA + rB (tail reduction).
  -- --------------------------------------------------------------------------
  have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
  have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB
  -- ── Inner product identity from hSumState ──
  have inner_identity : ∀ {D : ℕ} (X : MPSTensor d D) (N : ℕ),
      ∑ j : Fin rA, (μA j) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X N
    simp only [mpvInner]
    have h := congr_arg (fun v => @inner ℂ _ _ (mpvState (d := d) X N) v) (hSumState N)
    simp only [inner_sum, inner_smul_right] at h
    exact h
  -- ── Diagonal / off-diagonal inner product limits ──
  have hA_inner_diag : ∀ j : Fin rA,
      Tendsto (fun N => mpvInner (d := d) (A j) (A j) N) atTop (nhds 1) :=
    fun j => tendsto_inner_one (A j) (hA_self j)
  have hA_inner_off : ∀ i j : Fin rA, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (A i) (A j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (A i) (A j) (hA_cross i j hij)
  have hB_inner_diag : ∀ k : Fin rB,
      Tendsto (fun N => mpvInner (d := d) (B k) (B k) N) atTop (nhds 1) :=
    fun k => tendsto_inner_one (B k) (hB_self k)
  have hB_inner_off : ∀ i j : Fin rB, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (B i) (B j) N) atTop (nhds 0) :=
    fun i j hij => tendsto_inner_zero (B i) (B j) (hB_cross i j hij)
  -- ── Step A: ‖μA 0‖ = ‖μB 0‖ ──
  have hμA_ne : μA ⟨0, hrA_pos⟩ ≠ 0 := hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  have hμB_ne : μB ⟨0, hrB_pos⟩ ≠ 0 := hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero _
  have normalized_identity :
      ∀ {D : ℕ} (X : MPSTensor d D) (c : ℂ) (hc : c ≠ 0) (N : ℕ),
      ∑ j : Fin rA, (μA j / c) ^ N * mpvInner (d := d) X (A j) N =
        ∑ k : Fin rB, (μB k / c) ^ N * mpvInner (d := d) X (B k) N := by
    intro D X c hc N
    have h := inner_identity X N
    have hcN : c ^ N ≠ 0 := pow_ne_zero N hc
    simp only [div_pow, div_mul_eq_mul_div]
    rw [← Finset.sum_div, ← Finset.sum_div]
    exact congr_arg (· / c ^ N) h
  have hμA_le : ∀ j : Fin rA, ‖μA j‖ ≤ ‖μA ⟨0, hrA_pos⟩‖ := by
    intro j; exact hA.toIsCanonicalForm.mu_antitone
      (show (⟨0, hrA_pos⟩ : Fin rA) ≤ j from Fin.mk_le_mk.mpr (Nat.zero_le _))
  have hμB_le : ∀ k : Fin rB, ‖μB k‖ ≤ ‖μB ⟨0, hrB_pos⟩‖ := by
    intro k; exact hB.toIsCanonicalForm.mu_antitone
      (show (⟨0, hrB_pos⟩ : Fin rB) ≤ k from Fin.mk_le_mk.mpr (Nat.zero_le _))
  -- ── Step A: Prove ‖μA 0‖ = ‖μB 0‖. ──
  have mu0_norm_eq : ‖μA ⟨0, hrA_pos⟩‖ = ‖μB ⟨0, hrB_pos⟩‖ := by
    simpa [hrA_pos, hrB_pos] using
      dominant_weight_norm_eq_of_sameMPV₂_CFBNT
        (A := A) (B := B) hA hB hrA hrB hSumState hA_self hB_self hA_cross hB_cross
  -- ── Steps B+C: Match existence via dominant-weight contradiction + induction. ──
  set a0 : Fin rA := ⟨0, hrA_pos⟩
  set b0 : Fin rB := ⟨0, hrB_pos⟩
  -- ── Auxiliary: dominant case prover ──
  -- If ∀ k, overlap(A j₀, B k) → 0 AND j₀ is the dominant block, derive False.
  have dominant_A_contra :
      (∀ k, Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k) N) atTop (nhds 0)) →
      False := by
    intro hall
    have hall_inner : ∀ k, Tendsto (fun N => mpvInner (d := d) (A a0) (B k) N)
        atTop (nhds 0) := fun k => tendsto_inner_zero _ _ (hall k)
    have h_eq := normalized_identity (A a0) (μA a0) hμA_ne
    have hRHS : Tendsto (fun N => ∑ k, (μB k / μA a0) ^ N *
        mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rB))
        (fun (k : Fin rB) _ => show Tendsto _ atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]; exact (div_le_one (by positivity)).mpr
              (mu0_norm_eq ▸ hμB_le k)) (hall_inner k))
      simpa using this
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μA a0) ^ N *
        mpvInner (d := d) (A a0) (A j) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := a0) rfl (hA_inner_diag a0)
        (fun j hj => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
            (hA.mu_strict_anti (by
              simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                intro h; exact hj (Fin.ext h)))))
        (fun j hj => hA_inner_off a0 j hj.symm)
    exact zero_ne_one (tendsto_nhds_unique (hRHS.congr (fun N => (h_eq N).symm)) hLHS)
  have dominant_B_contra :
      (∀ j, Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0)) →
      False := by
    intro hall
    have hall_inner : ∀ j, Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N)
        atTop (nhds 0) := by
      intro j
      exact tendsto_inner_zero_swap (d := d) (A j) (B b0) (hall j)
    have h_eq := normalized_identity (B b0) (μB b0) hμB_ne
    have hLHS : Tendsto (fun N => ∑ j, (μA j / μB b0) ^ N *
        mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
      have := tendsto_finset_sum (Finset.univ : Finset (Fin rA))
        (fun (j : Fin rA) _ => show Tendsto _ atTop (nhds (0 : ℂ)) from
          bounded_mul_tendsto_zero _ _ (by
            rw [norm_div]; exact (div_le_one (by positivity)).mpr
              (mu0_norm_eq ▸ hμA_le j)) (hall_inner j))
      simpa using this
    have hRHS : Tendsto (fun N => ∑ k, (μB k / μB b0) ^ N *
        mpvInner (d := d) (B b0) (B k) N) atTop (nhds 1) :=
      sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner_diag b0)
        (fun k hk => by
          rw [norm_div]
          exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
            (hB.mu_strict_anti (by
              simp only [b0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                intro h; exact hk (Fin.ext h)))))
        (fun k hk => hB_inner_off b0 k hk.symm)
    exact zero_ne_one (tendsto_nhds_unique (hLHS.congr (fun N => h_eq N)) hRHS)
  -- ── Step B: Dominant cases (existence) ──
  have domA : ∃ k₀, ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k₀) N)
      atTop (nhds 0) := by
    by_contra h; push Not at h; exact dominant_A_contra h
  have domB : ∃ j₀, ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B b0) N)
      atTop (nhds 0) := by
    by_contra h; push Not at h; exact dominant_B_contra h
  -- ── Step C: Uniqueness of the match (BNT cross-overlap → 0 vs → 1 contradiction) ──
  have hA_inj_local := hA.toHasInjectiveBlocks.block_injective
  have hB_inj_local := hB.toHasInjectiveBlocks.block_injective
  have hA_left_local := hA.toIsLeftCanonicalBlockFamily.leftCanonical
  have hB_left_local := hB.toIsLeftCanonicalBlockFamily.leftCanonical
  have unique_A_match : ∀ (k : Fin rB) (j₁ j₂ : Fin rA),
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₁) (B k) N) atTop (nhds 0) →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₂) (B k) N) atTop (nhds 0) →
      j₁ = j₂ := by
    intro k j₁ j₂ h1 h2
    by_contra hne
    -- Both A j₁, A j₂ have non-decaying overlap with B k → GPE for both.
    have hdim1 : dimA j₁ = dimB k := by
      by_contra hd; exact h1 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) hd)
    have hdim2 : dimA j₂ = dimB k := by
      by_contra hd; exact h2 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) hd)
    have hgpe1 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim1) (A j₁)) (B k) := by
      by_contra h; exact h1 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim1 _ _ (hA_inj_local j₁) (hB_inj_local k) (hA_left_local j₁) (hB_left_local k) h)
    have hgpe2 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim2) (A j₂)) (B k) := by
      by_contra h; exact h2 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim2 _ _ (hA_inj_local j₂) (hB_inj_local k) (hA_left_local j₂) (hB_left_local k) h)
    -- Extract GPE data and MPV scaling.
    obtain ⟨X1, ζ1, _, hX1⟩ := hgpe1
    obtain ⟨X2, ζ2, _, hX2⟩ := hgpe2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k) σ = ζ1 ^ N * mpv (A j₁) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ, mpv_cast_dim hdim1]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k) σ = ζ2 ^ N * mpv (A j₂) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ, mpv_cast_dim hdim2]
    -- Norm of phases = 1.
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
    -- Cross-overlap of A j₁ and A j₂ via B k.
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (A j₁) (A j₂) N =
        (starRingEnd ℂ ζ1 * ζ2) ^ N * mpvOverlap (d := d) (B k) (B k) N := by
      intro N; simp only [mpvOverlap]
      have hζ1_star_mul : starRingEnd ℂ ζ1 * ζ1 = 1 := by
        have := Complex.conj_mul' ζ1; rw [this, hζ1_norm, Complex.ofReal_one, one_pow]
      have hζ2_star_mul : starRingEnd ℂ ζ2 * ζ2 = 1 := by
        have := Complex.conj_mul' ζ2; rw [this, hζ2_norm, Complex.ofReal_one, one_pow]
      have hA1_eq : ∀ σ : Cfg d N, mpv (A j₁) σ =
          (starRingEnd ℂ ζ1) ^ N * (ζ1 ^ N * mpv (A j₁) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ1_star_mul, one_pow, one_mul]
      have hA2_eq : ∀ σ : Cfg d N, mpv (A j₂) σ =
          (starRingEnd ℂ ζ2) ^ N * (ζ2 ^ N * mpv (A j₂) σ) := fun σ => by
        rw [← mul_assoc, ← mul_pow, hζ2_star_mul, one_pow, one_mul]
      have hStep : ∀ σ : Cfg d N, mpv (A j₁) σ * star (mpv (A j₂) σ) =
          (starRingEnd ℂ ζ1) ^ N * mpv (B k) σ *
          star ((starRingEnd ℂ ζ2) ^ N * mpv (B k) σ) := by
        intro σ; rw [hA1_eq σ, ← hmpv1 N σ, hA2_eq σ, ← hmpv2 N σ]
      simp_rw [hStep]; simp only [star_mul, star_pow, RCLike.star_def, starRingEnd_self_apply]
      rw [mul_pow]
      rw [Finset.mul_sum]; congr 1; ext σ; ring
    have hNormζ : ‖starRingEnd ℂ ζ1 * ζ2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
    -- Cross-overlap norm → 1, contradicting BNT cross → 0.
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) =
          fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
            ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]; have : (fun N => ‖(starRingEnd ℂ ζ1 * ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (B k) (B k) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (B k) (B k) N‖ := by
        ext N; rw [norm_pow, hNormζ, one_pow]
      rw [this]
      simpa only [one_mul] using hBB_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₂) N‖) atTop (nhds 0) := by
      convert (hA_cross j₁ j₂ hne).norm using 1; simp only [norm_zero]
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ── Similarly for B-side uniqueness ──
  have unique_B_match : ∀ (j : Fin rA) (k₁ k₂ : Fin rB),
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₁) N) atTop (nhds 0) →
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j) (B k₂) N) atTop (nhds 0) →
      k₁ = k₂ := by
    intro j k₁ k₂ h1 h2
    by_contra hne
    have hdim1 : dimA j = dimB k₁ := by
      by_contra hd; exact h1 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j) (hB_inj_local k₁) (hA_left_local j) (hB_left_local k₁) hd)
    have hdim2 : dimA j = dimB k₂ := by
      by_contra hd; exact h2 (mpvOverlap_tendsto_zero_of_dim_ne _ _
        (hA_inj_local j) (hB_inj_local k₂) (hA_left_local j) (hB_left_local k₂) hd)
    have hgpe1 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim1) (A j)) (B k₁) := by
      by_contra h; exact h1 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim1 _ _ (hA_inj_local j) (hB_inj_local k₁) (hA_left_local j) (hB_left_local k₁) h)
    have hgpe2 : GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) hdim2) (A j)) (B k₂) := by
      by_contra h; exact h2 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
        hdim2 _ _ (hA_inj_local j) (hB_inj_local k₂) (hA_left_local j) (hB_left_local k₂) h)
    obtain ⟨Y1, ω1, _, hY1⟩ := hgpe1
    obtain ⟨Y2, ω2, _, hY2⟩ := hgpe2
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k₁) σ = ω1 ^ N * mpv (A j) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y1 ω1 hY1 N σ, mpv_cast_dim hdim1]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B k₂) σ = ω2 ^ N * mpv (A j) σ := fun N σ => by
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ Y2 ω2 hY2 N σ, mpv_cast_dim hdim2]
    have hAA_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A j) (A j) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (A j) (hA_self j)
    have hBB1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₁) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (B k₁) (hB_self k₁)
    have hBB2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₂) (B k₂) N‖) atTop (nhds 1) :=
      tendsto_norm_selfOverlap_one (d := d) (B k₂) (hB_self k₂)
    have hω1_norm : ‖ω1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB1_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j) (B := B k₁) (ζ := ω1) hmpv1)
    have hω2_norm : ‖ω2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm hBB2_norm
        (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j) (B := B k₂) (ζ := ω2) hmpv2)
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B k₁) (B k₂) N =
        (ω1 * starRingEnd ℂ ω2) ^ N * mpvOverlap (d := d) (A j) (A j) N := by
      intro N; simp only [mpvOverlap]
      simp_rw [hmpv1 N, hmpv2 N, star_mul, star_pow]
      simp_rw [show star ω2 = starRingEnd ℂ ω2 from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ω1 ^ N * mpv (A j) x * (star (mpv (A j) x) * (starRingEnd ℂ ω2) ^ N) =
        ω1 ^ N * (starRingEnd ℂ ω2) ^ N * (mpv (A j) x * star (mpv (A j) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    have hNormω : ‖ω1 * starRingEnd ℂ ω2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hω1_norm, hω2_norm, mul_one]
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) =
          fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
            ‖mpvOverlap (d := d) (A j) (A j) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]; have : (fun N => ‖(ω1 * starRingEnd ℂ ω2) ^ N‖ *
          ‖mpvOverlap (d := d) (A j) (A j) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A j) (A j) N‖ := by
        ext N; rw [norm_pow, hNormω, one_pow]
      rw [this]
      simpa only [one_mul] using hAA_norm
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B k₁) (B k₂) N‖) atTop (nhds 0) := by
      convert (hB_cross k₁ k₂ hne).norm using 1; simp only [norm_zero]
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  -- ── Step D: For each B-block, choose its unique A-match ──
  -- From domB, B b0 has a match. For other B-blocks k, if ∀ j,
  -- overlap(A j, B k) → 0, that gives the B-direction dominant contradiction
  -- (same argument as dominant_B_contra but with B k in place of B b0).
  -- Actually, we use domB only for b0; for other B-blocks, the existence
  -- of an A-match will follow from the same dominant-weight argument.
  -- However, we only NEED the match for b0 for the main argument.
  --
  -- Key claim: the A-match for B b0 must be A a0.
  have match_B0_is_A0 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B b0) N)
      atTop (nhds 0) := by
    obtain ⟨j₁, hj₁⟩ := domB
    -- j₁ has non-decaying overlap with B b0.
    -- If j₁ = a0, done. Otherwise, show j₁ = a0 by norm argument.
    by_cases hj1 : j₁ = a0
    · subst hj1; exact hj₁
    · -- j₁ ≠ a0 means |μA j₁| < |μA a0|.
      -- From GPE(A j₁, B b0): extract phase ω and show |μA j₁| = |μA a0| → ⊥.
      -- The normalized identity with X = B b0, c = μB b0 gives:
      --   LHS (A-side) ≈ (μA j₁ * star(ω) / μB b0)^N → ? and RHS (B-side) → 1.
      -- Since |μA j₁| < |μA a0| = |μB b0|, the ratio < 1, LHS → 0 ≠ 1.
      exfalso
      -- Show uniqueness: j₁ is the only A-match for B b0.
      have huniq : ∀ j, j ≠ j₁ →
          Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N) atTop (nhds 0) :=
        fun j hj => by
          by_contra hnd
          exact hj (unique_A_match b0 j j₁ hnd hj₁)
      -- Extract GPE data.
      have hdim1 : dimA j₁ = dimB b0 := by
        by_contra hd; exact hj₁ (mpvOverlap_tendsto_zero_of_dim_ne _ _
          (hA_inj_local j₁) (hB_inj_local b0) (hA_left_local j₁) (hB_left_local b0) hd)
      have hgpe1 : GaugePhaseEquiv (d := d)
          (cast (congr_arg (MPSTensor d) hdim1) (A j₁)) (B b0) := by
        by_contra h; exact hj₁ (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
          hdim1 _ _ (hA_inj_local j₁) (hB_inj_local b0)
          (hA_left_local j₁) (hB_left_local b0) h)
      obtain ⟨X, ω, _, hX⟩ := hgpe1
      have hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv (B b0) σ = ω ^ N * mpv (A j₁) σ := fun N σ => by
        rw [mpv_eq_pow_mul_of_gaugePhase _ _ X ω hX N σ, mpv_cast_dim hdim1]
      have hBB_norm :
          Tendsto (fun N => ‖mpvOverlap (d := d) (B b0) (B b0) N‖) atTop (nhds 1) :=
        tendsto_norm_selfOverlap_one (d := d) (B b0) (hB_self b0)
      have hAA_norm :
          Tendsto (fun N => ‖mpvOverlap (d := d) (A j₁) (A j₁) N‖) atTop (nhds 1) :=
        tendsto_norm_selfOverlap_one (d := d) (A j₁) (hA_self j₁)
      have hω_norm : ‖ω‖ = 1 :=
        norm_eq_one_of_selfOverlap_scale hAA_norm hBB_norm
          (mpvOverlap_self_scale_of_mpv_eq_pow_mul (A := A j₁) (B := B b0) (ζ := ω) hmpv)
      have hInner_j1 : ∀ N, mpvInner (d := d) (B b0) (A j₁) N =
          (starRingEnd ℂ ω) ^ N * mpvInner (d := d) (A j₁) (A j₁) N := by
        intro N
        have hstate : mpvState (d := d) (B b0) N = ω ^ N • mpvState (d := d) (A j₁) N := by
          rw [PiLp.ext_iff]; intro σ
          simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply]
          exact hmpv N σ
        simp only [mpvInner, hstate, inner_smul_left, map_pow]
      have hInner_other : ∀ j, j ≠ j₁ →
          Tendsto (fun N => mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
        intro j hj
        exact tendsto_inner_zero_swap (d := d) (A j) (B b0) (huniq j hj)
      have h_eq := normalized_identity (B b0) (μB b0) hμB_ne
      have hRHS_one : Tendsto (fun N => ∑ k, (μB k / μB b0) ^ N *
          mpvInner (d := d) (B b0) (B k) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμB_ne) (j0 := b0) rfl (hB_inner_diag b0)
          (fun k hk => by
            rw [norm_div]
            exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
              (hB.mu_strict_anti (by
                simp only [b0, Fin.lt_def]; exact Nat.pos_of_ne_zero (by
                  intro h; exact hk (Fin.ext h)))))
          (fun k hk => hB_inner_off b0 k hk.symm)
      -- LHS: all terms → 0 since |μA j₁ / μB b0| < 1 (j₁ ≠ a0, strict ordering).
      have hRatio_lt : ‖μA j₁ / μB b0‖ < 1 := by
        rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμB_ne)).mpr
          (mu0_norm_eq ▸ hA.mu_strict_anti (by
            simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero
              (fun h => hj1 (Fin.ext h))))
      have hLHS_zero : Tendsto (fun N => ∑ j, (μA j / μB b0) ^ N *
          mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
        -- Split into j = j₁ and j ≠ j₁.
        have hsplit : ∀ N, ∑ j, (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N =
            (μA j₁ / μB b0) ^ N * mpvInner (d := d) (B b0) (A j₁) N +
            ∑ j ∈ Finset.univ.erase j₁,
              (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N := by
          intro N; rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁)]
        simp_rw [hsplit]
        -- The j₁ term: geometric × bounded → 0.
        have h_j1_term : Tendsto (fun N =>
            (μA j₁ / μB b0) ^ N * mpvInner (d := d) (B b0) (A j₁) N) atTop (nhds 0) :=
          geometric_mul_inner_tendsto_zero _ _ _ hRatio_lt (hB_self b0) (hA_self j₁)
        -- The rest: bounded × → 0 → 0.
        have h_rest : Tendsto (fun N => ∑ j ∈ Finset.univ.erase j₁,
            (μA j / μB b0) ^ N * mpvInner (d := d) (B b0) (A j) N) atTop (nhds 0) := by
          have := tendsto_finset_sum (Finset.univ.erase j₁)
            (fun (j : Fin rA) (hj : j ∈ Finset.univ.erase j₁) =>
              show Tendsto _ atTop (nhds (0 : ℂ)) from
              bounded_mul_tendsto_zero _ _ (by
                rw [norm_div]; exact (div_le_one (by positivity)).mpr
                  (mu0_norm_eq ▸ hμA_le j))
              (hInner_other j (Finset.ne_of_mem_erase hj)))
          simpa using this
        convert h_j1_term.add h_rest using 1; simp
      exact zero_ne_one (tendsto_nhds_unique
        (hLHS_zero.congr (fun N => h_eq N)) hRHS_one)
  -- ── Similarly: A a0's match on the B-side is B b0 ──
  have match_A0_is_B0 : ¬ Tendsto (fun N => mpvOverlap (d := d) (A a0) (B b0) N)
      atTop (nhds 0) := match_B0_is_A0
  -- ── Step E: GPE for dominant match + tail identity. ──
  have hdim_dom : dimA a0 = dimB b0 := by
    by_contra hd
    exact match_A0_is_B0 (mpvOverlap_tendsto_zero_of_dim_ne _ _
      (hA_inj_local a0) (hB_inj_local b0) (hA_left_local a0) (hB_left_local b0) hd)
  have hgpe_dom : GaugePhaseEquiv (d := d)
      (cast (congr_arg (MPSTensor d) hdim_dom) (A a0)) (B b0) := by
    by_contra h
    exact match_A0_is_B0 (mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left
      hdim_dom _ _ (hA_inj_local a0) (hB_inj_local b0)
      (hA_left_local a0) (hB_left_local b0) h)
  obtain ⟨X_dom, ζ, hX_dom_inv, hX_dom_eq⟩ := hgpe_dom
  have hmpv_dom : ∀ (N : ℕ) (σ : Fin N → Fin d),
      mpv (B b0) σ = ζ ^ N * mpv (A a0) σ := fun N σ => by
    rw [mpv_eq_pow_mul_of_gaugePhase _ _ X_dom ζ hX_dom_eq N σ, mpv_cast_dim hdim_dom]
  have hstate_dom : ∀ N,
      mpvState (d := d) (B b0) N = ζ ^ N • mpvState (d := d) (A a0) N := by
    intro N; ext σ
    simp only [PiLp.smul_apply, smul_eq_mul, mpvState_apply, hmpv_dom]
  have hζ_norm : ‖ζ‖ = 1 :=
    norm_eq_one_of_selfOverlap_scale
      (tendsto_norm_selfOverlap_one (d := d) (A a0) (hA_self a0))
      (tendsto_norm_selfOverlap_one (d := d) (B b0) (hB_self b0))
      (mpvOverlap_self_scale_of_mpv_eq_pow_mul
        (A := A a0) (B := B b0) (ζ := ζ) hmpv_dom)
  -- ── Show μA a0 = μB b0 * ζ ──
  -- From the normalized identity with X = A a0, c = μA a0:
  --   LHS → 1, and RHS has b0-term = (μB b0 * ζ / μA a0)^N * inner(A a0, A a0, N).
  -- Setting λ = μB b0 * ζ / μA a0 with |λ| = 1, we show λ^N → 1, hence λ = 1.
  have hμ_eq : μA a0 = μB b0 * ζ := by
    suffices h : μB b0 * ζ / μA a0 = 1 by
      have h' : μB b0 * ζ = μA a0 := by rwa [div_eq_iff hμA_ne, one_mul] at h
      exact h'.symm
    set ratio := μB b0 * ζ / μA a0
    have hratio_norm : ‖ratio‖ = 1 := by
      simp only [ratio, norm_div, norm_mul, hζ_norm, mul_one, mu0_norm_eq]
      exact div_self (ne_of_gt (norm_pos_iff.mpr hμB_ne))
    have hInner_b0 : ∀ N, mpvInner (d := d) (A a0) (B b0) N =
        ζ ^ N * mpvInner (d := d) (A a0) (A a0) N := by
      intro N; simp only [mpvInner, hstate_dom, inner_smul_right]
    have h_prod : Tendsto (fun N => ratio ^ N * mpvInner (d := d) (A a0) (A a0) N)
        atTop (nhds 1) := by
      have h_ni := normalized_identity (A a0) (μA a0) hμA_ne
      have hLHS : Tendsto (fun N => ∑ j, (μA j / μA a0) ^ N *
          mpvInner (d := d) (A a0) (A j) N) atTop (nhds 1) :=
        sum_tendsto_one_of_diag (hμ0 := hμA_ne) (j0 := a0) rfl (hA_inner_diag a0)
          (fun j hj => by
            rw [norm_div]; exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
              (hA.mu_strict_anti (by
                simp only [a0, Fin.lt_def]; exact Nat.pos_of_ne_zero
                  (fun h => hj (Fin.ext h)))))
          (fun j hj => hA_inner_off a0 j hj.symm)
      have hsplit : ∀ N, ∑ k, (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N =
          ratio ^ N * mpvInner (d := d) (A a0) (A a0) N +
          ∑ k ∈ Finset.univ.erase b0,
            (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N := by
        intro N
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
        congr 1
        simp only [hInner_b0, ratio, div_mul_eq_mul_div, mul_pow, div_pow]
        ring
      have h_rest : Tendsto (fun N => ∑ k ∈ Finset.univ.erase b0,
          (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) atTop (nhds 0) := by
        have := tendsto_finset_sum (Finset.univ.erase b0)
          (fun (k : Fin rB) (hk : k ∈ Finset.univ.erase b0) =>
            show Tendsto _ atTop (nhds (0 : ℂ)) from
            geometric_mul_inner_tendsto_zero _ _ _ (by
              rw [norm_div]
              exact (div_lt_one (norm_pos_iff.mpr hμA_ne)).mpr
                (lt_of_lt_of_eq (hB.mu_strict_anti
                  (show b0 < k from Fin.mk_lt_mk.mpr (Nat.pos_of_ne_zero
                    (fun h => (Finset.ne_of_mem_erase hk) (Fin.ext h)))))
                  mu0_norm_eq.symm))
              (hA_self a0) (hB_self k))
        simpa using this
      have hRHS_eq : ∀ N,
          (∑ k, (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) -
          (∑ k ∈ Finset.univ.erase b0,
            (μB k / μA a0) ^ N * mpvInner (d := d) (A a0) (B k) N) =
          ratio ^ N * mpvInner (d := d) (A a0) (A a0) N := by
        intro N; rw [hsplit]; ring
      have h_sub := ((hLHS.congr (fun N => h_ni N)).sub h_rest).congr hRHS_eq
      rwa [sub_zero] at h_sub
    have h_ratio_tendsto : Tendsto (fun N => ratio ^ N) atTop (nhds 1) := by
      have h_err : Tendsto (fun N => ratio ^ N *
          (mpvInner (d := d) (A a0) (A a0) N - 1)) atTop (nhds 0) :=
        bounded_mul_tendsto_zero ratio _ (by rw [hratio_norm])
          (show Tendsto (fun N => mpvInner (d := d) (A a0) (A a0) N - 1) atTop (nhds 0) by
            have := (hA_inner_diag a0).sub (tendsto_const_nhds (x := (1 : ℂ)))
            simp only [sub_self] at this; exact this)
      have h_decomp : ∀ N, ratio ^ N * mpvInner (d := d) (A a0) (A a0) N -
          ratio ^ N * (mpvInner (d := d) (A a0) (A a0) N - 1) = ratio ^ N := by
        intro N; ring
      have h_sub := h_prod.sub h_err
      rw [sub_zero] at h_sub
      exact h_sub.congr h_decomp
    exact eq_one_of_pow_tendsto_nhds_one h_ratio_tendsto
  have hTailState : ∀ N,
      ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N =
      ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N := by
    intro N
    have hN := hSumState N
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0),
        ← Finset.add_sum_erase _ _ (Finset.mem_univ b0)] at hN
    have hdom : μA a0 ^ N • (A a0).mpvState N =
        μB b0 ^ N • (B b0).mpvState N := by
      rw [hstate_dom, smul_smul, ← mul_pow, ← hμ_eq]
    rw [hdom] at hN
    exact add_left_cancel hN
  -- ── Step F: Non-dominant blocks via tail reduction + induction hypothesis. ──
  -- succA/succB embed Fin (r - 1) into Fin r as the (j+1)-th element.
  let succA : Fin (rA - 1) → Fin rA := fun j => ⟨j.val + 1, by omega⟩
  let succB : Fin (rB - 1) → Fin rB := fun k => ⟨k.val + 1, by omega⟩
  have succA_ne_a0 : ∀ j, succA j ≠ a0 := fun j => by simp [succA, a0]
  have succB_ne_b0 : ∀ k, succB k ≠ b0 := fun k => by simp [succB, b0]
  have succA_inj : Function.Injective succA := fun j₁ j₂ h => by
    simp [succA, Fin.ext_iff] at h; exact Fin.ext (by omega)
  have succB_inj : Function.Injective succB := fun k₁ k₂ h => by
    simp [succB, Fin.ext_iff] at h; exact Fin.ext (by omega)
  -- ── Auxiliary: reindex Finset sums from erase to Fin (r - 1) ──
  have hSumA_reindex : ∀ N,
      ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N =
      ∑ j : Fin (rA - 1), μA (succA j) ^ N • (A (succA j)).mpvState N := by
    intro N
    have h_eq : Finset.univ.erase a0 = (Finset.univ : Finset (Fin (rA - 1))).image succA := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_erase] at hx
        have hx_ne : x ≠ a0 := hx.1
        have hx_pos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx_ne (Fin.ext h))
        exact Finset.mem_image.mpr ⟨⟨x.val - 1, by omega⟩, Finset.mem_univ _,
          Fin.ext (by simp [succA]; omega)⟩
      · intro hx
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_erase.mpr ⟨succA_ne_a0 j, Finset.mem_univ _⟩
    rw [h_eq, Finset.sum_image (fun j _ k _ h => succA_inj h)]
  have hSumB_reindex : ∀ N,
      ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N =
      ∑ k : Fin (rB - 1), μB (succB k) ^ N • (B (succB k)).mpvState N := by
    intro N
    have h_eq : Finset.univ.erase b0 = (Finset.univ : Finset (Fin (rB - 1))).image succB := by
      ext x; constructor
      · intro hx
        rw [Finset.mem_erase] at hx
        have hx_ne : x ≠ b0 := hx.1
        have hx_pos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx_ne (Fin.ext h))
        exact Finset.mem_image.mpr ⟨⟨x.val - 1, by omega⟩, Finset.mem_univ _,
          Fin.ext (by simp [succB]; omega)⟩
      · intro hx
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hx
        exact Finset.mem_erase.mpr ⟨succB_ne_b0 k, Finset.mem_univ _⟩
    rw [h_eq, Finset.sum_image (fun k _ l _ h => succB_inj h)]
  have hTailReindex : ∀ N,
      ∑ j : Fin (rA - 1), μA (succA j) ^ N • (A (succA j)).mpvState N =
      ∑ k : Fin (rB - 1), μB (succB k) ^ N • (B (succB k)).mpvState N := by
    intro N; rw [← hSumA_reindex, ← hSumB_reindex]; exact hTailState N
  have succA_strictMono : StrictMono succA := fun a b h => by
    simp only [succA, Fin.mk_lt_mk]; omega
  have succB_strictMono : StrictMono succB := fun a b h => by
    simp only [succB, Fin.mk_lt_mk]; omega
  -- Hoist tail hypotheses used by both directions.
  have hEqual_tail : SameMPV₂
      (toTensorFromBlocks (d := d) (μ := μA ∘ succA) (fun j => A (succA j)))
      (toTensorFromBlocks (d := d) (μ := μB ∘ succB) (fun k => B (succB k))) := by
    intro N σ
    have hA_eq := mpv_toTensorFromBlocks_eq_sum (μA ∘ succA) (fun j => A (succA j)) σ
    have hB_eq := mpv_toTensorFromBlocks_eq_sum (μB ∘ succB) (fun k => B (succB k)) σ
    simp only [Function.comp, smul_eq_mul] at hA_eq hB_eq
    rw [hA_eq, hB_eq]
    have h := congr_arg (· σ) (hTailReindex N)
    simpa only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, mpvState_apply] using h
  have hA_tail : IsCanonicalFormBNT (μA ∘ succA) (fun j => A (succA j)) :=
    IsCanonicalFormBNT.ofSeparatedData
      (HasInjectiveBlocks.ofForall (fun k => hA_inj_local (succA k)))
      (IsLeftCanonicalBlockFamily.ofForall (fun k => hA_left_local (succA k)))
      ⟨hA.mu_strict_anti.comp_strictMono succA_strictMono,
       fun k => hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succA k)⟩
      (HasNormalizedSelfOverlap.ofForall (fun k => hA_self (succA k)))
      (fun j k hjk hdim => hA.blocks_not_equiv (succA j) (succA k)
        (fun h => hjk (succA_inj h)) hdim)
  have hB_tail : IsCanonicalFormBNT (μB ∘ succB) (fun k => B (succB k)) :=
    IsCanonicalFormBNT.ofSeparatedData
      (HasInjectiveBlocks.ofForall (fun k => hB_inj_local (succB k)))
      (IsLeftCanonicalBlockFamily.ofForall (fun k => hB_left_local (succB k)))
      ⟨hB.mu_strict_anti.comp_strictMono succB_strictMono,
       fun k => hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero (succB k)⟩
      (HasNormalizedSelfOverlap.ofForall (fun k => hB_self (succB k)))
      (fun j k hjk hdim => hB.blocks_not_equiv (succB j) (succB k)
        (fun h => hjk (succB_inj h)) hdim)
  -- Both directions proved simultaneously by contradiction + tail reduction.
  refine ⟨fun j₀ => ?_, fun k₀ => ?_⟩
  -- ── A-direction: ∃ k₀, ¬ overlap(A j₀, B k₀) → 0 ──
  · by_contra hall; push Not at hall
    have hj0_ne : j₀ ≠ a0 := by
      intro h; subst h; exact match_A0_is_B0 (hall b0)
    have hj0_pos : 0 < j₀.val := Nat.pos_of_ne_zero (fun h => hj0_ne (Fin.ext h))
    set j₀' : Fin (rA - 1) := ⟨j₀.val - 1, by omega⟩ with hj0'_def
    have hj0_eq : succA j₀' = j₀ := Fin.ext (by simp [succA, hj0'_def]; omega)
    by_cases hrB1 : rB = 1
    · -- rB = 1: B-tail empty → tail sum = 0 → LI contradiction.
      have hTailZero : ∀ N,
          ∑ j ∈ Finset.univ.erase a0, μA j ^ N • (A j).mpvState N = 0 := by
        intro N; rw [hTailState N, hSumB_reindex]
        subst hrB1; simp [Finset.univ_eq_empty]
      obtain ⟨N₀, hLI⟩ := hA.isBNT.eventually_li
      specialize hLI (N₀ + 1) (by omega)
      rw [Fintype.linearIndependent_iff] at hLI
      specialize hLI (fun j => if j = a0 then 0 else μA j ^ (N₀ + 1))
      have hzero : ∑ j : Fin rA,
          (if j = a0 then 0 else μA j ^ (N₀ + 1)) •
            (A j).mpvState (N₀ + 1) = 0 := by
        have h := hTailZero (N₀ + 1)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a0)]
        simp only [ite_true, zero_smul, zero_add]
        rw [show ∑ x ∈ Finset.univ.erase a0,
            (if x = a0 then (0 : ℂ) else μA x ^ (N₀ + 1)) • (A x).mpvState (N₀ + 1) =
            ∑ x ∈ Finset.univ.erase a0, μA x ^ (N₀ + 1) • (A x).mpvState (N₀ + 1) from
          Finset.sum_congr rfl (fun j hj => by rw [if_neg (Finset.ne_of_mem_erase hj)])]
        exact h
      have h_coeff := hLI hzero j₀
      simp only [hj0_ne, ite_false] at h_coeff
      exact pow_ne_zero _ (hA.toHasStrictOrderedNonzeroWeights.mu_ne_zero j₀) h_coeff
    · -- rB ≥ 2: apply the lemma recursively to the tail families.
      have IH := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
        (fun j => A (succA j)) (fun k => B (succB k))
        hA_tail hB_tail hEqual_tail
        (by omega) (by omega)
        hTailReindex
        (fun k => hA_self (succA k))
        (fun k => hB_self (succB k))
        (fun j k hjk => hA_cross (succA j) (succA k) (fun h => hjk (succA_inj h)))
        (fun j k hjk => hB_cross (succB j) (succB k) (fun h => hjk (succB_inj h)))
      obtain ⟨k', hk'⟩ := IH.1 j₀'
      apply hk'; change Tendsto (fun N => mpvOverlap (d := d)
        (A (succA j₀')) (B (succB k')) N) atTop (nhds 0)
      rw [hj0_eq]; exact hall (succB k')
  -- ── B-direction: ∃ j₀, ¬ overlap(A j₀, B k₀) → 0 ──
  · by_contra hall; push Not at hall
    have hk0_ne : k₀ ≠ b0 := by
      intro h; subst h; exact match_B0_is_A0 (hall a0)
    have hk0_pos : 0 < k₀.val := Nat.pos_of_ne_zero (fun h => hk0_ne (Fin.ext h))
    set k₀' : Fin (rB - 1) := ⟨k₀.val - 1, by omega⟩ with hk0'_def
    have hk0_eq : succB k₀' = k₀ := Fin.ext (by simp [succB, hk0'_def]; omega)
    -- Case split on rA.
    by_cases hrA1 : rA = 1
    · -- rA = 1: A-tail empty → tail sum = 0 → LI contradiction.
      have hTailZero : ∀ N,
          ∑ k ∈ Finset.univ.erase b0, μB k ^ N • (B k).mpvState N = 0 := by
        intro N; rw [← hTailState N, hSumA_reindex]
        subst hrA1; simp [Finset.univ_eq_empty]
      obtain ⟨N₀, hLI⟩ := hB.isBNT.eventually_li
      specialize hLI (N₀ + 1) (by omega)
      rw [Fintype.linearIndependent_iff] at hLI
      specialize hLI (fun k => if k = b0 then 0 else μB k ^ (N₀ + 1))
      have hzero : ∑ k : Fin rB,
          (if k = b0 then 0 else μB k ^ (N₀ + 1)) •
            (B k).mpvState (N₀ + 1) = 0 := by
        have h := hTailZero (N₀ + 1)
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ b0)]
        simp only [ite_true, zero_smul, zero_add]
        rw [show ∑ x ∈ Finset.univ.erase b0,
            (if x = b0 then (0 : ℂ) else μB x ^ (N₀ + 1)) • (B x).mpvState (N₀ + 1) =
            ∑ x ∈ Finset.univ.erase b0, μB x ^ (N₀ + 1) • (B x).mpvState (N₀ + 1) from
          Finset.sum_congr rfl (fun k hk => by rw [if_neg (Finset.ne_of_mem_erase hk)])]
        exact h
      have h_coeff := hLI hzero k₀
      simp only [hk0_ne, ite_false] at h_coeff
      exact pow_ne_zero _ (hB.toHasStrictOrderedNonzeroWeights.mu_ne_zero k₀) h_coeff
    · -- rA ≥ 2: apply the lemma recursively to the tail families.
      have IH := exists_nondecaying_overlap_of_sameMPV₂_CFBNT
        (fun j => A (succA j)) (fun k => B (succB k))
        hA_tail hB_tail hEqual_tail
        (by omega) (by omega)
        hTailReindex
        (fun k => hA_self (succA k))
        (fun k => hB_self (succB k))
        (fun j k hjk => hA_cross (succA j) (succA k) (fun h => hjk (succA_inj h)))
        (fun j k hjk => hB_cross (succB j) (succB k) (fun h => hjk (succB_inj h)))
      obtain ⟨j', hj'⟩ := IH.2 k₀'
      apply hj'; change Tendsto (fun N => mpvOverlap (d := d)
        (A (succA j')) (B (succB k₀')) N) atTop (nhds 0)
      rw [hk0_eq]; exact hall (succA j')
termination_by rA + rB

/-- **Non-decaying overlap existence for proportional-MPV BNT families.**

Source: arXiv:1606.00608, Theorem `thm1`, lines 1170--1192. In the proof,
fixing a block `B_k`, the authors rule out the possibility that all overlaps
`⟪V^{(N)}(B_k), V^{(N)}(A_j)⟫` tend to zero: otherwise the BNT expansion and
Lemma `Lem1` would contradict proportionality of the total MPV families. The
same argument with the two tensors interchanged gives the symmetric statement.

**Scope restriction (one-copy-per-sector):** The local hypothesis
`IsCanonicalFormBNT` is the already-grouped one-copy-per-sector canonical
form used in this development. CPSV16 Theorem II.1 is stated for the general
BNT canonical form with possible multiplicities. This restriction is documented in
`docs/paper-gaps/ft_one_copy_scope_restriction.tex`.

The proof body first derives the four BNT self- and cross-overlap convergence
facts and the lengthwise nonzero proportional scalar sequence from the stated
hypotheses. The remaining proof step is the dominant-block contradiction from
the normalized proportional projection identity; see issue #1563. -/
lemma exists_nondecaying_overlap_of_nonzeroProportionalMPV₂_CFBNT
    {d rA rB : ℕ}
    {dimA : Fin rA → ℕ} {dimB : Fin rB → ℕ}
    [∀ k, NeZero (dimA k)] [∀ k, NeZero (dimB k)]
    {μA : Fin rA → ℂ} {μB : Fin rB → ℂ}
    (A : (j : Fin rA) → MPSTensor d (dimA j))
    (B : (k : Fin rB) → MPSTensor d (dimB k))
    (hA : IsCanonicalFormBNT μA A)
    (hB : IsCanonicalFormBNT μB B)
    (hrA : rA ≠ 0) (hrB : rB ≠ 0)
    (hProp : NonzeroProportionalMPV₂
      (toTensorFromBlocks μA A) (toTensorFromBlocks μB B)) :
    (∀ j₀ : Fin rA, ∃ k₀ : Fin rB,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) ∧
    (∀ k₀ : Fin rB, ∃ j₀ : Fin rA,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A j₀) (B k₀) N) atTop (nhds 0)) := by
  have hrA_pos : 0 < rA := Nat.pos_of_ne_zero hrA
  have hrB_pos : 0 < rB := Nat.pos_of_ne_zero hrB
  let a0 : Fin rA := ⟨0, hrA_pos⟩
  let b0 : Fin rB := ⟨0, hrB_pos⟩
  have hDominant_contra :=
    dominant_projection_contradictions_of_eventuallyNonzeroProportionalMPV₂_CFBNT
      A B hA hB hrA hrB hProp.eventually
  have hDominantB_contra :
      (∀ j : Fin rA, Tendsto (fun N => mpvOverlap (d := d) (A j) (B b0) N)
        atTop (nhds 0)) → False := by
    simpa [b0] using hDominant_contra.1
  have hDominantA_contra :
      (∀ k : Fin rB, Tendsto (fun N => mpvOverlap (d := d) (A a0) (B k) N)
        atTop (nhds 0)) → False := by
    simpa [a0] using hDominant_contra.2
  -- Remaining CPSV16 line 1170--1192 step: lift the dominant contradictions
  -- `hDominantA_contra` and `hDominantB_contra` to arbitrary blocks by the
  -- same tail-reduction argument used in the equal-MPV theorem above.
  sorry

end HeteroEqualCase

end MPSTensor
