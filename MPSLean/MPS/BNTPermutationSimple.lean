import MPSLean.MPS.BNTMatching
import MPSLean.MPS.FundamentalTheoremProportional
import MPSLean.Spectral.SpectralGapRect
import MPSLean.MPS.MPVOverlap
import MPSLean.MPS.CastLemmas

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.Instances.Matrix

/-!
# BNT permutation rigidity — simplified (primitive branch)

This is a *simpler* alternative to `BNTPermutation.lean`, implementing the
permutation/phase-rigidity step for BNT families in the primitive (aperiodic) branch
of the Fundamental Theorem of MPS (Theorem 4.4 of arXiv:2011.12127).

## Main result

`MPSTensor.exists_perm_dimEq_gaugePhaseEquiv_of_overlapOrtho`:
Two BNT-like families with asymptotically orthonormal overlaps and equal MPV spans
agree blockwise up to a permutation, dimension equality, and gauge-phase equivalence.

## Proof strategy

1. Use `eventually_exists_invertible_changeBasis` to get, for large `N`, an invertible
   coefficient matrix `U_N` expressing each B-state in terms of the A-states.
2. For each block index `j`, show ∃ `i` such that `mpvOverlap(A_i, B_j)` does not tend to 0.
   (Contradiction: if all → 0, then inner products → 0, coefficients → 0,
   hence ‖B_j(N)‖ → 0, contradicting self-overlap → 1.)
3. Dimension match: if `dimA i ≠ dimB j`, overlap → 0 by `mpvOverlap_tendsto_zero_of_dim_ne`.
4. Gauge-phase equivalence: contrapositive of `mpvOverlap_tendsto_zero`.
5. Injectivity of the assignment (hence permutation) from B-off-diagonal orthogonality.
-/

open scoped BigOperators Matrix InnerProductSpace
open Filter Finset

namespace MPSTensor

/-! ## Overlap ↔ inner product conversion -/

private lemma tendsto_mpvInner_zero_of_overlap_zero
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (h : Tendsto (fun N => mpvOverlap (d := d) A B N) atTop (nhds (0 : ℂ))) :
    Tendsto (fun N => mpvInner (d := d) A B N) atTop (nhds (0 : ℂ)) := by
  have h' := h.star
  simpa [mpvOverlap_eq_star_mpvInner] using h'

private lemma tendsto_mpvInner_one_of_overlap_one
    {d D : ℕ} (A : MPSTensor d D)
    (h : Tendsto (fun N => mpvOverlap (d := d) A A N) atTop (nhds (1 : ℂ))) :
    Tendsto (fun N => mpvInner (d := d) A A N) atTop (nhds (1 : ℂ)) := by
  have h' := h.star
  simpa [mpvOverlap_eq_star_mpvInner] using h'

/-! ## Helper: norm of phase from self-overlap scaling -/

/-- If `mpvOverlap B B N = (ζ * star ζ)^N * mpvOverlap A A N` and both self-overlaps have
norm → 1, then `‖ζ‖ = 1`. -/
private lemma norm_eq_one_of_selfOverlap_scale
    {d D D' : ℕ} {A : MPSTensor d D} {B : MPSTensor d D'} {ζ : ℂ}
    (hAA : Tendsto (fun N => ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1))
    (hBB : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖) atTop (nhds 1))
    (hSelf : ∀ N : ℕ,
      mpvOverlap (d := d) B B N =
      (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) A A N) :
    ‖ζ‖ = 1 := by
  have hAA_ne : ∀ᶠ N in atTop, ‖mpvOverlap (d := d) A A N‖ ≠ 0 :=
    hAA.eventually_ne one_ne_zero
  have hRatio : Tendsto (fun N => ‖mpvOverlap (d := d) B B N‖ /
      ‖mpvOverlap (d := d) A A N‖) atTop (nhds 1) := by
    rw [show (1 : ℝ) = 1 / 1 from (one_div_one).symm]
    exact hBB.div hAA one_ne_zero
  have hRatioEq : ∀ᶠ N in atTop,
      ‖mpvOverlap (d := d) B B N‖ / ‖mpvOverlap (d := d) A A N‖ = (‖ζ‖ ^ 2) ^ N := by
    filter_upwards [hAA_ne] with N hN
    rw [hSelf N, norm_mul, norm_pow, show ‖ζ * starRingEnd ℂ ζ‖ = ‖ζ‖ ^ 2 from by
      rw [norm_mul, RCLike.norm_conj, sq]]
    rw [← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_div_cancel_of_imp (fun h => absurd h hN)
  have hPow : Tendsto (fun N => (‖ζ‖ ^ 2) ^ N) atTop (nhds 1) :=
    hRatio.congr' hRatioEq
  have h1 : ‖ζ‖ ^ 2 = 1 := by
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with h | h
    · exact zero_ne_one (tendsto_nhds_unique
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) h) hPow)
    · have hlt2 : ∀ᶠ n in atTop, (‖ζ‖ ^ 2) ^ n < 2 :=
        hPow.eventually (Iio_mem_nhds (by norm_num : (1:ℝ) < 2))
      rcases ((tendsto_atTop.1 (tendsto_pow_atTop_atTop_of_one_lt h) 2).and hlt2).exists
        with ⟨n, hn1, hn2⟩
      exact not_lt_of_ge hn1 hn2
  nlinarith [norm_nonneg ζ]

/-! ## Main theorem -/

set_option maxHeartbeats 800000 in
-- The proof involves multiple nested convergence arguments and Gram matrix inversions.
/--
**BNT permutation rigidity (primitive branch).**

Two finite families of primitive blocks whose MPV overlaps are asymptotically orthonormal
and which span the same MPV subspace at each system size must agree blockwise up to a
permutation, dimension equality, and gauge-phase equivalence.
-/
theorem exists_perm_dimEq_gaugePhaseEquiv_of_overlapOrtho
    {d g : ℕ}
    {dimA dimB : Fin g → ℕ}
    [∀ j, NeZero (dimA j)] [∀ j, NeZero (dimB j)]
    (A : (j : Fin g) → MPSTensor d (dimA j))
    (B : (j : Fin g) → MPSTensor d (dimB j))
    (hA_inj : ∀ j, IsInjective (A j))
    (hB_inj : ∀ j, IsInjective (B j))
    (hA_norm : ∀ j, (∑ i : Fin d, (A j i)ᴴ * (A j i)) = 1)
    (hB_norm : ∀ j, (∑ i : Fin d, (B j i)ᴴ * (B j i)) = 1)
    (hA_self : ∀ j, Tendsto (fun N => mpvOverlap (d := d) (A j) (A j) N) atTop (nhds (1 : ℂ)))
    (hA_off : ∀ i j, i ≠ j → Tendsto (fun N => mpvOverlap (d := d) (A i) (A j) N) atTop (nhds 0))
    (hB_self : ∀ j, Tendsto (fun N => mpvOverlap (d := d) (B j) (B j) N) atTop (nhds (1 : ℂ)))
    (hB_off : ∀ i j, i ≠ j → Tendsto (fun N => mpvOverlap (d := d) (B i) (B j) N) atTop (nhds 0))
    (hspan : ∀ N,
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (d := d) (A j) N))
      =
      Submodule.span ℂ (Set.range (fun j : Fin g => mpvState (d := d) (B j) N))) :
    ∃ perm : Fin g ≃ Fin g,
      ∀ j,
        ∃ hdim : dimA j = dimB (perm j),
          GaugePhaseEquiv (d := d)
            (cast (congr_arg (MPSTensor d) hdim) (A j))
            (B (perm j)) := by
  classical
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 0: Extract an eventually-valid change-of-basis matrix `U_N`.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hU_event :=
    MPSTensor.eventually_exists_invertible_changeBasis
      (A := A) (B := B)
      (hA_diag := hA_self) (hA_off := hA_off)
      (hB_diag := hB_self) (hB_off := hB_off)
      (hspan := hspan)
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hU_event
  let U : ℕ → Matrix (Fin g) (Fin g) ℂ := fun N =>
    if h : N0 ≤ N then (hN0 N h).choose else 0
  have hU_spec : ∀ N, N0 ≤ N →
      (U N).det ≠ 0 ∧
      ∀ j : Fin g,
        mpvState (d := d) (B j) N =
          ∑ i : Fin g, (U N) i j • mpvState (d := d) (A i) N := by
    intro N hN
    simp only [U, dif_pos hN]
    exact (hN0 N hN).choose_spec
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 1: Gram matrix of A tends to 1, and its inverse tends to 1.
  -- ═══════════════════════════════════════════════════════════════════════════
  have hA_inner_diag : ∀ i : Fin g,
      Tendsto (fun N => mpvInner (d := d) (A i) (A i) N) atTop (nhds (1 : ℂ)) :=
    fun i => tendsto_mpvInner_one_of_overlap_one (A i) (hA_self i)
  --
  have hA_inner_off : ∀ i j : Fin g, i ≠ j →
      Tendsto (fun N => mpvInner (d := d) (A i) (A j) N) atTop (nhds (0 : ℂ)) :=
    fun i j hij => tendsto_mpvInner_zero_of_overlap_zero (A i) (A j) (hA_off i j hij)
  --
  let GA : ℕ → Matrix (Fin g) (Fin g) ℂ := fun N i j => mpvInner (d := d) (A i) (A j) N
  --
  have hGA_tendsto : Tendsto GA atTop (nhds (1 : Matrix (Fin g) (Fin g) ℂ)) := by
    rw [tendsto_pi_nhds]; intro i; rw [tendsto_pi_nhds]; intro j
    simp only [Matrix.one_apply]
    split_ifs with h
    · subst h; exact hA_inner_diag i
    · exact hA_inner_off i j h
  --
  have hGA_inv_tendsto :
      Tendsto (fun N => (GA N)⁻¹) atTop (nhds (1 : Matrix (Fin g) (Fin g) ℂ)) := by
    have hcont : ContinuousAt Inv.inv (1 : Matrix (Fin g) (Fin g) ℂ) := by
      apply continuousAt_matrix_inv
      simp only [Ring.inverse_eq_inv', Matrix.det_one]
      exact ContinuousInv₀.continuousAt_inv₀ (x := (1 : ℂ)) one_ne_zero
    have h1 := hcont.tendsto.comp hGA_tendsto
    rwa [Function.comp_def, show (1 : Matrix (Fin g) (Fin g) ℂ)⁻¹ = 1 from
      Matrix.inv_eq_left_inv (one_mul _)] at h1
  --
  have hGA_inv_entry : ∀ i j : Fin g,
      Tendsto (fun N => (GA N)⁻¹ i j) atTop (nhds (if i = j then (1 : ℂ) else 0)) := by
    intro i j
    have h1 := (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hGA_inv_tendsto i)) j
    simpa [Matrix.one_apply] using h1
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 2: For each j, find i with non-decaying mixed overlap.
  -- ═══════════════════════════════════════════════════════════════════════════
  have exists_nonzero_overlap : ∀ j : Fin g,
      ∃ i : Fin g,
        ¬ Tendsto (fun N => mpvOverlap (d := d) (A i) (B j) N) atTop (nhds (0 : ℂ)) := by
    intro j
    by_contra hall
    push_neg at hall
    have hall_inner : ∀ i : Fin g,
        Tendsto (fun N => mpvInner (d := d) (A i) (B j) N) atTop (nhds (0 : ℂ)) :=
      fun i => tendsto_mpvInner_zero_of_overlap_zero (A i) (B j) (hall i)
    --
    let u : ℕ → Fin g → ℂ := fun N i => U N i j
    let v : ℕ → Fin g → ℂ := fun N k => mpvInner (d := d) (A k) (B j) N
    --
    -- Eventually v_k = ∑ i, GA_{ki} * u_i.
    have hvu : ∀ N, N0 ≤ N →
        ∀ k : Fin g, v N k = ∑ i : Fin g, GA N k i * u N i := by
      intro N hN k
      have hexp := (hU_spec N hN).2 j
      change mpvInner (d := d) (A k) (B j) N = ∑ i, mpvInner (d := d) (A k) (A i) N * U N i j
      simp only [mpvInner, hexp, inner_sum, inner_smul_right]
      congr 1; ext i; ring
    --
    -- GA det eventually nonzero.
    have hGA_det_tendsto : Tendsto (fun N => (GA N).det) atTop (nhds (1 : ℂ)) := by
      have := (continuous_id.matrix_det.tendsto (1 : Matrix (Fin g) (Fin g) ℂ)).comp hGA_tendsto
      simpa [Function.comp_def, Matrix.det_one] using this
    --
    have hGA_det_ne : ∀ᶠ N in atTop, (GA N).det ≠ 0 :=
      hGA_det_tendsto.eventually_ne one_ne_zero
    --
    -- Each component of u tends to 0.
    have hu_tendsto_zero : ∀ i : Fin g,
        Tendsto (fun N => u N i) atTop (nhds (0 : ℂ)) := by
      intro i
      have hterm : ∀ k : Fin g,
          Tendsto (fun N => (GA N)⁻¹ i k * v N k) atTop (nhds (0 : ℂ)) := by
        intro k
        have := (hGA_inv_entry i k).mul (hall_inner k)
        simp only [mul_zero] at this; exact this
      have hsum : Tendsto (fun N => ∑ k : Fin g, (GA N)⁻¹ i k * v N k) atTop (nhds (0 : ℂ)) := by
        have := tendsto_finset_sum Finset.univ (fun k _ => hterm k)
        simpa using this
      have hev : ∀ᶠ N in atTop, u N i = ∑ k : Fin g, (GA N)⁻¹ i k * v N k := by
        filter_upwards [hGA_det_ne, Filter.eventually_atTop.2 ⟨N0, fun N h => h⟩]
          with N hdetN hN0N
        have hunit : IsUnit (GA N).det := isUnit_iff_ne_zero.2 hdetN
        have _ : Invertible (GA N) := Matrix.invertibleOfIsUnitDet _ hunit
        have hvk : ∀ k, v N k = ∑ i, GA N k i * u N i := hvu N hN0N
        have hmat : (GA N).mulVec (u N) = v N := by
          ext k'; simp [Matrix.mulVec, dotProduct, hvk k']
        have hinv := Matrix.inv_mulVec_eq_vec (A := GA N) (u := v N) (v := u N) hmat.symm
        have := congr_fun hinv i
        simp only [Matrix.mulVec, dotProduct] at this
        exact this.symm
      exact hsum.congr' (hev.mono fun N hN => hN.symm)
    --
    -- ⟪B_j, B_j⟫ → 0, contradicting self-overlap → 1.
    have hBj_inner_zero : Tendsto (fun N => mpvInner (d := d) (B j) (B j) N)
        atTop (nhds (0 : ℂ)) := by
      have hprod : ∀ i : Fin g,
          Tendsto (fun N => starRingEnd ℂ (u N i) * v N i) atTop (nhds (0 : ℂ)) := by
        intro i
        have := (hu_tendsto_zero i).star.mul (hall_inner i)
        simp only [star_zero, zero_mul] at this; exact this
      have hsum : Tendsto (fun N => ∑ i : Fin g, starRingEnd ℂ (u N i) * v N i)
          atTop (nhds (0 : ℂ)) := by
        have := tendsto_finset_sum Finset.univ (fun i _ => hprod i)
        simpa using this
      have hev : ∀ᶠ N in atTop, mpvInner (d := d) (B j) (B j) N =
          ∑ i : Fin g, starRingEnd ℂ (u N i) * v N i := by
        filter_upwards [Filter.eventually_atTop.2 ⟨N0, fun N h => h⟩] with N hN0N
        have hexp := (hU_spec N hN0N).2 j
        simp only [mpvInner, hexp, sum_inner, inner_smul_left, v, u]
      exact hsum.congr' (hev.mono fun N hN => hN.symm)
    --
    have hBj_inner_one :
        Tendsto (fun N => mpvInner (d := d) (B j) (B j) N) atTop (nhds (1 : ℂ)) :=
      tendsto_mpvInner_one_of_overlap_one (B j) (hB_self j)
    --
    exact zero_ne_one (tendsto_nhds_unique hBj_inner_zero hBj_inner_one)
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 3: Define the matching function f and extract dim/gauge data.
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  let f : Fin g → Fin g := fun j => (exists_nonzero_overlap j).choose
  have hf_spec : ∀ j : Fin g,
      ¬ Tendsto (fun N => mpvOverlap (d := d) (A (f j)) (B j) N) atTop (nhds (0 : ℂ)) :=
    fun j => (exists_nonzero_overlap j).choose_spec
  --
  have hf_dim : ∀ j : Fin g, dimA (f j) = dimB j := by
    intro j
    by_contra hne
    exact hf_spec j (mpvOverlap_tendsto_zero_of_dim_ne (A (f j)) (B j)
      (hA_inj (f j)) (hB_inj j) (hA_norm (f j)) (hB_norm j) hne)
  --
  have hf_gauge : ∀ j : Fin g,
      GaugePhaseEquiv (d := d)
        (cast (congr_arg (MPSTensor d) (hf_dim j)) (A (f j)))
        (B j) := by
    intro j
    by_contra hNot
    have hdim := hf_dim j
    have hAcst_inj : IsInjective (cast (congr_arg (MPSTensor d) hdim) (A (f j))) :=
      (isInjective_cast_dim hdim (A (f j))).mpr (hA_inj (f j))
    have hAcst_norm : ∑ i : Fin d,
        (cast (congr_arg (MPSTensor d) hdim) (A (f j)) i)ᴴ *
        (cast (congr_arg (MPSTensor d) hdim) (A (f j)) i) = 1 :=
      (dsGauge_cast_dim hdim (A (f j))).mpr (hA_norm (f j))
    have hto0 := mpvOverlap_tendsto_zero
      (cast (congr_arg (MPSTensor d) hdim) (A (f j))) (B j)
      hAcst_inj (hB_inj j) hAcst_norm (hB_norm j) hNot
    exact hf_spec j (hto0.congr fun N => mpvOverlap_cast_dim_left hdim (A (f j)) (B j) N)
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 4: Show f is injective (hence a bijection on Fin g).
  -- ═══════════════════════════════════════════════════════════════════════════
  have hf_inj : Function.Injective f := by
    intro j1 j2 hfj
    by_contra hne
    have h_cross : Tendsto (fun N => mpvOverlap (d := d) (B j1) (B j2) N) atTop (nhds 0) :=
      hB_off j1 j2 hne
    --
    obtain ⟨X1, ζ1, hX1⟩ := hf_gauge j1
    obtain ⟨X2, ζ2, hX2⟩ := hf_gauge j2
    --
    -- MPV scaling formulas.
    have hmpv1 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B j1) σ = ζ1 ^ N * mpv (A (f j1)) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X1 ζ1 hX1 N σ, mpv_cast_dim (hf_dim j1)]
    have hmpv2 : ∀ (N : ℕ) (σ : Fin N → Fin d),
        mpv (B j2) σ = ζ2 ^ N * mpv (A (f j1)) σ := by
      intro N σ
      rw [mpv_eq_pow_mul_of_gaugePhase _ _ X2 ζ2 hX2 N σ, mpv_cast_dim (hf_dim j2), hfj]
    --
    -- Overlap scaling helper.
    have overlap_self_scale : ∀ (Dk : ℕ) (Bk : MPSTensor d Dk) (ζ : ℂ)
        (hmpv : ∀ (N : ℕ) (σ : Fin N → Fin d),
          mpv Bk σ = ζ ^ N * mpv (A (f j1)) σ),
        ∀ N : ℕ, mpvOverlap (d := d) Bk Bk N =
        (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (d := d) (A (f j1)) (A (f j1)) N := by
      intro Dk Bk ζ hmpv N
      show mpvOverlap Bk Bk N = (ζ * starRingEnd ℂ ζ) ^ N * mpvOverlap (A (f j1)) (A (f j1)) N
      simp only [mpvOverlap]
      simp_rw [hmpv N, star_mul, star_pow]
      simp_rw [show star ζ = starRingEnd ℂ ζ from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ζ ^ N * mpv (A (f j1)) x * (star (mpv (A (f j1)) x) * (starRingEnd ℂ ζ) ^ N) =
        ζ ^ N * (starRingEnd ℂ ζ) ^ N * (mpv (A (f j1)) x * star (mpv (A (f j1)) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    --
    -- Self-overlap of A(f j1) in norm → 1.
    have hAA_norm_tendsto :
        Tendsto (fun N => ‖mpvOverlap (d := d) (A (f j1)) (A (f j1)) N‖) atTop (nhds 1) := by
      convert (hA_self (f j1)).norm using 1; simp
    --
    -- BB overlap norms → 1.
    have hBB1_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B j1) (B j1) N‖) atTop (nhds 1) := by
      convert (hB_self j1).norm using 1; simp
    have hBB2_norm :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B j2) (B j2) N‖) atTop (nhds 1) := by
      convert (hB_self j2).norm using 1; simp
    --
    have hζ1_norm : ‖ζ1‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB1_norm
        (overlap_self_scale _ (B j1) ζ1 hmpv1)
    have hζ2_norm : ‖ζ2‖ = 1 :=
      norm_eq_one_of_selfOverlap_scale hAA_norm_tendsto hBB2_norm
        (overlap_self_scale _ (B j2) ζ2 hmpv2)
    --
    -- Cross overlap.
    have hCross_eq : ∀ N : ℕ,
        mpvOverlap (d := d) (B j1) (B j2) N =
        (ζ1 * starRingEnd ℂ ζ2) ^ N *
          mpvOverlap (d := d) (A (f j1)) (A (f j1)) N := by
      intro N
      show mpvOverlap (B j1) (B j2) N =
        (ζ1 * starRingEnd ℂ ζ2) ^ N * mpvOverlap (A (f j1)) (A (f j1)) N
      simp only [mpvOverlap]
      simp_rw [hmpv1 N, hmpv2 N, star_mul, star_pow]
      simp_rw [show star ζ2 = starRingEnd ℂ ζ2 from rfl]
      simp_rw [show ∀ (x : Cfg d N),
        ζ1 ^ N * mpv (A (f j1)) x * (star (mpv (A (f j1)) x) * (starRingEnd ℂ ζ2) ^ N) =
        ζ1 ^ N * (starRingEnd ℂ ζ2) ^ N * (mpv (A (f j1)) x * star (mpv (A (f j1)) x)) from
        fun x => by ring]
      rw [← Finset.mul_sum, mul_pow]
    --
    have hNormζ : ‖ζ1 * starRingEnd ℂ ζ2‖ = 1 := by
      rw [norm_mul, RCLike.norm_conj, hζ1_norm, hζ2_norm, mul_one]
    --
    have hCross_norm_one :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B j1) (B j2) N‖) atTop (nhds 1) := by
      have heq : (fun N => ‖mpvOverlap (d := d) (B j1) (B j2) N‖) =
          fun N => ‖(ζ1 * starRingEnd ℂ ζ2) ^ N‖ *
            ‖mpvOverlap (d := d) (A (f j1)) (A (f j1)) N‖ := by
        ext N; rw [hCross_eq, norm_mul]
      rw [heq]
      have : (fun N => ‖(ζ1 * starRingEnd ℂ ζ2) ^ N‖ *
          ‖mpvOverlap (d := d) (A (f j1)) (A (f j1)) N‖) =
          fun N => 1 * ‖mpvOverlap (d := d) (A (f j1)) (A (f j1)) N‖ := by
        ext N; rw [norm_pow, hNormζ, one_pow]
      rw [this]; simpa using hAA_norm_tendsto
    --
    have hCross_norm_zero :
        Tendsto (fun N => ‖mpvOverlap (d := d) (B j1) (B j2) N‖) atTop (nhds 0) := by
      convert h_cross.norm using 1; simp
    --
    exact zero_ne_one (tendsto_nhds_unique hCross_norm_zero hCross_norm_one)
  --
  -- ═══════════════════════════════════════════════════════════════════════════
  -- Step 5: Build the permutation and re-index.
  -- ═══════════════════════════════════════════════════════════════════════════
  --
  have hf_bij : Function.Bijective f :=
    ⟨hf_inj, (Finite.injective_iff_surjective.mp hf_inj)⟩
  let e : Fin g ≃ Fin g := Equiv.ofBijective f hf_bij
  refine ⟨e.symm, fun j => ?_⟩
  have hfe : f (e.symm j) = j := Equiv.ofBijective_apply_symm_apply f hf_bij j
  have hdim : dimA j = dimB (e.symm j) := by
    have := hf_dim (e.symm j); rw [hfe] at this; exact this
  exact ⟨hdim, gaugePhaseEquiv_cast_idx A B hfe (hf_dim (e.symm j)) (hf_gauge (e.symm j))⟩

end MPSTensor
