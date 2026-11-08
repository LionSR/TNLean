/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.AKLV.CenteredWindow
import TNLean.MPS.AreaLaw.AKLV.CutApproximationTail
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeAccuracyParameters
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeFilter
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeParameters
import TNLean.MPS.AreaLaw.AKLV.SequentialApproximation
import TNLean.MPS.AreaLaw.AKLV.VariableWindowRefinement

/-!
# Matrix product approximation of a frustration-free ground vector

At every cut, a product vector of good overlap with the original frustration-free
ground vector is filtered twice. The first filter, on the window of the entropy
theorem, gives a vector within squared distance `1/16` of the ground vector. The
second filter, of degree `s²` on a window enlarged by a cube-root increment, brings
it within squared distance `ρ`. If the enlarged window does not fit, the ground
vector itself has the boundary rank. Sequential truncation then gives a normalized
open-boundary matrix product state within `ε` of the ground vector.

Source: AKLV, arXiv:1301.1162v1, Section 5, lines 851–870, using Lemma 2.2
(`lem:mu1`, lines 332–337), Lemma `l:agsp` (lines 586–663) and the frustration-free
clipping preceding Theorem `t:ent` (lines 810–818). The source's gap `ε` is the
actual first excitation, so local dimension at least two and `g ≤ 1` are derived.

**Local fix (rate):** The bound on `log D` retains the factor
`u + log(z+1)`, with `u = 1 + log q + log(1/g)` and `z = log(2048(L+1)/ε²)`, and the
additive term `u³/g`. For accuracy `L^{-c}` at fixed `q` and `g` it is of order
`log^{2/3} L · log log L`. The printed `exp(O(ε^{-1/3} log^{2/3} n))` omits the factor
`log ℓ` of Lemma `l:agsp` (line 590) and is not asserted; see
`docs/paper-gaps/aklv13_frustration_free_mps_rate.tex`.
-/

open Matrix Polynomial Real
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- Two spectral values `0` and `g > 0` of a positive nearest-neighbour chain with
frustration-free unit ground vector force local dimension at least two and `g ≤ 1`.
This is the normalization of AKLV, arXiv:1301.1162v1, Section 5, before equation (4),
at ground energy zero. -/
theorem aklv_frustrationFree_dimension_and_gap_bounds {L q : ℕ}
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h j) (interval L j.val (j.val + 2)))
    (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (hzero : (∑ j, h j) *ᵥ WithLp.ofLp Ω = 0)
    (hgap : ((∑ j, h j) - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (hg : 0 < g) (hexcited : g ∈ spectrum ℝ (∑ j, h j)) :
    2 ≤ q ∧ g ≤ 1 := by
  classical
  have hH : (∑ j, h j).IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (Finset.sum_nonneg fun j _ ↦ h0 j)).isHermitian
  have hground : (∑ j, h j) *ᵥ WithLp.ofLp Ω = ((0 : ℝ) : ℂ) • WithLp.ofLp Ω := by
    rw [hzero, Complex.ofReal_zero, zero_smul]
  have hmu := Matrix.mem_spectrum_real_of_mulVec_eq_smul
    (by intro hz; simp only [hz, norm_zero, zero_ne_one] at hΩ) hground
  have hq : 2 ≤ q :=
    hH.two_le_local_dimension_of_two_spectral_values hmu hexcited (ne_of_lt hg)
  have hL : 0 < L := by
    by_contra hnot
    have hL0 : L = 0 := by omega
    have hcfg : Subsingleton (Fin L → Fin q) := by subst L; infer_instance
    let := hcfg
    obtain ⟨i, hi⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hmu
    obtain ⟨j, hj⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hexcited
    have heq : (0 : ℝ) = g := hi.symm.trans
      ((congrArg hH.eigenvalues (Subsingleton.elim i j)).trans hj)
    linarith
  have hgs : IsGappedGroundState (∑ j, h j) 0 Ω g :=
    isGappedGroundState_iff.mpr ⟨hΩ, hground,
      by simpa only [Complex.ofReal_zero, zero_smul, sub_zero] using hgap⟩
  exact ⟨hq, gap_le_one_of_positive_nearest_neighbor_terms hL hq h hsupp h0 h1 hgs⟩

/-- Two physical filters at one cut. The filter of degree `s₀²` on the window of width
`s₀`, applied to a product vector of good overlap, gives a vector of rank at most `D₀`
within squared distance `1/16` of the frustration-free ground vector. The filter of
degree `s²` on the window of width `s = s₀ + 2m` with the same centre then brings it
within eight times its squared shrinking amplitude, at rank at most `D₀D₁`.
AKLV, arXiv:1301.1162v1, Section 5, lines 862–868, with Lemma 2.2 (`lem:mu1`). -/
theorem exists_aklv_frustrationFree_two_filter_approximant {L q a s0 m s : ℕ}
    (hq : 1 ≤ q) (hs0 : 6 ≤ s0) (hs : s = s0 + 2 * m) (ha : a + s + 1 ≤ L)
    (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
    (hsupp : ∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
      (h j) (interval L j.val (j.val + 2)))
    (h0 : ∀ j, 0 ≤ h j) (h1 : ∀ j, h j ≤ 1)
    (Ω : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1)
    (g : ℝ) (hg : 0 < g) (hg1 : g ≤ 1)
    (hzero : (∑ j, h j) *ᵥ WithLp.ofLp Ω = 0)
    (hgap : ((∑ j, h j) - (g : ℂ) •
      (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef)
    (htrade : (((q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) : ℕ) : ℝ) *
      (4 * exp (-(4 * ((s0 ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * (1024 / g) + s0))))) ≤
        1 / 100000) :
    ∃ y : EuclideanSpace ℂ (Fin L → Fin q), ‖y‖ = 1 ∧
      ‖y - Ω‖ ^ 2 ≤
        8 * (2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * (1024 / g) + s)))) ^ 2 ∧
      (cutMatrix y (a + s / 2)).rank ≤
        (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1)) * (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1)) := by
  classical
  let t := 1024 / g
  let k := a + s / 2
  let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
  let D1 : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
  let delta0 := 4 * exp (-(4 * ((s0 ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * t + s0))))
  change (D0 : ℝ) * delta0 ≤ 1 / 100000 at htrade
  have hk0 : a + m + s0 / 2 = k := by dsimp only [k]; omega
  have ha0 : a + m + s0 + 1 ≤ L := by omega
  have hsquare (n : ℕ) (hn : 0 < n) : n ^ 2 / n = n ∧ Nat.sqrt (n ^ 2) = n :=
    ⟨by rw [pow_two, Nat.mul_div_cancel _ hn], Nat.sqrt_eq' n⟩
  -- The filter at the initial window and its product-overlap initialization.
  obtain ⟨-, -, -, -, -, hfilter0⟩ :=
    exists_aklv_frustrationFree_chebyshev_filter (a := a + m) (s := s0) hq hs0 ha0
      h hsupp h0 h1 Ω hΩ g t hg hg1 le_rfl hzero hgap
  obtain ⟨p0, -, -, hfix0, -, -, hrank0, hperp0⟩ := hfilter0 (s0 ^ 2)
  let K0 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval
    (aklvTwoBlockHamiltonian (a + m + 2) (a + m + s0 - 1) h (fun _ ↦ 0) t Finset.univ) p0
  have hrank0' : operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) K0) ≤ D0 := by
    rw [← hk0]
    change _ ≤ (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
    obtain ⟨hdiv, hsqrt⟩ := hsquare s0 (by omega)
    simpa only [hdiv, hsqrt, two_mul] using hrank0
  have hDelta0 :
      (2 * exp (-2 * ((s0 ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * t + s0)))) ^ 2 = delta0 := by
    dsimp only [delta0]
    rw [mul_pow, ← exp_nat_mul]
    norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
    congr 1
    congr 1
    ring
  have hperp0' (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
      (horth : ⟪Ω, ψ⟫_ℂ = 0) :
      ⟪Ω, toEuclideanLin K0 ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K0 ψ‖ ^ 2 ≤ delta0 := by
    obtain ⟨horthK, hnormK⟩ := hperp0 ψ hψ horth
    exact ⟨horthK, hnormK.trans_eq hDelta0⟩
  have hD0pos : 0 < D0 := Nat.pow_pos (Nat.mul_pos (by omega) (Nat.succ_pos _))
  have hdelta0 : 0 ≤ delta0 := by dsimp only [delta0]; positivity
  obtain ⟨χ, _vL, _vR, c0, _hχ, _hproduct, _hoverlapχ, _hK0χ, _hc0, hx, hxrank, hxΩ⟩ :=
    exists_cut_product_filtered_output (k := k) K0 Ω hΩ hfix0 hdelta0 hD0pos
      hperp0' hrank0' (by linarith only [htrade])
  set x := c0 • (‖toEuclideanLin K0 χ‖⁻¹ : ℂ) • toEuclideanLin K0 χ
  have hxΩ' : ‖x - Ω‖ ^ 2 ≤ 1 / 16 := by linarith only [hxΩ, htrade]
  -- The filter of degree `s²` at the enlarged window.
  obtain ⟨-, -, -, -, -, hfilter1⟩ :=
    exists_aklv_frustrationFree_chebyshev_filter (a := a) (s := s) hq (by omega) ha
      h hsupp h0 h1 Ω hΩ g t hg hg1 le_rfl hzero hgap
  obtain ⟨p1, -, -, hfix1, -, -, hrank1, hperp1⟩ := hfilter1 (s ^ 2)
  let K1 : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval
    (aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h (fun _ ↦ 0) t Finset.univ) p1
  have hrank1' : operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
      (leftBlock L k) K1) ≤ D1 := by
    change _ ≤ (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
    obtain ⟨hdiv, hsqrt⟩ := hsquare s (by omega)
    simpa only [hdiv, hsqrt, two_mul] using hrank1
  let b := 2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * t + s)))
  -- The overlap of the initialized vector and the filtered output.
  have hoverlap : 1 / 2 ≤ ‖⟪Ω, x⟫_ℂ‖ := by
    have hid := norm_sub_sq (𝕜 := ℂ) Ω x
    rw [hΩ, hx, norm_sub_rev Ω x] at hid
    change ‖x - Ω‖ ^ 2 = 1 ^ 2 - 2 * (⟪Ω, x⟫_ℂ).re + 1 ^ 2 at hid
    have hre := Complex.re_le_norm ⟪Ω, x⟫_ℂ
    linarith only [hid, hre, hxΩ']
  have hoverlap0 : ⟪Ω, x⟫_ℂ ≠ 0 := by
    intro hz0
    rw [hz0, norm_zero] at hoverlap
    linarith only [hoverlap]
  have hres : ‖x - ⟪Ω, x⟫_ℂ • Ω‖ ^ 2 ≤ 1 := by
    have hp := (Submodule.span ℂ {Ω})ᗮ.norm_starProjection_apply_le x
    rw [Submodule.starProjection_orthogonal_val,
      Submodule.starProjection_unit_singleton ℂ hΩ] at hp
    simpa only [hx, one_pow] using pow_le_pow_left₀ (norm_nonneg _) hp 2
  obtain ⟨hK1x, c, hc, hyunit, hyerror⟩ :=
    exists_phase_normalized_filter_output K1 Ω x hΩ hfix1 (b ^ 2) hperp1 hoverlap0
  refine ⟨c • (‖toEuclideanLin K1 x‖⁻¹ : ℂ) • toEuclideanLin K1 x, hyunit, ?_, ?_⟩
  · have hinner : (1 : ℝ) / 4 ≤ ‖⟪Ω, x⟫_ℂ‖ ^ 2 := by
      have h2 := pow_le_pow_left₀ (by norm_num) hoverlap 2
      linarith only [h2]
    calc
      _ ≤ 2 * b ^ 2 * ‖x - ⟪Ω, x⟫_ℂ • Ω‖ ^ 2 / ‖⟪Ω, x⟫_ℂ‖ ^ 2 := hyerror
      _ ≤ 2 * b ^ 2 * 1 / (1 / 4) := by
        apply div_le_div₀ (by positivity) _ (by norm_num) hinner
        exact mul_le_mul_of_nonneg_left hres (by positivity)
      _ = 8 * b ^ 2 := by ring
  · have hc0 : c ≠ 0 := by
      intro hz0
      simp only [hz0, norm_zero, zero_ne_one] at hc
    have hyrank := normalized_cut_schmidtRank_le (k := k) K1 x c hc0 hK1x
    change (cutMatrix (c • (‖toEuclideanLin K1 x‖⁻¹ : ℂ) • toEuclideanLin K1 x) k).rank ≤
      _ * (cutMatrix x k).rank at hyrank
    change (cutMatrix x k).rank ≤ D0 at hxrank
    change _ ≤ D0 * D1
    exact hyrank.trans ((Nat.mul_le_mul hrank1' hxrank).trans_eq (Nat.mul_comm _ _))

/-- At every cut of a frustration-free chain, a unit vector within squared distance `ρ`
of the original ground vector has Schmidt rank at most one common `D`, with the
cube-root logarithmic bound. The gap is a projector lower bound with `0 < g ≤ 1`.
AKLV, arXiv:1301.1162v1, Section 5, lines 862–870, with the rate of the module's
local fix. -/
theorem exists_aklv_frustrationFree_per_cut_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ (L q : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      2 ≤ q →
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = 0 →
      ((∑ j, h j) - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → g ≤ 1 → ∀ rho : ℝ, 0 < rho → rho ≤ 1 →
      let u := 1 + log (q : ℝ) + log (1 / g)
      let z := aklvAccuracyLog rho
      ∃ D : ℕ, log (D : ℝ) ≤
          C * (u ^ 3 / g + (z ^ 2 / g) ^ ((1 : ℝ) / 3) * (u + log (z + 1))) ∧
        ∀ k : ℕ, k ≤ L → ∃ y : EuclideanSpace ℂ (Fin L → Fin q),
          ‖y‖ = 1 ∧ ‖y - Ω‖ ^ 2 ≤ rho ∧ (cutMatrix y k).rank ≤ D := by
  obtain ⟨A, hA, _hA21, hscalar⟩ := exists_aklv_frustrationFree_scalar_parameters
  let W := 8192 * (A + 1) * (1 + log 8192) ^ 2
  let R := 8192 * (198 * (A + 1) * (6 + 2 * log (A + 1))) * (1 + log 8192) ^ 3
  have hlogA : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hlog8192 : 0 ≤ log (8192 : ℝ) := log_nonneg (by norm_num)
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  refine ⟨10001 * R + W + 8400000, by positivity, ?_⟩
  intro L q h g Ω hq hsupp h0 h1 hΩ hzero hgap hg hg1 rho hrho hrho1 u z
  let g0 := g / 8192
  let u0 := 1 + log (q : ℝ) + log (1 / g0)
  let s0 : ℕ := ⌈A * u0 ^ 2 / g0⌉₊
  let D0 : ℕ := (q * (s0 ^ 2 + 1)) ^ (32 * (2 * s0 + 1))
  obtain ⟨hs21, hsInv, hsUpper, -, -, -, -, htrade, -, hlogD⟩ := hscalar q g hq hg hg1
  change 21 ≤ s0 at hs21
  change 1 / g ≤ (s0 : ℝ) at hsInv
  change (s0 : ℝ) ≤ W / g * u ^ 2 at hsUpper
  change log (D0 : ℝ) ≤ R / g * u ^ 3 at hlogD
  let m := aklvFrustrationFreeIncrement g rho
  let s := s0 + 2 * m
  let D1 : ℕ := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
  let r := (z ^ 2 / g) ^ ((1 : ℝ) / 3)
  have hz : 1 ≤ z := (aklvAccuracyLog_bounds hrho hrho1).1
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (show 1 ≤ q by omega))
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hr0 : 0 ≤ r := rpow_nonneg (by positivity) _
  have hB : aklvFrustrationFreeRankBound q s0 g rho = max (D0 * D1) (q ^ (s - s / 2)) := by
    unfold aklvFrustrationFreeRankBound
    rfl
  refine ⟨aklvFrustrationFreeRankBound q s0 g rho, ?_, ?_⟩
  · have hbound := aklvFrustrationFreeRankBound_log_le hq hg hg1 hrho hrho1
      (show 1 ≤ s0 by omega) hR hW hlogD hsUpper
    change log (aklvFrustrationFreeRankBound q s0 g rho : ℝ) ≤
      (10001 * R + W) * (u ^ 3 / g) + 8400000 * (r * (u + log (z + 1))) at hbound
    change _ ≤ (10001 * R + W + 8400000) * (u ^ 3 / g + r * (u + log (z + 1)))
    have hX : 0 ≤ u ^ 3 / g := by positivity
    have hY : 0 ≤ r * (u + log (z + 1)) := by
      have := log_nonneg (show (1 : ℝ) ≤ z + 1 by linarith)
      positivity
    linarith only [hbound, hX, mul_nonneg (show 0 ≤ 10001 * R + W by positivity) hY]
  · intro k hk
    rw [hB]
    rcases aklv_centered_window_or_exact_rank (by omega : 1 ≤ q) hk Ω (s := s) with
      hfit | hexact
    · obtain ⟨a, hcenter, ha⟩ := hfit
      obtain ⟨y, hy, hyerror, hyrank⟩ := exists_aklv_frustrationFree_two_filter_approximant
        (s0 := s0) (m := m) (s := s) (by omega) (by omega) rfl ha h hsupp h0 h1 Ω hΩ g hg hg1
        hzero hgap htrade
      rw [hcenter] at hyrank
      refine ⟨y, hy, ?_, hyrank.trans (le_max_left _ _)⟩
      -- The shrinking factor of the second filter.
      obtain ⟨_hr1, hr3, hm6, -, -⟩ := aklvFrustrationFreeIncrement_bounds hg hg1 hrho hrho1
      change r ^ 3 = z ^ 2 / g at hr3
      change 6 * r ≤ (m : ℝ) at hm6
      have hs12 : 12 * r ≤ (s : ℝ) := by
        have hsR : (s : ℝ) = s0 + 2 * m := by dsimp only [s]; push_cast; ring
        have hs0R : (0 : ℝ) ≤ s0 := Nat.cast_nonneg _
        linarith only [hsR, hs0R, hm6]
      have hscale : 1728 * z ^ 2 ≤ g * (s : ℝ) ^ 3 := by
        have hcube := pow_le_pow_left₀ (by linarith only [hr0]) hs12 3
        have hid : (12 * r) ^ 3 = 1728 * (z ^ 2 / g) := by rw [mul_pow, hr3]; norm_num
        rw [hid] at hcube
        calc
          1728 * z ^ 2 = g * (1728 * (z ^ 2 / g)) := by field_simp
          _ ≤ g * (s : ℝ) ^ 3 := mul_le_mul_of_nonneg_left hcube hg.le
      have hsInv' : 1 / g ≤ (s : ℝ) :=
        hsInv.trans (by exact_mod_cast (Nat.le_add_right s0 (2 * m)))
      have hb := aklvFrustrationFree_shrink_le hg hrho hrho1 hsInv' hscale
      have hb0 : 0 ≤ 2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) * sqrt ((g / 2) / (2 * (1024 / g) + s))) :=
        by positivity
      have hbsq := pow_le_pow_left₀ hb0 hb 2
      have hrho2 : rho ^ 2 ≤ rho := pow_le_of_le_one hrho.le hrho1 two_ne_zero
      calc
        _ ≤ 8 * (2 * exp (-2 * ((s ^ 2 : ℕ) : ℝ) *
            sqrt ((g / 2) / (2 * (1024 / g) + s)))) ^ 2 := hyerror
        _ ≤ 8 * (rho / 64) ^ 2 := mul_le_mul_of_nonneg_left hbsq (by norm_num)
        _ ≤ rho := by linarith only [hrho2, hrho]
    · exact ⟨Ω, hΩ, by simpa using hrho.le, hexact.trans (le_max_right _ _)⟩

/-- A frustration-free unit ground vector with gap `g`, the actual first excited energy,
is within `ε` of a normalized open-boundary matrix product state of bond dimension `D`
with `log D ≤ C[u³/g + (z²/g)^{1/3}(u + log(z+1))]`, where `u = 1 + log q + log(1/g)`
and `z = log(2048(L+1)/ε²)`. The constant `C` is universal.

AKLV, arXiv:1301.1162v1, Section 5, lines 851–870. The hypotheses are those of the
source; the rate is that of the module's local fix. -/
theorem exists_aklv_frustrationFree_sequential_mps_approximation :
    ∃ C : ℝ, 0 < C ∧ ∀ (L q : ℕ)
      (h : Fin (L - 1) → Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ)
      (g : ℝ) (Ω : EuclideanSpace ℂ (Fin L → Fin q)),
      (∀ j, Entropy.IsSupportedOn (n := fun _ : Fin L ↦ q)
        (h j) (interval L j.val (j.val + 2))) →
      (∀ j, 0 ≤ h j) → (∀ j, h j ≤ 1) → ‖Ω‖ = 1 →
      (∑ j, h j) *ᵥ WithLp.ofLp Ω = 0 →
      ((∑ j, h j) - (g : ℂ) •
        (1 - vecMulVec (WithLp.ofLp Ω) (star (WithLp.ofLp Ω)))).PosSemidef →
      0 < g → g ∈ spectrum ℝ (∑ j, h j) →
      ∀ epsilon : ℝ, 0 < epsilon → epsilon ≤ 1 →
      let rho := epsilon ^ 2 / (16 * ((L : ℝ) + 1))
      let u := 1 + log (q : ℝ) + log (1 / g)
      let z := aklvAccuracyLog rho
      ∃ D : ℕ, log (D : ℝ) ≤
          C * (u ^ 3 / g + (z ^ 2 / g) ^ ((1 : ℝ) / 3) * (u + log (z + 1))) ∧
        aklvSpectralTruncation Ω D ≠ 0 ∧
        ‖aklvNormalizedSpectralTruncation Ω D‖ = 1 ∧
        IsOpenMPS L q D (fun x ↦ aklvNormalizedSpectralTruncation Ω D x) ∧
        ‖aklvNormalizedSpectralTruncation Ω D - Ω‖ ≤ epsilon := by
  obtain ⟨C, hC, hcut⟩ := exists_aklv_frustrationFree_per_cut_approximation
  refine ⟨C, hC, ?_⟩
  intro L q h g Ω hsupp h0 h1 hΩ hzero hgap hg hexcited epsilon hepsilon hepsilon1 rho u z
  obtain ⟨hq, hg1⟩ :=
    aklv_frustrationFree_dimension_and_gap_bounds h hsupp h0 h1 g Ω hΩ hzero hgap hg hexcited
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  have hrho1 : rho ≤ 1 := by
    dsimp only [rho]
    apply (div_le_iff₀ (by positivity : 0 < 16 * ((L : ℝ) + 1))).2
    have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have he2 : epsilon ^ 2 ≤ 1 := pow_le_one₀ hepsilon.le hepsilon1
    linarith only [hL, he2]
  obtain ⟨D, hlog, hcuts⟩ := hcut L q h g Ω hq hsupp h0 h1 hΩ hzero hgap hg hg1 rho hrho hrho1
  refine ⟨D, hlog, ?_⟩
  have htail (k : ℕ) (hk : k ≤ L) :
      1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
        (leftBlock L k) Ω).kyFanNorm D ≤ rho := by
    obtain ⟨y, hy, herror, hrank⟩ := hcuts k hk
    exact one_sub_kyFanNorm_le_of_unit_cut_rank_approximation Ω y hΩ hy herror hrank
  exact aklvNormalizedSpectralTruncation_spec Ω hΩ hepsilon hepsilon1 fun k hk ↦
    htail k (Finset.mem_Ico.mp hk).2.le

end TNLean.MPS.AreaLaw
