/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Entropy.AGSPRegionalEntropy
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeFilter
import TNLean.MPS.AreaLaw.AKLV.FrustrationFreeParameters
import TNLean.MPS.AreaLaw.AKLV.PhysicalEntropy

/-!
# Entropy of the original frustration-free ground vector at every cut

One universal constant bounds the original vector's regional entropy at every
physical cut. A fitting window uses the actual clipped Chebyshev filter, which
fixes that same vector. If the window does not fit, the smaller-side dimension
bound suffices. No first-excited-energy, product-overlap, spectral-tail, filter,
or fitting-window hypothesis is supplied.

Source: AKLV, arXiv:1301.1162v1, the proof of `t:ent`, lines 810–846, and the
favorable approximate-projector entropy consequence `col:half`, lines 350–361.

**Scope restriction (logarithmic rate):** The bound retains
`1 + log q + log(1/g)` with an explicit lower gap `0 < g ≤ 1` and `q ≥ 2`.
It does not claim the sharper removal of inverse-gap logarithms from the
printed rate. The clipping and entropy scope are recorded in
`docs/paper-gaps/aklv13_two_block_robustness.tex`.
-/

open Matrix Polynomial Real
open scoped BigOperators InnerProductSpace ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- A universal inverse-gap cubic-logarithmic entropy bound for the original
frustration-free unit ground vector, uniformly over chain lengths and cuts.
The gap is a projector lower bound; it need not be an attained excitation.
AKLV, arXiv:1301.1162v1, `t:ent`, lines 810–846, with the logarithmic rate
specified in the module's scope restriction. -/
theorem exists_aklv_frustrationFree_physical_entropy_bound :
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
      0 < g → g ≤ 1 → ∀ k : ℕ, k ≤ L →
      Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) Ω ≤
        C / g * (1 + log (q : ℝ) + log (1 / g)) ^ 3 := by
  obtain ⟨A, hA, _hA21, hscalar⟩ := exists_aklv_frustrationFree_scalar_parameters
  let W := 8192 * (A + 1) * (1 + log 8192) ^ 2
  let R := 8192 * (198 * (A + 1) * (6 + 2 * log (A + 1))) * (1 + log 8192) ^ 3
  let C := 4 * R + W
  have hA0 : 0 ≤ A := by linarith
  have hlogA : 0 ≤ log (A + 1) := log_nonneg (by linarith)
  have hlog8192 : 0 ≤ log (8192 : ℝ) := log_nonneg (by norm_num)
  have hW : 0 < W := by dsimp only [W]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro L q h g Ω hq hsupp h0 h1 hΩ hzero hgap hg hg1 k hk
  classical
  let g0 := g / 8192
  let u := 1 + log (q : ℝ) + log (1 / g)
  let u0 := 1 + log (q : ℝ) + log (1 / g0)
  let s : ℕ := ⌈A * u0 ^ 2 / g0⌉₊
  let ell := s ^ 2
  let t := 1024 / g
  let D := (q * (s ^ 2 + 1)) ^ (32 * (2 * s + 1))
  let delta := 4 * exp (-(4 * (ell : ℝ) * sqrt ((g / 2) / (2 * t + s))))
  obtain ⟨hs21, _hsInv, hsUpper, hdiv, hsqrt, _hpositive, _hdelta,
      htrade, _htradeSmall, hlogD⟩ := hscalar q g hq hg hg1
  change 21 ≤ s at hs21
  change (s : ℝ) ≤ W / g * u ^ 2 at hsUpper
  change ell / s = s at hdiv
  change Nat.sqrt ell = s at hsqrt
  change (D : ℝ) * delta ≤ 1 / 100000 at htrade
  change log (D : ℝ) ≤ R / g * u ^ 3 at hlogD
  have hlogg : 0 ≤ log (1 / g) := log_nonneg ((one_le_div hg).mpr hg1)
  have hlogq : 0 ≤ log (q : ℝ) := log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hu : 1 ≤ u := by dsimp only [u]; linarith
  have hu0 : 0 ≤ u := by linarith
  have hlogqu : log (q : ℝ) ≤ u := by dsimp only [u]; linarith
  by_cases hfit : ∃ a : ℕ, a + s / 2 = k ∧ a + s + 1 ≤ L
  · obtain ⟨a, hcenter, hfit⟩ := hfit
    obtain ⟨_hBpos, _hBH, _hBnorm, _hBΩ, _hBgap, hfilter⟩ :=
      exists_aklv_frustrationFree_chebyshev_filter (a := a) (s := s)
        (by omega : 1 ≤ q) (by omega : 6 ≤ s) hfit h hsupp h0 h1 Ω hΩ
        g t hg hg1 le_rfl hzero hgap
    obtain ⟨p, _hdegree, _hp0, hfix, _herror, _hshortRank, hrank, hperp⟩ := hfilter ell
    let B := aklvTwoBlockHamiltonian (a + 2) (a + s - 1) h (fun _ ↦ 0) t Finset.univ
    let K : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ := Polynomial.aeval B p
    have hrankD : operatorSchmidtRank (Entropy.cutOperator (n := fun _ : Fin L ↦ q)
        (leftBlock L (a + s / 2)) K) ≤ D := by
      change _ ≤ (q * (ell + 1)) ^ (32 * (2 * s + 1))
      simpa only [hdiv, hsqrt, two_mul] using hrank
    have hDeltaEq :
        (2 * exp (-2 * (ell : ℝ) * sqrt ((g / 2) / (2 * t + s)))) ^ 2 = delta := by
      dsimp only [delta]
      rw [mul_pow, ← exp_nat_mul]
      norm_num only [Nat.cast_ofNat, show (2 : ℝ) ^ 2 = 4 by norm_num]
      congr 1
      congr 1
      ring
    have hperpDelta (ψ : EuclideanSpace ℂ (Fin L → Fin q))
        (hψ : ‖ψ‖ = 1) (horth : ⟪Ω, ψ⟫_ℂ = 0) :
        ⟪Ω, toEuclideanLin K ψ⟫_ℂ = 0 ∧ ‖toEuclideanLin K ψ‖ ^ 2 ≤ delta := by
      obtain ⟨horthK, hnormK⟩ := hperp ψ hψ horth
      exact ⟨horthK, hnormK.trans_eq hDeltaEq⟩
    have hbound := Entropy.regionEntropy_le_four_log_of_cutOperatorSchmidtRank
      (D := D) (δ := delta) (leftBlock L (a + s / 2)) K Ω hΩ hfix hperpDelta hrankD
      (htrade.trans (by norm_num))
    rw [hcenter] at hbound
    calc
      _ ≤ 4 * log (D : ℝ) := hbound
      _ ≤ 4 * (R / g * u ^ 3) := mul_le_mul_of_nonneg_left hlogD (by norm_num)
      _ = (4 * R) / g * u ^ 3 := by ring
      _ ≤ C / g * u ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ hg.le
        dsimp only [C]
        linarith
  · have hsmall := (aklv_short_side_of_no_centered_window hk hfit).trans (Nat.sub_le _ _)
    calc
      _ ≤ ((min k (L - k) : ℕ) : ℝ) * log (q : ℝ) :=
        aklv_regionEntropy_le_short_side hk Ω hΩ
      _ ≤ (s : ℝ) * u := mul_le_mul (by exact_mod_cast hsmall) hlogqu hlogq
        (Nat.cast_nonneg s)
      _ ≤ (W / g * u ^ 2) * u := mul_le_mul_of_nonneg_right hsUpper (by linarith)
      _ = W / g * u ^ 3 := by ring
      _ ≤ C / g * u ^ 3 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply div_le_div_of_nonneg_right _ hg.le
        dsimp only [C]
        linarith

end TNLean.MPS.AreaLaw
