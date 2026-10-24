/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.SpectralCutoff
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# One level of Hastings' hierarchical projection

Section II of Hastings, *Solving gapped Hamiltonians locally*, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 630–707, builds a state close to the ground state from local spectral
projections. Each ground state `Ψ_a` is an approximate eigenvector of every pair operator
`M = M_{k,k+1}`: `‖(M - ⟨Ψ_a, M Ψ_a⟩) Ψ_a‖ ≤ ε` (eq. `low`). At the first level `P^1_k` projects
onto the eigenvectors of `M` whose eigenvalues lie within `x` of `c = ⟨Ψ_a, M Ψ_a⟩`. At each
later level the normalized image `Ψ^1_a = P^1_k P^1_{k+2} Ψ_a / ‖·‖` of the previous level
replaces `Ψ_a`, and the window stays centred at `c` (line 681). The source states the
recursion `b_m = (ε + 2 b_{m-1})^{1 - 1/h}` with `h = log₂ N` levels (lines 696–704).

This file proves the estimates of one level and the recursion as an inequality between real
numbers.

* **One level.** The window projection `P = windowProjection M c x` satisfies
  `‖ψ - P ψ‖ ≤ ‖(M - c) ψ‖ / x` (lines 640–650), and hence `⟨ψ, P ψ⟩ ≥ 1 - ‖(M - c) ψ‖ / x`
  for a unit vector, which with `x = ε^{1/h}` is the bound `1 - b₁` of lines 653–657. If
  `‖(M - c) ψ‖ < x ‖ψ‖`, the spectrum of `M` meets the window (lines 658–667).
* **Normalization.** For commuting orthogonal projections that each move a unit vector by at
  most `b`, the normalized image of the vector under their product is within `2 b` of it
  (lines 686–689).
* **Perturbation.** `‖(M - c) φ‖ ≤ ‖(M - c) ψ‖ + ‖M - c‖ ‖φ - ψ‖` (lines 690–695), and
  `‖M - c‖ ≤ 2 ‖M‖` for `|c| ≤ ‖M‖`. The source writes the perturbation term as
  `2 b₁ J l_proj`, that is, with `‖M - c‖ ≤ J l_proj`; the bound here keeps `‖M - c‖`.
* **Compression.** The source's later levels project inside the range of `Q`, the product
  of the two projections of the level below (lines 673–685). Their projection is
  `P = Q * windowProjection (Q * M * Q) c x`, so `P Q = P` and `P` annihilates `ker Q`,
  even when the window contains zero. For `Q φ = φ`, it agrees with the ambient window,
  and `‖(Q M Q - c) φ‖ ≤ ‖(M - c) φ‖` gives the one-level bound in terms of `M`.
* **Nested projections.** If `P ≤ Q`, the deficiency of `ψ` under `P` is controlled by its
  deficiency under `Q` and that of the normalized image `Q ψ / ‖Q ψ‖` under `P`. This is how
  the deficiencies of consecutive levels combine, since the source projects at level `m` inside
  the range of the level `m - 1` projections (lines 671–676).
* **The recursion.** With `b₀ = 0` and `b_{m+1} = (ε + a b_m)^s`, `0 < ε ≤ 1`, `0 ≤ s ≤ 1`,
  `b_m ≤ (∑_{j<m} aʲ) ε^{sᵐ}`. For the source's `a = 2` and `s = 1 - 1/h` this is
  `b_h ≤ (2ʰ - 1) ε^{(1-1/h)^h}`, which for `N = 2ʰ` and `ε = e^{-l_proj/l_fac}` is the bound
  `N exp(-(l_proj/l_fac)(1 - 1/h)^h)` of lines 705–707. Since `(1 - 1/h)^h ≥ 1/4` for
  `h ≥ 2`, `b_h ≤ (2ʰ - 1) ε^{1/4}`. The source's further `∼ N exp(-l_proj/(e l_fac))` is the
  limit `(1 - 1/h)^h → 1/e`, approached from below, so it is an order of magnitude and not an
  upper bound; the constant `1/4` takes its place.

**Local fix (deficiency in norm):** the source bounds the deficiency of a level by an
expectation, `x ⟨Ψ_a, (1 - P^1) Ψ_a⟩ ≤ ε` with `b₁ = ε / x` (lines 645–657), and then uses
`‖Ψ^1_a - Ψ_a‖ ≤ 2 b₁` (line 689). An expectation bound `⟨Ψ, (1 - P) Ψ⟩ ≤ b` gives only
`‖(1 - P) Ψ‖ ≤ √b`, which would change the recursion. The spectral step proves the stronger
`‖(1 - P) Ψ‖ ≤ ε / x`, so here the deficiency `b` of a level is measured in norm. It implies the
printed `⟨Ψ, P Ψ⟩ ≥ 1 - b`, and with it the normalization bound `2 b` and the second level
hold as printed. From the third level on, the window stays centred at the expectation in `Ψ_a`,
so the residual must be compared with `Ψ_a`. If consecutive normalized vectors differ by at
most `2 b_j`, the triangle inequality gives distance at most `2 ∑_{j<m} b_j`. This yields
an accumulated scalar majorant `(ε + 2 ∑_{j<m} b_j)^s`, whose coefficient bound grows like
`3^{m-1}`. It does not establish the source's smaller recurrence, nor show that a sharper
argument is impossible. The identification of either majorant with the complete hierarchy
remains open. The recursion theorems below concern the printed scalar recurrence only.
Documented in
`docs/paper-gaps/hastings05_hierarchical_projection.tex`.

Not formalized here: the supersite grouping of lines 609–628, the energy bound eq. `hchy` and
the count of at most `2n` final states (lines 709–730), which the source states with "one may
show", and the extensions to higher dimensions (lines 745–756).

## Main statements

* `windowProjection`: the spectral projection of `M` onto its eigenvalues within `x` of `c`.
* `norm_sub_windowProjection_le`: `‖ψ - P ψ‖ ≤ ‖(M - c) ψ‖ / x`.
* `one_sub_div_le_re_inner_windowProjection`: `⟨ψ, P ψ⟩ ≥ 1 - ‖(M - c) ψ‖ / x`.
* `exists_mem_spectrum_abs_sub_le`: an eigenvalue of `M` lies within `x` of `c`.
* `norm_inv_norm_smul_sub_le_two_mul`: normalizing the image under two commuting projections.
* `norm_toEuclideanLin_le_add`, `norm_sub_smul_one_le_two_mul`: the residual of a nearby
  vector.
* `norm_sub_windowProjection_le_of_norm_sub_le`: one level combined.
* `norm_toEuclideanLin_compress_sub_le`: the residual under a compression.
* `compressedWindowProjection`, `compressedWindowProjection_mul`: the spectral window
  inside the preceding subspace.
* `norm_sub_compressedWindowProjection_le_of_norm_sub_le`: the combined bound there.
* `norm_sub_sq_le_of_mul_eq`: nested projections.
* `levelDeficiency`, `levelDeficiency_le`, `levelDeficiency_two_le`,
  `levelDeficiency_exp_le`, `levelDeficiency_le_rpow_quarter`: the recursion.
-/

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder InnerProductSpace

namespace TNLean.MPS.AreaLaw.LocalSolution

open TNLean.MPS.AreaLaw.Hastings

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

section Projection

/-- For an orthogonal projection `P`, `re ⟨ψ, P ψ⟩ = ‖P ψ‖²`. -/
theorem re_inner_toEuclideanLin_eq_norm_sq {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ ι) : (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re = ‖toEuclideanLin P ψ‖ ^ 2 := by
  rw [Entropy.norm_toEuclideanLin_sq, ← star_eq_conjTranspose, hP.isSelfAdjoint.star_eq,
    hP.isIdempotentElem.eq]

/-- Pythagoras for an orthogonal projection: `‖P ψ‖² + ‖ψ - P ψ‖² = ‖ψ‖²`. -/
theorem norm_sq_add_norm_sub_sq {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (ψ : EuclideanSpace ℂ ι) :
    ‖toEuclideanLin P ψ‖ ^ 2 + ‖ψ - toEuclideanLin P ψ‖ ^ 2 = ‖ψ‖ ^ 2 := by
  rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex, re_inner_toEuclideanLin_eq_norm_sq hP]
  ring

/-- For an orthogonal projection `P` and a unit vector `ψ`, the expectation of `P` is one minus
the squared distance from `ψ` to `P ψ`. -/
theorem re_inner_eq_one_sub_norm_sub_sq {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re = 1 - ‖ψ - toEuclideanLin P ψ‖ ^ 2 := by
  have h := norm_sq_add_norm_sub_sq hP ψ
  rw [hψ] at h
  rw [re_inner_toEuclideanLin_eq_norm_sq hP]
  linarith

/-- **Deficiency in norm gives the expectation bound.** If an orthogonal projection `P` moves a
unit vector by at most `δ`, then `⟨ψ, P ψ⟩ ≥ 1 - δ`. This is the passage from the norm bound to
the printed `⟨Ψ_a, P^1_k Ψ_a⟩ ≥ 1 - b₁`, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 645–657. -/
theorem one_sub_le_re_inner_of_norm_sub_le {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) {δ : ℝ}
    (h : ‖ψ - toEuclideanLin P ψ‖ ≤ δ) : 1 - δ ≤ (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re := by
  have e := re_inner_eq_one_sub_norm_sub_sq hP hψ
  have hnn : 0 ≤ (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re := by
    rw [re_inner_toEuclideanLin_eq_norm_sq hP]
    positivity
  have hd := norm_nonneg (ψ - toEuclideanLin P ψ)
  nlinarith

/-- The squared form: if `P` moves a unit vector by at most `δ`, then `⟨ψ, P ψ⟩ ≥ 1 - δ²`. -/
theorem one_sub_sq_le_re_inner_of_norm_sub_le {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) {δ : ℝ}
    (h : ‖ψ - toEuclideanLin P ψ‖ ≤ δ) : 1 - δ ^ 2 ≤ (⟪ψ, toEuclideanLin P ψ⟫_ℂ).re := by
  rw [re_inner_eq_one_sub_norm_sub_sq hP hψ]
  have := pow_le_pow_left₀ (norm_nonneg _) h 2
  linarith

/-- If `P` is an orthogonal projection, the product `P P'` moves `ψ` in squared norm by at
most the sum of the squares of what `P` and `P'` move it, since `ψ - P ψ` and
`P (ψ - P' ψ)` are orthogonal. -/
theorem norm_sub_mul_sq_le_of_isStarProjection {P : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (P' : Matrix ι ι ℂ) (ψ : EuclideanSpace ℂ ι) :
    ‖ψ - toEuclideanLin (P * P') ψ‖ ^ 2 ≤
      ‖ψ - toEuclideanLin P ψ‖ ^ 2 + ‖ψ - toEuclideanLin P' ψ‖ ^ 2 := by
  set w := ψ - toEuclideanLin P' ψ
  have hsplit : ψ - toEuclideanLin (P * P') ψ =
      (ψ - toEuclideanLin P ψ) + toEuclideanLin P w := by
    rw [toEuclideanLin_mul_apply, map_sub]
    abel
  have hH : Pᴴ = P := by
    rw [← star_eq_conjTranspose]
    exact hP.isSelfAdjoint.star_eq
  have horth : ⟪ψ - toEuclideanLin P ψ, toEuclideanLin P w⟫_ℂ = 0 := by
    rw [← LinearMap.adjoint_inner_left, ← toEuclideanLin_conjTranspose_eq_adjoint, hH, map_sub,
      ← toEuclideanLin_mul_apply, hP.isIdempotentElem.eq, sub_self, inner_zero_left]
  have hcontr : ‖toEuclideanLin P w‖ ≤ ‖w‖ :=
    (Entropy.norm_toEuclideanLin_le P w).trans
      (mul_le_of_le_one_left (norm_nonneg _) (IsStarProjection.norm_le P hP))
  rw [hsplit, ← sq_abs, abs_norm, sq, norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _
    horth]
  have := pow_le_pow_left₀ (norm_nonneg _) hcontr 2
  nlinarith

end Projection

section Normalization

/-- **Normalization at most doubles the distance.** For any vector `v` and unit vector `ψ`,
`‖v / ‖v‖ - ψ‖ ≤ 2 ‖v - ψ‖`, since `|1 - ‖v‖| ≤ ‖v - ψ‖`. For `v = 0` the left side is
`‖ψ‖ = 1`. -/
theorem norm_inv_norm_smul_sub_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {v ψ : E} (hψ : ‖ψ‖ = 1) : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ψ‖ ≤ 2 * ‖v - ψ‖ := by
  by_cases hv : v = 0
  · subst hv
    simp [hψ]
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h1 : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ = |1 - ‖v‖| := by
    have e : ((‖v‖⁻¹ : ℝ) : ℂ) • v - v = (((‖v‖⁻¹ - 1 : ℝ)) : ℂ) • v := by
      rw [Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
    rw [e, norm_smul, Complex.norm_real, Real.norm_eq_abs, ← abs_norm v, ← abs_mul, abs_norm,
      sub_mul, inv_mul_cancel₀ hn, one_mul]
  have h2 : |1 - ‖v‖| ≤ ‖v - ψ‖ := by
    rw [← hψ, norm_sub_rev v]
    exact abs_norm_sub_norm_le ψ v
  calc ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - ψ‖ = ‖(((‖v‖⁻¹ : ℝ) : ℂ) • v - v) + (v - ψ)‖ := by
        congr 1
        abel
    _ ≤ ‖((‖v‖⁻¹ : ℝ) : ℂ) • v - v‖ + ‖v - ψ‖ := norm_add_le _ _
    _ ≤ 2 * ‖v - ψ‖ := by rw [h1]; linarith

/-- **Normalizing the image under an orthogonal projection.** For an orthogonal projection `Q`
and a unit vector `ψ`, `‖Q ψ / ‖Q ψ‖ - ψ‖² ≤ 2 ‖ψ - Q ψ‖²`. If `Q ψ ≠ 0`,
the left side is `2 - 2 ‖Q ψ‖` and the right side `2 - 2 ‖Q ψ‖²`. If `Q ψ = 0`,
the normalized image is interpreted as zero, and the inequality is `1 ≤ 2`. -/
theorem norm_inv_norm_smul_toEuclideanLin_sub_sq_le {Q : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    ‖((‖toEuclideanLin Q ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin Q ψ - ψ‖ ^ 2 ≤
      2 * ‖ψ - toEuclideanLin Q ψ‖ ^ 2 := by
  have hsplit := norm_sq_add_norm_sub_sq hQ ψ
  have hre := re_inner_toEuclideanLin_eq_norm_sq hQ ψ
  set v := toEuclideanLin Q ψ
  rw [hψ] at hsplit
  have ht0 : 0 ≤ ‖v‖ := norm_nonneg _
  have ht1 : ‖v‖ ≤ 1 := by nlinarith [sq_nonneg ‖ψ - v‖]
  rcases ht0.eq_or_lt with h0 | hpos
  · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
    rw [hv0]
    simp [hψ]
  · have hv : v ≠ 0 := norm_pos_iff.mp hpos
    have hu : ‖((‖v‖⁻¹ : ℝ) : ℂ) • v‖ = 1 := by
      rw [Complex.ofReal_inv]
      exact norm_smul_inv_norm hv
    have hinner : (⟪((‖v‖⁻¹ : ℝ) : ℂ) • v, ψ⟫_ℂ).re = ‖v‖ := by
      rw [inner_smul_left, Complex.conj_ofReal, Complex.re_ofReal_mul, ← inner_conj_symm,
        Complex.conj_re, hre]
      field_simp
    rw [norm_sub_sq (𝕜 := ℂ), RCLike.re_to_complex, hu, hinner, hψ]
    nlinarith

/-- **The normalized image under two projections**, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 686–689. If `P`, `P'` are commuting orthogonal projections that each move the unit
vector `ψ` by at most `b`, then `Ψ¹ = P P' ψ / ‖P P' ψ‖` satisfies `‖Ψ¹ - ψ‖ ≤ 2 b`. With the
deficiency `b₁` measured in norm (module docstring), this is the source's `|Ψ¹_a - Ψ_a| ≤ 2 b₁`
for `P = P^1_k`, `P' = P^1_{k+2}`. -/
theorem norm_inv_norm_smul_sub_le_two_mul {P P' : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (hP' : IsStarProjection P') (hc : Commute P P') {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1)
    {b : ℝ} (h : ‖ψ - toEuclideanLin P ψ‖ ≤ b) (h' : ‖ψ - toEuclideanLin P' ψ‖ ≤ b) :
    ‖((‖toEuclideanLin (P * P') ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin (P * P') ψ - ψ‖ ≤ 2 * b := by
  have hb : 0 ≤ b := (norm_nonneg _).trans h
  have h1 := norm_inv_norm_smul_toEuclideanLin_sub_sq_le (hP.mul hP' hc) hψ
  have h2 := norm_sub_mul_sq_le_of_isStarProjection hP P' ψ
  have h3 := pow_le_pow_left₀ (norm_nonneg _) h 2
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h' 2
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp ?_
  nlinarith

/-- **Nested projections.** Let `P ≤ Q` be orthogonal projections, `P Q = P`, let `ψ` be a unit
vector and `ψ' = Q ψ / ‖Q ψ‖`. Then
`‖ψ - P ψ‖² ≤ ‖ψ - Q ψ‖² + ‖ψ' - P ψ'‖²`. In the source the projection of level `m` lies under
the product of the two projections of level `m - 1` below it (arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 671–676), so the deficiency of a state under the level-`m` projection is
bounded by those of the earlier levels and that of the normalized intermediate state. -/
theorem norm_sub_sq_le_of_mul_eq {P Q : Matrix ι ι ℂ} (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (hPQ : P * Q = P) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    ‖ψ - toEuclideanLin P ψ‖ ^ 2 ≤ ‖ψ - toEuclideanLin Q ψ‖ ^ 2 +
      ‖((‖toEuclideanLin Q ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin Q ψ -
        toEuclideanLin P (((‖toEuclideanLin Q ψ‖⁻¹ : ℝ) : ℂ) • toEuclideanLin Q ψ)‖ ^ 2 := by
  have hPψ : toEuclideanLin P ψ = toEuclideanLin P (toEuclideanLin Q ψ) := by
    rw [← toEuclideanLin_mul_apply, hPQ]
  have hsP := norm_sq_add_norm_sub_sq hP ψ
  have hsQ := norm_sq_add_norm_sub_sq hQ ψ
  rw [hψ] at hsP hsQ
  set v := toEuclideanLin Q ψ
  rcases (norm_nonneg v).eq_or_lt with h0 | hpos
  · have hv0 : v = 0 := norm_eq_zero.mp h0.symm
    have hP0 : toEuclideanLin P ψ = 0 := by rw [hPψ, hv0, map_zero]
    rw [hP0, hv0]
    simp only [sub_zero, hψ]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have hv : v ≠ 0 := norm_pos_iff.mp hpos
    set u := ((‖v‖⁻¹ : ℝ) : ℂ) • v
    have hu : ‖u‖ = 1 := by
      rw [show u = ((‖v‖ : ℂ))⁻¹ • v by rw [← Complex.ofReal_inv]]
      exact norm_smul_inv_norm hv
    have hvu : v = ((‖v‖ : ℝ) : ℂ) • u := by
      rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one,
        one_smul]
    have hsu := norm_sq_add_norm_sub_sq hP u
    rw [hu] at hsu
    have hPvu : toEuclideanLin P v = ((‖v‖ : ℝ) : ℂ) • toEuclideanLin P u := by
      rw [← map_smul, ← hvu]
    have hPv : ‖toEuclideanLin P ψ‖ = ‖v‖ * ‖toEuclideanLin P u‖ := by
      rw [hPψ, hPvu, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_norm]
    rw [hPv] at hsP
    have hs1 : ‖toEuclideanLin P u‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖u - toEuclideanLin P u‖]
    have ht1 : ‖v‖ ^ 2 ≤ 1 := by nlinarith [sq_nonneg ‖ψ - v‖]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (sub_nonneg.mpr ht1)]

end Normalization

section Window

/-- The real multiple `c • 1` of the identity matrix, written with a complex scalar, is the
image of `c` under the algebra map. -/
theorem ofReal_smul_one_eq_algebraMap (c : ℝ) :
    ((c : ℂ) • 1 : Matrix ι ι ℂ) = algebraMap ℝ (Matrix ι ι ℂ) c := by
  rw [Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul]

omit [Fintype ι] in
/-- `M - c` is Hermitian for a Hermitian `M` and a real `c`. -/
theorem isHermitian_sub_ofReal_smul_one {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (c : ℝ) :
    (M - (c : ℂ) • 1).IsHermitian := by
  rw [IsHermitian, conjTranspose_sub, conjTranspose_smul, conjTranspose_one, hM.eq,
    Complex.star_def, Complex.conj_ofReal]

/-- The window projection `P^1` of arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 640–642:
the spectral projection of `M` onto its eigenvalues `λ` with `|λ - c| ≤ x`. In the source
`c = ⟨Ψ_a, M Ψ_a⟩`. -/
noncomputable def windowProjection (M : Matrix ι ι ℂ) (c x : ℝ) : Matrix ι ι ℂ :=
  spectralCutoff (M - (c : ℂ) • 1) x

/-- The window projection of a Hermitian matrix is an orthogonal projection. -/
theorem isStarProjection_windowProjection {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (c x : ℝ) :
    IsStarProjection (windowProjection M c x) :=
  isStarProjection_spectralCutoff (isHermitian_sub_ofReal_smul_one hM c) x

/-- The later-level window projection inside the range of `Q`, rather than on the whole
ambient space. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
noncomputable def compressedWindowProjection (Q M : Matrix ι ι ℂ) (c x : ℝ) :
    Matrix ι ι ℂ :=
  Q * windowProjection (Q * M * Q) c x

/-- The spectral window of a compressed operator commutes with the projection onto the
compressing subspace. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
theorem commute_windowProjection_compress {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    (M : Matrix ι ι ℂ) (c x : ℝ) : Commute (windowProjection (Q * M * Q) c x) Q := by
  have hcomm : Commute (Q * M * Q) Q := by
    change (Q * M * Q) * Q = Q * (Q * M * Q)
    simp only [mul_assoc]
    rw [hQ.isIdempotentElem.eq, ← mul_assoc Q Q (M * Q), hQ.isIdempotentElem.eq]
  unfold windowProjection spectralCutoff
  apply Commute.cfc_real
  rw [ofReal_smul_one_eq_algebraMap]
  exact hcomm.sub_left (Algebra.commute_algebraMap_left c Q)

/-- The window projection restricted to the compressing subspace is an orthogonal
projection. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
theorem isStarProjection_compressedWindowProjection {Q M : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (hM : M.IsHermitian) (c x : ℝ) :
    IsStarProjection (compressedWindowProjection Q M c x) := by
  have hQM : (Q * M * Q).IsHermitian := by
    simpa only [hQ.isSelfAdjoint.isHermitian.eq] using
      isHermitian_mul_mul_conjTranspose Q hM
  exact hQ.mul (isStarProjection_windowProjection hQM c x)
    (commute_windowProjection_compress hQ M c x).symm

/-- The later-level projection lies inside the preceding subspace, as required in
Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
theorem compressedWindowProjection_mul {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    (M : Matrix ι ι ℂ) (c x : ℝ) :
    compressedWindowProjection Q M c x * Q = compressedWindowProjection Q M c x := by
  rw [compressedWindowProjection, mul_assoc,
    (commute_windowProjection_compress hQ M c x).eq, ← mul_assoc, hQ.isIdempotentElem.eq]

/-- On the preceding subspace the restricted projection agrees with the ambient spectral
window. Hastings, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
theorem toEuclideanLin_compressedWindowProjection_of_mem {Q : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (M : Matrix ι ι ℂ) (c x : ℝ)
    {φ : EuclideanSpace ℂ ι} (hφ : toEuclideanLin Q φ = φ) :
    toEuclideanLin (compressedWindowProjection Q M c x) φ =
      toEuclideanLin (windowProjection (Q * M * Q) c x) φ := by
  rw [compressedWindowProjection, ← (commute_windowProjection_compress hQ M c x).eq,
    toEuclideanLin_mul_apply, hφ]

/-- The later-level projection annihilates the orthogonal complement of the preceding
subspace, including when the spectral window contains zero. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–685. -/
theorem toEuclideanLin_compressedWindowProjection_eq_zero {Q : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (M : Matrix ι ι ℂ) (c x : ℝ)
    {φ : EuclideanSpace ℂ ι} (hφ : toEuclideanLin Q φ = 0) :
    toEuclideanLin (compressedWindowProjection Q M c x) φ = 0 := by
  rw [← compressedWindowProjection_mul hQ M c x, toEuclideanLin_mul_apply, hφ, map_zero]

/-- **One level.** For a Hermitian `M`, a real `c` and `x > 0`, the window projection moves a
vector `ψ` by at most `‖(M - c) ψ‖ / x`. This is the spectral step of
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 645–650, measured in norm. -/
theorem norm_sub_windowProjection_le {M : Matrix ι ι ℂ} (hM : M.IsHermitian) (c : ℝ) {x : ℝ}
    (hx : 0 < x) (ψ : EuclideanSpace ℂ ι) :
    ‖ψ - toEuclideanLin (windowProjection M c x) ψ‖ ≤
      ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ / x :=
  norm_sub_spectralCutoff_le (isHermitian_sub_ofReal_smul_one hM c) hx ψ

/-- **The expectation bound of the first level**, arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 645–657: for a unit vector `ψ`, `⟨ψ, P ψ⟩ ≥ 1 - ‖(M - c) ψ‖ / x`. With
`‖(M - c) ψ‖ ≤ ε` and `x = ε^{1/h}` the right side is `1 - b₁`, `b₁ = ε^{1 - 1/h}`. -/
theorem one_sub_div_le_re_inner_windowProjection {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (c : ℝ) {x : ℝ} (hx : 0 < x) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    1 - ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ / x ≤
      (⟪ψ, toEuclideanLin (windowProjection M c x) ψ⟫_ℂ).re :=
  one_sub_le_re_inner_of_norm_sub_le (isStarProjection_windowProjection hM c x) hψ
    (norm_sub_windowProjection_le hM c hx ψ)

/-- The squared form of `one_sub_div_le_re_inner_windowProjection`:
`⟨ψ, P ψ⟩ ≥ 1 - (‖(M - c) ψ‖ / x)²`. -/
theorem one_sub_div_sq_le_re_inner_windowProjection {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (c : ℝ) {x : ℝ} (hx : 0 < x) {ψ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) :
    1 - (‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ / x) ^ 2 ≤
      (⟪ψ, toEuclideanLin (windowProjection M c x) ψ⟫_ℂ).re :=
  one_sub_sq_le_re_inner_of_norm_sub_le (isStarProjection_windowProjection hM c x) hψ
    (norm_sub_windowProjection_le hM c hx ψ)

/-- If no point of the spectrum of `M` lies within `x` of `c`, the window projection is zero. -/
theorem windowProjection_eq_zero {M : Matrix ι ι ℂ} {c x : ℝ}
    (h : ∀ μ ∈ spectrum ℝ M, x < |μ - c|) : windowProjection M c x = 0 := by
  rw [windowProjection, spectralCutoff, ofReal_smul_one_eq_algebraMap,
    ← cfc_zero ℝ (M - algebraMap ℝ (Matrix ι ι ℂ) c)]
  refine cfc_congr fun t ht ↦ ?_
  rw [← spectrum.sub_singleton_eq] at ht
  obtain ⟨μ, hμ, c', hc', rfl⟩ := ht
  rw [Set.mem_singleton_iff] at hc'
  subst hc'
  simp [not_le.mpr (h μ hμ)]

/-- **An eigenvalue in the window**, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 658–667.
For a Hermitian `M`, `x > 0` and a nonzero vector `ψ` with `‖(M - c) ψ‖ < x ‖ψ‖`, the spectrum
of `M` has a point within `x` of `c`; otherwise the window projection would vanish and move `ψ`
by `‖ψ‖`. -/
theorem exists_mem_spectrum_abs_sub_le {M : Matrix ι ι ℂ} (hM : M.IsHermitian) {c x : ℝ}
    (hx : 0 < x) {ψ : EuclideanSpace ℂ ι}
    (h : ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ < x * ‖ψ‖) :
    ∃ μ ∈ spectrum ℝ M, |μ - c| ≤ x := by
  by_contra hne
  simp only [not_exists, not_and, not_le] at hne
  have hle := norm_sub_windowProjection_le hM c hx ψ
  rw [windowProjection_eq_zero hne, map_zero, LinearMap.zero_apply, sub_zero,
    le_div_iff₀ hx] at hle
  linarith

end Window

section Perturbation

/-- **The residual of a nearby vector.** For any matrix `N`, `‖N φ‖ ≤ ‖N ψ‖ + ‖N‖ ‖φ - ψ‖`.
With `N = M - c` this is the step of arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 690–695, where the source bounds the second term by `2 b₁ J l_proj`. -/
theorem norm_toEuclideanLin_le_add (N : Matrix ι ι ℂ) (φ ψ : EuclideanSpace ℂ ι) :
    ‖toEuclideanLin N φ‖ ≤ ‖toEuclideanLin N ψ‖ + ‖N‖ * ‖φ - ψ‖ := by
  have e : toEuclideanLin N φ = toEuclideanLin N ψ + toEuclideanLin N (φ - ψ) := by
    rw [map_sub]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add_right (Entropy.norm_toEuclideanLin_le N _) _)

/-- `‖M - c‖ ≤ ‖M‖ + |c|`. -/
theorem norm_sub_ofReal_smul_one_le (M : Matrix ι ι ℂ) (c : ℝ) :
    ‖M - (c : ℂ) • 1‖ ≤ ‖M‖ + |c| := by
  refine (norm_sub_le _ _).trans (add_le_add_right ?_ _)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg c) (IsStarProjection.norm_le _ (IsStarProjection.one _))

/-- `‖M - c‖ ≤ 2 ‖M‖` when `|c| ≤ ‖M‖`, as for `c = ⟨ψ, M ψ⟩` with a unit vector `ψ`
(`abs_re_inner_toEuclideanLin_le`). The source's perturbation term `2 b₁ J l_proj`
(arXiv:cond-mat/0508554v3, `proj3new.tex`, line 694) is `‖M - c‖ ‖Ψ¹_a - Ψ_a‖` with
`‖M - c‖ ≤ J l_proj`; in general this bound carries the factor `2 ‖M‖`. -/
theorem norm_sub_smul_one_le_two_mul {M : Matrix ι ι ℂ} {c : ℝ} (hc : |c| ≤ ‖M‖) :
    ‖M - (c : ℂ) • 1‖ ≤ 2 * ‖M‖ := by
  linarith [norm_sub_ofReal_smul_one_le M c]

/-- For a unit vector `ψ`, `|re ⟨ψ, M ψ⟩| ≤ ‖M‖`. -/
theorem abs_re_inner_toEuclideanLin_le (M : Matrix ι ι ℂ) {ψ : EuclideanSpace ℂ ι}
    (hψ : ‖ψ‖ = 1) : |(⟪ψ, toEuclideanLin M ψ⟫_ℂ).re| ≤ ‖M‖ := by
  refine (Complex.abs_re_le_norm _).trans ((norm_inner_le_norm (𝕜 := ℂ) _ _).trans ?_)
  rw [hψ, one_mul]
  simpa [hψ] using Entropy.norm_toEuclideanLin_le M ψ

/-- **One level combined.** If `‖(M - c) ψ‖ ≤ ε`, `‖φ - ψ‖ ≤ η` and `x > 0`, the window
projection of `M` at `c` and `x` moves `φ` by at most `(ε + ‖M - c‖ η) / x`. With `ψ = Ψ_a`,
`φ = Ψ¹_a`, `η = 2 b₁` and `x` the window of the second level, this is the estimate behind the
deficiency `b₂` of arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 690–699, with the window
kept centred at `c = ⟨Ψ_a, M Ψ_a⟩` as at line 681. For the source's second-level
projection inside the range of `Q = P^1_k P^1_{k+2}` (lines 673–685), use
`norm_sub_compressedWindowProjection_le_of_norm_sub_le`. -/
theorem norm_sub_windowProjection_le_of_norm_sub_le {M : Matrix ι ι ℂ} (hM : M.IsHermitian)
    (c : ℝ) {x : ℝ} (hx : 0 < x) {φ ψ : EuclideanSpace ℂ ι} {ε η : ℝ}
    (hres : ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ ≤ ε) (hdist : ‖φ - ψ‖ ≤ η) :
    ‖φ - toEuclideanLin (windowProjection M c x) φ‖ ≤ (ε + ‖M - (c : ℂ) • 1‖ * η) / x :=
  (norm_sub_windowProjection_le hM c hx φ).trans <| div_le_div_of_nonneg_right
    ((norm_toEuclideanLin_le_add _ φ ψ).trans
      (add_le_add hres (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))) hx.le

/-- **The residual under a compression.** If `Q` is an orthogonal projection and `Q φ = φ`, then
`‖(Q M Q - c) φ‖ ≤ ‖(M - c) φ‖`. At the second level of arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 673–685, the source projects with the compressed operator
`P^1_k P^1_{k+2} M P^1_{k+2} P^1_k`, and `Ψ¹_a` lies in the range of `P^1_k P^1_{k+2}`. -/
theorem norm_toEuclideanLin_compress_sub_le {Q : Matrix ι ι ℂ} (hQ : IsStarProjection Q)
    (M : Matrix ι ι ℂ) (c : ℝ) {φ : EuclideanSpace ℂ ι} (hφ : toEuclideanLin Q φ = φ) :
    ‖toEuclideanLin (Q * M * Q - (c : ℂ) • 1) φ‖ ≤ ‖toEuclideanLin (M - (c : ℂ) • 1) φ‖ := by
  have h : toEuclideanLin (Q * M * Q - (c : ℂ) • 1) φ =
      toEuclideanLin Q (toEuclideanLin (M - (c : ℂ) • 1) φ) := by
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      toEuclideanLin_mul_apply, toEuclideanLin_one_apply, hφ]
  rw [h]
  exact (Entropy.norm_toEuclideanLin_le Q _).trans
    (mul_le_of_le_one_left (norm_nonneg _) (IsStarProjection.norm_le Q hQ))

/-- The spectral window inside the preceding subspace moves a vector in that subspace by
at most its uncompressed residual divided by the window radius. Hastings,
arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 673–695. -/
theorem norm_sub_compressedWindowProjection_le {Q M : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx : 0 < x)
    {φ : EuclideanSpace ℂ ι} (hφ : toEuclideanLin Q φ = φ) :
    ‖φ - toEuclideanLin (compressedWindowProjection Q M c x) φ‖ ≤
      ‖toEuclideanLin (M - (c : ℂ) • 1) φ‖ / x := by
  rw [toEuclideanLin_compressedWindowProjection_of_mem hQ M c x hφ]
  have hQM : (Q * M * Q).IsHermitian := by
    simpa only [hQ.isSelfAdjoint.isHermitian.eq] using
      isHermitian_mul_mul_conjTranspose Q hM
  exact (norm_sub_windowProjection_le hQM c hx φ).trans
    (div_le_div_of_nonneg_right (norm_toEuclideanLin_compress_sub_le hQ M c hφ) hx.le)

/-- The combined residual estimate for the source's later-level projection, with the
window centred at the original expectation. Hastings, arXiv:cond-mat/0508554v3,
`proj3new.tex`, lines 673–699. Only the intermediate vector must lie in the preceding
subspace; the reference vector need not lie there. -/
theorem norm_sub_compressedWindowProjection_le_of_norm_sub_le {Q M : Matrix ι ι ℂ}
    (hQ : IsStarProjection Q) (hM : M.IsHermitian) (c : ℝ) {x : ℝ} (hx : 0 < x)
    {φ ψ : EuclideanSpace ℂ ι} {ε η : ℝ} (hφ : toEuclideanLin Q φ = φ)
    (hres : ‖toEuclideanLin (M - (c : ℂ) • 1) ψ‖ ≤ ε) (hdist : ‖φ - ψ‖ ≤ η) :
    ‖φ - toEuclideanLin (compressedWindowProjection Q M c x) φ‖ ≤
      (ε + ‖M - (c : ℂ) • 1‖ * η) / x :=
  (norm_sub_compressedWindowProjection_le hQ hM c hx hφ).trans <|
    div_le_div_of_nonneg_right ((norm_toEuclideanLin_le_add _ φ ψ).trans
      (add_le_add hres (mul_le_mul_of_nonneg_left hdist (norm_nonneg _)))) hx.le

end Perturbation

section Recursion

/-- The scalar recurrence stated for the deficiencies in arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 696–704: `b₀ = 0` and `b_{m+1} = (ε + a b_m)^s`. The source takes `a = 2` and
`s = 1 - 1/h`, so that `b₁ = ε^{1 - 1/h}`. Identifying this sequence with the
deficiencies of the complete hierarchy remains open; see the module docstring. -/
noncomputable def levelDeficiency (ε a s : ℝ) : ℕ → ℝ
  | 0 => 0
  | m + 1 => (ε + a * levelDeficiency ε a s m) ^ s

theorem levelDeficiency_zero (ε a s : ℝ) : levelDeficiency ε a s 0 = 0 := rfl

theorem levelDeficiency_succ (ε a s : ℝ) (m : ℕ) :
    levelDeficiency ε a s (m + 1) = (ε + a * levelDeficiency ε a s m) ^ s := rfl

theorem levelDeficiency_nonneg {ε a : ℝ} (hε : 0 ≤ ε) (ha : 0 ≤ a) (s : ℝ) :
    ∀ m, 0 ≤ levelDeficiency ε a s m
  | 0 => le_rfl
  | m + 1 => by
    have := levelDeficiency_nonneg hε ha s m
    exact Real.rpow_nonneg (by positivity) _

/-- **The recursion.** For `0 < ε ≤ 1`, `a ≥ 0` and `0 ≤ s ≤ 1`,
`b_m ≤ (∑_{j<m} aʲ) ε^{sᵐ}`. Each step uses `ε ≤ ε^{sᵐ}` and `C^s ≤ C` for `C ≥ 1`. -/
theorem levelDeficiency_le {ε a s : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (m : ℕ) :
    levelDeficiency ε a s m ≤ (∑ j ∈ Finset.range m, a ^ j) * ε ^ (s ^ m) := by
  induction m with
  | zero => simp [levelDeficiency]
  | succ m ih =>
    have hsum : ∑ j ∈ Finset.range (m + 1), a ^ j = 1 + a * ∑ j ∈ Finset.range m, a ^ j := by
      rw [Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_succ', pow_zero]
      ring
    have hC : 0 ≤ ∑ j ∈ Finset.range m, a ^ j :=
      Finset.sum_nonneg fun j _ ↦ pow_nonneg ha j
    have hE : ε ≤ ε ^ (s ^ m) := Real.self_le_rpow_of_le_one hε0.le hε1 (pow_le_one₀ hs0 hs1)
    have hE0 : 0 ≤ ε ^ (s ^ m) := Real.rpow_nonneg hε0.le _
    have hb := levelDeficiency_nonneg hε0.le ha s m
    have hstep : ε + a * levelDeficiency ε a s m ≤
        (1 + a * ∑ j ∈ Finset.range m, a ^ j) * ε ^ (s ^ m) := by
      nlinarith [mul_le_mul_of_nonneg_left ih ha]
    have hC1 : 1 ≤ 1 + a * ∑ j ∈ Finset.range m, a ^ j := by nlinarith
    rw [levelDeficiency_succ, hsum]
    calc (ε + a * levelDeficiency ε a s m) ^ s
        ≤ ((1 + a * ∑ j ∈ Finset.range m, a ^ j) * ε ^ (s ^ m)) ^ s :=
          Real.rpow_le_rpow (by positivity) hstep hs0
      _ = (1 + a * ∑ j ∈ Finset.range m, a ^ j) ^ s * ε ^ (s ^ (m + 1)) := by
          rw [Real.mul_rpow (by positivity) hE0, ← Real.rpow_mul hε0.le, pow_succ]
      _ ≤ (1 + a * ∑ j ∈ Finset.range m, a ^ j) * ε ^ (s ^ (m + 1)) := by
          gcongr
          exact Real.rpow_le_self_of_one_le hC1 hs1

/-- **The source's recursion**, `a = 2`: `b_m ≤ (2ᵐ - 1) ε^{sᵐ}`. -/
theorem levelDeficiency_two_le {ε s : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) (m : ℕ) : levelDeficiency ε 2 s m ≤ (2 ^ m - 1) * ε ^ (s ^ m) := by
  have h := levelDeficiency_le hε0 hε1 zero_le_two hs0 hs1 m
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)] at h
  norm_num at h
  exact h

/-- The exponent `1 - 1/h` of the source lies in `[0, 1]` for every natural `h`. -/
theorem one_sub_inv_natCast_mem_Icc (h : ℕ) : 1 - 1 / (h : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  rw [one_div]
  exact ⟨sub_nonneg.mpr (Nat.cast_inv_le_one h), sub_le_self _ (inv_nonneg.mpr h.cast_nonneg)⟩

/-- `(1 - 1/h)^h ≥ 1/4` for `h ≥ 2`. The value `1/4` is attained at `h = 2`; for `h ≥ 4`,
`(1 - 1/h)^{h-1} ≥ e^{-1} ≥ 1/3` and `1 - 1/h ≥ 3/4`. -/
theorem quarter_le_one_sub_inv_pow {h : ℕ} (hh : 2 ≤ h) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (h : ℝ)) ^ h := by
  rcases (show h = 2 ∨ h = 3 ∨ 4 ≤ h by omega) with rfl | rfl | h4
  · norm_num
  · norm_num
  obtain ⟨n, rfl⟩ : ∃ n, h = n + 1 := ⟨h - 1, by omega⟩
  have hn : (3 : ℝ) ≤ n := by exact_mod_cast (by omega : 3 ≤ n)
  have hn0 : (0 : ℝ) < n := by linarith
  push_cast
  have hbase : Real.exp (-(1 / (n : ℝ))) ≤ 1 - 1 / ((n : ℝ) + 1) := by
    have e : 1 - 1 / ((n : ℝ) + 1) = (1 / (n : ℝ) + 1)⁻¹ := by
      field_simp
      ring
    rw [e, Real.exp_neg]
    exact inv_anti₀ (by positivity) (Real.add_one_le_exp _)
  have hpow : Real.exp (-1) ≤ (1 - 1 / ((n : ℝ) + 1)) ^ n := by
    have e : Real.exp (-1) = Real.exp (-(1 / (n : ℝ))) ^ n := by
      rw [← Real.exp_nat_mul]
      congr 1
      field_simp
    rw [e]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hbase n
  have hexp : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
  have hlast : (3 / 4 : ℝ) ≤ 1 - 1 / ((n : ℝ) + 1) := by
    have : 1 / ((n : ℝ) + 1) ≤ 1 / 4 :=
      one_div_le_one_div_of_le (by norm_num) (by linarith)
    linarith
  rw [pow_succ]
  nlinarith [hexp.trans hpow]

/-- **The bound after `h` levels**, arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 705–707:
with `s = 1 - 1/h`, `b_h ≤ (2ʰ - 1) ε^{(1 - 1/h)^h}`. For `N = 2ʰ` sites this is below
`N ε^{(1 - 1/h)^h}`. -/
theorem levelDeficiency_self_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (h : ℕ) :
    levelDeficiency ε 2 (1 - 1 / (h : ℝ)) h ≤
      (2 ^ h - 1) * ε ^ ((1 - 1 / (h : ℝ)) ^ h) :=
  levelDeficiency_two_le hε0 hε1 (one_sub_inv_natCast_mem_Icc h).1
    (one_sub_inv_natCast_mem_Icc h).2 h

/-- The source's form of the bound after `h` levels: for `ε = e^{-t}` with `t ≥ 0` (in the
source `t = l_proj / l_fac`), `b_h ≤ 2ʰ exp(-t (1 - 1/h)^h)`, which is
`N exp(-(l_proj/l_fac)(1 - 1/h)^h)` for `N = 2ʰ`. arXiv:cond-mat/0508554v3, `proj3new.tex`,
lines 705–707. -/
theorem levelDeficiency_exp_le {t : ℝ} (ht : 0 ≤ t) (h : ℕ) :
    levelDeficiency (Real.exp (-t)) 2 (1 - 1 / (h : ℝ)) h ≤
      2 ^ h * Real.exp (-(t * (1 - 1 / (h : ℝ)) ^ h)) := by
  have hb := levelDeficiency_self_le (Real.exp_pos (-t))
    (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)) h
  rw [← Real.exp_mul, neg_mul] at hb
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le)

/-- With `(1 - 1/h)^h ≥ 1/4`, the bound after `h ≥ 2` levels is `b_h ≤ (2ʰ - 1) ε^{1/4}`. -/
theorem levelDeficiency_le_rpow_quarter {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) {h : ℕ}
    (hh : 2 ≤ h) :
    levelDeficiency ε 2 (1 - 1 / (h : ℝ)) h ≤ (2 ^ h - 1) * ε ^ (1 / 4 : ℝ) := by
  refine (levelDeficiency_self_le hε0 hε1 h).trans ?_
  have h2 : (1 : ℝ) ≤ 2 ^ h := one_le_pow₀ one_le_two
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_ge hε0 hε1 (quarter_le_one_sub_inv_pow hh)) (by linarith)

end Recursion

end TNLean.MPS.AreaLaw.LocalSolution
