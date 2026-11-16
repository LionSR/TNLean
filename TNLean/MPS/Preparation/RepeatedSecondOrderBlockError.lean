/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.RelativeSecondOrderOverlap

/-!
# Second-order approximation for repeated overlapping blocks

For at least two blocks of sites, the corrected approximation to a direct sum of normal
left-canonical tensors has error at most `C y exp(C y)`, where
`y = M exp(-2γ q/ξ)`. The constant is independent of all nonzero complex copy weights,
even when their power sums nearly cancel. Both overlap and target-norm errors are
estimated relative to `∑ⱼ |βⱼ|²`; this positive quantity is never bounded below uniformly.

The relative-row overlaps have the quadratic rate by
`exists_norm_relative_row_overlap_sub_ite_le_exp_sq`. The target-norm error decays as
`exp(-γ Mq/ξ)`, which is bounded by `exp(-2γ q/ξ)` for `M ≥ 2`. Short block lengths
and the range `C y ≥ 1` use the trivial error bound.

This is a project refinement of arXiv:2307.01696, Supplemental Material, Lemma 1′(ii),
eq. `eq:fid_err_gen_non_normal`. The corrected multiplicity state replaces eq. (S7),
and the rate includes the mixed transfer spectra. See
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex` and
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`. The one-block case `M = 1`
requires a separate projection argument and is not asserted here.
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators Matrix.Norms.L2Operator

namespace MPSTensor

variable {d D b : ℕ} {m Dj : Fin b → ℕ}
  {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

/-- **Second-order normalized-state error for at least two blocks.** Under the hypotheses
of `exists_approximationError_le_repeatedOverlappingBlockSum`, the corrected approximating
state satisfies `ε ≤ C y exp(C y)`, `y = M exp(-2γ q/ξ)`, for every `M ≥ 2` and every
block length `q`. The constant precedes all nonzero complex copy weights; the only
condition on their power sums is `β ≠ 0`, needed to define a normalized seed.

Project refinement of arXiv:2307.01696, Supplemental Material, Lemma 1′(ii),
eq. `eq:fid_err_gen_non_normal`, for the corrected state and mixed-transfer rate.
The statement is explicitly restricted to `M ≥ 2`; no one-block estimate is assumed. -/
theorem exists_approximationError_le_repeatedOverlappingBlockSum_sq_of_two_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, ∀ (q M : ℕ) [NeZero M],
      2 ≤ M → bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) *
            Real.exp (C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂))) := by
  set x := Real.exp (-γ / correlationLength lam₂) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : ∀ q : ℕ, Real.exp (-(2 * γ) * q / correlationLength lam₂) =
      (x ^ 2) ^ q := fun q => by
    rw [Real.exp_neg_mul_div_eq_pow, exp_neg_two_mul_div_correlationLength]
  simp_rw [hxq]
  -- The trivial bound `ε ≤ 1` suffices whenever `C M x^{2q} ≥ 1`.
  have htriv : ∀ (C : ℝ), 1 ≤ C → ∀ (μ : CopyWeights b m) (q M : ℕ) [NeZero M],
      1 ≤ C * ((M : ℝ) * (x ^ 2) ^ q) →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * (x ^ 2) ^ q) * Real.exp (C * (M * (x ^ 2) ^ q)) := fun C hC μ q M _ hu => by
    have h2 : 1 ≤ Real.exp (C * (M * (x ^ 2) ^ q)) := Real.one_le_exp (by linarith)
    have h3 : 0 ≤ ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
        (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ := norm_nonneg _
    nlinarith
  rcases le_or_gt 1 x with hx1 | hx1
  · -- For `e^{-γ/ξ} ≥ 1` the rate is at least `1` and the bound is trivial.
    refine ⟨1, one_pos, fun μ q M _ _ _ => htriv 1 le_rfl μ q M ?_⟩
    have := one_le_pow₀ (one_le_pow₀ hx1 (n := 2)) (n := q)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith
  have hl : ‖lam₂‖ < 1 := by
    rw [hx_def, neg_div_correlationLength, Real.exp_lt_one_iff] at hx1
    have hlog : Real.log ‖lam₂‖ < 0 := by
      by_contra h
      nlinarith [not_lt.1 h]
    rcases (norm_nonneg lam₂).lt_or_eq with hpos | h0
    · exact (Real.log_neg_iff hpos).1 hlog
    · rw [← h0, Real.log_zero] at hlog; exact absurd hlog (lt_irrefl 0)
  have hz := fun j j' => exists_norm_relative_row_overlap_sub_ite_le_exp_sq hι hdisj
    hN hA hσ htr hfix hl hlam hmix hγ0 hγ hx1 j j'
  choose C₀ hC₀ q₀ hgen using hz
  set Q := ∑ p : Fin b × Fin b, q₀ p.1 p.2
  have hQ : ∀ p : Fin b × Fin b, q₀ p.1 p.2 ≤ Q := fun p =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ p)
  obtain ⟨Kt, hKt, hnorm⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix hl hlam hmix
    hγ0 hγ
  set Cz : Fin b × Fin b → ℝ := fun p => C₀ p.1 p.2
  have hCz : ∀ p, 0 < Cz p := fun p => hC₀ p.1 p.2
  set S := ∑ p, Cz p
  have hS : 0 ≤ S := Finset.sum_nonneg fun p _ => (hCz p).le
  have hx2 : 0 < x ^ 2 := pow_pos hx0 2
  have hx21 : x ^ 2 ≤ 1 := pow_le_one₀ hx0.le hx1.le
  have hxq₀ : 0 < (x ^ 2) ^ Q := pow_pos hx2 Q
  refine ⟨S + Kt + 1 + ((x ^ 2) ^ Q)⁻¹, by positivity, fun μ q M _ hM2 hβ => ?_⟩
  set Cf := S + Kt + 1 + ((x ^ 2) ^ Q)⁻¹
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set u := (M : ℝ) * (x ^ 2) ^ q
  have hu : 0 ≤ u := by positivity
  -- Short blocks: the trivial bound.
  by_cases hshort : q = 0 ∨ q < Q
  · refine htriv Cf (by simp only [Cf]; linarith [inv_nonneg.2 hxq₀.le]) μ q M ?_
    have hxle : (x ^ 2) ^ Q ≤ (x ^ 2) ^ q := by
      rcases hshort with h | h
      · subst h; exact pow_le_one₀ hx2.le hx21
      · exact pow_le_pow_of_le_one hx2.le hx21 h.le
    have h1 : 1 ≤ ((x ^ 2) ^ Q)⁻¹ * (x ^ 2) ^ q := by
      rw [inv_mul_eq_div, le_div_iff₀ hxq₀, one_mul]; exact hxle
    have h2 : ((x ^ 2) ^ Q)⁻¹ * (x ^ 2) ^ q ≤ Cf * u := by
      have : ((x ^ 2) ^ Q)⁻¹ ≤ Cf := by simp only [Cf]; linarith
      calc ((x ^ 2) ^ Q)⁻¹ * (x ^ 2) ^ q ≤ Cf * (x ^ 2) ^ q := by gcongr
        _ ≤ Cf * u := by
            simp only [u]; gcongr; exact le_mul_of_one_le_left (by positivity) hM
    linarith
  rw [not_or, not_lt] at hshort
  obtain ⟨hq0, hq⟩ := hshort
  by_cases hbig : 1 ≤ Cf * u
  · exact htriv Cf (by simp only [Cf]; linarith [inv_nonneg.2 hxq₀.le]) μ q M hbig
  have hsmall : Cf * u < 1 := lt_of_not_ge hbig
  -- The ingredients.
  set A := repeatedBlockSum Aj ι μ
  set β := bntWeight μ (M * q)
  set bb : ℝ := ∑ l, ‖β l‖ ^ 2
  have hbb : 0 < bb := sum_norm_sq_pos_of_ne_zero hβ
  have hsb : 0 < Real.sqrt bb := Real.sqrt_pos.2 hbb
  have hβle : ∀ j, ‖β j‖ ≤ Real.sqrt bb := fun j =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))
  set P := Matrix.polarPos (physicalMatrix (blockTensor A q))
  set w : Fin b → Fin b → ℂ := fun j j' =>
    mpvOverlap (ofPhysicalMatrixLM (relativeRow A ι μ q j j')) (fixedPointTensor (σ j)) M
  set z : Fin b → ℂ := fun j => mpvOverlap (ofPhysicalMatrixLM ((copyIsometry ι μ q j)ᴴ * P))
    (fixedPointTensor (σ j)) M
  have hzw : ∀ j, z j = ∑ j', β j' * w j j' := fun j =>
    mpvOverlap_conjTranspose_copyIsometry_mul_polarPos hι hdisj μ hq0 j
      _ M
  set v := copyApproxVector A q M (ghzAmplitude β) (copyIsometry ι μ q) σ
  set num := ∑ τ, star (v τ) * mpv A (blockedConfigEquiv d M q τ)
  set Sz := ∑ j, star (β j) * z j
  have hnum : num = ((Real.sqrt bb : ℝ) : ℂ)⁻¹ * Sz := by
    simp only [num, v, sum_star_copyApproxVector_mul_mpv, Sz, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ghzAmplitude, star_div₀, Complex.star_def, Complex.conj_ofReal, bb]
    ring
  set t := ‖mpvState A (M * q)‖
  have hov : t⁻¹ * ‖num‖ ≤ ‖copyApproxOverlap A q M (ghzAmplitude β) (copyIsometry ι μ q) σ‖ := by
    rw [copyApproxOverlap_eq]
    exact inv_mul_norm_le_norm_of_sum_norm_sq_le_one v _
      (sum_norm_sq_copyApproxVector_le A q M hβ
        (fun j => conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q)
        (fun j k h => conjTranspose_copyIsometry_mul_eq_zero hdisj μ q h)
        (fun j => (hσ j).posSemidef) htr) (norm_nonneg _)
  -- The overlaps of the blocks, relative to the weights.
  have hwj : ∀ p : Fin b × Fin b, ‖w p.1 p.2 - (if p.1 = p.2 then 1 else 0)‖ ≤
      Cz p * u * Real.exp (Cz p * u) := fun p => by
    have hCS : Cz p ≤ S := Finset.single_le_sum
      (fun p _ => (hCz p).le) (Finset.mem_univ p)
    have hsmallp : Cz p * u < 1 := by
      have hCf : S ≤ Cf := by
        simp only [Cf]
        linarith [inv_nonneg.2 hxq₀.le]
      exact (mul_le_mul_of_nonneg_right (hCS.trans hCf) hu).trans_lt hsmall
    have h := hgen p.1 p.2 μ q ((hQ p).trans hq) hq0 M hM2
    simp only [hxq] at h
    exact h hsmallp
  -- The rescaled overlap: `∑ⱼ conj(βⱼ) zⱼ = b (1 + O(∑ |w - δ|))`.
  set δ' := ∑ p : Fin b × Fin b, ‖w p.1 p.2 - (if p.1 = p.2 then 1 else 0)‖
  have hSz : ‖Sz / (bb : ℂ) - 1‖ ≤ δ' := by
    have hbbC : (bb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbb.ne'
    have hrw : Sz / (bb : ℂ) - 1 = (∑ p : Fin b × Fin b, star (β p.1) * β p.2 *
        (w p.1 p.2 - (if p.1 = p.2 then 1 else 0))) / (bb : ℂ) := by
      rw [eq_div_iff hbbC, sub_mul, div_mul_cancel₀ _ hbbC, one_mul]
      simp only [Sz, hzw, bb, Complex.ofReal_sum, Fintype.sum_prod_type, mul_sub,
        Finset.sum_sub_distrib, Finset.mul_sum, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      congr 1
      · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
        ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        rw [Complex.star_def, Complex.conj_mul']
        push_cast
        ring
    rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbb, div_le_iff₀ hbb]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun p _ => ?_
    rw [norm_mul, norm_mul, norm_star, mul_comm _ bb]
    gcongr
    calc ‖β p.1‖ * ‖β p.2‖ ≤ Real.sqrt bb * Real.sqrt bb := by
          gcongr
          · exact hβle p.1
          · exact hβle p.2
      _ = bb := Real.mul_self_sqrt hbb.le
  have hNq : M * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq0
  have ht2 : |(t / Real.sqrt bb) ^ 2 - 1| ≤ Kt * x ^ (M * q) := by
    have h := hnorm (Real.sqrt bb) β hβle (M * q)
    have hT : t ^ 2 = ∑ s : Fin (M * q) → Fin d, ‖∑ j, β j * mpv (Aj j) s‖ ^ 2 := by
      simp only [t, EuclideanSpace.norm_sq_eq, mpvState_apply, A,
        mpv_repeatedBlockSum hι hdisj μ hNq]
      rfl
    rw [← hT, Real.sq_sqrt hbb.le] at h
    have he : (t / Real.sqrt bb) ^ 2 - 1 = (t ^ 2 - bb) / bb := by
      rw [div_pow, Real.sq_sqrt hbb.le]
      field_simp
    rw [he, abs_div, abs_of_pos hbb, div_le_iff₀ hbb]
    linarith [h]
  have hmain := one_sub_norm_div_le_of_norm_sub_le
    (div_nonneg (norm_nonneg _) hsb.le) (by simpa using hSz) (by simpa using ht2)
  rw [div_eq_inv_mul] at hmain
  have hkey : (t / Real.sqrt bb)⁻¹ * ‖Sz / (bb : ℂ)‖ = t⁻¹ * ‖num‖ := by
    rw [hnum, norm_mul, norm_div, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsb, abs_of_pos hbb,
      inv_div]
    rcases eq_or_ne t 0 with ht | ht
    · simp [ht]
    · field_simp
      rw [Real.sq_sqrt hbb.le, mul_comm]
  rw [hkey] at hmain
  -- At least two blocks make the target-norm error quadratic in x^q.
  have hη : Kt * x ^ (M * q) ≤ Kt * u := by
    have hpow : x ^ (M * q) ≤ (x ^ 2) ^ q := by
      rw [← pow_mul]
      exact pow_le_pow_of_le_one hx0.le hx1.le (Nat.mul_le_mul_right q hM2)
    exact (mul_le_mul_of_nonneg_left hpow hKt).trans
      (mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (by positivity) hM) hKt)
  have hCf : S + Kt + 1 ≤ Cf := by
    simp only [Cf]
    linarith [inv_nonneg.2 hxq₀.le]
  have hexp : 1 ≤ Real.exp (Cf * u) := Real.one_le_exp (by positivity)
  have hδ : δ' ≤ S * u * Real.exp (Cf * u) := by
    calc
      _ ≤ ∑ p : Fin b × Fin b, Cz p * u * Real.exp (Cf * u) := by
        refine Finset.sum_le_sum fun p _ => (hwj p).trans ?_
        have hCS : Cz p ≤ S := Finset.single_le_sum
          (fun p _ => (hCz p).le) (Finset.mem_univ p)
        have hSC : S ≤ Cf := by linarith
        exact mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (hCS.trans hSC) hu))
          (mul_nonneg (hCz p).le hu)
      _ = S * u * Real.exp (Cf * u) := by rw [← Finset.sum_mul, ← Finset.sum_mul]
  calc
    _ ≤ δ' + Kt * x ^ (M * q) := by linarith [hmain, hov]
    _ ≤ S * u * Real.exp (Cf * u) + Kt * u * Real.exp (Cf * u) :=
      add_le_add hδ (hη.trans (le_mul_of_one_le_right (by positivity) hexp))
    _ = (S + Kt) * u * Real.exp (Cf * u) := by ring
    _ ≤ Cf * u * Real.exp (Cf * u) := by gcongr; linarith

/-- The linear-in-`y` consequence of
`exists_approximationError_le_repeatedOverlappingBlockSum_sq_of_two_le`, for the corrected
state in arXiv:2307.01696, Supplemental Material, Lemma 1′(ii). The constant remains
independent of the nonzero complex copy weights. -/
theorem exists_approximationError_le_mul_repeatedOverlappingBlockSum_sq_of_two_le
    (hι : ∀ j k, Function.Injective (ι j k))
    (hdisj : ∀ p p' : (j : Fin b) × Fin (m j), p ≠ p' → ∀ a a', ι p.1 p.2 a ≠ ι p'.1 p'.2 a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, ∀ (q M : ℕ) [NeZero M],
      2 ≤ M → bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-(2 * γ) * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum_sq_of_two_le
    hι hdisj hN hA hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ q M _ hM hβ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity)
    (h μ q M hM hβ) ?_
  linarith [norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)]

end MPSTensor
