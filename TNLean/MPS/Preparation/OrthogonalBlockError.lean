/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OrthogonalBlockSum

/-!
# The approximation error for orthogonal blocks of multiplicity one

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound
the error of the approximating state of eq. (S7) for a tensor that is not normal by
`ε = O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`, with `ξ_diag` the largest correlation length of
the normal blocks. As printed the bound fails, both for a block of multiplicity two
(`docs/paper-gaps/mswc24_multiplicity_fixed_point.tex`) and for two blocks of multiplicity one
whose `q`-site states overlap (`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`).

This file proves the bound for blocks of multiplicity one with positive weights whose `q`-site
states are orthogonal: for `Aⁱ = ⊕ⱼ μⱼ A_jⁱ` with `μⱼ > 0`, normal blocks `A_j` in the gauge of
eq. (5), and a common bound `λ₂` on the subleading eigenvalues of their transfer maps, there is
`C` such that `ε ≤ C y e^{C y}` with `y = (N/q) e^{-γ q/ξ_diag}`, for every block length `q` at
which the blocked tensors of distinct blocks satisfy `B_jᴴ B_{j'} = 0`, and every number of
blocks `M ≥ 1` (`exists_approximationError_le_blockSum`); in `O`-form, `ε ≤ C y`
(`exists_approximationError_le_mul_blockSum`).

Under the orthogonality the states of distinct blocks, before and after the replacement by the
fixed points, are exactly orthogonal, so the term `O(e^{-N/ξ_offdiag})` of the source's proof
vanishes and no condition `q = o(N)` is needed; the proof reduces to Lemma 1'(i) for each
block (`MPSTensor.exists_norm_mpvOverlap_polarPosTensor_sub_one_le`,
`MPSTensor.exists_abs_norm_mpvState_sq_sub_one_le`).

**Scope restriction (multiplicity one, orthogonal blocks):** Lemma 1'(ii) is proved only for
`m_j = 1`, weights `μⱼ > 0`, and blocks whose `q`-site states are orthogonal. For `m_j = 1`
the phase of `μⱼ` can be absorbed into `A_j`, which stays normal with the same transfer map,
so the positivity of `μⱼ` only fixes that presentation; the orthogonality is an additional
hypothesis, without which the statement fails. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.one_sub_norm_sum_div_le` — the error of a weighted combination of block overlaps.
* `MPSTensor.sum_star_mpv_approximatingTensor_mul_mpv` — the overlap of the approximating state
  of a normal block with its target is `⟨φ_M(P_∞)|φ_M(P_q)⟩`.
* `MPSTensor.exists_approximationError_le_blockSum`,
  `MPSTensor.exists_approximationError_le_mul_blockSum` — Lemma 1'(ii) for orthogonal blocks
  of multiplicity one.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, Lemma 1'(ii) (`eq:fid_err_gen_non_normal`).
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### An elementary estimate -/

/-- If `p ≥ 0` has positive total `P`, the normalized combination `∑ⱼ pⱼ zⱼ / (√P √(∑ⱼ pⱼ cⱼ))`
of numbers `zⱼ` close to `1`, normalized by the numbers `cⱼ` close to `1`, has modulus at least
`1 - 2 ∑ⱼ (|zⱼ - 1| + |cⱼ - 1|)`. This is the triangle inequality of arXiv:2307.01696,
Supplemental Material, proof of Lemma 1'(ii), once the cross terms vanish. -/
theorem one_sub_norm_sum_div_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hP : 0 < ∑ j, p j) (z : ι → ℂ) (c : ι → ℝ) :
    1 - ‖∑ j, (p j : ℂ) * z j‖ / (Real.sqrt (∑ j, p j) * Real.sqrt (∑ j, p j * c j)) ≤
      2 * ∑ j, (‖z j - 1‖ + |c j - 1|) := by
  set P := ∑ j, p j
  set δ := ∑ j, ‖z j - 1‖
  set η := ∑ j, |c j - 1|
  have hδ : 0 ≤ δ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hη : 0 ≤ η := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsplit : ∑ j, (‖z j - 1‖ + |c j - 1|) = δ + η := Finset.sum_add_distrib
  rw [hsplit]
  have hpP : ∀ j, p j / P ≤ 1 := fun j =>
    (div_le_one hP).2 (Finset.single_le_sum (fun j _ => hp j) (Finset.mem_univ j))
  -- The normalized combinations.
  set a : ℂ := ∑ j, ((p j / P : ℝ) : ℂ) * z j
  set C : ℝ := ∑ j, p j / P * c j
  have ha : ‖a - 1‖ ≤ δ := by
    have e : a - 1 = ∑ j, ((p j / P : ℝ) : ℂ) * (z j - 1) := by
      have h1 : ∑ j, ((p j / P : ℝ) : ℂ) = 1 := by
        rw [← Complex.ofReal_sum, ← Finset.sum_div, div_self hP.ne', Complex.ofReal_one]
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1, a]
    rw [e]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hp j) hP.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) (hpP j)
  have hC : |C - 1| ≤ η := by
    have e : C - 1 = ∑ j, p j / P * (c j - 1) := by
      have h1 : ∑ j, p j / P = 1 := by rw [← Finset.sum_div, div_self hP.ne']
      simp only [mul_sub, mul_one, Finset.sum_sub_distrib, h1, C]
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul, abs_of_nonneg (div_nonneg (hp j) hP.le)]
    exact mul_le_of_le_one_left (abs_nonneg _) (hpP j)
  -- Rewrite the quotient through the normalized combinations.
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.2 hP
  have hq : ‖∑ j, (p j : ℂ) * z j‖ / (Real.sqrt P * Real.sqrt (∑ j, p j * c j)) =
      ‖a‖ / Real.sqrt C := by
    have hnum : ∑ j, (p j : ℂ) * z j = (P : ℂ) * a := by
      simp only [a, Finset.mul_sum, Complex.ofReal_div]
      refine Finset.sum_congr rfl fun j _ => ?_
      have : (P : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hP.ne'
      field_simp
    have hden : Real.sqrt (∑ j, p j * c j) = Real.sqrt P * Real.sqrt C := by
      rw [← Real.sqrt_mul hP.le]
      congr 1
      simp only [C, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      field_simp
    rw [hnum, hden, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP,
      ← mul_assoc, Real.mul_self_sqrt hP.le, mul_div_mul_left _ _ hP.ne']
  rw [hq]
  have hle1 : 1 - ‖a‖ / Real.sqrt C ≤ 1 := by
    have : 0 ≤ ‖a‖ / Real.sqrt C := by positivity
    linarith
  rcases lt_or_ge (1 / 2 : ℝ) η with hη2 | hη2
  · linarith
  · have hC2 : 1 / 2 ≤ C := by linarith [(abs_le.1 (hC.trans hη2)).1]
    set s := Real.sqrt C
    have hs2 : s ^ 2 = C := Real.sq_sqrt (by linarith)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg C
    have hs : 1 / 2 ≤ s := by nlinarith
    have hs1 : |s - 1| ≤ |C - 1| := by
      rw [← hs2, show s ^ 2 - 1 = (s - 1) * (s + 1) by ring, abs_mul]
      exact le_mul_of_one_le_right (abs_nonneg _) (by rw [abs_of_pos (by linarith)]; linarith)
    have hna : 1 - ‖a‖ ≤ ‖a - 1‖ := by
      have := norm_sub_norm_le (1 : ℂ) a
      rw [norm_one, norm_sub_rev] at this
      exact this
    rw [sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ (by linarith)]
    have hsη : s ≤ 1 + η := by linarith [le_abs_self (s - 1)]
    have haδ : 1 - δ ≤ ‖a‖ := by linarith
    rcases le_or_gt (1 - 2 * (δ + η)) 0 with h | h
    · nlinarith [norm_nonneg a]
    · nlinarith [mul_le_mul_of_nonneg_left hsη h.le, mul_nonneg hδ hη]

/-! ### The overlap of one block -/

/-- For an injective blocked tensor, the overlap of the approximating state `φ_M(V P_∞)` with the
periodic state of `A` on `N = qM` sites, read in blocks, is `⟨φ_M(P_∞)|φ_M(P_q)⟩`.

arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(i): the first term of the triangle
inequality "is exactly equal to the LHS of" eq. (S9). -/
theorem sum_star_mpv_approximatingTensor_mul_mpv (A : MPSTensor d D) {q : ℕ}
    (hB : Kraus.IsInjective (blockTensor A q)) (σ : Matrix (Fin D) (Fin D) ℂ) (M : ℕ)
    [NeZero M] :
    ∑ τ : Fin M → Fin (blockPhysDim d q),
        star (mpv (approximatingTensor (blockTensor A q) σ) τ) *
          mpv A (blockedConfigEquiv d M q τ) =
      mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor σ) M := by
  simp only [mpv_blockedConfigEquiv_eq_sum_polar, mpv_approximatingTensor]
  rw [(isIsometry_polarIsoMatrix_of_isInjective hB).sum_star_mul_tensorPower]
  simp only [mpvOverlap, mpv_fixedPointTensor]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-- The squared norm of the periodic state on `N = qM` sites, as a sum over blocked
configurations. -/
theorem sum_star_mpv_blockedConfigEquiv (A : MPSTensor d D) (q M : ℕ) :
    ∑ τ : Fin M → Fin (blockPhysDim d q),
        star (mpv A (blockedConfigEquiv d M q τ)) * mpv A (blockedConfigEquiv d M q τ) =
      ((‖mpvState A (M * q)‖ ^ 2 : ℝ) : ℂ) := by
  rw [ofReal_norm_mpvState_sq, mpvOverlap, ← (blockedConfigEquiv d M q).sum_comp]
  exact Finset.sum_congr rfl fun τ _ => mul_comm _ _

/-! ### The error for orthogonal blocks -/

variable {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- The overlap of the approximating state of eq. (S7) with the target, for orthogonal blocks
of multiplicity one whose blocked tensors are injective: with `pⱼ = μⱼ^{2N}`,
`zⱼ = ⟨φ_M(P_{j,∞})|φ_M(P_{j,q})⟩` and `cⱼ = ‖φ_N(A_j)‖²`,
`|⟨φ̃_N|φ_N⟩| = |∑ⱼ pⱼ zⱼ| / (√(∑ⱼ pⱼ) √(∑ⱼ pⱼ cⱼ))`. -/
theorem norm_nonNormalApproxOverlap_blockSum (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {μ : Fin b → ℝ} (hμ : ∀ j, 0 < μ j)
    [NeZero b] {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ}
    (hσ : ∀ j, (σ j).PosSemidef) (htr : ∀ j, (σ j).trace = 1) {q : ℕ} (hq : q ≠ 0)
    (hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q))
    (horth : ∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
      physicalMatrix (blockTensor (Aj j') q) = 0) (M : ℕ) [NeZero M] :
    ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
        (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
        (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ =
      ‖∑ j, ((μ j ^ (2 * (M * q)) : ℝ) : ℂ) *
          mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M‖ /
        (Real.sqrt (∑ j, μ j ^ (2 * (M * q))) *
          Real.sqrt (∑ j, μ j ^ (2 * (M * q)) * ‖mpvState (Aj j) (M * q)‖ ^ 2)) := by
  have : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  set N := M * q
  have hN : N ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq
  set β : Fin b → ℂ := fun j => (μ j : ℂ) ^ N
  set r : ℝ := Real.sqrt (∑ l, ‖β l‖ ^ 2)
  have hβn : ∀ j, ‖β j‖ ^ 2 = μ j ^ (2 * N) := fun j => by
    simp only [β, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hμ j)]
    ring
  have hr : r = Real.sqrt (∑ j, μ j ^ (2 * N)) := by simp only [r, hβn]
  have hβ0 : β ≠ 0 := by
    intro h
    have := congrFun h 0
    simp only [β, Pi.zero_apply, pow_eq_zero_iff hN, Complex.ofReal_eq_zero] at this
    exact (hμ 0).ne' this
  set A := blockSum Aj ι fun j => (μ j : ℂ)
  set s : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (approximatingTensor (blockTensor (Aj j) q) (σ j)) τ
  set t : (j : Fin b) → (Fin M → Fin (blockPhysDim d q)) → ℂ :=
    fun j τ => mpv (Aj j) (blockedConfigEquiv d M q τ)
  have hS : ∀ τ, nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ =
      ∑ j, ghzAmplitude β j * s j τ := fun τ =>
    nonNormalApproxVector_blockSum hι hdisj hμ hq horth σ M _ τ
  have hT : ∀ τ, mpv A (blockedConfigEquiv d M q τ) = ∑ j, β j * t j τ := fun τ =>
    mpv_blockSum hι hdisj _ hN _
  -- Cross terms vanish.
  have hss : ∀ j j', ∑ τ, star (s j τ) * s j' τ = if j = j' then 1 else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact mpv_approximatingTensor_norm_sq (hB j) (hσ j) (htr j)
    · have := mpvOverlap_eq_zero (X := approximatingTensor (blockTensor (Aj j') q) (σ j'))
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul (horth j j' h) _ _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => mul_comm _ _
  have hst : ∀ j j', ∑ τ, star (s j τ) * t j' τ = if j = j' then
      mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M
      else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact sum_star_mpv_approximatingTensor_mul_mpv (Aj j) (hB j) (σ j) M
    · have := mpvOverlap_eq_zero (X := blockTensor (Aj j') q)
        (Y := approximatingTensor (blockTensor (Aj j) q) (σ j))
        (conjTranspose_physicalMatrix_approximatingTensor_mul_blocked (horth j j' h) _)
        (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => by
        rw [mul_comm]; simp only [s, t, mpv_blockedConfigEquiv]
  have htt : ∀ j j', ∑ τ, star (t j τ) * t j' τ = if j = j' then
      ((‖mpvState (Aj j) N‖ ^ 2 : ℝ) : ℂ) else 0 := fun j j' => by
    split_ifs with h
    · subst h; exact sum_star_mpv_blockedConfigEquiv (Aj j) q M
    · have := mpvOverlap_eq_zero (X := blockTensor (Aj j') q) (Y := blockTensor (Aj j) q)
        (horth j j' h) (NeZero.ne M)
      rw [mpvOverlap] at this
      rw [← this]
      exact Finset.sum_congr rfl fun τ _ => by
        rw [mul_comm]; simp only [t, mpv_blockedConfigEquiv]
  -- The three sums.
  have hX : ∑ τ, star (nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ) *
      nonNormalApproxVector A q M (ghzAmplitude β)
        (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ = 1 := by
    simp only [hS]
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ (fun _ => 1) s s hss]
    simpa only [mul_one] using ghzAmplitude_norm_sq hβ0
  have hY : ((‖mpvState A N‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ((μ j ^ (2 * N) * ‖mpvState (Aj j) N‖ ^ 2 : ℝ) : ℂ) := by
    rw [← sum_star_mpv_blockedConfigEquiv]
    simp only [hT]
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ _ t t htt]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hβn, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_conj_mul_self]
    rfl
  have hZ : ∑ τ, star (nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ) *
      mpv A (blockedConfigEquiv d M q τ) =
      (r : ℂ)⁻¹ * ∑ j, ((μ j ^ (2 * N) : ℝ) : ℂ) *
        mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M := by
    simp only [hS, hT]
    rw [sum_star_sum_mul_sum_of_orthogonal _ _ _ s t hst, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsβ : star (β j) * β j = ((μ j ^ (2 * N) : ℝ) : ℂ) := by
      rw [← hβn, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    have hr' : star ((Real.sqrt (∑ l, ‖β l‖ ^ 2) : ℝ) : ℂ) = (r : ℂ) := by
      simp [r]
    rw [ghzAmplitude, star_div₀, hr', div_mul_eq_mul_div, hsβ]
    ring
  -- Assemble.
  have hXr : Real.sqrt (∑ τ, ‖nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ‖ ^ 2) = 1 := by
    have h := ofReal_sum_norm_sq (nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))))
    rw [hX, ← Complex.ofReal_one] at h
    rw [Complex.ofReal_injective h, Real.sqrt_one]
  have hYr : ‖mpvState A N‖ = Real.sqrt (∑ j, μ j ^ (2 * N) * ‖mpvState (Aj j) N‖ ^ 2) := by
    rw [← Complex.ofReal_sum] at hY
    rw [← Complex.ofReal_injective hY, Real.sqrt_sq (norm_nonneg _)]
  rw [nonNormalApproxOverlap_eq]
  change ‖((Real.sqrt (∑ τ, ‖nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ‖ ^ 2) : ℂ)⁻¹ *
      (‖mpvState A N‖ : ℂ)⁻¹) * ∑ τ, star (nonNormalApproxVector A q M (ghzAmplitude β)
      (fun j => embedPair (ι j) (fixedPointPair (σ j))) τ) *
      mpv A (blockedConfigEquiv d M q τ)‖ = _
  rw [hZ, hXr, hYr, ← hr]
  simp only [Complex.ofReal_one, inv_one, one_mul, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg, Real.sqrt_nonneg]
  rw [div_eq_inv_mul, mul_inv, hr, abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- **Approximation error for orthogonal blocks of multiplicity one** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), in the scope of the module docstring). Let
`Aⁱ = ⊕ⱼ μⱼ A_jⁱ` with `μⱼ > 0`, the block `j` placed on the bond coordinates `ι_j`, let every
block `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`,
`Tr σ_j = 1` (eq. (5)), let `λ₂` bound the moduli of the eigenvalues other than `1` of every
transfer map `E_{A_j}`, so that `ξ = -1/log|λ₂|` bounds the correlation lengths `ξ_jj`, and let
`0 < γ < 1/2`. There is `C > 0` such that for every block length `q` at which the `q`-site
states of distinct blocks are orthogonal, `B_jᴴ B_{j'} = 0`, and every number of blocks
`M ≥ 1`, with `N = qM`, `βⱼ = μⱼ^N` (eq. (S4) for `m_j = 1`), the pairs of the `σ_j` embedded
along `ι_j`, and `y = (N/q) e^{-γ q/ξ}`, the error `ε = 1 - |⟨φ̃_N|φ_N⟩|` of the approximating
state of eq. (S7) satisfies `ε ≤ C y e^{C y}`.

No condition `q = o(N)` is needed: under the orthogonality the source's off-diagonal term
vanishes. -/
theorem exists_approximationError_le_blockSum [NeZero b] (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {μ : Fin b → ℝ} (hμ : ∀ j, 0 < μ j)
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
          (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  choose C₁ hC₁ hover using fun j =>
    exists_norm_mpvOverlap_polarPosTensor_sub_one_le (Aj j) (hN j) (hA j) (hσ j) (htr j)
      (hfix j) (hlam j) hγ0 hγ
  choose K₅ hK₅ hc using fun j =>
    exists_abs_norm_mpvState_sq_sub_one_le (Aj j) (hN j) (hA j) (hσ j) (htr j) (hfix j)
      (hlam j) hγ0 hγ
  choose L hLpos hL using hN
  set x := Real.exp (-γ / correlationLength lam₂)
  have hx : 0 < x := Real.exp_pos _
  set S₁ := ∑ j, C₁ j
  set S₂ := ∑ j, K₅ j
  set S₃ := ∑ j, (x ^ L j)⁻¹
  have hS₁ : 0 ≤ S₁ := Finset.sum_nonneg fun j _ => (hC₁ j).le
  have hS₂ : 0 ≤ S₂ := Finset.sum_nonneg fun j _ => hK₅ j
  have hS₃ : 0 ≤ S₃ := Finset.sum_nonneg fun j _ => by positivity
  set C := 2 * (S₁ + S₂) + S₃ + 1
  refine ⟨C, by positivity, fun q M _ horth => ?_⟩
  have hxq : Real.exp (-γ * q / correlationLength lam₂) = x ^ q := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  rw [hxq]
  set u := (M : ℝ) * x ^ q
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hu : 0 ≤ u := by positivity
  have hexp : 1 ≤ Real.exp (C * u) := Real.one_le_exp (by positivity)
  set ov := nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
    (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q)) (fun j => embedPair (ι j) (fixedPointPair (σ j)))
  have hε1 : 1 - ‖ov‖ ≤ 1 := by linarith [norm_nonneg ov]
  by_cases hbig : 1 ≤ C * u
  · exact hε1.trans (hbig.trans (le_mul_of_one_le_right (by positivity) hexp))
  rw [not_le] at hbig
  have hx1 : x < 1 := by
    by_contra h
    rw [not_lt] at h
    have : 1 ≤ u := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ h)
    have : 1 ≤ C := by linarith
    nlinarith
  have hLq : ∀ j, L j ≤ q := fun j => by
    by_contra h
    rw [not_le] at h
    have hxLq : x ^ L j ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le h.le
    have h1 : x ^ L j ≤ u := hxLq.trans (le_mul_of_one_le_left (by positivity) hM)
    have h2 : 1 ≤ (x ^ L j)⁻¹ * u := by
      rw [← inv_mul_cancel₀ (by positivity : x ^ L j ≠ 0)]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (x ^ L j)⁻¹ ≤ S₃ :=
      Finset.single_le_sum (f := fun j => (x ^ L j)⁻¹) (fun j _ => by positivity)
        (Finset.mem_univ j)
    have h4 : (x ^ L j)⁻¹ * u ≤ C * u := mul_le_mul_of_nonneg_right (by linarith) hu
    linarith
  have hq : q ≠ 0 := fun h => by have := hLq 0; have := hLpos 0; omega
  have hB : ∀ j, Kraus.IsInjective (blockTensor (Aj j) q) := fun j =>
    (isNBlkInjective_iff_blockTensor_isInjective (Aj j) q).1
      (isNBlkInjective_of_le (hLpos j) (hL j) (hLq j))
  have hnorm := norm_nonNormalApproxOverlap_blockSum hι hdisj hμ (fun j => (hσ j).posSemidef)
    htr hq hB horth M
  change ‖ov‖ = _ at hnorm
  have hp : 0 < ∑ j, μ j ^ (2 * (M * q)) :=
    Finset.sum_pos (fun j _ => pow_pos (hμ j) _) Finset.univ_nonempty
  have hmain := one_sub_norm_sum_div_le (fun j => μ j ^ (2 * (M * q)))
    (fun j => (pow_pos (hμ j) _).le) hp
    (fun j => mpvOverlap (polarPosTensor (blockTensor (Aj j) q)) (fixedPointTensor (σ j)) M)
    (fun j => ‖mpvState (Aj j) (M * q)‖ ^ 2)
  rw [← hnorm] at hmain
  refine hmain.trans ?_
  -- Each block contributes at most `C₁ u e^{C₁ u} + K₅ u`.
  have hblock : ∀ j, ‖mpvOverlap (polarPosTensor (blockTensor (Aj j) q))
      (fixedPointTensor (σ j)) M - 1‖ + |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1| ≤
      C₁ j * u * Real.exp (S₁ * u) + K₅ j * u := fun j => by
    have h1 := hover j q M
    rw [hxq] at h1
    have h1' : C₁ j * u * Real.exp (C₁ j * u) ≤ C₁ j * u * Real.exp (S₁ * u) := by
      have : C₁ j ≤ S₁ := Finset.single_le_sum (f := C₁) (fun j _ => (hC₁ j).le)
        (Finset.mem_univ j)
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right this hu))
        (mul_nonneg (hC₁ j).le hu)
    have h2 : |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1| ≤ K₅ j * u := by
      refine (hc j (M * q)).trans (mul_le_mul_of_nonneg_left ?_ (hK₅ j))
      calc (x ^ 2) ^ (M * q) = x ^ (2 * (M * q)) := (pow_mul _ _ _).symm
        _ ≤ x ^ q := pow_le_pow_of_le_one hx.le hx1.le (by
            have := Nat.one_le_iff_ne_zero.2 (NeZero.ne M); nlinarith)
        _ ≤ u := le_mul_of_one_le_left (by positivity) hM
    linarith
  calc 2 * ∑ j, (‖mpvOverlap (polarPosTensor (blockTensor (Aj j) q))
        (fixedPointTensor (σ j)) M - 1‖ + |‖mpvState (Aj j) (M * q)‖ ^ 2 - 1|)
      ≤ 2 * ∑ j, (C₁ j * u * Real.exp (S₁ * u) + K₅ j * u) := by
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hblock j) (by norm_num)
    _ = 2 * (S₁ * u * Real.exp (S₁ * u) + S₂ * u) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    _ ≤ C * u * Real.exp (C * u) := by
        have hS₁C : S₁ ≤ C := by linarith
        have he : Real.exp (S₁ * u) ≤ Real.exp (C * u) :=
          Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hS₁C hu)
        have h1 : S₁ * u * Real.exp (S₁ * u) ≤ S₁ * u * Real.exp (C * u) := by gcongr
        have h2 : S₂ * u ≤ S₂ * u * Real.exp (C * u) :=
          le_mul_of_one_le_right (by positivity) hexp
        have h3 : 2 * (S₁ + S₂) * u * Real.exp (C * u) ≤ C * u * Real.exp (C * u) := by
          gcongr; linarith
        nlinarith

/-- **Approximation error for orthogonal blocks of multiplicity one, `O`-form**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12)): in the setting of
`exists_approximationError_le_blockSum`, there is `C` with `ε ≤ C (N/q) e^{-γ q/ξ}` for every
block length `q` at which the `q`-site states of distinct blocks are orthogonal and every number
of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_blockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j))
    (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a') {μ : Fin b → ℝ} (hμ : ∀ j, 0 < μ j)
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ} (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      (∀ j j', j ≠ j' → (physicalMatrix (blockTensor (Aj j) q))ᴴ *
        physicalMatrix (blockTensor (Aj j') q) = 0) →
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
          (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_blockSum hι hdisj hμ hN hA hσ htr hfix
    hlam hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ horth => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M horth) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun j => (μ j : ℂ)) q M
    (ghzAmplitude fun j => (μ j : ℂ) ^ (M * q))
    (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

end MPSTensor
