/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockOverlap

/-!
# The approximation error for blocks with overlapping states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound
the error of the approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal by
`ε = O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`, with `ξ_diag = max_j ξ_jj`. When the `q`-site
states of distinct blocks overlap, this rate is false: for the blocks `A_1 = (1, 0)` and
`A_2 = (3/5, 4/5)` the error is at least `(9/25)^q / 16`, while `ξ_diag` can be taken
arbitrarily small (`MPSTensor.isBNTCanonicalForm_and_not_approximationError_le_overlappingBlock`).

This file proves that the source's construction nevertheless converges, at the rate governed by
the larger of the correlation lengths of the blocks and of their mixed transfer maps. For
normal blocks of multiplicity one and unit weights, let `λ₂` bound the moduli of the eigenvalues
other than `1` of every transfer map `E_{jj}` and of all eigenvalues of the mixed transfer maps
`E_{jj'}`, `j ≠ j'`, so that `ξ = -1/log|λ₂|` bounds both `ξ_diag` and
`ξ_off-diag = max_{j≠j'} ξ_{jj'}`, and let `0 < γ < 1/2`. Then there is `C` with
`ε ≤ C y e^{C y}`, `y = M e^{-γ q/ξ} = (N/q) e^{-γ q/ξ}`, for every block length `q` and every
number of blocks `M ≥ 1` (`exists_approximationError_le_overlappingBlockSum`), and in `O`-form
`ε ≤ C y` (`exists_approximationError_le_mul_overlappingBlockSum`). No condition `q = o(N)` is
needed, and no orthogonality of the blocks.

The proof: after `V^{⊗M}` the overlap of the approximating state with the target is
`b^{-1/2} ∑ⱼ zⱼ` (`sum_star_nonNormalApproxVector_mul_mpv`), with the overlaps `zⱼ` of the
positive part of the whole blocked tensor with the fixed points of the blocks; `V^{⊗M}` does not
increase norms, so normalizing the approximating state can only increase the overlap; `zⱼ` is
`1` up to `O(y e^{O(y)})` (`exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le`), and the
squared norm of the target is `b` up to `O(e^{-γ N/ξ})`
(`exists_abs_norm_mpvState_blockSum_sq_sub_le`).

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (multiplicity one, unit weights):** every block occurs once, with weight
`μⱼ = 1`, so that `βⱼ = 1` and `αⱼ = b^{-1/2}`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

## Main declarations

* `MPSTensor.sum_star_nonNormalApproxVector_mul_mpv` — the unnormalized overlap after `V^{⊗M}`.
* `MPSTensor.one_sub_norm_div_le_of_norm_sub_le` — the elementary estimate combining the errors.
* `MPSTensor.exists_approximationError_le_overlappingBlockSum`,
  `MPSTensor.exists_approximationError_le_mul_overlappingBlockSum` — Lemma 1'(ii) for blocks of
  multiplicity one and unit weights whose states may overlap, at the corrected rate.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D b : ℕ}

/-! ### The overlap after the partial isometry -/

/-- **The overlap after `V^{⊗M}`.** For any tensor `A` and pairs `ω_j` of matrices `σ'_j`, the
unnormalized approximating state `V^{⊗M} ∑ⱼ αⱼ |Ω_j⟩` of arXiv:2307.01696, Supplemental
Material, eq. (S7), has overlap `∑ⱼ conj(αⱼ) ⟨φ_M(P_{σ'_j})|φ_M(P)⟩` with the periodic state of `A`
on `N = qM` sites, where `P` is the positive part of the `q`-site blocked tensor and `P_{σ'_j}`
the fixed-point tensor of `σ'_j`. The source uses `V†V = Π` and `Π P = P`; no injectivity is
needed. -/
theorem sum_star_nonNormalApproxVector_mul_mpv (A : MPSTensor d D) (q M : ℕ) [NeZero M]
    (α : Fin b → ℂ) (σ' : Fin b → Matrix (Fin D) (Fin D) ℂ) :
    ∑ τ, star (nonNormalApproxVector A q M α (fun j => fixedPointPair (σ' j)) τ) *
        mpv A (blockedConfigEquiv d M q τ) =
      ∑ j, star (α j) *
        mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor (σ' j)) M := by
  set Bq := blockTensor A q
  set V := Matrix.polarIso (physicalMatrix Bq)
  set e : (Fin M → Fin (D * D)) ≃ (Fin M → Fin D × Fin D) :=
    Equiv.piCongrRight fun _ => virtualPairEquiv D
  set m : (Fin M → Fin D × Fin D) → ℂ := fun c => mpv (polarPosTensor Bq) (e.symm c)
  have hT : ∀ τ, mpv A (blockedConfigEquiv d M q τ) = (tensorPower M V *ᵥ m) τ := by
    intro τ
    rw [mpv_blockedConfigEquiv_eq_sum_polar]
    simp only [mulVec, dotProduct, tensorPower, of_apply, m]
    exact Fintype.sum_equiv e _ _ fun τ' => by
      simp [e, polarIsoMatrix, V, Bq]
  have hfixP : tensorPower M (Vᴴ * V) *ᵥ m = m := by
    funext c
    have h : mpv (rotatePhysical (polarSupportMatrix Bq) (polarPosTensor Bq)) (e.symm c) =
        mpv (polarPosTensor Bq) (e.symm c) := by rw [rotatePhysical_polarSupportMatrix]
    rw [mpv_rotatePhysical] at h
    change _ = mpv (polarPosTensor Bq) (e.symm c)
    rw [← h, Matrix.conjTranspose_polarIso_mul_polarIso]
    simp only [mulVec, dotProduct, tensorPower, of_apply, m]
    refine (Fintype.sum_equiv e.symm _ _ fun c' => ?_)
    simp [e, polarSupportMatrix, Bq]
  have hpair : ∀ j, ∑ c, star (pairProductState (fixedPointPair (σ' j)) c) * m c =
      mpvOverlap (polarPosTensor Bq) (fixedPointTensor (σ' j)) M := fun j => by
    rw [mpvOverlap]
    refine (Fintype.sum_equiv e.symm _ _ fun c => ?_)
    rw [mpv_fixedPointTensor, mul_comm]
    simp [e, m, virtualPairEquiv]
  calc ∑ τ, star (nonNormalApproxVector A q M α (fun j => fixedPointPair (σ' j)) τ) *
        mpv A (blockedConfigEquiv d M q τ)
      = ∑ τ, star ((tensorPower M V *ᵥ nonNormalFixedPointState α
          (fun j => fixedPointPair (σ' j))) τ) * (tensorPower M V *ᵥ m) τ := by
        simp only [hT]; rfl
    _ = ∑ c, star (nonNormalFixedPointState α (fun j => fixedPointPair (σ' j)) c) * m c := by
        rw [sum_star_tensorPower_mulVec_mul, hfixP]
    _ = ∑ j, star (α j) * ∑ c, star (pairProductState (fixedPointPair (σ' j)) c) * m c := by
        simp only [nonNormalFixedPointState, star_sum, star_mul', Finset.sum_mul,
          Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => by ring
    _ = _ := by simp only [hpair]

/-! ### An elementary estimate -/

/-- If `‖S - b‖ ≤ δ` and `|t² - b| ≤ η` with `b ≥ 1` and `t ≥ 0`, then
`1 - ‖S‖ / (√b t) ≤ δ + η`. This combines the overlap `S = ∑ⱼ zⱼ` and the norm `t = ‖φ_N‖` in the
triangle inequality of arXiv:2307.01696, Supplemental Material, proof of Lemma 1'(ii). -/
theorem one_sub_norm_div_le_of_norm_sub_le {b : ℝ} (hb : 1 ≤ b) {S : ℂ} {t δ η : ℝ}
    (ht : 0 ≤ t) (hS : ‖S - b‖ ≤ δ) (hT : |t ^ 2 - b| ≤ η) :
    1 - t⁻¹ * (‖S‖ / Real.sqrt b) ≤ δ + η := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hS
  have hη : 0 ≤ η := (abs_nonneg _).trans hT
  have hnn : 0 ≤ t⁻¹ * (‖S‖ / Real.sqrt b) := by positivity
  rcases le_or_gt 1 (δ + η) with h | h
  · linarith
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.2 (by linarith)
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt (by linarith)
  have ht2 := abs_le.1 hT
  have htpos : 0 < t := by
    rcases ht.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at ht2; nlinarith [ht2.1]
  have hS' : b - δ ≤ ‖S‖ := by
    have := norm_sub_norm_le (b : ℂ) S
    rw [norm_sub_rev, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)] at this
    linarith
  set w := Real.sqrt b * t
  have hw : 0 < w := mul_pos hsb htpos
  have hw2 : 2 * w ≤ b + t ^ 2 := by nlinarith [sq_nonneg (Real.sqrt b - t)]
  have hwle : w ≤ b + η / 2 := by linarith [ht2.2]
  have heq : t⁻¹ * (‖S‖ / Real.sqrt b) = ‖S‖ / w := by
    simp only [w]; field_simp
  rw [heq]
  have : 1 - δ - η ≤ ‖S‖ / w := by
    rw [le_div_iff₀ hw]
    nlinarith [mul_le_mul_of_nonneg_right hwle (by linarith : (0 : ℝ) ≤ 1 - δ - η)]
  linarith

/-! ### The approximation error -/

variable {Dj : Fin b → ℕ} {Aj : (j : Fin b) → MPSTensor d (Dj j)}
  {ι : (j : Fin b) → Fin (Dj j) → Fin D}

/-- The normalized weights of unit weights are `αⱼ = b^{-1/2}`. -/
theorem ghzAmplitude_one [NeZero b] (j : Fin b) :
    ghzAmplitude (fun _ : Fin b => (1 : ℂ)) j = ((Real.sqrt b : ℝ) : ℂ)⁻¹ := by
  simp [ghzAmplitude]

/-- **Approximation error for blocks with overlapping states** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate of the module docstring).
Let `Aⁱ = ⊕ⱼ A_jⁱ` be the direct sum with unit weights of blocks placed on the bond coordinates
`ι_j`, let every block `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`,
`σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the moduli of the eigenvalues other than `1` of
every transfer map `E_{A_j}` and the moduli of all eigenvalues of the mixed transfer maps
`E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of distinct blocks, so that `ξ = -1/log|λ₂|` bounds
`ξ_diag = max_j ξ_jj` and `ξ_off-diag = max_{j≠j'} ξ_{jj'}`, and let `0 < γ < 1/2`. There is
`C > 0` such that for every block length `q` and every number of blocks `M ≥ 1`, with `N = qM`,
`βⱼ = 1` (eq. (S4) for `m_j = 1` and `μ_{j,1} = 1`), the pairs of the `σ_j` embedded along `ι_j`,
and `y = M e^{-γ q/ξ}` (`= (N/q) e^{-γ q/ξ}` for `q ≥ 1`), the error `ε = 1 - |⟨φ~_N|φ_N⟩|` of the
approximating state of eq. (S7) satisfies `ε ≤ C y e^{C y}`.

The `q`-site states of distinct blocks need not be orthogonal, and no condition `q = o(N)` is
needed. The source's rate `e^{-γ q/ξ_diag}` fails for overlapping blocks
(`isBNTCanonicalForm_and_not_approximationError_le_overlappingBlock`); here `ξ` also bounds the
correlation lengths `ξ_{jj'}` of the mixed transfer maps. -/
theorem exists_approximationError_le_overlappingBlockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  set x := Real.exp (-γ / correlationLength lam₂) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : ∀ q : ℕ, Real.exp (-γ * q / correlationLength lam₂) = x ^ q := fun q =>
    Real.exp_neg_mul_div_eq_pow _ _ q
  simp_rw [hxq]
  -- The trivial bound `ε ≤ 1`, which suffices whenever `M x^q ≥ 1`.
  have htriv : ∀ (C : ℝ), 1 ≤ C → ∀ (q M : ℕ) [NeZero M], 1 ≤ (M : ℝ) * x ^ q →
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) := fun C hC q M _ hu => by
    have h1 : 1 ≤ C * (M * x ^ q) := by nlinarith
    have h2 : 1 ≤ Real.exp (C * (M * x ^ q)) := Real.one_le_exp (by linarith)
    have h3 : 0 ≤ ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M
        (ghzAmplitude fun _ => 1) (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ :=
      norm_nonneg _
    nlinarith
  rcases le_or_gt 1 ‖lam₂‖ with hl | hl
  · -- For `|λ₂| ≥ 1` the rate is at least `1` and the bound is trivial.
    have hx1 : 1 ≤ x := by
      rw [hx_def, neg_div_correlationLength]
      exact Real.one_le_exp (mul_nonneg hγ0.le (Real.log_nonneg hl))
    refine ⟨1, one_pos, fun q M _ => htriv 1 le_rfl q M ?_⟩
    have := one_le_pow₀ hx1 (n := q)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  have hDD : NeZero D := ⟨fun h => by subst h; exact (ι 0 0).elim0⟩
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hl.le
  choose Cz hCz hz using fun j => exists_norm_mpvOverlap_polarPosTensor_blockSum_sub_one_le hι
    hdisj hN hA hσ htr hfix hl hlam hmix hγ0 (by linarith) j
  obtain ⟨Kt, hKt, hnorm⟩ := exists_abs_norm_mpvState_blockSum_sq_sub_le hι hdisj hN hA hσ htr
    hfix hl hlam hmix hγ0 hγ
  set S := ∑ j, Cz j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => (hCz j).le
  refine ⟨S + Kt + 1, by positivity, fun q M _ => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact htriv _ (by linarith) 0 M (by simp [hM])
  have hq0 : q ≠ 0 := hq.ne'
  -- The ingredients.
  set A := blockSum Aj ι fun _ => (1 : ℂ)
  set ω : Fin b → Fin D × Fin D → ℂ := fun j => embedPair (ι j) (fixedPointPair (σ j))
  set α : Fin b → ℂ := ghzAmplitude fun _ => 1
  set σ' : Fin b → Matrix (Fin D) (Fin D) ℂ := fun j => embeddedBlockState (ι j) (σ j)
  have hω : ω = fun j => fixedPointPair (σ' j) :=
    funext fun j => embedPair_fixedPointPair (hι j) (hσ j).posSemidef
  set v := nonNormalApproxVector A q M α ω
  set z : Fin b → ℂ := fun j =>
    mpvOverlap (polarPosTensor (blockTensor A q)) (fixedPointTensor (σ' j)) M
  set num := ∑ τ, star (v τ) * mpv A (blockedConfigEquiv d M q τ)
  have hnum : num = ((Real.sqrt b : ℝ) : ℂ)⁻¹ * ∑ j, z j := by
    simp only [num, v, hω]
    rw [sum_star_nonNormalApproxVector_mul_mpv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show α j = ghzAmplitude (fun _ => (1 : ℂ)) j from rfl, ghzAmplitude_one, star_inv₀,
      Complex.star_def, Complex.conj_ofReal]
  -- The approximating vector has norm at most one.
  have hvle : ∑ τ, ‖v τ‖ ^ 2 ≤ 1 := by
    have hidem := Matrix.conjTranspose_polarIso_mul_polarIso
      (physicalMatrix (blockTensor A q))
    have h := sum_norm_sq_tensorPower_mulVec_le (M := M)
      (W := Matrix.polarIso (physicalMatrix (blockTensor A q)))
      (by rw [hidem, Matrix.polarSupport_mul_polarSupport])
      (nonNormalFixedPointState α ω)
    have horth : ∀ j j', ∑ p, star (ω j p) * ω j' p = if j = j' then 1 else 0 := by
      intro j j'
      split_ifs with h'
      · subst h'
        simp only [ω]
        rw [inner_embedPair_self (hι j), fixedPointPair_norm_sq (hσ j).posSemidef, htr j]
      · exact inner_embedPair_eq_zero_of_disjoint (hdisj j j' h') _ _
    have hβ : (fun _ : Fin b => (1 : ℂ)) ≠ 0 := fun h' => one_ne_zero (congrFun h' 0)
    have hΩ := nonNormalFixedPointState_norm_sq (NeZero.ne M) hβ horth
    rw [← ofReal_sum_norm_sq, ← Complex.ofReal_one] at hΩ
    have hΩ' := Complex.ofReal_injective hΩ
    exact h.trans hΩ'.le
  -- The overlap is at least `|num| / ‖φ_N‖`.
  set t := ‖mpvState A (M * q)‖
  have hov : t⁻¹ * ‖num‖ ≤ ‖nonNormalApproxOverlap A q M α ω‖ := by
    rw [nonNormalApproxOverlap_eq]
    change t⁻¹ * ‖num‖ ≤ ‖((Real.sqrt (∑ τ, ‖v τ‖ ^ 2) : ℂ)⁻¹ * (t : ℂ)⁻¹) * num‖
    rw [norm_mul, norm_mul, norm_inv, norm_inv, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (norm_nonneg _)]
    rcases (Real.sqrt_nonneg (∑ τ, ‖v τ‖ ^ 2)).lt_or_eq with hpos | hzero
    · have hle : Real.sqrt (∑ τ, ‖v τ‖ ^ 2) ≤ 1 := Real.sqrt_le_one.mpr hvle
      have h1 : 1 ≤ (Real.sqrt (∑ τ, ‖v τ‖ ^ 2))⁻¹ := one_le_inv₀ hpos |>.2 hle
      have h2 : 0 ≤ t⁻¹ * ‖num‖ := by positivity
      nlinarith
    · have hv0 : ∀ τ, v τ = 0 := by
        have hsum : ∑ τ, ‖v τ‖ ^ 2 = 0 := by
          have := Real.sqrt_eq_zero'.1 hzero.symm
          linarith [Finset.sum_nonneg fun τ (_ : τ ∈ Finset.univ) => sq_nonneg ‖v τ‖]
        intro τ
        have := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => sq_nonneg ‖v τ‖).1 hsum τ
          (Finset.mem_univ τ)
        simpa using this
      have : num = 0 := Finset.sum_eq_zero fun τ _ => by rw [hv0 τ, star_zero, zero_mul]
      rw [this, norm_zero, mul_zero]
      positivity
  -- Combine.
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne b)
  have hSz : ‖∑ j, z j - (b : ℝ)‖ ≤ ∑ j, ‖z j - 1‖ := by
    have : ∑ j, z j - ((b : ℝ) : ℂ) = ∑ j, (z j - 1) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, mul_one, Complex.ofReal_natCast]
    rw [this]
    exact norm_sum_le _ _
  have hNq : M * q ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hq0
  have hmain := one_sub_norm_div_le_of_norm_sub_le hb1 (norm_nonneg _) hSz
    (hnorm (M * q) hNq)
  have hnum' : t⁻¹ * (‖∑ j, z j‖ / Real.sqrt b) = t⁻¹ * ‖num‖ := by
    rw [hnum, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), div_eq_inv_mul]
  rw [hnum'] at hmain
  have hzj : ∀ j, ‖z j - 1‖ ≤ Cz j * u * Real.exp (S * u) := fun j => by
    refine (hz j q M hq0).trans ?_
    have hCS : Cz j ≤ S :=
      Finset.single_le_sum (f := Cz) (fun j _ => (hCz j).le) (Finset.mem_univ j)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCS hu))
      (mul_nonneg (hCz j).le hu)
  have hδ : ∑ j, ‖z j - 1‖ ≤ S * u * Real.exp (S * u) := by
    refine (Finset.sum_le_sum fun j _ => hzj j).trans_eq ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hη : Kt * x ^ (M * q) ≤ Kt * u := by
    refine mul_le_mul_of_nonneg_left ?_ hKt
    calc x ^ (M * q) ≤ x ^ q := pow_le_pow_of_le_one hx0.le hx1 (Nat.le_mul_of_pos_left q
          (Nat.pos_of_ne_zero (NeZero.ne M)))
      _ ≤ u := le_mul_of_one_le_left (by positivity) hM
  have hexp : 1 ≤ Real.exp ((S + Kt + 1) * u) := Real.one_le_exp (by positivity)
  have he : Real.exp (S * u) ≤ Real.exp ((S + Kt + 1) * u) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hu)
  calc 1 - ‖nonNormalApproxOverlap A q M α ω‖ ≤ 1 - t⁻¹ * ‖num‖ := by linarith
    _ ≤ ∑ j, ‖z j - 1‖ + Kt * x ^ (M * q) := hmain
    _ ≤ S * u * Real.exp (S * u) + Kt * u := add_le_add hδ hη
    _ ≤ (S + Kt + 1) * u * Real.exp ((S + Kt + 1) * u) := by
        have h1 : S * u * Real.exp (S * u) ≤ S * u * Real.exp ((S + Kt + 1) * u) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg hS hu)
        have h2 : Kt * u ≤ Kt * u * Real.exp ((S + Kt + 1) * u) :=
          le_mul_of_one_le_right (mul_nonneg hKt hu) hexp
        have h3 : 0 ≤ u * Real.exp ((S + Kt + 1) * u) := by positivity
        nlinarith

/-- **Approximation error for blocks with overlapping states, `O`-form** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), at the corrected rate): in the setting of
`exists_approximationError_le_overlappingBlockSum`, there is `C` with
`ε ≤ C (N/q) e^{-γ q/ξ}` for every block length `q` and every number of blocks `M ≥ 1`. -/
theorem exists_approximationError_le_mul_overlappingBlockSum [NeZero b]
    (hι : ∀ j, Function.Injective (ι j)) (hdisj : ∀ j j', j ≠ j' → ∀ a a', ι j a ≠ ι j' a')
    (hN : ∀ j, Kraus.IsNormal (Aj j)) (hA : ∀ j, IsLeftCanonical (Aj j))
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosDef)
    (htr : ∀ j, (σ j).trace = 1) (hfix : ∀ j, Kraus.transferMap (Aj j) (σ j) = σ j)
    {lam₂ : ℂ}
    (hlam : ∀ j μ', Module.End.HasEigenvalue (Kraus.transferMap (Aj j)) μ' →
      μ' ≠ 1 → ‖μ'‖ ≤ ‖lam₂‖)
    (hmix : ∀ j j', j ≠ j' → ∀ μ', Module.End.HasEigenvalue (Kraus.mixedMapLM (Aj j) (Aj j')) μ' →
      ‖μ'‖ ≤ ‖lam₂‖)
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q M : ℕ) [NeZero M],
      1 - ‖nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M (ghzAmplitude fun _ => 1)
          (fun j => embedPair (ι j) (fixedPointPair (σ j)))‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_overlappingBlockSum hι hdisj hN hA hσ htr
    hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h q M) ?_
  linarith [norm_nonneg (nonNormalApproxOverlap (blockSum Aj ι fun _ => 1) q M
    (ghzAmplitude fun _ => 1) (fun j => embedPair (ι j) (fixedPointPair (σ j))))]

end MPSTensor
