/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockError
import TNLean.MPS.Preparation.RepeatedBlockError
import TNLean.MPS.Preparation.RepeatedOverlappingBlockOverlap

/-!
# The approximation error for repeated blocks with overlapping states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound the
error of the approximating state of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal by
`ε = O((N/q) e^{-γ q/ξ_diag})` for `q = o(N)`. Two corrections are needed in general: for
`m_j ≥ 2` the fixed-point state of eq. (S7) is replaced by the corrected state
`∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` (`TNLean.MPS.Preparation.RepeatedBlockSum`), and when the `q`-site states
of distinct blocks overlap the rate contains the correlation lengths of the mixed transfer maps
(`TNLean.MPS.Preparation.OverlappingBlockError`). This file combines both.

Let the blocks `A_j` be normal in the gauge `∑ᵢ (A_jⁱ)† A_jⁱ = 1` with fixed points `σ_j > 0` of
trace one, let `λ₂` bound the moduli of the eigenvalues other than `1` of every `E_{jj}` and of all
eigenvalues of the mixed transfer maps `E_{jj'}`, `j ≠ j'`, so that `ξ = -1/log|λ₂|` bounds
`ξ_diag` and `ξ_off-diag`, and let `0 < γ < 1/2`. There is `C`, independent of the weights, such
that for all complex weights with `|μ_{j,k}| ≤ 1`, every `q`, and every `M ≥ 1` with
`βⱼ = ∑ₖ μ_{j,k}^N` not all zero,

  `ε ≤ C y e^{C y} / (min(1, b))^{1/2}`,  `y = M e^{-γ q/ξ}`,  `b = ∑ⱼ |βⱼ|²`

(`exists_approximationError_le_repeatedOverlappingBlockSum`). For real weights `0 ≤ μ_{j,k} ≤ 1`
of which one equals `1`, `b ≥ 1` and this is `ε ≤ C y e^{C y}` and `ε ≤ C y`
(`exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg`,
`exists_approximationError_le_mul_repeatedOverlappingBlockSum_of_nonneg`).

The proof: after `V^{⊗M}` the overlap of the corrected state with the target is
`b^{-1/2} ∑ⱼ conj(βⱼ) zⱼ` with `zⱼ = ⟨Ω_j|φ_M(L_jᴴ P)⟩` (`sum_star_copyApproxVector_mul_mpv`);
`V^{⊗M}` does not increase norms and the states `L_j^{⊗M} |Ω_j⟩` are orthonormal
(`sum_norm_sq_copyApproxVector_le`), so normalizing the approximating state can only increase the
overlap; `zⱼ` is `βⱼ` up to `O(y e^{O(y)})`
(`exists_norm_mpvOverlap_sub_bntWeight_le_of_norm_sub_copyPosLimitRow_le` with
`exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le`); and the squared norm of the target
`∑ⱼ βⱼ |φ_N(A_j)⟩` is `b` up to `b K e^{-γ N/ξ}` (`exists_abs_sum_norm_sq_sum_mpv_sub_le`).

**Local fix (corrected fixed-point state):** the approximating state is the corrected state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, not the state of eq. (S7), which fails for `m_j ≥ 2`. Documented
in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

**Local fix (rate of the overlapping blocks):** the rate `e^{-γ q/ξ_diag}` of the source is
replaced by `e^{-γ q/ξ}` with `ξ ≥ max(ξ_diag, ξ_off-diag)`. Documented in
`docs/paper-gaps/mswc24_block_form_mixed_overlap.tex`.

**Scope restriction (cancelling weights):** the bound of
`exists_approximationError_le_repeatedOverlappingBlockSum` carries the factor
`(min(1, b))^{-1/2}`, which is `1` unless the sums `βⱼ = ∑ₖ μ_{j,k}^N` of the weights cancel; the
source's bound has no such factor. Documented in
`docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSTensor.sum_star_copyApproxVector_mul_mpv` — the unnormalized overlap after `V^{⊗M}`.
* `MPSTensor.sum_norm_sq_copyApproxVector_le` — the corrected approximating vector has norm at
  most one.
* `MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum` — Lemma 1'(ii) for
  repeated blocks whose states may overlap, for the corrected state at the corrected rate.
* `MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg`,
  `MPSTensor.exists_approximationError_le_mul_repeatedOverlappingBlockSum_of_nonneg` — the case
  of real weights in `[0, 1]`.

## References

* [MSWC23] D. Malz, G. Styliaris, Z.-Y. Wei, J. I. Cirac,
  *Preparation of matrix product states with log-depth quantum circuits*,
  arXiv:2307.01696, Supplemental Material, eqs. (S2)–(S12) and Lemma 1'(ii)
  (`eq:fid_err_gen_non_normal`).
-/

open scoped Matrix Kronecker ComplexOrder MatrixOrder BigOperators NNReal ENNReal
open Matrix

namespace MPSTensor

variable {d D b : ℕ} {m : Fin b → ℕ} {Dj : Fin b → ℕ}

/-! ### The overlap of the corrected state -/

/-- Applying `Wᴴ^{⊗M}` on the physical legs of the positive part: the tensor read from `Wᴴ P` is
the positive part with `Wᴴ` applied to its physical leg. -/
private theorem ofPhysicalMatrixLM_mul_polarPos {n D' : ℕ} (B : MPSTensor n D)
    (W : Matrix (Fin D × Fin D) (Fin D' × Fin D') ℂ) :
    ofPhysicalMatrixLM (Wᴴ * Matrix.polarPos (physicalMatrix B)) =
      rotatePhysical (Wᴴ.submatrix (virtualPairEquiv D') (virtualPairEquiv D))
        (polarPosTensor B) := by
  refine physicalMatrix_injective ?_
  rw [physicalMatrix_rotatePhysical]
  change (Wᴴ * Matrix.polarPos (physicalMatrix B)).submatrix (virtualPairEquiv D') id =
    Wᴴ.submatrix (virtualPairEquiv D') (virtualPairEquiv D) *
      (Matrix.polarPos (physicalMatrix B)).submatrix (virtualPairEquiv D) id
  rw [Matrix.submatrix_mul_equiv]

/-- **The overlap of the corrected state after `V^{⊗M}`.** For any tensor `A`, matrices `L_j` and
`σ_j`, the unnormalized corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` has overlap
`∑ⱼ conj(αⱼ) ⟨φ_M(P_{σ_j})|φ_M(L_jᴴ P)⟩` with the periodic state of `A` on `N = qM` sites, where
`P` is the positive part of the `q`-site blocked tensor, `L_jᴴ P` is read as a tensor whose
physical leg is the pair of bond indices of block `j`, and `P_{σ_j}` is the fixed-point tensor of
`σ_j` (arXiv:2307.01696, Supplemental Material, eq. (S7), corrected as in
`TNLean.MPS.Preparation.RepeatedBlockSum`). -/
theorem sum_star_copyApproxVector_mul_mpv (A : MPSTensor d D) (q M : ℕ) [NeZero M]
    (α : Fin b → ℂ) (L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ)
    (σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ) :
    ∑ τ, star (copyApproxVector A q M α L σ τ) * mpv A (blockedConfigEquiv d M q τ) =
      ∑ j, star (α j) * mpvOverlap (ofPhysicalMatrixLM ((L j)ᴴ *
        Matrix.polarPos (physicalMatrix (blockTensor A q)))) (fixedPointTensor (σ j)) M := by
  set Bq := blockTensor A q
  set m : (Fin M → Fin D × Fin D) → ℂ := fun c =>
    mpv (polarPosTensor Bq) fun k => (virtualPairEquiv D).symm (c k)
  have hblock : ∀ j, ∑ c, star ((tensorPower M (L j) *ᵥ
      pairProductState (fixedPointPair (σ j))) c) * m c =
      mpvOverlap (ofPhysicalMatrixLM ((L j)ᴴ * Matrix.polarPos (physicalMatrix Bq)))
        (fixedPointTensor (σ j)) M := fun j => by
    have hdot : ∑ c, star ((tensorPower M (L j) *ᵥ
        pairProductState (fixedPointPair (σ j))) c) * m c =
        ∑ c', star (pairProductState (fixedPointPair (σ j)) c') *
          (tensorPower M (L j)ᴴ *ᵥ m) c' := by
      change star (tensorPower M (L j) *ᵥ pairProductState (fixedPointPair (σ j))) ⬝ᵥ m =
        star (pairProductState (fixedPointPair (σ j))) ⬝ᵥ (tensorPower M (L j)ᴴ *ᵥ m)
      rw [star_mulVec, ← dotProduct_mulVec, conjTranspose_tensorPower]
    rw [hdot, ofPhysicalMatrixLM_mul_polarPos, mpvOverlap]
    let e : (Fin M → Fin (Dj j * Dj j)) ≃ (Fin M → Fin (Dj j) × Fin (Dj j)) :=
      Equiv.piCongrRight fun _ => virtualPairEquiv (Dj j)
    let eD : (Fin M → Fin (D * D)) ≃ (Fin M → Fin D × Fin D) :=
      Equiv.piCongrRight fun _ => virtualPairEquiv D
    refine (Fintype.sum_equiv e.symm _ _ fun c => ?_)
    rw [mpv_fixedPointTensor, mpv_rotatePhysical, mul_comm]
    congr 1
    · simp only [mulVec, dotProduct, tensorPower, of_apply, m]
      refine (Fintype.sum_equiv eD.symm _ _ fun c' => ?_)
      simp only [conjTranspose_apply, RCLike.star_def, virtualPairEquiv, Equiv.symm_symm, mpv_eq,
        coeff_eq, Equiv.piCongrRight_symm_apply, Pi.map_apply, submatrix_apply,
        Equiv.symm_apply_apply, mul_eq_mul_left_iff, e, eD]
      left
      rfl
    · simp [e, virtualPairEquiv]
  rw [copyApproxVector, sum_star_tensorPower_polarIso_mulVec_mul_mpv]
  change ∑ c, star (copyFixedPointState α L σ c) * m c = _
  simp only [copyFixedPointState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, star_sum,
    star_mul', Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hblock j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- **The corrected approximating vector has norm at most one.** For isometries `L_j` with
orthogonal ranges, positive semidefinite `σ_j` of trace one, and `β ≠ 0`, the states
`L_j^{⊗M} |Ω_j⟩` are orthonormal, so `∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩` with `αⱼ = βⱼ / (∑ₗ |βₗ|²)^{1/2}` is a
unit vector, and `V^{⊗M}` does not increase norms (`Matrix.sum_norm_sq_tensorPower_mulVec_le`). -/
theorem sum_norm_sq_copyApproxVector_le (A : MPSTensor d D) (q M : ℕ) [NeZero M]
    {β : Fin b → ℂ} (hβ : β ≠ 0)
    {L : (j : Fin b) → Matrix (Fin D × Fin D) (Fin (Dj j) × Fin (Dj j)) ℂ}
    (hiso : ∀ j, (L j)ᴴ * L j = 1) (horth : ∀ j k, j ≠ k → (L j)ᴴ * L k = 0)
    {σ : (j : Fin b) → Matrix (Fin (Dj j)) (Fin (Dj j)) ℂ} (hσ : ∀ j, (σ j).PosSemidef)
    (htr : ∀ j, (σ j).trace = 1) :
    ∑ τ, ‖copyApproxVector A q M (ghzAmplitude β) L σ τ‖ ^ 2 ≤ 1 := by
  classical
  set F : Fin b → (Fin M → Fin D × Fin D) → ℂ :=
    fun j => tensorPower M (L j) *ᵥ pairProductState (fixedPointPair (σ j))
  have horthF : ∀ j k, ∑ c, star (F j c) * F k c = if j = k then 1 else 0 := fun j k => by
    simp only [F]
    rw [sum_star_tensorPower_mulVec_mul]
    split_ifs with h
    · subst h
      rw [hiso, tensorPower_one, one_mulVec,
        pairProductState_fixedPointPair_norm_sq (hσ j) (htr j)]
    · rw [horth j k h, tensorPower_zero (NeZero.ne M), zero_mulVec]
      simp
  have hstate : ((∑ c, ‖copyFixedPointState (M := M) (ghzAmplitude β) L σ c‖ ^ 2 : ℝ) : ℂ) = 1 := by
    rw [ofReal_sum_norm_sq]
    have h := sum_star_sum_mul_sum_of_orthogonal (ghzAmplitude β) (ghzAmplitude β) (fun _ => 1)
      F F horthF
    simp only [mul_one] at h
    rw [ghzAmplitude_norm_sq hβ] at h
    rw [← h]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [copyFixedPointState, F, Finset.sum_apply]
  have hidem := Matrix.conjTranspose_polarIso_mul_polarIso (physicalMatrix (blockTensor A q))
  have h := sum_norm_sq_tensorPower_mulVec_le (M := M)
    (W := Matrix.polarIso (physicalMatrix (blockTensor A q)))
    (by rw [hidem, Matrix.polarSupport_mul_polarSupport]) (copyFixedPointState (ghzAmplitude β) L σ)
  exact h.trans (Complex.ofReal_injective (hstate.trans Complex.ofReal_one.symm)).le

/-! ### The approximation error -/

variable {Aj : (j : Fin b) → MPSTensor d (Dj j)} {ι : (j : Fin b) → Fin (m j) → Fin (Dj j) → Fin D}

open scoped Matrix.Norms.L2Operator in
/-- **Approximation error for repeated blocks with overlapping states** (arXiv:2307.01696,
Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected approximating state at the
corrected rate, in the scope of the module docstring). Let
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` (eq. (S2)), the copy `k` of block `j` placed on the
bond coordinates `ι_{j,k}` with a nonzero weight, let every block `A_j` be normal in the gauge
`∑ᵢ (A_jⁱ)† A_jⁱ = 1`, `E_{A_j}(σ_j) = σ_j`, `σ_j > 0`, `Tr σ_j = 1` (eq. (5)), let `λ₂` bound the
moduli of the eigenvalues other than `1` of every transfer map `E_{A_j}` and the moduli of all
eigenvalues of the mixed transfer maps `E_{jj'}(X) = ∑ᵢ A_jⁱ X (A_{j'}ⁱ)†` of distinct blocks, so
that `ξ = -1/log|λ₂|` bounds `ξ_diag` and `ξ_off-diag`, and let `0 < γ < 1/2`. There is `C > 0`
such that for all weights with `|μ_{j,k}| ≤ 1`, every block length `q`, and every number of
blocks `M ≥ 1` with `N = qM` and `βⱼ = ∑ₖ μ_{j,k}^N` not all zero (eq. (S4)), the error
`ε = 1 - |⟨φ~_N|φ_N⟩|` of the corrected approximating state `V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`
satisfies `ε ≤ C y e^{C y} / (min(1, b))^{1/2}` with `y = M e^{-γ q/ξ}` and `b = ∑ⱼ |βⱼ|²`.

The `q`-site states of distinct blocks need not be orthogonal, and no condition `q = o(N)` is
needed. The factor `(min(1, b))^{-1/2}` is `1` when `b ≥ 1`, for instance for real weights in
`[0, 1]` one of which is `1` (`exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg`);
it enters because the estimates of the overlaps `zⱼ` are absolute, while the sums `βⱼ` may
cancel. -/
theorem exists_approximationError_le_repeatedOverlappingBlockSum
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, (∀ j k, ‖μ j k‖ ≤ 1) → ∀ (q M : ℕ) [NeZero M],
      bntWeight μ (M * q) ≠ 0 →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
            Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) /
          Real.sqrt (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2)) := by
  set x := Real.exp (-γ / correlationLength lam₂) with hx_def
  have hx0 : 0 < x := Real.exp_pos _
  have hxq : ∀ q : ℕ, Real.exp (-γ * q / correlationLength lam₂) = x ^ q := fun q =>
    Real.exp_neg_mul_div_eq_pow _ _ q
  simp_rw [hxq]
  -- The trivial bound `ε ≤ 1`, which suffices whenever `M x^q ≥ 1`.
  have htriv : ∀ (C : ℝ), 1 ≤ C → ∀ (μ : CopyWeights b m) (q M : ℕ) [NeZero M],
      bntWeight μ (M * q) ≠ 0 → 1 ≤ (M : ℝ) * x ^ q →
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) /
          Real.sqrt (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2)) := fun C hC μ q M _ hβ hu => by
    have hs1 : Real.sqrt (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2)) ≤ 1 :=
      Real.sqrt_le_one.2 (min_le_left _ _)
    have h1 : 1 ≤ C * (M * x ^ q) := by nlinarith
    have h2 : 1 ≤ Real.exp (C * (M * x ^ q)) := Real.one_le_exp (by linarith)
    have h3 : 1 ≤ C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) := by nlinarith
    have h4 : 1 ≤ C * (M * x ^ q) * Real.exp (C * (M * x ^ q)) /
        Real.sqrt (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2)) := by
      rcases (Real.sqrt_nonneg (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2))).lt_or_eq with hs | hs
      · rw [le_div_iff₀ hs]; nlinarith
      · rw [← hs, div_zero]
        exfalso
        obtain ⟨l, hl⟩ := Function.ne_iff.1 hβ
        have hp : 0 < ∑ j, ‖bntWeight μ (M * q) j‖ ^ 2 :=
          lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2)
            (Finset.single_le_sum (f := fun j => ‖bntWeight μ (M * q) j‖ ^ 2)
              (fun _ _ => by positivity) (Finset.mem_univ l))
        have : 0 < Real.sqrt (min 1 (∑ j, ‖bntWeight μ (M * q) j‖ ^ 2)) :=
          Real.sqrt_pos.2 (lt_min one_pos hp)
        linarith
    have h5 := norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
      (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)
    linarith
  rcases le_or_gt 1 ‖lam₂‖ with hl | hl
  · -- For `|λ₂| ≥ 1` the rate is at least `1` and the bound is trivial.
    have hx1 : 1 ≤ x := by
      rw [hx_def, neg_div_correlationLength]
      exact Real.one_le_exp (mul_nonneg hγ0.le (Real.log_nonneg hl))
    refine ⟨1, one_pos, fun μ _ q M _ hβ => htriv 1 le_rfl μ q M hβ ?_⟩
    have := one_le_pow₀ hx1 (n := q)
    have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
    nlinarith
  have hx1 : x ≤ 1 := exp_neg_div_correlationLength_le_one hγ0.le hl.le
  obtain ⟨K₁, hK₁, hpos⟩ := exists_norm_polarPos_blockTensor_repeatedBlockSum_sub_le hι hdisj hN
    hA hσ htr hfix hl hlam hmix hγ0 hγ
  have hz : ∀ j, ∃ C : ℝ, 0 < C ∧ (0 < m j → ∀ μ : (j : Fin b) → Fin (m j) → ℂ,
      (∀ k, ‖μ j k‖ ≤ 1) → ∀ (q : ℕ) (G : Matrix (Fin (Dj j) × Fin (Dj j)) (Fin D × Fin D) ℂ)
        (δ : ℝ) (M : ℕ) [NeZero M], ‖G - copyPosLimitRow ι μ q σ j‖ ≤ δ →
      ‖mpvOverlap (ofPhysicalMatrixLM G) (fixedPointTensor (σ j)) M - bntWeight μ (M * q) j‖ ≤
        C * (M * δ) * Real.exp (C * (M * δ))) := fun j => by
    by_cases hm : 0 < m j
    · obtain ⟨C, hC, h⟩ := exists_norm_mpvOverlap_sub_bntWeight_le_of_norm_sub_copyPosLimitRow_le
        hι hdisj (fun j => (hσ j).posSemidef) htr j hm
      exact ⟨C, hC, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose C₀ hC₀ hgen using hz
  obtain ⟨Kt, hKt, hnorm⟩ := exists_abs_sum_norm_sq_sum_mpv_sub_le hN hA hσ htr hfix hl hlam hmix
    hγ0 hγ
  set Cz : Fin b → ℝ := fun j => C₀ j * K₁ + 1
  have hCz : ∀ j, 0 < Cz j := fun j =>
    add_pos_of_nonneg_of_pos (mul_nonneg (hC₀ j).le hK₁) one_pos
  set S := ∑ j, Cz j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => (hCz j).le
  refine ⟨S + Kt + 1, by positivity, fun μ hμ q M _ hβ => ?_⟩
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  set u := (M : ℝ) * x ^ q
  have hu : 0 ≤ u := by positivity
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    exact htriv _ (by linarith) μ 0 M hβ (by simp [hM])
  have hq0 : q ≠ 0 := hq.ne'
  have hD : ∀ j, NeZero (Dj j) := fun j => Matrix.neZero_of_trace_eq_one (htr j)
  -- The ingredients.
  set A := repeatedBlockSum Aj ι μ
  set β := bntWeight μ (M * q)
  set bb : ℝ := ∑ l, ‖β l‖ ^ 2
  have hbb : 0 < bb := by
    obtain ⟨l, hl⟩ := Function.ne_iff.1 hβ
    exact lt_of_lt_of_le (pow_pos (norm_pos_iff.2 hl) 2)
      (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2) (fun _ _ => by positivity)
        (Finset.mem_univ l))
  have hsb : 0 < Real.sqrt bb := Real.sqrt_pos.2 hbb
  have hβle : ∀ j, ‖β j‖ ≤ Real.sqrt bb := fun j =>
    Real.le_sqrt_of_sq_le (Finset.single_le_sum (f := fun j => ‖β j‖ ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ j))
  set P := Matrix.polarPos (physicalMatrix (blockTensor A q))
  set z : Fin b → ℂ := fun j => mpvOverlap (ofPhysicalMatrixLM ((copyIsometry ι μ q j)ᴴ * P))
    (fixedPointTensor (σ j)) M
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
  -- The overlaps of the blocks.
  have hzj : ∀ j, ‖z j - β j‖ ≤ Cz j * u * Real.exp (Cz j * u) := fun j => by
    have hG : ‖(copyIsometry ι μ q j)ᴴ * P - copyPosLimitRow ι μ q σ j‖ ≤ K₁ * x ^ q := by
      rw [← conjTranspose_copyIsometry_mul_copyPosLimit hι hdisj μ q σ j, ← Matrix.mul_sub]
      refine (Matrix.l2_opNorm_mul _ _).trans ?_
      rw [Matrix.l2_opNorm_conjTranspose]
      refine (mul_le_of_le_one_left (norm_nonneg _)
        (Matrix.l2_opNorm_le_one_of_conjTranspose_mul_self_eq_one
          (conjTranspose_copyIsometry_mul_self hι hdisj (μ.weight_fun_ne_zero j) q))).trans ?_
      exact hpos μ hμ q hq0
    have h := hgen j (μ.mult_pos j) μ (hμ j) q _ (K₁ * x ^ q) M hG
    have hre : C₀ j * (M * (K₁ * x ^ q)) = C₀ j * K₁ * u := by simp only [u]; ring
    calc ‖z j - β j‖ ≤ C₀ j * (M * (K₁ * x ^ q)) * Real.exp (C₀ j * (M * (K₁ * x ^ q))) := h
      _ = C₀ j * K₁ * u * Real.exp (C₀ j * K₁ * u) := by rw [hre]
      _ ≤ Cz j * u * Real.exp (Cz j * u) := by
          have : C₀ j * K₁ ≤ Cz j := by simp only [Cz]; linarith
          have h0 : 0 ≤ C₀ j * K₁ := mul_nonneg (hC₀ j).le hK₁
          gcongr
  -- Rescaled overlap and norm.
  set δ' := (∑ j, ‖z j - β j‖) / Real.sqrt bb
  have hSz : ‖Sz / (bb : ℂ) - 1‖ ≤ δ' := by
    have hbbC : (bb : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hbb.ne'
    have hrw : Sz / (bb : ℂ) - 1 = (∑ j, star (β j) * (z j - β j)) / (bb : ℂ) := by
      rw [eq_div_iff hbbC, sub_mul, div_mul_cancel₀ _ hbbC, one_mul]
      simp only [Sz, bb, Complex.ofReal_sum, mul_sub, Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj']
      push_cast
      ring
    rw [hrw, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbb]
    have hsum : ‖∑ j, star (β j) * (z j - β j)‖ ≤ Real.sqrt bb * ∑ j, ‖z j - β j‖ := by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, norm_star]
      exact mul_le_mul_of_nonneg_right (hβle j) (norm_nonneg _)
    rw [div_le_iff₀ hbb]
    calc ‖∑ j, star (β j) * (z j - β j)‖ ≤ Real.sqrt bb * ∑ j, ‖z j - β j‖ := hsum
      _ = δ' * bb := by
          simp only [δ']
          rw [div_mul_eq_mul_div, eq_div_iff hsb.ne']
          conv_rhs => rw [← Real.mul_self_sqrt hbb.le]
          ring
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
  have hmain := one_sub_norm_div_le_of_norm_sub_le (b := 1) le_rfl
    (div_nonneg (norm_nonneg _) hsb.le) (by simpa using hSz) (by simpa using ht2)
  have hkey : (t / Real.sqrt bb)⁻¹ * (‖Sz / (bb : ℂ)‖ / Real.sqrt 1) = t⁻¹ * ‖num‖ := by
    rw [hnum, Real.sqrt_one, div_one, norm_mul, norm_div, norm_inv, Complex.norm_real,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hsb, abs_of_pos hbb,
      inv_div]
    rcases eq_or_ne t 0 with ht | ht
    · simp [ht]
    · field_simp
      rw [Real.sq_sqrt hbb.le, mul_comm]
  rw [hkey] at hmain
  -- Combine.
  set s := Real.sqrt (min 1 bb)
  have hs : 0 < s := Real.sqrt_pos.2 (lt_min one_pos hbb)
  have hs1 : s ≤ 1 := Real.sqrt_le_one.2 (min_le_left _ _)
  have hsbb : s ≤ Real.sqrt bb := Real.sqrt_le_sqrt (min_le_right _ _)
  have hzj' : ∀ j, ‖z j - β j‖ ≤ Cz j * u * Real.exp (S * u) := fun j => by
    refine (hzj j).trans ?_
    have hCS : Cz j ≤ S :=
      Finset.single_le_sum (f := Cz) (fun j _ => (hCz j).le) (Finset.mem_univ j)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hCS hu))
      (mul_nonneg (hCz j).le hu)
  have hδ : ∑ j, ‖z j - β j‖ ≤ S * u * Real.exp (S * u) := by
    refine (Finset.sum_le_sum fun j _ => hzj' j).trans_eq ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hδ' : δ' ≤ S * u * Real.exp (S * u) / s := by
    simp only [δ']
    calc (∑ j, ‖z j - β j‖) / Real.sqrt bb ≤ (∑ j, ‖z j - β j‖) / s :=
          div_le_div_of_nonneg_left (Finset.sum_nonneg fun _ _ => norm_nonneg _) hs hsbb
      _ ≤ S * u * Real.exp (S * u) / s := by gcongr
  have hη : Kt * x ^ (M * q) ≤ Kt * u / s := by
    have h1 : x ^ (M * q) ≤ u := by
      calc x ^ (M * q) ≤ x ^ q := pow_le_pow_of_le_one hx0.le hx1 (Nat.le_mul_of_pos_left q
            (Nat.pos_of_ne_zero (NeZero.ne M)))
        _ ≤ u := le_mul_of_one_le_left (by positivity) hM
    calc Kt * x ^ (M * q) ≤ Kt * u := mul_le_mul_of_nonneg_left h1 hKt
      _ ≤ Kt * u / s := le_div_self (by positivity) hs hs1
  have hexp : 1 ≤ Real.exp ((S + Kt + 1) * u) := Real.one_le_exp (by positivity)
  have he : Real.exp (S * u) ≤ Real.exp ((S + Kt + 1) * u) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (by linarith) hu)
  have hfin : S * u * Real.exp (S * u) + Kt * u ≤
      (S + Kt + 1) * u * Real.exp ((S + Kt + 1) * u) := by
    have h1 : S * u * Real.exp (S * u) ≤ S * u * Real.exp ((S + Kt + 1) * u) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hS hu)
    have h2 : Kt * u ≤ Kt * u * Real.exp ((S + Kt + 1) * u) :=
      le_mul_of_one_le_right (mul_nonneg hKt hu) hexp
    have h3 : 0 ≤ u * Real.exp ((S + Kt + 1) * u) := by positivity
    nlinarith
  calc 1 - ‖copyApproxOverlap A q M (ghzAmplitude β) (copyIsometry ι μ q) σ‖
      ≤ 1 - t⁻¹ * ‖num‖ := by linarith
    _ ≤ δ' + Kt * x ^ (M * q) := hmain
    _ ≤ S * u * Real.exp (S * u) / s + Kt * u / s := add_le_add hδ' hη
    _ = (S * u * Real.exp (S * u) + Kt * u) / s := by rw [add_div]
    _ ≤ (S + Kt + 1) * u * Real.exp ((S + Kt + 1) * u) / s := by gcongr

/-- For real weights `0 ≤ μ_{j,k} ≤ 1`, one of which equals `1`, the weights `βⱼ = ∑ₖ μ_{j,k}^N`
satisfy `∑ⱼ |βⱼ|² ≥ 1`. -/
private theorem one_le_sum_norm_bntWeight_sq {μ : (j : Fin b) → Fin (m j) → ℂ}
    (hμ : ∀ j k, 0 ≤ μ j k) {j₀ : Fin b} {k₀ : Fin (m j₀)} (h₀ : μ j₀ k₀ = 1) (N : ℕ) :
    1 ≤ ∑ j, ‖bntWeight μ N j‖ ^ 2 := by
  have h1 : (1 : ℂ) ≤ bntWeight μ N j₀ := by
    have := Finset.single_le_sum (f := fun k => μ j₀ k ^ N) (fun k _ => pow_nonneg (hμ j₀ k) N)
      (Finset.mem_univ k₀)
    simpa [bntWeight, h₀] using this
  have h2 : 1 ≤ ‖bntWeight μ N j₀‖ := by
    have hre := (Complex.le_def.1 h1).1
    simp only [Complex.one_re] at hre
    exact hre.trans ((le_abs_self _).trans (Complex.abs_re_le_norm _))
  calc (1 : ℝ) ≤ ‖bntWeight μ N j₀‖ ^ 2 := one_le_pow₀ h2
    _ ≤ ∑ j, ‖bntWeight μ N j‖ ^ 2 := Finset.single_le_sum (f := fun j => ‖bntWeight μ N j‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ j₀)

/-- A complex number `0 ≤ z ≤ 1` has `|z| ≤ 1`. -/
private theorem norm_le_one_of_nonneg_of_le_one {z : ℂ} (h0 : 0 ≤ z) (h1 : z ≤ 1) : ‖z‖ ≤ 1 := by
  have him : z.im = 0 := ((Complex.le_def.1 h0).2).symm
  have hz : z = (z.re : ℂ) := Complex.ext rfl (by simp [him])
  rw [hz, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by simpa using (Complex.le_def.1 h0).1)]
  simpa using (Complex.le_def.1 h1).1

/-- **Approximation error for repeated blocks with overlapping states and real weights**
(arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected approximating
state at the corrected rate). In the setting of
`exists_approximationError_le_repeatedOverlappingBlockSum`, there is `C > 0` such that for all
real weights `0 ≤ μ_{j,k} ≤ 1` of which one equals `1` (the normalization of the source, after
eq. (S2)), every block length `q`, and every number of blocks `M ≥ 1`, the error of the corrected
approximating state satisfies `ε ≤ C y e^{C y}` with `y = M e^{-γ q/ξ}`: then `βⱼ ≥ 0` and
`∑ⱼ |βⱼ|² ≥ 1`. -/
theorem exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, (∀ j k, 0 ≤ μ j k ∧ μ j k ≤ 1) →
      (∃ j k, μ j k = 1) → ∀ (q M : ℕ) [NeZero M],
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) *
          Real.exp (C * (M * Real.exp (-γ * q / correlationLength lam₂))) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum hι hdisj hN hA
    hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C, hC, fun μ hμ ⟨j₀, k₀, h₀⟩ q M _ => ?_⟩
  have hb := one_le_sum_norm_bntWeight_sq (fun j k => (hμ j k).1) h₀ (M * q)
  have hβ : bntWeight μ (M * q) ≠ 0 := fun h' => by
    rw [h'] at hb
    norm_num at hb
  have h' := h μ (fun j k => norm_le_one_of_nonneg_of_le_one (hμ j k).1 (hμ j k).2) q M hβ
  rwa [min_eq_left hb, Real.sqrt_one, div_one] at h'

/-- **Approximation error for repeated blocks with overlapping states and real weights,
`O`-form** (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii), eq. (S12), for the corrected
approximating state at the corrected rate): in the setting of
`exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg`, there is `C` with
`ε ≤ C M e^{-γ q/ξ}`, which is `C (N/q) e^{-γ q/ξ}` for `q ≥ 1`. -/
theorem exists_approximationError_le_mul_repeatedOverlappingBlockSum_of_nonneg
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
    {γ : ℝ} (hγ0 : 0 < γ) (hγ : γ < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ μ : CopyWeights b m, (∀ j k, 0 ≤ μ j k ∧ μ j k ≤ 1) →
      (∃ j k, μ j k = 1) → ∀ (q M : ℕ) [NeZero M],
      1 - ‖copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
          (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ‖ ≤
        C * (M * Real.exp (-γ * q / correlationLength lam₂)) := by
  obtain ⟨C, hC, h⟩ := exists_approximationError_le_repeatedOverlappingBlockSum_of_nonneg hι hdisj
    hN hA hσ htr hfix hlam hmix hγ0 hγ
  refine ⟨C * Real.exp C + 1, by positivity, fun μ hμ hμ1 q M _ => ?_⟩
  refine le_mul_of_le_mul_exp_of_le hC.le zero_le_one (by positivity) (h μ hμ hμ1 q M) ?_
  linarith [norm_nonneg (copyApproxOverlap (repeatedBlockSum Aj ι μ) q M
    (ghzAmplitude (bntWeight μ (M * q))) (copyIsometry ι μ q) σ)]

end MPSTensor
