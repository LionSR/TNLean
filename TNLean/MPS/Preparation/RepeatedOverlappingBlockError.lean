/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.OverlappingBlockError
import TNLean.MPS.Preparation.RepeatedOverlappingBlockOverlap

/-!
# The corrected state for repeated blocks with overlapping states

Malz, Styliaris, Wei, and Cirac (arXiv:2307.01696, Supplemental Material, Lemma 1'(ii)) bound the
error of the approximating state of eq. (S7) for a tensor
`Aⁱ = ⊕ⱼ diag(μ_{j,1}, …, μ_{j,m_j}) ⊗ A_jⁱ` that is not normal. For `m_j ≥ 2` the fixed-point
state of eq. (S7) is replaced by the corrected state `∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`
(`TNLean.MPS.Preparation.RepeatedBlockSum`). This file proves the two steps of the error bound
that hold for any blocks, whether or not their `q`-site states overlap: after `V^{⊗M}` the overlap
of the corrected state with the target is `∑ⱼ conj(αⱼ) zⱼ` with `zⱼ = ⟨Ω_j|φ_M(L_jᴴ P)⟩`
(`sum_star_copyApproxVector_mul_mpv`), and `V^{⊗M}` does not increase norms while the states
`L_j^{⊗M} |Ω_j⟩` are orthonormal (`sum_norm_sq_copyApproxVector_le`), so normalizing the
approximating state can only increase the overlap. The error bound itself is
`MPSTensor.exists_approximationError_le_repeatedOverlappingBlockSum`
(`TNLean.MPS.Preparation.RepeatedOverlappingBlockWeights`).

**Local fix (corrected fixed-point state):** the approximating state is the corrected state
`V^{⊗M} ∑ⱼ αⱼ L_j^{⊗M} |Ω_j⟩`, not the state of eq. (S7), which fails for `m_j ≥ 2`. Documented
in `docs/paper-gaps/mswc24_repeated_block_corrected_state.tex`.

## Main declarations

* `MPSTensor.sum_star_copyApproxVector_mul_mpv` — the unnormalized overlap after `V^{⊗M}`.
* `MPSTensor.sum_norm_sq_copyApproxVector_le` — the corrected approximating vector has norm at
  most one.

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

end MPSTensor
