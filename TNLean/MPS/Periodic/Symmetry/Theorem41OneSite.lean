/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Symmetry.Theorem41Defs
import TNLean.MPS.Periodic.EqualCaseGlobal

/-!
# The one-site boundary of periodic refinement

For one-site blocking, the physical alphabet is merely reindexed. Thus every
matrix product tensor is one-refinable, whereas one-divisibility of its transfer
map asserts that the transfer map is trace preserving. This gives a direct
formal test of the missing trace-preservation hypothesis in the printed
forward implication of arXiv:1708.00029, Theorem 4.1, lines 717--731. See
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- Every tensor is one-refinable: the one-site blocking is a permutation of
physical labels. Source: arXiv:1708.00029, lines 719--724. -/
theorem isPRefinable_one {d D : ℕ} (B : MPSTensor d D) : IsPRefinable B 1 := by
  classical
  let E : Fin d ≃ Fin (blockPhysDim d 1) := (singleBlockEquiv d).symm
  let W : Matrix (Fin (blockPhysDim d 1)) (Fin d) ℂ := permMatrixOfEquiv E
  refine ⟨B, W, ?_, ?_⟩
  · have h : Wᴴ = Wᵀ := by
      ext i j
      simp [W, permMatrixOfEquiv, Matrix.conjTranspose_apply, Matrix.transpose_apply]
    rw [h]
    exact permMatrixOfEquiv_transpose_mul E
  · intro N τ
    change mpv (blockTensor B 1) τ =
      ∑ σ : Fin N → Fin d, (∏ k : Fin N, W (τ k) (σ k)) * mpv B σ
    rw [mpv_blockTensor_one]
    rw [Finset.sum_eq_single (fun x => E.symm (τ x))]
    · simp [W, permMatrixOfEquiv, E]
    · intro σ _ hσ
      have hcoord : ∃ k : Fin N, σ k ≠ E.symm (τ k) := by
        by_contra h
        simp only [not_exists, not_ne_iff] at h
        exact hσ (funext h)
      obtain ⟨k, hk⟩ := hcoord
      have hne : τ k ≠ E (σ k) := by
        intro he
        exact hk ((E.symm_apply_apply (σ k)).symm.trans (congrArg E.symm he.symm))
      have hz : W (τ k) (σ k) = 0 := by simp [W, permMatrixOfEquiv, hne]
      have hp : (∏ x : Fin N, W (τ x) (σ x)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ k) hz
      simp [hp]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- One-divisibility is precisely the channel condition. In particular,
one-refinability alone cannot imply one-divisibility unless the transfer map is
trace preserving. Source: arXiv:1708.00029, lines 717--731; the missing
hypothesis is recorded in
`docs/paper-gaps/dccsp17_thm41_forward_trace_preservation.tex`. -/
theorem isPDivisibleChannel_one_iff {D : ℕ}
    (E : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) :
    IsPDivisibleChannel E 1 ↔ IsChannel E := by
  constructor
  · rintro ⟨E', hE', hpow⟩
    simpa using hpow ▸ hE'
  · intro hE
    exact ⟨E, hE, by simp⟩

end MPSTensor
