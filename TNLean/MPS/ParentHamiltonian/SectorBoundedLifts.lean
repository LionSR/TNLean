/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.BlockSubspaceOverlap

/-!
# Bounded lifts from finitely many subspaces

Suppose a linear map has bounded preimages on each member of a finite family
of subspaces. A lower Gram estimate controls the components of a vector in
their joint space, and hence gives bounded preimages on that joint space.
The bound is independent of the dimensions of the subspaces.

This is a finite-sum consequence of the lower Gram estimate in Nachtergaele,
arXiv:cond-mat/9410110, Lemma `overlapestimate`, lines 2109--2175.
-/

open scoped BigOperators InnerProductSpace
namespace Submodule

variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [Fintype ι]

/-- Bounded preimages on finitely many subspaces and a lower Gram estimate
give bounded preimages on their joint space. The factor two is a convenient
relaxation of the lower Gram bound. Source: Nachtergaele,
arXiv:cond-mat/9410110, Lemma `overlapestimate`, lines 2109--2175. -/
theorem exists_norm_le_preimage_of_mem_iSup_of_lower_gram
    (T : E →ₗ[ℂ] F) (W : ι → Submodule ℂ F)
    (C : ι → ℝ) (hC : ∀ i, 0 ≤ C i)
    (hLower : ∀ v : ∀ i, W i,
      (1 / 2 : ℝ) * (∑ i, ‖(v i : F)‖ ^ 2) ≤ ‖∑ i, (v i : F)‖ ^ 2)
    (hLift : ∀ i, ∀ x ∈ W i, ∃ u, T u = x ∧ ‖u‖ ≤ C i * ‖x‖)
    {x : F} (hx : x ∈ ⨆ i, W i) :
    ∃ u, T u = x ∧ ‖u‖ ≤ 2 * (∑ i, C i) * ‖x‖ := by
  classical
  obtain ⟨v, hv⟩ := exists_sum_eq_of_mem_iSup W hx
  have hGram := hLower v
  rw [hv] at hGram
  have hSumBound : ∑ i, ‖(v i : F)‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 := by
    linarith
  have hvNorm (i : ι) : ‖(v i : F)‖ ≤ 2 * ‖x‖ := by
    have hi : ‖(v i : F)‖ ^ 2 ≤ ∑ j, ‖(v j : F)‖ ^ 2 :=
      Finset.single_le_sum (fun j _ => sq_nonneg ‖(v j : F)‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (v i : F), norm_nonneg x]
  choose u hu hNorm using fun i => hLift i (v i) (v i).property
  refine ⟨∑ i, u i, ?_, ?_⟩
  · simpa only [map_sum, hu] using hv
  · calc
      ‖∑ i, u i‖ ≤ ∑ i, ‖u i‖ := norm_sum_le _ _
      _ ≤ ∑ i, C i * (2 * ‖x‖) := Finset.sum_le_sum fun i _ =>
        (hNorm i).trans (mul_le_mul_of_nonneg_left (hvNorm i) (hC i))
      _ = 2 * (∑ i, C i) * ‖x‖ := by rw [← Finset.sum_mul]; ring

end Submodule
