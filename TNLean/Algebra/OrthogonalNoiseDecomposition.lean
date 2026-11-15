/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Orthogonal decomposition of Kraus coefficient noise

Split a family of middle-block coefficient vectors into its projection
onto the outside coefficient span and an orthogonal residual. Outside
cross correlations are preserved, the middle Gram matrix splits, and the
total noise dimension is the sum of the outside and residual dimensions.
These are the noise-space identities in the cyclic root-selection
arguments for arXiv:1708.00029, Theorem 4.1; no channel selector is asserted.
-/

open Module

namespace KrausNoise

private theorem span_finrank_split {𝕜 E α β : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (u : α → E) (v v₀ v₁ : β → E)
    (hSum : ∀ j, v j = v₀ j + v₁ j)
    (h₀ : ∀ j, v₀ j ∈ Submodule.span 𝕜 (Set.range u))
    (h₁ : ∀ j, v₁ j ∈ (Submodule.span 𝕜 (Set.range u))ᗮ) :
    finrank 𝕜 (Submodule.span 𝕜 (Set.range (Sum.elim u v))) =
      finrank 𝕜 (Submodule.span 𝕜 (Set.range u)) +
        finrank 𝕜 (Submodule.span 𝕜 (Set.range v₁)) := by
  let W := Submodule.span 𝕜 (Set.range u)
  let R := Submodule.span 𝕜 (Set.range v₁)
  let T := Submodule.span 𝕜 (Set.range (Sum.elim u v))
  let _ : CompleteSpace W := FiniteDimensional.complete 𝕜 W
  have hWT : W ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
  have hRT : R ≤ T := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    have hEq : v₁ j = v j - v₀ j := by rw [hSum j]; abel
    rw [hEq]
    exact T.sub_mem (Submodule.subset_span ⟨Sum.inr j, rfl⟩) (hWT (h₀ j))
  have hSpan : T = W ⊔ R := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i | j, rfl⟩
      · exact (show W ≤ W ⊔ R from le_sup_left) (Submodule.subset_span ⟨i, rfl⟩)
      · change v j ∈ W ⊔ R
        rw [hSum j]
        exact (W ⊔ R).add_mem ((show W ≤ W ⊔ R from le_sup_left) (h₀ j))
          ((show R ≤ W ⊔ R from le_sup_right) (Submodule.subset_span ⟨j, rfl⟩))
    · exact sup_le hWT hRT
  have hRorth : R ≤ Wᗮ := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact h₁ j
  have hDisjoint : Disjoint W R := W.isCompl_orthogonal.disjoint.mono_right hRorth
  have hDim := Submodule.finrank_sup_add_finrank_inf_eq W R
  change finrank 𝕜 T = finrank 𝕜 W + finrank 𝕜 R
  rw [hSpan]
  simpa only [hDisjoint.eq_bot, finrank_bot, add_zero] using hDim

/-- Projecting middle-block coefficient vectors onto the outside noise
span preserves the outside cross correlations and separates an
orthogonal residual Gram matrix. The dimensions add exactly. This is
the noise decomposition used in the written cyclic selection argument
for arXiv:1708.00029, Theorem 4.1; the completely positive channel
construction from these identities remains a separate obligation. -/
theorem exists_orthogonal_noise_decomposition {𝕜 E α β : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    (u : α → E) (v : β → E) :
    ∃ v₀ v₁ : β → E,
      (∀ j, v j = v₀ j + v₁ j) ∧
      (∀ j, v₀ j ∈ Submodule.span 𝕜 (Set.range u)) ∧
      (∀ j, v₁ j ∈ (Submodule.span 𝕜 (Set.range u))ᗮ) ∧
      (∀ i j, inner 𝕜 (u i) (v j) = inner 𝕜 (u i) (v₀ j)) ∧
      (∀ i j, inner 𝕜 (v i) (v j) =
        inner 𝕜 (v₀ i) (v₀ j) + inner 𝕜 (v₁ i) (v₁ j)) ∧
      finrank 𝕜 (Submodule.span 𝕜 (Set.range (Sum.elim u v))) =
        finrank 𝕜 (Submodule.span 𝕜 (Set.range u)) +
          finrank 𝕜 (Submodule.span 𝕜 (Set.range v₁)) := by
  let W := Submodule.span 𝕜 (Set.range u)
  let _ : CompleteSpace W := FiniteDimensional.complete 𝕜 W
  let v₀ : β → E := fun j => W.starProjection (v j)
  let v₁ : β → E := fun j => v j - v₀ j
  have hSum (j : β) : v j = v₀ j + v₁ j := by dsimp only [v₁]; abel
  have h₀ (j : β) : v₀ j ∈ W := W.starProjection_apply_mem (v j)
  have h₁ (j : β) : v₁ j ∈ Wᗮ := W.sub_starProjection_mem_orthogonal (v j)
  have hCross (i j : β) : inner 𝕜 (v₀ i) (v₁ j) = 0 := h₁ j (v₀ i) (h₀ i)
  have hCross' (i j : β) : inner 𝕜 (v₁ i) (v₀ j) = 0 :=
    inner_eq_zero_symm.mpr (hCross j i)
  refine ⟨v₀, v₁, hSum, h₀, h₁, ?_, ?_, span_finrank_split u v v₀ v₁ hSum h₀ h₁⟩
  · intro i j
    have hZero : inner 𝕜 (u i) (v₁ j) = 0 :=
      h₁ j (u i) (Submodule.subset_span ⟨i, rfl⟩)
    rw [hSum j, inner_add_right, hZero, add_zero]
  · intro i j
    rw [hSum i, hSum j]
    simp only [inner_add_left, inner_add_right, hCross, hCross', add_zero, zero_add]

end KrausNoise
