/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.GappedInteractionPath
import Mathlib.Topology.Path

/-!
# Concatenation of symmetric gapped interaction paths

The common-space path condition of arXiv:1010.3732,
`sec:phases-definition-no-sym` and `sec:def-sym-phases`, is transitive.
Concatenation preserves the local norm bound and symmetry, and the minimum
of the two positive spectral-gap bounds is a uniform bound for the result.
-/

namespace MPSTensor.SymmetricGappedInteractionPath

variable {G : Type} [Group G] {d : ℕ}
variable {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
variable {h₀ h₁ h₂ : MPOTensor.ChainOperator d 2}

/-- Restriction of the interaction to the parameter interval, regarded as
a continuous path. Source: arXiv:1010.3732, lines 413–426. -/
noncomputable def toPath (P : SymmetricGappedInteractionPath U h₀ h₁) : Path h₀ h₁ :=
  Path.ofLine P.continuous P.interaction_zero P.interaction_one

/-- Concatenate the two continuous interactions and extend constantly beyond
the parameter interval. Source: arXiv:1010.3732, lines 413–426. -/
noncomputable def concatenatedInteraction
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (Q : SymmetricGappedInteractionPath U h₁ h₂) :
    ℝ → MPOTensor.ChainOperator d 2 :=
  (P.toPath.trans Q.toPath).extend

/-- Each interaction in a concatenation occurs on one of the two original
paths. Source: arXiv:1010.3732, lines 413–426. -/
theorem concatenatedInteraction_mem
    (P : SymmetricGappedInteractionPath U h₀ h₁)
    (Q : SymmetricGappedInteractionPath U h₁ h₂) (γ : ℝ) :
    (∃ t ∈ Set.Icc (0 : ℝ) 1,
      P.concatenatedInteraction Q γ = P.interaction t) ∨
    (∃ t ∈ Set.Icc (0 : ℝ) 1,
      P.concatenatedInteraction Q γ = Q.interaction t) := by
  have h : P.concatenatedInteraction Q γ ∈
      Set.range P.toPath ∪ Set.range Q.toPath := by
    rw [← Path.trans_range, ← Path.extend_range]
    exact Set.mem_range_self γ
  rcases h with ⟨t, ht⟩ | ⟨t, ht⟩
  · exact Or.inl ⟨t, t.property, ht.symm⟩
  · exact Or.inr ⟨t, t.property, ht.symm⟩

/-- Concatenating symmetric gapped paths preserves a uniform positive gap.
Source: arXiv:1010.3732, `sec:phases-definition-no-sym` and
`sec:def-sym-phases`. -/
noncomputable def trans (P : SymmetricGappedInteractionPath U h₀ h₁)
    (Q : SymmetricGappedInteractionPath U h₁ h₂) :
    SymmetricGappedInteractionPath U h₀ h₂ where
  interaction := P.concatenatedInteraction Q
  interaction_zero := Path.extend_zero _
  interaction_one := Path.extend_one _
  hermitian γ _ := by
    rcases P.concatenatedInteraction_mem Q γ with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · rw [heq]; exact P.hermitian t ht
    · rw [heq]; exact Q.hermitian t ht
  norm_le_one γ _ := by
    rcases P.concatenatedInteraction_mem Q γ with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · rw [heq]; exact P.norm_le_one t ht
    · rw [heq]; exact Q.norm_le_one t ht
  continuous := (P.toPath.trans Q.toPath).continuous_extend.continuousOn
  gap := by
    obtain ⟨δ₀, hδ₀, hgap₀⟩ := P.gap
    obtain ⟨δ₁, hδ₁, hgap₁⟩ := Q.gap
    refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, ?_⟩
    intro γ _ N hN
    rcases P.concatenatedInteraction_mem Q γ with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · rw [heq]
      obtain ⟨E, hE, hspec⟩ := hgap₀ t ht N hN
      exact ⟨E, hE, fun z hz => ⟨(hspec z hz).1,
        (hspec z hz).2.imp id (fun h => (add_le_add (le_refl E) (min_le_left δ₀ δ₁)).trans h)⟩⟩
    · rw [heq]
      obtain ⟨E, hE, hspec⟩ := hgap₁ t ht N hN
      exact ⟨E, hE, fun z hz => ⟨(hspec z hz).1,
        (hspec z hz).2.imp id (fun h => (add_le_add (le_refl E) (min_le_right δ₀ δ₁)).trans h)⟩⟩
  symmetric γ _ g N hN := by
    rcases P.concatenatedInteraction_mem Q γ with ⟨t, ht, heq⟩ | ⟨t, ht, heq⟩
    · rw [heq]; exact P.symmetric t ht g N hN
    · rw [heq]; exact Q.symmetric t ht g N hN

end MPSTensor.SymmetricGappedInteractionPath
