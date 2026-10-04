/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.ExactMPSGappedPhase
import TNLean.MPS.Symmetry.GappedInteractionPathComposition

/-!
# Concatenation of continuous exact MPS ground states

Two exact ground-state realizations with the same ambient bond dimension
and equal tensors at their common endpoint concatenate continuously.
Source context: arXiv:1010.3732, Sections II.C and II.F.2.
-/

namespace MPSTensor

private theorem synchronized_trans_mem
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {x₀ x₁ x₂ : X} {y₀ y₁ y₂ : Y}
    (P : Path x₀ x₁) (R : Path x₁ x₂)
    (A : Path y₀ y₁) (B : Path y₁ y₂)
    (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
    (∃ t : unitInterval,
      (P.trans R).extend γ = P t ∧ (A.trans B).extend γ = A t) ∨
    (∃ t : unitInterval,
      (P.trans R).extend γ = R t ∧ (A.trans B).extend γ = B t) := by
  rw [Path.extend_apply _ hγ, Path.extend_apply _ hγ,
    Path.trans_apply, Path.trans_apply]
  by_cases h : γ ≤ 1 / 2
  · refine Or.inl ⟨⟨2 * γ, by constructor <;> linarith [hγ.1, hγ.2]⟩, ?_⟩
    simp only [dite_eq_left h, and_self]
  · refine Or.inr ⟨⟨2 * γ - 1, by constructor <;> linarith [hγ.1, hγ.2]⟩, ?_⟩
    simp only [dite_eq_right h, and_self]

/-- Continuous exact MPS ground families concatenate when their ambient
bond dimensions agree and their joining tensors are literally equal.
Source context: arXiv:1010.3732, Sections II.C and II.F.2. -/
noncomputable def ExactMPSGroundPath.trans
    {G : Type} [Group G] {d : ℕ}
    {U : G →* Matrix.unitaryGroup (Fin d) ℂ}
    {h₀ h₁ h₂ : MPOTensor.ChainOperator d 2}
    {P : SymmetricGappedInteractionPath U h₀ h₁}
    {R : SymmetricGappedInteractionPath U h₁ h₂}
    (Q : ExactMPSGroundPath P) (S : ExactMPSGroundPath R)
    (hD : Q.bondDimension = S.bondDimension)
    (hTensor : HEq (Q.tensor 1) (S.tensor 0)) :
    ExactMPSGroundPath (P.trans R) := by
  rcases Q with ⟨D, hDpos, A, hA, hInjA, hneA, hLineA⟩
  rcases S with ⟨D', hDpos', B, hB, hInjB, hneB, hLineB⟩
  dsimp only at hD hTensor
  subst D'
  have hAB : A 1 = B 0 := eq_of_heq hTensor
  let aPath : Path (A 0) (A 1) := Path.ofLine hA rfl rfl
  let bPath : Path (A 1) (B 1) := Path.ofLine hB hAB.symm rfl
  let T := aPath.trans bPath
  have hmem (γ : ℝ) (hγ : γ ∈ Set.Icc (0 : ℝ) 1) :
      (∃ t ∈ Set.Icc (0 : ℝ) 1,
        (P.trans R).interaction γ = P.interaction t ∧ T.extend γ = A t) ∨
      (∃ t ∈ Set.Icc (0 : ℝ) 1,
        (P.trans R).interaction γ = R.interaction t ∧ T.extend γ = B t) := by
    rcases synchronized_trans_mem P.toPath R.toPath aPath bPath γ hγ with
      ⟨t, hPt, hAt⟩ | ⟨t, hRt, hBt⟩
    · exact Or.inl ⟨t, t.property, hPt, hAt⟩
    · exact Or.inr ⟨t, t.property, hRt, hBt⟩
  refine ⟨D, hDpos, T.extend, T.continuous_extend.continuousOn, ?_, ?_, ?_⟩
  · intro γ hγ
    rcases hmem γ hγ with ⟨t, ht, _, hT⟩ | ⟨t, ht, _, hT⟩
    · rw [hT]; exact hInjA t ht
    · rw [hT]; exact hInjB t ht
  · intro γ hγ N hN
    rcases hmem γ hγ with ⟨t, ht, _, hT⟩ | ⟨t, ht, _, hT⟩
    · rw [hT]; exact hneA t ht N hN
    · rw [hT]; exact hneB t ht N hN
  · intro γ hγ N hN
    rcases hmem γ hγ with ⟨t, ht, hP, hT⟩ | ⟨t, ht, hR, hT⟩
    · rw [hP, hT]; exact hLineA t ht N hN
    · rw [hR, hT]; exact hLineB t ht N hN

end MPSTensor
