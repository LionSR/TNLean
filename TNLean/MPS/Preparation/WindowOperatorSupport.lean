/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Spectrum
import TNLean.MPS.MPDO.PhysicalGibbsEmbedding
import TNLean.MPS.Preparation.LocalCircuit
import TNLean.MPS.Preparation.WindowCorrelator

/-!
# Operators on windows of a chain: algebra, norm and support

The chapter's proof of the depth lower bound (`thm:ldp_depth_lower_bound`, the
chapter's version of arXiv:2307.01696, Theorem 1) places a fixed operator on many
windows of consecutive sites of the chain and uses three facts about the resulting
operators:

* placing an operator on a window is a unital `*`-homomorphism, so it preserves
  products and adjoints and does not increase the operator norm
  (`chainWindowOperator_mul`, `chainWindowOperator_conjTranspose`,
  `norm_toEuclideanCLM_chainWindowOperator_le`);
* an operator on a window inside a larger window is an operator on the smaller
  window (`chainWindowOperator_chainWindowOperator`);
* an operator on the window of sites `a, …, a + L - 1` acts on those sites in the sense
  of the light-cone file `TNLean.MPS.Preparation.LocalCircuit`
  (`chainWindowOperator_mem_supportedOperators`).

All windows here are windows that do not wrap around the ring: `a + L ≤ N`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d : ℕ}

/-- On a window that does not wrap around, `chainWindowOperator` is the unital algebra
homomorphism `MPOTensor.embedLocalOperatorAlgHom`. This is the placement of the operators
`𝒪₁`, `𝒪'ₛ` of arXiv:2307.01696, Supplemental Material, proof of Theorem 1, on sites of
the chain. -/
theorem chainWindowOperator_eq_embedLocalOperatorAlgHom {L N a : ℕ} (ha : a < N)
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a X =
      MPOTensor.embedLocalOperatorAlgHom (d := d) L N (by omega) ⟨a, ha⟩ X := by
  rw [chainWindowOperator, dite_eq_left ⟨by omega, ha⟩]
  rfl

/-- Placing operators on a window preserves products (arXiv:2307.01696, Supplemental
Material, proof of Theorem 1). -/
theorem chainWindowOperator_mul {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a (X * Y) = chainWindowOperator N a X * chainWindowOperator N a Y := by
  simp only [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL, map_mul]

/-- Placing operators on a window is additive (arXiv:2307.01696, Supplemental Material,
proof of Theorem 1). -/
theorem chainWindowOperator_sub {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N)
    (X Y : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a (X - Y) = chainWindowOperator N a X - chainWindowOperator N a Y := by
  simp only [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL, map_sub]

/-- Placing operators on a window is homogeneous (arXiv:2307.01696, Supplemental Material,
proof of Theorem 1). -/
theorem chainWindowOperator_smul {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N) (c : ℂ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a (c • X) = c • chainWindowOperator N a X := by
  simp only [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL, map_smul]

/-- The window operator of `X - c` is the window operator of `X` minus `c`: the centred
observables `𝒪 - ⟨𝒪⟩` of the chapter's proof of `thm:ldp_depth_lower_bound`
(arXiv:2307.01696, Supplemental Material, proof of Theorem 1). -/
theorem chainWindowOperator_sub_smul_one {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N) (c : ℂ)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a (X - c • 1) = chainWindowOperator N a X - c • 1 := by
  rw [chainWindowOperator_sub ha haL, chainWindowOperator_smul ha haL,
    chainWindowOperator_one ha haL]

/-- Placing operators on a window commutes with the adjoint (arXiv:2307.01696,
Supplemental Material, proof of Theorem 1). -/
theorem chainWindowOperator_conjTranspose {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a Xᴴ = (chainWindowOperator N a X)ᴴ := by
  simp only [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL]
  exact MPOTensor.embedLocalOperator_conjTranspose L N _ _ X

/-- A Hermitian operator placed on a window is Hermitian (arXiv:2307.01696, Supplemental
Material, proof of Theorem 1, Hermitian observables `𝒪₁`, `𝒪'ₛ`). -/
theorem chainWindowOperator_isHermitian {L N a : ℕ} (ha : a < N) (haL : a + L ≤ N)
    {X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ} (hX : X.IsHermitian) :
    (chainWindowOperator N a X).IsHermitian := by
  rw [Matrix.IsHermitian, ← chainWindowOperator_conjTranspose ha haL, hX.eq]

/-- Placing operators on a window as a unital `*`-algebra homomorphism. -/
noncomputable def chainWindowStarAlgHom (L N a : ℕ) (ha : a < N) (haL : a + L ≤ N) :
    Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ →⋆ₐ[ℂ] Matrix (Cfg d N) (Cfg d N) ℂ where
  toAlgHom := MPOTensor.embedLocalOperatorAlgHom (d := d) L N (by omega) ⟨a, ha⟩
  map_star' X := by
    change MPOTensor.embedLocalOperatorAlgHom (d := d) L N _ _ Xᴴ =
      (MPOTensor.embedLocalOperatorAlgHom (d := d) L N _ _ X)ᴴ
    exact MPOTensor.embedLocalOperator_conjTranspose L N _ _ X

/-- Placing an operator on a window does not increase its operator norm, since a
`*`-homomorphism of C⋆-algebras is contractive. This bounds the norms of the translated
observables in the chapter's proof of `thm:ldp_depth_lower_bound` (arXiv:2307.01696,
Supplemental Material, proof of Theorem 1, "observables of norm one"). -/
theorem norm_toEuclideanCLM_chainWindowOperator_le {L N a : ℕ} (ha : a < N)
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (chainWindowOperator N a X)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin L → Fin d) (𝕜 := ℂ) X‖ := by
  open scoped Matrix.Norms.L2Operator in
  have h := NonUnitalStarAlgHom.norm_apply_le (chainWindowStarAlgHom (d := d) L N a ha haL) X
  rw [Matrix.cstar_norm_def, Matrix.cstar_norm_def] at h
  rw [chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL]
  exact h

/-- **Nested windows.** An operator on the window of sites `b, …, b + L - 1` of a chain of
`w` sites, placed on the window `a, …, a + w - 1` of a chain of `N` sites, is the operator
on the window `a + b, …, a + b + L - 1`. This identifies the block operators of the
chapter's proof of `thm:ldp_depth_lower_bound` (arXiv:2307.01696, Supplemental Material,
proof of Theorem 1) with products of translated observables. -/
theorem chainWindowOperator_chainWindowOperator {L w N a b : ℕ} (ha : a < N)
    (haw : a + w ≤ N) (hb : b < w) (hbL : b + L ≤ w)
    (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a (chainWindowOperator w b X) = chainWindowOperator N (a + b) X := by
  classical
  ext τ σ
  rw [chainWindowOperator_apply ha haw,
    chainWindowOperator_apply (N := N) (a := a + b) (by omega) (by omega)]
  have hX : ∀ ν : Cfg d N, (fun j : Fin L ↦
      (fun i : Fin w ↦ ν ⟨a + i.val, by omega⟩) ⟨b + j.val, by omega⟩) =
      fun j : Fin L ↦ ν ⟨a + b + j.val, by omega⟩ := by
    intro ν
    funext j
    exact congrArg ν (Fin.ext (by simp only; omega))
  by_cases h₁ : ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + w) → τ k = σ k
  · rw [ite_eq_left h₁, chainWindowOperator_apply hb hbL]
    by_cases h₂ : ∀ k : Fin w, ¬ (b ≤ k.val ∧ k.val < b + L) →
        τ ⟨a + k.val, by omega⟩ = σ ⟨a + k.val, by omega⟩
    · rw [ite_eq_left h₂, ite_eq_left]
      · exact congrArg₂ X (hX τ) (hX σ)
      intro k hk
      by_cases hkw : a ≤ k.val ∧ k.val < a + w
      · have := h₂ ⟨k.val - a, by omega⟩ (by simp only; omega)
        simpa [show a + (k.val - a) = k.val by omega] using this
      · exact h₁ k hkw
    · rw [ite_eq_right h₂, ite_eq_right]
      intro h
      exact h₂ fun k hk ↦ h _ (by simp only; omega)
  · rw [ite_eq_right h₁, ite_eq_right]
    intro h
    exact h₁ fun k hk ↦ h k (by omega)

/-- **Support of a window operator.** The operator `X` placed on the sites
`a, …, a + L - 1` acts on those sites in the sense of `MPSPreparation.supportedOperators`.
This is what the light cone of arXiv:2307.01696, Supplemental Material, proof of
Theorem 1, is applied to. -/
theorem chainWindowOperator_mem_supportedOperators {L N a : ℕ} (ha : a < N)
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a X ∈
      MPSPreparation.supportedOperators d {k : Fin N | a ≤ k.val ∧ k.val < a + L} := by
  classical
  set S : Set (Fin N) := {k : Fin N | a ≤ k.val ∧ k.val < a + L}
  have hunit : ∀ τ₀ σ₀ : Fin L → Fin d,
      chainWindowOperator N a (Matrix.single τ₀ σ₀ (1 : ℂ)) ∈
        MPSPreparation.supportedOperators d S := by
    intro τ₀ σ₀
    let m : Fin N → Matrix (Fin d) (Fin d) ℂ := fun k ↦
      if h : a ≤ k.val ∧ k.val < a + L then
        Matrix.single (τ₀ ⟨k.val - a, by omega⟩) (σ₀ ⟨k.val - a, by omega⟩) 1
      else 1
    have hm : ∀ k ∉ S, m k = 1 := fun k hk ↦ dite_eq_right hk
    have heq : chainWindowOperator N a (Matrix.single τ₀ σ₀ (1 : ℂ)) = Matrix.finKronecker m := by
      ext τ σ
      rw [chainWindowOperator_apply ha haL, Matrix.finKronecker_apply]
      by_cases hc : (∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k) ∧
          τ₀ = (fun j : Fin L ↦ τ ⟨a + j.val, by omega⟩) ∧
          σ₀ = (fun j : Fin L ↦ σ ⟨a + j.val, by omega⟩)
      · obtain ⟨h1, h2, h3⟩ := hc
        rw [ite_eq_left h1, Matrix.single_apply, ite_eq_left ⟨h2, h3⟩]
        symm
        refine Finset.prod_eq_one fun k _ ↦ ?_
        simp only [m]
        by_cases hk : a ≤ k.val ∧ k.val < a + L
        · rw [dite_eq_left hk, Matrix.single_apply, ite_eq_left]
          have hk' : a + (k.val - a) = k.val := by omega
          constructor
          · rw [h2]; exact congrArg τ (Fin.ext (by simp only; omega))
          · rw [h3]; exact congrArg σ (Fin.ext (by simp only; omega))
        · rw [dite_eq_right hk, Matrix.one_apply, ite_eq_left (h1 k hk)]
      · symm
        rw [not_and_or, not_and_or] at hc
        rcases hc with hc | hc | hc
        · simp only [not_forall] at hc
          obtain ⟨k, hk, hne⟩ := hc
          rw [ite_eq_right (fun h ↦ hne (h k hk))]
          refine Finset.prod_eq_zero (Finset.mem_univ k) ?_
          simp only [m]
          rw [dite_eq_right hk, Matrix.one_apply, ite_eq_right hne]
        · have hne : ∃ j : Fin L, τ₀ j ≠ τ ⟨a + j.val, by omega⟩ := by
            by_contra h
            push Not at h
            exact hc (funext h)
          obtain ⟨j, hj⟩ := hne
          by_cases h1 : ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k
          · rw [ite_eq_left h1, Matrix.single_apply, ite_eq_right (fun h ↦ hc h.1)]
            refine Finset.prod_eq_zero (Finset.mem_univ (⟨a + j.val, by omega⟩ : Fin N)) ?_
            simp only [m]
            rw [dite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + L by omega), Matrix.single_apply,
              ite_eq_right]
            rintro ⟨h, -⟩
            refine hj (Eq.trans ?_ h)
            exact congrArg τ₀ (Fin.ext (by simp only; omega))
          · rw [ite_eq_right h1]
            refine Finset.prod_eq_zero (Finset.mem_univ (⟨a + j.val, by omega⟩ : Fin N)) ?_
            simp only [m]
            rw [dite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + L by omega), Matrix.single_apply,
              ite_eq_right]
            rintro ⟨h, -⟩
            refine hj (Eq.trans ?_ h)
            exact congrArg τ₀ (Fin.ext (by simp only; omega))
        · have hne : ∃ j : Fin L, σ₀ j ≠ σ ⟨a + j.val, by omega⟩ := by
            by_contra h
            push Not at h
            exact hc (funext h)
          obtain ⟨j, hj⟩ := hne
          by_cases h1 : ∀ k : Fin N, ¬ (a ≤ k.val ∧ k.val < a + L) → τ k = σ k
          · rw [ite_eq_left h1, Matrix.single_apply, ite_eq_right (fun h ↦ hc h.2)]
            refine Finset.prod_eq_zero (Finset.mem_univ (⟨a + j.val, by omega⟩ : Fin N)) ?_
            simp only [m]
            rw [dite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + L by omega), Matrix.single_apply,
              ite_eq_right]
            rintro ⟨-, h⟩
            refine hj (Eq.trans ?_ h)
            exact congrArg σ₀ (Fin.ext (by simp only; omega))
          · rw [ite_eq_right h1]
            refine Finset.prod_eq_zero (Finset.mem_univ (⟨a + j.val, by omega⟩ : Fin N)) ?_
            simp only [m]
            rw [dite_eq_left (show a ≤ a + j.val ∧ a + j.val < a + L by omega), Matrix.single_apply,
              ite_eq_right]
            rintro ⟨-, h⟩
            refine hj (Eq.trans ?_ h)
            exact congrArg σ₀ (Fin.ext (by simp only; omega))
    rw [heq]
    exact MPSPreparation.finKronecker_mem_supportedOperators hm
  have hX : X = ∑ τ₀ : Fin L → Fin d, ∑ σ₀ : Fin L → Fin d,
      X τ₀ σ₀ • Matrix.single τ₀ σ₀ (1 : ℂ) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hX, chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL, map_sum]
  refine Submodule.sum_mem _ fun τ₀ _ ↦ ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun σ₀ _ ↦ ?_
  rw [map_smul, ← chainWindowOperator_eq_embedLocalOperatorAlgHom ha haL]
  exact Submodule.smul_mem _ _ (hunit τ₀ σ₀)

end MPSTensor
