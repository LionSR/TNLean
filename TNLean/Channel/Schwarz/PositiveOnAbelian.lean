/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Schwarz.KadisonSchwarz

/-!
# Positive maps on commuting / abelian matrix domains

This file records the finite-dimensional matrix-endomorphism scaffold around Wolf
Proposition 1.6: a positive map is completely positive when restricted to a
commutative `*`-subalgebra.

For the current TNLean pipeline we isolate the concrete matrix ingredients needed
later for the normal-operator Schwarz inequality. The key definition
`IsPositiveOnCommuting` is phrased in terms of quadratic forms of block matrices
whose images under the map commute pairwise.

The main amplification theorem is currently left as a placeholder
`quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` with a
`-- Wolf Prop 1.6` marker. The surrounding algebraic helper lemmas about the
normal generators `{A, Aᴴ, Aᴴ * A, 1}` are proved and are intended to support
later refinements toward Wolf Proposition 5.1.
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix Finset Complex

namespace PositiveOnAbelian

variable {D : ℕ}

/-- Quadratic-form positivity for a block matrix with matrix entries.

This is the concrete finite-dimensional formulation of positivity used in the
current file: for every block vector `ψ`, the quadratic form of the block matrix
is nonnegative. -/
def BlockPositive {n D : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ ψ : Fin n → Fin D → ℂ,
    0 ≤ ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (a i j).mulVec (ψ j)

/-- The block images of `a` under `T` commute pairwise. -/
def PairwiseCommuteImages {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)) : Prop :=
  ∀ i j k l, Commute (T (a i j)) (T (a k l))

/-- The quadratic form obtained after applying a linear map `T` blockwise. -/
noncomputable def blockQuadraticForm {n D : ℕ}
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ)
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ψ : Fin n → Fin D → ℂ) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n, star (ψ i) ⬝ᵥ (T (a i j)).mulVec (ψ j)

/-- A map is **positive on commuting block families** if it preserves
block-quadratic-form positivity whenever the image family is pairwise commuting.

This is the concrete stand-in for “the restriction to a commutative
`*`-subalgebra is completely positive” that is sufficient for the normal-input
Schwarz argument used later in the project. -/
def IsPositiveOnCommuting
    (T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∀ {n : ℕ} (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ)),
    BlockPositive a →
    PairwiseCommuteImages T a →
    ∀ ψ : Fin n → Fin D → ℂ, 0 ≤ blockQuadraticForm T a ψ

section NormalGenerators

variable {A : Matrix (Fin D) (Fin D) ℂ}

/-- A normal matrix commutes with its adjoint. -/
theorem commute_conjTranspose_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute A Aᴴ := by
  simpa [Commute] using hA.symm

/-- For a normal matrix `A`, the generator `A` commutes with `Aᴴ * A`. -/
theorem commute_conjTranspose_mul_self_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute A (Aᴴ * A) := by
  exact (commute_conjTranspose_of_normal (A := A) hA).mul_right (Commute.refl A)

/-- For a normal matrix `A`, the generator `Aᴴ` commutes with `Aᴴ * A`. -/
theorem conjTranspose_commute_conjTranspose_mul_self_of_normal
    (hA : Aᴴ * A = A * Aᴴ) : Commute Aᴴ (Aᴴ * A) := by
  exact (Commute.refl Aᴴ).mul_right
    (Commute.symm (commute_conjTranspose_of_normal (A := A) hA))

/-- For a normal matrix `A`, the generators `{A, Aᴴ, Aᴴ * A, 1}` commute pairwise. -/
theorem normal_generators_pairwise_commute
    (hA : Aᴴ * A = A * Aᴴ) :
    Commute A Aᴴ ∧
      Commute A (Aᴴ * A) ∧
      Commute A (1 : Matrix (Fin D) (Fin D) ℂ) ∧
      Commute Aᴴ (Aᴴ * A) ∧
      Commute Aᴴ (1 : Matrix (Fin D) (Fin D) ℂ) ∧
      Commute (Aᴴ * A) (1 : Matrix (Fin D) (Fin D) ℂ) := by
  refine ⟨commute_conjTranspose_of_normal (A := A) hA, ?_⟩
  refine ⟨commute_conjTranspose_mul_self_of_normal (A := A) hA, ?_⟩
  refine ⟨Commute.one_right A, ?_⟩
  refine ⟨conjTranspose_commute_conjTranspose_mul_self_of_normal (A := A) hA, ?_⟩
  exact ⟨Commute.one_right Aᴴ, Commute.one_right (Aᴴ * A)⟩

end NormalGenerators

/-- Wolf Proposition 1.6 in the block-quadratic-form form used later in the
pipeline: positivity upgrades to positivity of every finite amplification once
all block images commute pairwise. -/
theorem quadraticForm_nonneg_of_isPositiveMap_of_commuting_images
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {n : ℕ}
    (a : Matrix (Fin n) (Fin n) (Matrix (Fin D) (Fin D) ℂ))
    (ha : BlockPositive a)
    (hcomm : PairwiseCommuteImages T a)
    (ψ : Fin n → Fin D → ℂ) :
    0 ≤ blockQuadraticForm T a ψ := by
  -- Wolf Prop 1.6
  sorry

/-- A positive map is positive on commuting block families.

This packages `quadraticForm_nonneg_of_isPositiveMap_of_commuting_images` into a
single reusable predicate. -/
theorem isPositiveOnCommuting_of_isPositiveMap
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T) :
    IsPositiveOnCommuting T := by
  intro n a ha hcomm ψ
  exact quadraticForm_nonneg_of_isPositiveMap_of_commuting_images hT a ha hcomm ψ

/-- Wolf Proposition 1.6 / Proposition 5.1 interface for normal inputs.

This is the concrete normal-operator Schwarz inequality needed later: if `T` is
positive and subunital on the identity, then normal inputs satisfy the usual
Kadison--Schwarz conclusion. -/
theorem map_conjTranspose_mul_map_le_of_normal_of_subunital
    {T : Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ}
    (hT : IsPositiveMap T)
    {A : Matrix (Fin D) (Fin D) ℂ}
    (hA : Aᴴ * A = A * Aᴴ)
    (h_subunital : T 1 ≤ (1 : Matrix (Fin D) (Fin D) ℂ)) :
    T Aᴴ * T A ≤ T (Aᴴ * A) := by
  -- Wolf Prop 1.6
  sorry

end PositiveOnAbelian
