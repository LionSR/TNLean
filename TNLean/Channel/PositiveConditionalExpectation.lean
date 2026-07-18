/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.HermitianHelpers
import TNLean.Channel.PartialTrace
import TNLean.Channel.PositiveFunctional
import TNLean.Channel.WolfProps

/-!
# Positive conditional expectations onto one matrix factor

This file determines the form of a positive linear retraction from a matrix algebra onto
the unital subalgebra consisting of the identity on the left tensor factor and an arbitrary
matrix on the right tensor factor.

## Main results

* `Matrix.extractRightFactorMap`: the right matrix factor of the image of a linear map.
* `Matrix.exists_density_of_positive_retraction_onto_right_factor`: the one-factor form of
  a positive conditional expectation.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Proposition 1.5 and
  Equation (1.40)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder Kronecker
open Matrix

namespace Matrix

variable {m d : ℕ} [NeZero m]

/-- Extract the right matrix factor from the image of a linear map by restricting to one
diagonal block in the left tensor factor.

For maps whose image consists of matrices of the form $1_m\otimes X$, this restriction is
the unique matrix $X$. This is the factor restriction used in Wolf, Proposition 1.5. -/
noncomputable def extractRightFactorMap
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun A := (E A).submatrix (fun j ↦ (0, j)) (fun j ↦ (0, j))
  map_add' A B := by
    ext i j
    simp
  map_smul' c A := by
    ext i j
    simp

@[simp]
theorem extractRightFactorMap_apply
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) (i j : Fin d) :
    extractRightFactorMap E A i j = E A (0, i) (0, j) :=
  rfl

/-- If the image of $E$ lies in $1_m\otimes M_d(\mathbb C)$, then the extracted right
factor reconstructs the whole image.

This is the one-factor range restriction in Wolf, Proposition 1.5. -/
theorem eq_one_kronecker_extractRightFactorMap
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hRange : ∀ A, ∃ X : Matrix (Fin d) (Fin d) ℂ,
      E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ extractRightFactorMap E A := by
  obtain ⟨X, hX⟩ := hRange A
  have hExtract : extractRightFactorMap E A = X := by
    ext i j
    simp [hX]
  rw [hX, hExtract]

/-- Positivity passes from a map with range in $1_m\otimes M_d(\mathbb C)$ to its
extracted right-factor map.

This is the positivity restriction used in Wolf, Proposition 1.5. -/
theorem extractRightFactorMap_posSemidef
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hE : IsPositiveMap E) (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hA : A.PosSemidef) :
    (extractRightFactorMap E A).PosSemidef := by
  exact (hE A hA).submatrix (fun j ↦ (0, j))

/-- If $E$ fixes $1_m\otimes M_d(\mathbb C)$ pointwise, then its extracted right-factor
map sends $1_m\otimes X$ to $X$.

This is the one-factor retraction condition in Wolf, Proposition 1.5. -/
theorem extractRightFactorMap_one_kronecker
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hFix : ∀ X : Matrix (Fin d) (Fin d) ℂ,
      E ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) =
        (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (X : Matrix (Fin d) (Fin d) ℂ) :
    extractRightFactorMap E
      ((1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X) = X := by
  ext i j
  simp [hFix]

/-- A scalar action on simple tensors determines the extracted map on every matrix as a
weighted partial trace.

The calculation is the one-factor part of Equation (1.40) following Wolf,
Proposition 1.5. -/
theorem extractRightFactorMap_eq_weighted_partialTrace
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ) (ρ : Matrix (Fin m) (Fin m) ℂ)
    (hρ : ∀ Y : Matrix (Fin m) (Fin m) ℂ, f Y = (ρ * Y).trace)
    (hScalar : ∀ (Y : Matrix (Fin m) (Fin m) ℂ)
      (X : Matrix (Fin d) (Fin d) ℂ),
      extractRightFactorMap E (Y ⊗ₖ X) = f Y • X)
    (A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) :
    extractRightFactorMap E A =
      Matrix.partialTraceLeft
        ((ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * A) := by
  classical
  refine Matrix.induction_on' A ?_ ?_ ?_
  · ext i j
    simp [Matrix.partialTraceLeft_apply]
  · intro A B hA hB
    rw [map_add, hA, hB]
    ext i j
    simp [Matrix.partialTraceLeft_apply, Matrix.mul_add, Finset.sum_add_distrib]
  · rintro ⟨i, j⟩ ⟨k, l⟩ c
    have hSingle :
        (Matrix.single (i, j) (k, l) c :
          Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ) =
          Matrix.single i k c ⊗ₖ Matrix.single j l 1 := by
      rw [Matrix.single_kronecker_single]
      simp
    rw [hSingle]
    rw [hScalar, hρ]
    rw [← Matrix.traceLeft_kronecker]
    simp only [Matrix.traceLeft]
    rw [← Matrix.mul_kronecker_mul]
    simp

/-- A normalized positive scalar action on simple tensors is represented by a density
matrix and gives the weighted-partial-trace form of the whole map.

This is the final functional representation step in Wolf, Proposition 1.5 and
Equation (1.40). -/
theorem exists_density_of_scalar_action
    (E : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ)
    (hRange : ∀ A, ∃ X : Matrix (Fin d) (Fin d) ℂ,
      E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ X)
    (f : Matrix (Fin m) (Fin m) ℂ →ₗ[ℂ] ℂ)
    (hPositive : ∀ Y : Matrix (Fin m) (Fin m) ℂ,
      Y.PosSemidef → (0 : ℂ) ≤ f Y)
    (hOne : f 1 = 1)
    (hScalar : ∀ (Y : Matrix (Fin m) (Fin m) ℂ)
      (X : Matrix (Fin d) (Fin d) ℂ),
      extractRightFactorMap E (Y ⊗ₖ X) = f Y • X) :
    ∃ ρ : Matrix (Fin m) (Fin m) ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ A : Matrix (Fin m × Fin d) (Fin m × Fin d) ℂ,
        E A = (1 : Matrix (Fin m) (Fin m) ℂ) ⊗ₖ
          Matrix.partialTraceLeft
            ((ρ ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ)) * A) := by
  obtain ⟨ρ, hρ, hρtrace, hRepresentation⟩ :=
    Matrix.exists_density_of_positive_functional f hPositive hOne
  refine ⟨ρ, hρ, hρtrace, fun A ↦ ?_⟩
  rw [eq_one_kronecker_extractRightFactorMap E hRange A]
  rw [extractRightFactorMap_eq_weighted_partialTrace E f ρ hRepresentation hScalar A]

end Matrix
