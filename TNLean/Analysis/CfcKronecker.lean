/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sirui Lu
-/
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.Order

/-!
# Continuous functional calculus through the unital tensor embeddings

The unital tensor embeddings $A \mapsto A \otimes \mathbf 1$ and
$B \mapsto \mathbf 1 \otimes B$ are continuous star-algebra homomorphisms of the
finite-dimensional matrix algebra. Because the continuous functional calculus
commutes with continuous star-algebra homomorphisms (`StarAlgHomClass.map_cfc`),
applying a real function $f$ through either embedding agrees with applying it to
the embedded factor:
$$f(A \otimes \mathbf 1) = f(A) \otimes \mathbf 1, \qquad
  f(\mathbf 1 \otimes B) = \mathbf 1 \otimes f(B).$$

These are pure matrix facts about the functional calculus on Kronecker products.
They are gathered here, at the foundational analysis layer, so that the relative
entropy stack and the operator convexity boundary can both use them without
either depending on the other.

## Main results

* `Matrix.cfc_kronecker_one` — the continuous functional calculus through the
  unital left tensor embedding: $f(A \otimes \mathbf 1) = f(A) \otimes \mathbf 1$.
* `Matrix.cfc_one_kronecker` — the right embedding version:
  $f(\mathbf 1 \otimes B) = \mathbf 1 \otimes f(B)$.
-/

open scoped Kronecker

namespace Matrix

variable {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- The unital left tensor embedding $A \mapsto A \otimes \mathbf 1$ as a star
algebra homomorphism of complex matrix algebras. -/
noncomputable def leftKroneckerEmbed :
    Matrix m m ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun A := A ⊗ₖ (1 : Matrix n n ℂ)
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := zero_kronecker _
  map_add' A B := add_kronecker A B _
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      smul_kronecker, one_kronecker_one]
  map_star' A := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_kronecker,
      conjTranspose_one]

@[simp] theorem leftKroneckerEmbed_apply (A : Matrix m m ℂ) :
    leftKroneckerEmbed (n := n) A = A ⊗ₖ (1 : Matrix n n ℂ) := rfl

/-- The unital right tensor embedding $B \mapsto \mathbf 1 \otimes B$ as a star
algebra homomorphism of complex matrix algebras. -/
noncomputable def rightKroneckerEmbed :
    Matrix n n ℂ →⋆ₐ[ℂ] Matrix (m × n) (m × n) ℂ where
  toFun B := (1 : Matrix m m ℂ) ⊗ₖ B
  map_one' := one_kronecker_one
  map_mul' A B := by rw [← mul_kronecker_mul, mul_one]
  map_zero' := kronecker_zero _
  map_add' A B := kronecker_add _ A B
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      kronecker_smul, one_kronecker_one]
  map_star' B := by
    rw [star_eq_conjTranspose, star_eq_conjTranspose, conjTranspose_kronecker,
      conjTranspose_one]

@[simp] theorem rightKroneckerEmbed_apply (B : Matrix n n ℂ) :
    rightKroneckerEmbed (m := m) B = (1 : Matrix m m ℂ) ⊗ₖ B := rfl

/-- **Functional calculus through the left tensor embedding.** For a Hermitian
matrix $A$ and a real function $f$,
$f(A \otimes \mathbf 1) = f(A) \otimes \mathbf 1$. This is the instance of
`StarAlgHomClass.map_cfc` at the unital embedding `leftKroneckerEmbed`. -/
theorem cfc_kronecker_one {A : Matrix m m ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f (A ⊗ₖ (1 : Matrix n n ℂ)) = (cfc f A) ⊗ₖ (1 : Matrix n n ℂ) := by
  have hcont : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (leftKroneckerEmbed (m := m) (n := n)) :=
    LinearMap.continuous_of_finiteDimensional
      ((leftKroneckerEmbed (m := m) (n := n) :
        Matrix m m ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ))
  have hsa : IsSelfAdjoint A := hA
  have hsa' : IsSelfAdjoint (leftKroneckerEmbed (n := n) A) := by
    rw [leftKroneckerEmbed_apply, IsSelfAdjoint, star_eq_conjTranspose,
      conjTranspose_kronecker, hA.eq, conjTranspose_one]
  simpa [leftKroneckerEmbed_apply] using
    (StarAlgHomClass.map_cfc (leftKroneckerEmbed (m := m) (n := n)) f A
      hcont hcontφ hsa hsa').symm

/-- **Functional calculus through the right tensor embedding.** For a Hermitian
matrix $B$ and a real function $f$,
$f(\mathbf 1 \otimes B) = \mathbf 1 \otimes f(B)$. This is the instance of
`StarAlgHomClass.map_cfc` at the unital embedding `rightKroneckerEmbed`. -/
theorem cfc_one_kronecker {B : Matrix n n ℂ} (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((1 : Matrix m m ℂ) ⊗ₖ B) = (1 : Matrix m m ℂ) ⊗ₖ (cfc f B) := by
  have hcont : ContinuousOn f (spectrum ℝ B) := B.finite_real_spectrum.continuousOn f
  have hcontφ : Continuous (rightKroneckerEmbed (m := m) (n := n)) :=
    LinearMap.continuous_of_finiteDimensional
      ((rightKroneckerEmbed (m := m) (n := n) :
        Matrix n n ℂ →ₗ[ℂ] Matrix (m × n) (m × n) ℂ))
  have hsa : IsSelfAdjoint B := hB
  have hsa' : IsSelfAdjoint (rightKroneckerEmbed (m := m) B) := by
    rw [rightKroneckerEmbed_apply, IsSelfAdjoint, star_eq_conjTranspose,
      conjTranspose_kronecker, hB.eq, conjTranspose_one]
  simpa [rightKroneckerEmbed_apply] using
    (StarAlgHomClass.map_cfc (rightKroneckerEmbed (m := m) (n := n)) f B
      hcont hcontφ hsa hsa').symm

end Matrix
