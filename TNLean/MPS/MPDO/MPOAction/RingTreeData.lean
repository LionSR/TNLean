/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexOfRing
import TNLean.MPS.Operator.Boundary.BoundaryTransport
import TNLean.MPS.Operator.ReductionComposition

/-!
# Exact fusion and action trees over an exact ring

A worked example records its tensors, its analysis maps `V` and its synthesis
maps `W` over a ring `R` with an embedding `f : R →+* ℂ`, such as the golden
or Eisenstein integers. The three defining identities of an exact
biorthogonal decomposition (Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`eq:orthoW`, `eq:orthoV`, `fusiontensors` and `fusiontensors2`, lines
361--391 and 459--490) are then finitely many identities over `R`, decided
there and transported to the complex matrices.

The contractions of fusion and action trees use the Kronecker products
`X ⊗ 1` and `1 ⊗ X` and the bond reassociation; their versions over `R`
commute with the embedding, so a normalized tree contraction is the image of
a trace computed over `R`.

## Main definitions

* `MPSTensor.kronIdR`, `MPSTensor.idKronR`, `MPSTensor.mulTensorAssocInvMatrixR`:
  the Kronecker products with an identity and the bond reassociation over `R`.

## Main statements

* `MPSTensor.isBiorthogonalDecomposition_complexOfRing`: identities over `R`
  give an exact biorthogonal decomposition of the complex images.
* `MPSTensor.complexOfRing_kronIdR`, `MPSTensor.complexOfRing_idKronR`,
  `MPSTensor.complexOfRing_mulTensorAssocInvMatrixR`, `MPSTensor.trace_complexOfRing`:
  the embedding commutes with these operations and with the trace.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {R : Type*} [CommRing R] (f : R →+* ℂ)
  {ι : Type*} [Fintype ι] {d D : ℕ} {δ : ι → ℕ}

/-- **Exact biorthogonal decompositions from identities over an exact ring.**
If the retraction, orthogonality and letter-reconstruction identities hold
over `R`, they hold for the complex images. Source: GLM23,
arXiv:2203.12563v3, `eq:orthoW`, `eq:orthoV`, `fusiontensors` and
`fusiontensors2`, lines 361--391 and 459--490. -/
theorem isBiorthogonalDecomposition_complexOfRing
    (B : Fin d → Matrix (Fin D) (Fin D) R)
    (A : ∀ c : ι, Fin d → Matrix (Fin (δ c)) (Fin (δ c)) R)
    (V : ∀ c : ι, Matrix (Fin (δ c)) (Fin D) R)
    (W : ∀ c : ι, Matrix (Fin D) (Fin (δ c)) R)
    (hretract : ∀ c, V c * W c = 1)
    (horthogonal : ∀ c b, c ≠ b → V c * W b = 0)
    (hletter : ∀ i, B i = ∑ c, W c * A c i * V c) :
    IsBiorthogonalDecomposition (fun i ↦ complexOfRing f (B i))
      (fun c i ↦ complexOfRing f (A c i)) (fun c ↦ complexOfRing f (V c))
      (fun c ↦ complexOfRing f (W c)) where
  retract c := by
    rw [← complexOfRing_mul, hretract, complexOfRing_one]
  orthogonal c b hcb := by
    rw [← complexOfRing_mul, horthogonal c b hcb, complexOfRing_zero]
  letter i := by
    rw [hletter, complexOfRing_sum]
    exact Finset.sum_congr rfl fun c _ ↦ by rw [complexOfRing_mul, complexOfRing_mul]

/-- `X ⊗ 1` over `R`, in the bond order of `MPOTensor.kronId`. -/
def kronIdR {m n : ℕ} (X : Matrix (Fin m) (Fin n) R) (D : ℕ) :
    Matrix (Fin (m * D)) (Fin (n * D)) R :=
  (X ⊗ₖ (1 : Matrix (Fin D) (Fin D) R)).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- `1 ⊗ X` over `R`, in the bond order of `MPOTensor.idKron`. -/
def idKronR {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin (D * m)) (Fin (D * n)) R :=
  ((1 : Matrix (Fin D) (Fin D) R) ⊗ₖ X).submatrix finProdFinEquiv.symm finProdFinEquiv.symm

/-- The inverse bond reassociation over `R`, the permutation matrix of
`MPOTensor.mulTensorAssocInvMatrix`. -/
def mulTensorAssocInvMatrixR (D₁ D₂ D₃ : ℕ) :
    Matrix (Fin (D₁ * (D₂ * D₃))) (Fin (D₁ * D₂ * D₃)) R :=
  (MPOTensor.mulTensorAssocEquiv D₁ D₂ D₃).symm.toPEquiv.toMatrix

@[simp] theorem complexOfRing_kronIdR {m n : ℕ} (X : Matrix (Fin m) (Fin n) R) (D : ℕ) :
    complexOfRing f (kronIdR X D) = MPOTensor.kronId (complexOfRing f X) D := by
  ext i j
  simp only [complexOfRing_apply, kronIdR, MPOTensor.kronId, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

@[simp] theorem complexOfRing_idKronR {m n : ℕ} (D : ℕ) (X : Matrix (Fin m) (Fin n) R) :
    complexOfRing f (idKronR D X) = MPOTensor.idKron D (complexOfRing f X) := by
  ext i j
  simp only [complexOfRing_apply, idKronR, MPOTensor.idKron, Matrix.submatrix_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, map_mul]
  split_ifs <;> simp

@[simp] theorem complexOfRing_mulTensorAssocInvMatrixR (D₁ D₂ D₃ : ℕ) :
    complexOfRing f (mulTensorAssocInvMatrixR D₁ D₂ D₃) =
      MPOTensor.mulTensorAssocInvMatrix D₁ D₂ D₃ := by
  ext i j
  simp only [complexOfRing_apply, mulTensorAssocInvMatrixR,
    MPOTensor.mulTensorAssocInvMatrix, PEquiv.toMatrix_apply]
  split_ifs <;> simp

/-- The trace of the complex image is the image of the trace. -/
@[simp] theorem trace_complexOfRing {n : Type*} [Fintype n] (X : Matrix n n R) :
    (complexOfRing f X).trace = f X.trace := by
  simp [Matrix.trace, map_sum]

end MPSTensor
