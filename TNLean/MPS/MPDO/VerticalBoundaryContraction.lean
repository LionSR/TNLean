/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.VerticalCF

/-!
# Contraction of vertical canonical form with a bond matrix

Appendix C.4 of arXiv:1606.00608 contracts the horizontal bond indices of the
one-site vertical canonical-form identity against an arbitrary matrix $X$.
The resulting physical operator is

\[
  M(X) = U^\dagger
    \left(\bigoplus_\alpha \mu_\alpha \otimes M_\alpha(X)\right) U.
\]

This file records the coefficient-level contraction and proves that, for the
vertically viewed MPO tensor, it is exactly the one-site physical closure from
Definition 4.1.  It also proves that the contraction commutes with the
coisometric change of physical coordinates appearing in vertical canonical
form.

## References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
  Appendix C.4, lines 1955--1976.
-/

open scoped BigOperators Matrix

noncomputable section

namespace MPSTensor

variable {d D R : ℕ}

/-- Contract a matrix $X$ into the paired bond index of a tensor whose
letters are indexed by $\operatorname{Fin}(D^2)$.  The order
$X_{ba} A_{ab}$ agrees with the trace convention
$\operatorname{tr}(A_{ab}X)$.

For a vertical BNT block $M_\alpha$, this is the operator denoted
$M_\alpha(X)$ in arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
def contractBondMatrix (A : MPSTensor (D * D) d) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ where
  toFun X := ∑ ab : Fin (D * D), X ab.modNat ab.divNat • A ab
  map_add' X Y := by
    ext i j
    simp [Matrix.sum_apply, Matrix.smul_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c X := by
    ext i j
    simp [Matrix.sum_apply, Matrix.smul_apply, Finset.mul_sum, mul_assoc]

@[simp]
theorem contractBondMatrix_apply (A : MPSTensor (D * D) d)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    contractBondMatrix A X =
      ∑ ab : Fin (D * D), X ab.modNat ab.divNat • A ab :=
  rfl

/-- Contraction commutes with multiplying every tensor letter on the left and
right by fixed matrices.

This is the linear contraction of the letterwise vertical canonical-form
identity in arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem contractBondMatrix_mul_mul
    (A : MPSTensor (D * D) d) (L : Matrix (Fin R) (Fin d) ℂ)
    (K : Matrix (Fin d) (Fin R) ℂ) (X : Matrix (Fin D) (Fin D) ℂ) :
    contractBondMatrix (fun ab ↦ L * A ab * K) X =
      L * contractBondMatrix A X * K := by
  simp only [contractBondMatrix_apply, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Contracting a bond matrix into a direct-sum tensor gives the direct sum of
the contractions into its blocks, with the same weights.

This is the explicit weighted direct sum
$\bigoplus_\alpha \mu_\alpha\otimes M_\alpha(X)$ in
arXiv:1606.00608, Appendix C.4, lines 1955--1976, with the diagonal entries of
each $\mu_\alpha$ written as repeated blocks. -/
theorem contractBondMatrix_toTensorFromBlocks {r : ℕ} {dim : Fin r → ℕ}
    (μ : Fin r → ℂ) (A : (k : Fin r) → MPSTensor (D * D) (dim k))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    contractBondMatrix (toTensorFromBlocks μ A) X =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k ↦ μ k • contractBondMatrix (A k) X) := by
  ext p q
  simp [contractBondMatrix, toTensorFromBlocks, Matrix.reindex_apply,
    Matrix.blockDiagonal'_apply, Matrix.sum_apply, Matrix.smul_apply,
    Finset.mul_sum, mul_left_comm]

end MPSTensor

namespace MPOTensor

variable {d D R : ℕ}

/-- Contracting a bond matrix into the vertically viewed MPO tensor gives the
one-site physical closure.

Source: arXiv:1606.00608, Definition 4.1, line 657, and Appendix C.4,
lines 1955--1976. -/
theorem contractBondMatrix_verticalTensor_eq_physClose1 (M : MPOTensor d D) :
    MPSTensor.contractBondMatrix (verticalTensor M) = physClose1 M := by
  apply LinearMap.ext
  intro X
  ext i j
  rw [MPSTensor.contractBondMatrix_apply, Matrix.sum_apply]
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  simp [Matrix.trace, Matrix.mul_apply, mul_comm]

/-- The bond-matrix contraction of an assembled vertical tensor is the
weighted block diagonal of the contractions into its repeated BNT blocks.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem contractBondMatrix_verticalAssembledTensor {g : ℕ}
    (dim mult : Fin g → ℕ) (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (X : Matrix (Fin D) (Fin D) ℂ) :
    MPSTensor.contractBondMatrix (verticalAssembledTensor dim mult weight A) X =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun q ↦
          verticalCopyWeights mult weight q •
            MPSTensor.contractBondMatrix (verticalCopyBlocks dim mult A q) X) := by
  exact MPSTensor.contractBondMatrix_toTensorFromBlocks
    (verticalCopyWeights mult weight) (verticalCopyBlocks dim mult A) X

/-- A letterwise vertical canonical-form identity remains valid after
contracting an arbitrary horizontal bond matrix $X$.  On the left, the
contraction is the one-site physical closure $M(X)$; on the right, it is the
weighted direct sum of the sector operators $M_\alpha(X)$.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem mul_physClose1_mul_conjTranspose_of_vertical_forward
    (M : MPOTensor d D) (B : MPSTensor (D * D) R)
    (U : Matrix (Fin R) (Fin d) ℂ)
    (hForward : ∀ ab, U * verticalTensor M ab * Uᴴ = B ab)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    U * physClose1 M X * Uᴴ = MPSTensor.contractBondMatrix B X := by
  rw [← contractBondMatrix_verticalTensor_eq_physClose1]
  rw [← MPSTensor.contractBondMatrix_mul_mul]
  apply congrArg (fun C : MPSTensor (D * D) R ↦
    MPSTensor.contractBondMatrix C X)
  funext ab
  exact hForward ab

/-- The contracted forward identity in vertical canonical coordinates,
written as the explicit weighted direct sum of the sector operators
$M_\alpha(X)$.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem mul_physClose1_mul_conjTranspose_of_verticalAssembledTensor
    (M : MPOTensor d D) {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hForward : ∀ ab,
      U * verticalTensor M ab * Uᴴ = verticalAssembledTensor dim mult weight A ab)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    U * physClose1 M X * Uᴴ =
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun q ↦
          verticalCopyWeights mult weight q •
            MPSTensor.contractBondMatrix (verticalCopyBlocks dim mult A q) X) := by
  rw [mul_physClose1_mul_conjTranspose_of_vertical_forward M
    (verticalAssembledTensor dim mult weight A) U hForward X]
  exact contractBondMatrix_verticalAssembledTensor dim mult weight A X

/-- The contracted reverse identity reconstructs the one-site physical
closure from the weighted vertical sectors.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem physClose1_eq_of_vertical_reconstruction
    (M : MPOTensor d D) (B : MPSTensor (D * D) R)
    (U : Matrix (Fin R) (Fin d) ℂ)
    (hReconstruct : ∀ ab, verticalTensor M ab = Uᴴ * B ab * U)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    physClose1 M X = Uᴴ * MPSTensor.contractBondMatrix B X * U := by
  rw [← contractBondMatrix_verticalTensor_eq_physClose1]
  calc
    MPSTensor.contractBondMatrix (verticalTensor M) X =
        MPSTensor.contractBondMatrix (fun ab ↦ Uᴴ * B ab * U) X := by
      apply congrArg (fun C : MPSTensor (D * D) d ↦
        MPSTensor.contractBondMatrix C X)
      funext ab
      exact hReconstruct ab
    _ = Uᴴ * MPSTensor.contractBondMatrix B X * U :=
      MPSTensor.contractBondMatrix_mul_mul B Uᴴ U X

/-- The one-site physical closure reconstructed from an assembled vertical
canonical form, with its weighted sector direct sum written explicitly.

Source: arXiv:1606.00608, Appendix C.4, lines 1955--1976. -/
theorem physClose1_eq_of_verticalAssembledTensor_reconstruction
    (M : MPOTensor d D) {g : ℕ} (dim mult : Fin g → ℕ)
    (weight : (α : Fin g) → Fin (mult α) → ℂ)
    (A : (α : Fin g) → MPSTensor (D * D) (dim α))
    (U : Matrix
      (Fin (∑ q : Fin (∑ α : Fin g, mult α), verticalCopyDim dim mult q))
      (Fin d) ℂ)
    (hReconstruct : ∀ ab,
      verticalTensor M ab = Uᴴ * verticalAssembledTensor dim mult weight A ab * U)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    physClose1 M X = Uᴴ *
      Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun q ↦
          verticalCopyWeights mult weight q •
            MPSTensor.contractBondMatrix (verticalCopyBlocks dim mult A q) X) * U := by
  rw [physClose1_eq_of_vertical_reconstruction M
    (verticalAssembledTensor dim mult weight A) U hReconstruct X]
  rw [contractBondMatrix_verticalAssembledTensor]

end MPOTensor
