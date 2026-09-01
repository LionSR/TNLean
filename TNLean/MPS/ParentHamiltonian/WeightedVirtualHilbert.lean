/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.FrobeniusHilbert
import QICLean.Analysis.MatrixSqrt

/-!
# Weighted virtual matrix Hilbert space

A positive-definite matrix `ρ` equips the virtual matrix algebra with the
inner product

`⟪X, Y⟫_ρ = Matrix.trace (ρ * Xᴴ * Y)`.

This module activates Mathlib's weighted matrix norm and inner product locally
and identifies the resulting Hilbert space isometrically with the Euclidean
space of matrix entries. The isometry sends `X` to the Frobenius vectorization
of `X * CFC.sqrt ρ`; its inverse multiplies on the right by `(CFC.sqrt ρ)⁻¹`.

The weighted inner product is equation (5.6) of Fannes--Nachtergaele--Werner,
*Communications in Mathematical Physics* 144 (1992), 443--490,
DOI 10.1007/BF02099178. No estimate from the subsequent lemmas is asserted here.

## Main declarations

* `Matrix.rhoWeighted_inner`: the weighted inner-product formula in the source convention.
* `Matrix.rhoWeighted_norm_sq`: the corresponding squared-norm formula.
* `Matrix.rhoWeightedEquivEuclidean`: the linear isometric Euclidean identification.
* `Matrix.rhoWeightedEquivEuclidean_apply`: its forward formula.
* `Matrix.rhoWeightedEquivEuclidean_symm_apply`: its inverse formula.
-/

open scoped ComplexOrder Matrix MatrixOrder Matrix.Norms.Frobenius

namespace Matrix

noncomputable section

private noncomputable def frobeniusLinearEquiv (D : ℕ) :
    Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) :=
  (Matrix.frobeniusEquivEuclidean (Fin D) (Fin D)).toLinearEquiv

private theorem inner_frobeniusLinearEquiv
    {D : ℕ} (X Y : Matrix (Fin D) (Fin D) ℂ) :
    inner ℂ (frobeniusLinearEquiv D X) (frobeniusLinearEquiv D Y) =
      Matrix.trace (Xᴴ * Y) :=
  Matrix.inner_frobeniusEquivEuclidean X Y

-- Use the seminormed parent of the weighted normed structure below. This keeps the
-- norm hierarchy coherent while overriding the ambient Frobenius instances.

/-- Mathlib's weighted matrix inner product agrees, by cyclicity of the trace,
with the convention `Tr(ρ Xᴴ Y)` in FNW 1992, equation (5.6). -/
theorem rhoWeighted_inner {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef) (X Y : Matrix (Fin D) (Fin D) ℂ) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    inner ℂ X Y = Matrix.trace (ρ * Xᴴ * Y) := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  change Matrix.trace (Y * ρ * Xᴴ) = Matrix.trace (ρ * Xᴴ * Y)
  exact (Matrix.trace_mul_cycle ρ Xᴴ Y).symm

/-- The squared weighted norm is the real part of `Tr(ρ Xᴴ X)`. -/
theorem rhoWeighted_norm_sq {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ)
    (hρ : ρ.PosDef) (X : Matrix (Fin D) (Fin D) ℂ) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    ‖X‖ ^ 2 = (Matrix.trace (ρ * Xᴴ * X)).re := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  calc
    ‖X‖ ^ 2 = (inner ℂ X X).re := (inner_self_eq_norm_sq (𝕜 := ℂ) X).symm
    _ = (Matrix.trace (ρ * Xᴴ * X)).re :=
      congrArg Complex.re (rhoWeighted_inner ρ hρ X X)

private theorem inner_rightMul_cfcSqrt
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    inner ℂ (frobeniusLinearEquiv D (X * CFC.sqrt ρ))
        (frobeniusLinearEquiv D (Y * CFC.sqrt ρ)) = inner ℂ X Y := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rw [inner_frobeniusLinearEquiv, rhoWeighted_inner ρ hρ]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_cfc_sqrt]
  calc
    Matrix.trace (CFC.sqrt ρ * Xᴴ * (Y * CFC.sqrt ρ)) =
        Matrix.trace (CFC.sqrt ρ * (Xᴴ * Y) * CFC.sqrt ρ) := by
          simp only [Matrix.mul_assoc]
    _ = Matrix.trace (CFC.sqrt ρ * CFC.sqrt ρ * (Xᴴ * Y)) :=
      Matrix.trace_mul_cycle (CFC.sqrt ρ) (Xᴴ * Y) (CFC.sqrt ρ)
    _ = Matrix.trace (ρ * Xᴴ * Y) := by
      rw [CFC.sqrt_mul_sqrt_self ρ hρ.posSemidef.nonneg]
      simp only [Matrix.mul_assoc]

/-- Right multiplication by `sqrt ρ`, followed by Frobenius vectorization,
is a complex linear isometric equivalence from the `ρ`-weighted matrix space
to the Euclidean space of its entries. -/
noncomputable def rhoWeightedEquivEuclidean
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    Matrix (Fin D) (Fin D) ℂ ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin D × Fin D) := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  exact {
    toFun X := frobeniusLinearEquiv D (X * CFC.sqrt ρ)
    invFun x := (frobeniusLinearEquiv D).symm x * (CFC.sqrt ρ)⁻¹
    map_add' X Y := by
      rw [Matrix.add_mul, map_add]
    map_smul' c X := by
      rw [Matrix.smul_mul, map_smul]
      rfl
    left_inv X := by
      change (frobeniusLinearEquiv D).symm
          (frobeniusLinearEquiv D (X * CFC.sqrt ρ)) * (CFC.sqrt ρ)⁻¹ = X
      rw [(frobeniusLinearEquiv D).symm_apply_apply, Matrix.mul_assoc,
        Matrix.mul_nonsing_inv _ hρ.isUnit_det_cfc_sqrt, Matrix.mul_one]
    right_inv x := by
      change frobeniusLinearEquiv D
          (((frobeniusLinearEquiv D).symm x * (CFC.sqrt ρ)⁻¹) * CFC.sqrt ρ) = x
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hρ.isUnit_det_cfc_sqrt, Matrix.mul_one,
        (frobeniusLinearEquiv D).apply_symm_apply]
    norm_map' X := by
      have hsquare : ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ ^ 2 = ‖X‖ ^ 2 := by
        calc
          ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ ^ 2 =
              (inner ℂ (frobeniusLinearEquiv D (X * CFC.sqrt ρ))
                (frobeniusLinearEquiv D (X * CFC.sqrt ρ))).re :=
            (inner_self_eq_norm_sq (𝕜 := ℂ)
              (frobeniusLinearEquiv D (X * CFC.sqrt ρ))).symm
          _ = (inner ℂ X X).re :=
            congrArg Complex.re (inner_rightMul_cfcSqrt ρ hρ X X)
          _ = ‖X‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) X
      change ‖frobeniusLinearEquiv D (X * CFC.sqrt ρ)‖ = ‖X‖
      nlinarith [norm_nonneg (frobeniusLinearEquiv D (X * CFC.sqrt ρ)), norm_nonneg X]
  }

/-- The weighted Euclidean equivalence sends `X` to the Frobenius vectorization
of `X * sqrt ρ`. -/
@[simp]
theorem rhoWeightedEquivEuclidean_apply
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    rhoWeightedEquivEuclidean ρ hρ X =
      WithLp.toLp 2 (X * CFC.sqrt ρ).vec := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rfl

/-- The inverse weighted Euclidean equivalence applies inverse Frobenius
vectorization and then multiplies on the right by `(sqrt ρ)⁻¹`. -/
@[simp]
theorem rhoWeightedEquivEuclidean_symm_apply
    {D : ℕ} (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (x : EuclideanSpace ℂ (Fin D × Fin D)) :
    letI : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixNormedAddCommGroup ρ hρ
    letI : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
      (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
    letI : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
      Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
    (rhoWeightedEquivEuclidean ρ hρ).symm x =
      Matrix.of (fun i j => WithLp.ofLp x (j, i)) * (CFC.sqrt ρ)⁻¹ := by
  let : NormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixNormedAddCommGroup ρ hρ
  let : SeminormedAddCommGroup (Matrix (Fin D) (Fin D) ℂ) :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  let : InnerProductSpace ℂ (Matrix (Fin D) (Fin D) ℂ) :=
    Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  rfl

end

end Matrix
