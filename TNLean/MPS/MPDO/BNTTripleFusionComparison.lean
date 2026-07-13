/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BNTLeftTripleFusion
import TNLean.MPS.MPDO.BNTRightTripleFusion

/-!
# Comparison of the two triple-fusion parenthesizations

The two iterated fusion isometries identify the left- and right-associated
triple product tensors with doubly indexed direct sums. The canonical
reassociation matrix \(A_{\alpha,\beta,\gamma}\) between their bond spaces gives
the full comparison

\[
  C_{\alpha,\beta,\gamma}
    = U^{\mathrm L}_{\alpha,\beta,\gamma}
      A_{\alpha,\beta,\gamma}
      (U^{\mathrm R}_{\alpha,\beta,\gamma})^\dagger.
\]

When the trace-power coefficients are independent of the positive chain
length, every positive diagonal matrix \(\chi_{\alpha,\beta,\gamma}\) is an
identity matrix. The comparison then intertwines the two unweighted doubly
indexed direct sums, letter by letter.

This is the full isometry comparison underlying the fixed-final
\(F\)-transformation in the associativity argument of arXiv:1511.08090. No
restriction to a fixed final label, invertibility assertion,
\(F\)-transformation, or pentagon identity is made here. The fixed-label
extraction in that source additionally uses a simultaneous left inverse
separating the single-block tensors.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  lines 995--1010
* [Bultinck--Marien--Williamson--Sahinoglu--Haegeman--Verstraete 2015]
  arXiv:1511.08090, Section ``Associativity and the pentagon equation'',
  lines 237--277 of the source
-/

open scoped Matrix BigOperators ComplexOrder Kronecker
open Matrix

namespace MPOTensor.BNTFusionIsometryFamily

universe u

variable {Λ : Type u} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionIsometryFamily Λ p)

/-- The row index of the left-associated triple-fusion direct sum.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, equation
`Fmove`, left indices \((e,d,\mu,\nu)\). -/
abbrev LeftTripleFusionIndex (α β γ : Λ) : Type u :=
  (δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim α β δ) × Fin (Fam.chi.dim δ γ ε) ×
    Fin (Fam.bondDim ε)

/-- The row index of the right-associated triple-fusion direct sum.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, equation
`Fmove`, right indices \((f,d,\lambda,\sigma)\). -/
abbrev RightTripleFusionIndex (α β γ : Λ) : Type u :=
  (δ : Λ) × (ε : Λ) × Fin (Fam.chi.dim β γ δ) × Fin (Fam.chi.dim α δ ε) ×
    Fin (Fam.bondDim ε)

/-- The full comparison between the left- and right-associated triple-fusion
direct sums,
\(C=U^{\mathrm L}A(U^{\mathrm R})^\dagger\), where \(A\) is the canonical
reassociation of the three bond spaces.

This matrix compares the full ranges of the two iterated fusion isometries. It
is not a fixed-final-label \(F\)-transformation, and no invertibility is asserted.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, Section
``Associativity and the pentagon equation'', lines 237--277 of the source. -/
noncomputable def tripleFusionComparison (α β γ : Λ) :
    Matrix (Fam.LeftTripleFusionIndex α β γ)
      (Fam.RightTripleFusionIndex α β γ) ℂ :=
  Fam.leftFusionIsometry α β γ *
    mulTensorAssocMatrix (Fam.bondDim α) (Fam.bondDim β) (Fam.bondDim γ) *
      (Fam.rightFusionIsometry α β γ)ᴴ

private theorem mulTensorAssocMatrix_mul_conjTranspose (D₁ D₂ D₃ : ℕ) :
    mulTensorAssocMatrix D₁ D₂ D₃ * (mulTensorAssocMatrix D₁ D₂ D₃)ᴴ = 1 := by
  ext x y
  simp [mulTensorAssocMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    PEquiv.toMatrix_apply, Matrix.one_apply]

private theorem conjTranspose_mul_mulTensorAssocMatrix (D₁ D₂ D₃ : ℕ) :
    (mulTensorAssocMatrix D₁ D₂ D₃)ᴴ * mulTensorAssocMatrix D₁ D₂ D₃ = 1 := by
  classical
  ext x y
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single ((mulTensorAssocEquiv D₁ D₂ D₃).symm x)]
  · simp [mulTensorAssocMatrix, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply]
  · intro z _ hz
    have hf : mulTensorAssocEquiv D₁ D₂ D₃ z ≠ x := by
      intro h
      apply hz
      exact (mulTensorAssocEquiv D₁ D₂ D₃).injective
        (h.trans ((mulTensorAssocEquiv D₁ D₂ D₃).apply_symm_apply x).symm)
    simp [mulTensorAssocMatrix, Matrix.conjTranspose_apply, PEquiv.toMatrix_apply, hf]
  · simp

/-- The product of the full triple-fusion comparison with its adjoint is the
range projection of the left iterated fusion isometry:
\[
  C_{\alpha,\beta,\gamma}C_{\alpha,\beta,\gamma}^\dagger
    = U^{\mathrm L}_{\alpha,\beta,\gamma}
      (U^{\mathrm L}_{\alpha,\beta,\gamma})^\dagger.
\]

The right iterated fusion map is an isometry and the bond reassociation is a
permutation, so both factors cancel between the two copies of the comparison.
The remaining projection is not asserted to be the identity. Such an assertion
requires completeness of the fusion decomposition, which is the additional
hypothesis in the invertible total fusion-matrix argument of the source.

Source: arXiv:1511.08090, source lines 181--191 and 237--252. -/
theorem tripleFusionComparison_mul_conjTranspose (α β γ : Λ) :
    Fam.tripleFusionComparison α β γ * (Fam.tripleFusionComparison α β γ)ᴴ =
      Fam.leftFusionIsometry α β γ * (Fam.leftFusionIsometry α β γ)ᴴ := by
  unfold tripleFusionComparison
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Fam.rightFusionIsometry α β γ)ᴴ,
    Fam.rightFusionIsometry_isometry, Matrix.one_mul]
  rw [← Matrix.mul_assoc (mulTensorAssocMatrix (Fam.bondDim α)
      (Fam.bondDim β) (Fam.bondDim γ)),
    mulTensorAssocMatrix_mul_conjTranspose, Matrix.one_mul]

/-- The product of the adjoint of the full triple-fusion comparison with the
comparison is the range projection of the right iterated fusion isometry:
\[
  C_{\alpha,\beta,\gamma}^\dagger C_{\alpha,\beta,\gamma}
    = U^{\mathrm R}_{\alpha,\beta,\gamma}
      (U^{\mathrm R}_{\alpha,\beta,\gamma})^\dagger.
\]

The left iterated fusion map is an isometry and the bond reassociation is a
permutation, so both factors cancel between the two copies of the comparison.
The remaining projection is not asserted to be the identity. Such an assertion
requires completeness of the fusion decomposition, which is the additional
hypothesis in the invertible total fusion-matrix argument of the source.

Source: arXiv:1511.08090, source lines 181--191 and 237--252. -/
theorem conjTranspose_mul_tripleFusionComparison (α β γ : Λ) :
    (Fam.tripleFusionComparison α β γ)ᴴ * Fam.tripleFusionComparison α β γ =
      Fam.rightFusionIsometry α β γ * (Fam.rightFusionIsometry α β γ)ᴴ := by
  unfold tripleFusionComparison
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Fam.leftFusionIsometry α β γ)ᴴ,
    Fam.leftFusionIsometry_isometry, Matrix.one_mul]
  rw [← Matrix.mul_assoc
      (mulTensorAssocMatrix (Fam.bondDim α) (Fam.bondDim β) (Fam.bondDim γ))ᴴ,
    conjTranspose_mul_mulTensorAssocMatrix, Matrix.one_mul]

/-- **The full triple-fusion comparison intertwines the unweighted direct
sums.** Suppose the positive trace-power coefficients are independent of the
positive chain length. For every letter, if

\[
  D^{\mathrm L}_{ik}
    = \bigoplus_{\delta,\varepsilon}
        1_{r_{\alpha\beta}^{\delta}}\otimes
        \bigl(1_{r_{\delta\gamma}^{\varepsilon}}
          \otimes M_\varepsilon^{ik}\bigr)
\]

and \(D^{\mathrm R}_{ik}\) is the analogous direct sum for the right
parenthesization, then
\[
  D^{\mathrm L}_{ik} C_{\alpha,\beta,\gamma}
    = C_{\alpha,\beta,\gamma} D^{\mathrm R}_{ik}.
\]

The result concerns the full direct sums. It neither selects a final label nor
asserts that the comparison is invertible.

Source: arXiv:1606.00608, lines 995--1010; arXiv:1511.08090, equations
`zippercondition2` and `Fmove`, and lines 237--277 of the source. -/
theorem tripleFusionComparison_intertwines_of_lengthIndependent
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent) (α β γ : Λ) (i k : Fin p) :
    (Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
      (1 : Matrix (Fin (Fam.chi.dim α β δ)) (Fin (Fam.chi.dim α β δ)) ℂ) ⊗ₖ
        ((1 : Matrix (Fin (Fam.chi.dim δ γ ε))
          (Fin (Fam.chi.dim δ γ ε)) ℂ) ⊗ₖ Fam.tensor ε i k)) *
        Fam.tripleFusionComparison α β γ =
      Fam.tripleFusionComparison α β γ *
        (Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
          (1 : Matrix (Fin (Fam.chi.dim β γ δ))
            (Fin (Fam.chi.dim β γ δ)) ℂ) ⊗ₖ
            ((1 : Matrix (Fin (Fam.chi.dim α δ ε))
              (Fin (Fam.chi.dim α δ ε)) ℂ) ⊗ₖ Fam.tensor ε i k)) := by
  have hLeft :
      Fam.leftFusionIsometry α β γ *
          (mulTensor (mulTensor (Fam.tensor α) (Fam.tensor β)) (Fam.tensor γ)) i k *
          (Fam.leftFusionIsometry α β γ)ᴴ =
        Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
          (1 : Matrix (Fin (Fam.chi.dim α β δ))
            (Fin (Fam.chi.dim α β δ)) ℂ) ⊗ₖ
            ((1 : Matrix (Fin (Fam.chi.dim δ γ ε))
              (Fin (Fam.chi.dim δ γ ε)) ℂ) ⊗ₖ Fam.tensor ε i k) := by
    rw [Fam.leftFusion_apply]
    simp_rw [Fam.chi_matrix_eq_one_of_lengthIndependent c hχ hLI]
  have hRight :
      Fam.rightFusionIsometry α β γ *
          (mulTensor (Fam.tensor α) (mulTensor (Fam.tensor β) (Fam.tensor γ))) i k *
          (Fam.rightFusionIsometry α β γ)ᴴ =
        Matrix.blockDiagonal' fun δ => Matrix.blockDiagonal' fun ε =>
          (1 : Matrix (Fin (Fam.chi.dim β γ δ))
            (Fin (Fam.chi.dim β γ δ)) ℂ) ⊗ₖ
            ((1 : Matrix (Fin (Fam.chi.dim α δ ε))
              (Fin (Fam.chi.dim α δ ε)) ℂ) ⊗ₖ Fam.tensor ε i k) := by
    rw [Fam.rightFusion_apply]
    simp_rw [Fam.chi_matrix_eq_one_of_lengthIndependent c hχ hLI]
  unfold tripleFusionComparison
  rw [← hLeft, ← hRight]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, Fam.leftFusionIsometry_isometry,
    Fam.rightFusionIsometry_isometry, Matrix.one_mul]
  simpa only [Matrix.mul_assoc] using congrArg
    (fun X => Fam.leftFusionIsometry α β γ * X *
      (Fam.rightFusionIsometry α β γ)ᴴ)
    (mulTensor_mul_assocMatrix (Fam.tensor α) (Fam.tensor β) (Fam.tensor γ) i k)

end MPOTensor.BNTFusionIsometryFamily
