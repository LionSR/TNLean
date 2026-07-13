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
