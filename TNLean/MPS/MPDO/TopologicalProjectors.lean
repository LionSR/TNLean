/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Irreducible.Basic
import TNLean.MPS.MPDO.BNTTripleFusionSeparation

/-!
# The local projectors in the length-independent fusion form

For the length-independent case following Theorem IV.13 of
arXiv:1606.00608, every structure matrix
$\chi_{\alpha,\beta,\gamma}$ is the identity on its multiplicity space.
Consequently, if the terminal matrices $P_\gamma$ are orthogonal
projections, then
\[
  Q_{\alpha,\beta}
    = \bigoplus_\gamma
        \chi_{\alpha,\beta,\gamma}\otimes P_\gamma
\]
is a projection.  If the labelled tensors form a basis of normal tensors,
the corresponding fusion map is unitary, and
$U_{\alpha,\beta}^\dagger Q_{\alpha,\beta}U_{\alpha,\beta}$ is again an
orthogonal projection.

These are the one-fusion-step projector statements in the recursive
construction at source lines 999--1010.  The spectral decomposition of the
terminal matrices, iteration along an arbitrary chain, and the commuting Gibbs
decomposition are separate steps.

## References

* arXiv:1606.00608, lines 999--1016.
-/

open scoped Matrix Kronecker

namespace MPOTensor.BNTFusionIsometryFamily

variable {g p : ℕ}
variable (Fam : BNTFusionIsometryFamily (Fin g) p)

private theorem isStarProjection_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
    {m n : ℕ} (U : Matrix (Fin m) (Fin n) ℂ) (Q : Matrix (Fin m) (Fin m) ℂ)
    (hQ : IsStarProjection Q) (hU : U * Uᴴ = 1) :
    IsStarProjection (Uᴴ * Q * U) := by
  rw [isStarProjection_iff']
  constructor
  · calc
      (Uᴴ * Q * U) * (Uᴴ * Q * U) = Uᴴ * (Q * ((U * Uᴴ) * (Q * U))) := by
        simp only [Matrix.mul_assoc]
      _ = Uᴴ * (Q * (Q * U)) := by rw [hU, Matrix.one_mul]
      _ = Uᴴ * ((Q * Q) * U) := by simp only [Matrix.mul_assoc]
      _ = Uᴴ * Q * U := by rw [hQ.isIdempotentElem.eq, Matrix.mul_assoc]
  · rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    have hQadj : Qᴴ = Q := by
      simpa [Matrix.star_eq_conjTranspose] using hQ.isSelfAdjoint.star_eq
    rw [hQadj, Matrix.mul_assoc]

/-- The single fusion layer of the operator $Q$ at source lines 999--1010,
with terminal matrices $P_\gamma$.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def projectorQBlock
    (P : ∀ γ : Fin g,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α β : Fin g) :
    Matrix ((γ : Fin g) ×
        (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ)))
      ((γ : Fin g) ×
        (Fin (Fam.chi.dim α β γ) × Fin (Fam.bondDim γ))) ℂ :=
  Matrix.blockDiagonal' fun γ => Fam.chi.matrix α β γ ⊗ₖ P γ

/-- In the length-independent case, the chi matrices in a single fusion layer
are identities.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem projectorQBlock_eq_unweighted
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : ∀ γ : Fin g,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α β : Fin g) :
    Fam.projectorQBlock P α β =
      Matrix.blockDiagonal' fun γ =>
        (1 : Matrix (Fin (Fam.chi.dim α β γ))
          (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ P γ := by
  unfold projectorQBlock
  simp_rw [Fam.chi_matrix_eq_one_of_lengthIndependent c hχ hLI]

/-- A single fusion layer is a self-adjoint idempotent when its terminal
matrices are self-adjoint idempotents and the structure coefficients are
length independent.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem projectorQBlock_isStarProjection
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : ∀ γ : Fin g,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (hP : ∀ γ : Fin g, IsStarProjection (P γ))
    (α β : Fin g) :
    IsStarProjection (Fam.projectorQBlock P α β) := by
  rw [Fam.projectorQBlock_eq_unweighted c hχ hLI]
  rw [isStarProjection_iff']
  constructor
  · rw [← Matrix.blockDiagonal'_mul]
    congr 1
    funext γ
    rw [← Matrix.mul_kronecker_mul, Matrix.one_mul, (hP γ).isIdempotentElem.eq]
  · rw [Matrix.star_eq_conjTranspose, Matrix.blockDiagonal'_conjTranspose]
    congr 1
    funext γ
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
    have hPγ : (P γ)ᴴ = P γ := by
      simpa [Matrix.star_eq_conjTranspose] using (hP γ).isSelfAdjoint.star_eq
    rw [hPγ]

/-- The fusion-layer operator transported to the product bond space by the
fusion map.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
noncomputable def conjugatedProjectorQBlock
    (P : ∀ γ : Fin g,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (α β : Fin g) :
    Matrix (Fin (Fam.bondDim α * Fam.bondDim β))
      (Fin (Fam.bondDim α * Fam.bondDim β)) ℂ :=
  (Fam.fusionIsometry α β)ᴴ * Fam.projectorQBlock P α β *
    Fam.fusionIsometry α β

/-- For a source basis of normal tensors, the fusion map is unitary in the
length-independent case, so conjugating the fusion-layer operator gives an
orthogonal projection on the product bond space.

Source: arXiv:1606.00608, BNT separation at lines 317--345, the fusion map at
lines 986--993, and the recursive projector at lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem conjugatedProjectorQBlock_isOrthogonalProjection
    {D : ℕ} {A : MPSTensor (p * p) D}
    (hBNT : MPSTensor.IsCPSVBasisOfNormalTensors A
      (fun γ : Fin g =>
        ⟨Fam.bondDim γ, (Fam.tensor γ).toMPSTensor⟩))
    (c : BNTLabelCoefficientFamily (Fin g))
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : ∀ γ : Fin g,
      Matrix (Fin (Fam.bondDim γ)) (Fin (Fam.bondDim γ)) ℂ)
    (hP : ∀ γ : Fin g, IsStarProjection (P γ))
    (α β : Fin g) :
    IsOrthogonalProjection (Fam.conjugatedProjectorQBlock P α β) :=
  (isStarProjection_conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
    (Fam.fusionIsometry α β) (Fam.projectorQBlock P α β)
    (Fam.projectorQBlock_isStarProjection c hχ hLI P hP α β)
    (Fam.fusionIsometry_mul_conjTranspose_eq_one_of_bnt_of_lengthIndependent
      hBNT c hχ hLI α β)).isOrthogonalProjection

end MPOTensor.BNTFusionIsometryFamily
