/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Channel.Irreducible.Basic
import TNLean.MPS.MPDO.BNTFusionTensorClause
import TNLean.MPS.MPDO.BNTTripleFusionSeparation

/-!
# The local projectors in the length-independent fusion form

For the length-independent case following Theorem 4.14 of
arXiv:1606.00608, every structure matrix
$\chi_{\alpha,\beta,\gamma}$ is the identity on its multiplicity space.
Consequently, if the terminal matrices $P_\gamma$ are orthogonal
projections, then
\[
  Q_{\alpha,\beta}
    = \bigoplus_\gamma
        \chi_{\alpha,\beta,\gamma}\otimes P_\gamma
\]
is a projection.  The source terminal matrices $\operatorname{tr}(M_\gamma)$
act on the common physical space of the vertically read tensors.  Transport
through the sequential fusion circuit belongs to the arbitrary-chain
construction.  The earlier full-support formulation instead gives a
conditional projection statement for terminal operators on the virtual bond
spaces.

These are the one-fusion-step projector statements in the recursive
construction at source lines 999--1010.  The spectral decomposition of the
terminal matrices, iteration along an arbitrary chain, and the commuting Gibbs
decomposition are separate steps.

## References

* arXiv:1606.00608, lines 999--1016.
-/

open scoped Matrix Kronecker

namespace MPOTensor.BNTFusionCoisometryFamily

variable {Λ : Type*} [Fintype Λ] [DecidableEq Λ] {p : ℕ}
variable (Fam : BNTFusionCoisometryFamily Λ p)

/-- The single fusion layer of the operator $Q$ on the active product sectors,
with terminal matrices $P_\gamma$.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (one fusion layer):** The arbitrary-chain recursive
operator at line 999 and its sequential fusion circuit are not asserted here.
Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
noncomputable def projectorQBlock
    (P : Λ → Matrix (Fin p) (Fin p) ℂ)
    (α β : Λ) :
    Matrix ((γ : Λ) ×
        (Fin (Fam.chi.dim α β γ) × Fin p))
      ((γ : Λ) ×
        (Fin (Fam.chi.dim α β γ) × Fin p)) ℂ :=
  Matrix.blockDiagonal' fun γ => Fam.chi.matrix α β γ ⊗ₖ P γ

/-- In the length-independent case, the chi matrices in one active fusion
layer are identities.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem projectorQBlock_eq_unweighted
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : Λ → Matrix (Fin p) (Fin p) ℂ)
    (α β : Λ) :
    Fam.projectorQBlock P α β =
      Matrix.blockDiagonal' fun γ =>
        (1 : Matrix (Fin (Fam.chi.dim α β γ))
          (Fin (Fam.chi.dim α β γ)) ℂ) ⊗ₖ P γ := by
  unfold projectorQBlock
  simp_rw [DiagonalChiFamily.matrix_eq_one_of_forall_entry_eq_one
    (hχ.entry_eq_one_of_lengthIndependent Fam.posEntries hLI)]

/-- One active fusion layer is a self-adjoint idempotent when its terminal
matrices are self-adjoint idempotents and the structure coefficients are
length independent.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem projectorQBlock_isStarProjection
    (c : BNTLabelCoefficientFamily Λ)
    (hχ : c.HasPositiveLengthChiTracePowerForm Fam.chi)
    (hLI : c.LengthIndependent)
    (P : Λ → Matrix (Fin p) (Fin p) ℂ)
    (hP : ∀ γ : Λ, IsStarProjection (P γ))
    (α β : Λ) :
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

end MPOTensor.BNTFusionCoisometryFamily

namespace MPOTensor.BNTFusionTensorClause

variable {d D : ℕ} {M : MPOTensor d D}

/-- The single active fusion layer associated with a chosen vertical canonical
decomposition of an MPO tensor.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (one fusion layer):** This definition records one step of
the recursive operator at line 999, not its iteration along an arbitrary
chain.  Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
noncomputable def projectorQBlock
    (H : BNTFusionTensorClause M)
    (P : Fin H.labelCount → Matrix (Fin D) (Fin D) ℂ)
    (α β : Fin H.labelCount) :
    Matrix ((γ : Fin H.labelCount) ×
        (Fin (H.chi.dim α β γ) × Fin D))
      ((γ : Fin H.labelCount) ×
        (Fin (H.chi.dim α β γ) × Fin D)) ℂ :=
  H.toBNTFusionCoisometryFamily.projectorQBlock P α β

/-- Length independence makes the tensor-attached active fusion layer a
self-adjoint idempotent when its terminal matrices are self-adjoint
idempotents.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`. -/
theorem projectorQBlock_isStarProjection
    (H : BNTFusionTensorClause M)
    (hLI : (BNTLabelCoefficientFamily.ofChi H.chi).LengthIndependent)
    (P : Fin H.labelCount → Matrix (Fin D) (Fin D) ℂ)
    (hP : ∀ γ : Fin H.labelCount, IsStarProjection (P γ))
    (α β : Fin H.labelCount) :
    IsStarProjection (H.projectorQBlock P α β) :=
  H.toBNTFusionCoisometryFamily.projectorQBlock_isStarProjection
    (BNTLabelCoefficientFamily.ofChi H.chi)
    (BNTLabelCoefficientFamily.ofChi_hasPositiveLengthChiTracePowerForm H.chi)
    hLI P hP α β

end MPOTensor.BNTFusionTensorClause

namespace MPOTensor.BNTFusionIsometryFamily

variable {g p : ℕ}
variable (Fam : BNTFusionIsometryFamily (Fin g) p)

/-- A conditional single fusion layer with terminal matrices $P_\gamma$ on
the virtual bond spaces.

Source: arXiv:1606.00608, lines 999--1010 of
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (virtual-bond terminal operators):** The source terminal
matrices $\operatorname{tr}(M_\gamma)$ act on a common physical space.  This
definition instead gives a mathematically valid virtual-bond construction for
the older full-support fusion family.  Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
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
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (virtual-bond terminal operators):** This identity
concerns the conditional virtual-bond construction, not the physical terminal
matrices in the source recursion.  Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
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
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (virtual-bond terminal operators):** This theorem concerns
the conditional virtual-bond construction, not the physical terminal matrices
in the source recursion.  Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex`. -/
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
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (virtual-bond terminal operators):** This transport is
defined only for the older full-support fusion family.  It is not the
sequential physical-space transport in the source recursion.  Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex` and
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
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
`Papers/1606.00608/MPDO-22-12-17-2.tex`.

**Scope restriction (full-support virtual transport):** The BNT hypothesis and
length independence imply the additional full-support relation needed here.
The theorem concerns virtual-bond terminal operators, not the physical
terminal matrices or the sequential circuit of the source recursion.
Documented in
`docs/paper-gaps/cpsv16_topological_projector_recursion.tex` and
`docs/paper-gaps/cpsv16_figure11_fusion_coisometry.tex`. -/
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
  (IsStarProjection.conjTranspose_mul_mul_of_mul_conjTranspose_eq_one
    (Fam.projectorQBlock_isStarProjection c hχ hLI P hP α β)
    (Fam.fusionIsometry α β)
    (Fam.fusionIsometry_mul_conjTranspose_eq_one_of_bnt_of_lengthIndependent
      hBNT c hχ hLI α β)).isOrthogonalProjection

end MPOTensor.BNTFusionIsometryFamily
