/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixSingleSpan
import TNLean.MPS.Preparation.BlockedPolar
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

/-!
# Polar deformation of an injective tensor

Write the physical matrix of a tensor as `M = V P`, with `P` positive and
`V` isometric when the tensor is injective. The affine path
`V ((1 - γ) 1 + γ P)` joins the isometric tensor to the original tensor,
in the original physical space, including when `M` is rectangular.

Source: arXiv:1010.3732, Section II.C, eq. `eq:1d-iso:polardec` and
the interpolation immediately following it. Right polar factors express
the same path as the source's physical positive factor on the image of `V`.
-/

open scoped Matrix MatrixOrder ComplexOrder Kronecker

namespace MPSTensor

variable {d D : ℕ}

/-- A left inverse of the physical matrix expresses every matrix unit as
a linear combination of tensor letters, and hence proves injectivity.
Source: arXiv:1010.3732, Section II.C, injective isometric form. -/
theorem isInjective_of_leftInverse_physicalMatrix (A : MPSTensor d D)
    (R : Matrix (Fin D × Fin D) (Fin d) ℂ) (hR : R * physicalMatrix A = 1) :
    Kraus.IsInjective A := by
  apply Submodule.eq_top_of_forall_single_mem
  intro a b
  have hunit : Matrix.single a b (1 : ℂ) = ∑ i, R (a, b) i • A i := by
    ext c e
    have h := congrFun (congrFun hR (a, b)) (c, e)
    simpa [Matrix.mul_apply, physicalMatrix, Matrix.single_apply,
      Matrix.one_apply, Prod.ext_iff, Matrix.sum_apply, Matrix.smul_apply,
      smul_eq_mul] using h.symm
  rw [hunit]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- The isometric tensor in the original physical space. Source:
arXiv:1010.3732, Section II.C, eq. `eq:1d-iso:polardec`. -/
noncomputable def polarIsometricTensor (A : MPSTensor d D) : MPSTensor d D :=
  ofPhysicalMatrix (Matrix.polarIso (physicalMatrix A))

/-- The positive factor interpolated with the identity. Source:
arXiv:1010.3732, Section II.C, the formula for `Q_γ`. -/
noncomputable def polarDeformationPos (A : MPSTensor d D) (γ : ℝ) :
    Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ :=
  (1 - γ) • 1 + γ • Matrix.polarPos (physicalMatrix A)

/-- The polar path from the isometric tensor to the original tensor.
Source: arXiv:1010.3732, Section II.C, `P_γ = Q_γ W`. -/
noncomputable def polarDeformation (A : MPSTensor d D) (γ : ℝ) : MPSTensor d D :=
  ofPhysicalMatrix (Matrix.polarIso (physicalMatrix A) * polarDeformationPos A γ)

/-- The positive factor stays strictly positive along an injective polar
path. Source: arXiv:1010.3732, Section II.C, `Q_γ > 0`. -/
theorem posDef_polarDeformationPos {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    {γ : ℝ} (hγ : γ ∈ Set.Icc 0 1) : (polarDeformationPos A γ).PosDef := by
  have hP := Matrix.posDef_polarPos_of_injective (physicalMatrix A)
    (injective_physicalMatrix_mulVec_of_isInjective hA)
  by_cases hzero : γ = 0
  · simp [polarDeformationPos, hzero, Matrix.PosDef.one]
  · exact Matrix.PosDef.posSemidef_add
      ((Matrix.PosSemidef.one : (1 : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ).PosSemidef).smul
        (sub_nonneg.mpr hγ.2))
      (hP.smul (lt_of_le_of_ne hγ.1 (Ne.symm hzero)))

/-- Every tensor on the polar path is injective. No relation between the
physical dimension and the square of the bond dimension is assumed.
Source: arXiv:1010.3732, Section II.C, preservation of standard form. -/
theorem isInjective_polarDeformation {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    {γ : ℝ} (hγ : γ ∈ Set.Icc 0 1) : Kraus.IsInjective (polarDeformation A γ) := by
  let P := polarDeformationPos A γ
  let V := Matrix.polarIso (physicalMatrix A)
  have hP : P.PosDef := posDef_polarDeformationPos hA hγ
  have hV : Vᴴ * V = 1 := Matrix.isIsometry_polarIso_of_injective _
    (injective_physicalMatrix_mulVec_of_isInjective hA)
  apply isInjective_of_leftInverse_physicalMatrix _ (P⁻¹ * Vᴴ)
  change P⁻¹ * Vᴴ * (V * P) = 1
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ, hV, Matrix.one_mul]
  exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit)

/-- The polar path starts at the isometric tensor. Source:
arXiv:1010.3732, Section II.C, `P₀ = W`. -/
@[simp] theorem polarDeformation_zero (A : MPSTensor d D) :
    polarDeformation A 0 = polarIsometricTensor A := by
  simp [polarDeformation, polarDeformationPos, polarIsometricTensor]

/-- The polar path ends at the original tensor. Source:
arXiv:1010.3732, Section II.C, `P₁ = P`. -/
@[simp] theorem polarDeformation_one (A : MPSTensor d D) :
    polarDeformation A 1 = A := by
  simp [polarDeformation, polarDeformationPos, Matrix.polarIso_mul_polarPos]

/-- The polar path is continuous in the original physical space. Source:
arXiv:1010.3732, Section II.C, continuity of the interpolation. -/
theorem continuous_polarDeformation (A : MPSTensor d D) :
    Continuous (polarDeformation A) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro a
  apply continuous_pi
  intro b
  change Continuous fun γ : ℝ =>
    (Matrix.polarIso (physicalMatrix A) * polarDeformationPos A γ) i (a, b)
  have h : Continuous fun γ : ℝ =>
      Matrix.polarIso (physicalMatrix A) * polarDeformationPos A γ := by
    unfold polarDeformationPos
    fun_prop
  exact (continuous_apply (a, b)).comp ((continuous_apply i).comp h)

/-- A unitary covariance of the physical matrix commutes with its positive
polar factor on the virtual pair space. Source: arXiv:1010.3732,
Section II.C, paragraph “Isometric form and symmetries”. -/
theorem polarPos_commute_of_unitary_covariance (A : MPSTensor d D)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hCov : U * physicalMatrix A = physicalMatrix A * K) :
    Commute (Matrix.polarPos (physicalMatrix A)) K := by
  let M := physicalMatrix A
  have hU' : Uᴴ * U = 1 := (Matrix.mem_unitaryGroup_iff').mp hU
  have hK' : K * Kᴴ = 1 := (Matrix.mem_unitaryGroup_iff).mp hK
  have hGram : Kᴴ * (Mᴴ * M * K) = Mᴴ * M := by
    calc
      Kᴴ * (Mᴴ * M * K) = (M * K)ᴴ * (M * K) := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = (U * M)ᴴ * (U * M) := by rw [hCov]
      _ = Mᴴ * M := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc Uᴴ, hU', Matrix.one_mul]
  have hComm : Commute (Mᴴ * M) K := by
    apply (commute_iff_eq _ _).2
    have h := congrArg (K * ·) hGram
    simpa only [← Matrix.mul_assoc, hK', Matrix.one_mul] using h
  unfold Matrix.polarPos
  rw [CFC.sqrt_eq_real_sqrt _ (Matrix.posSemidef_conjTranspose_mul_self _).nonneg,
    cfcₙ_eq_cfc]
  exact hComm.cfc_real Real.sqrt

/-- The isometric polar factor has the same unitary covariance as an
injective tensor. Source: arXiv:1010.3732, Section II.C, symmetry of `W`. -/
theorem polarIso_covariance_of_isInjective {A : MPSTensor d D}
    (hA : Kraus.IsInjective A) (U : Matrix (Fin d) (Fin d) ℂ)
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hCov : U * physicalMatrix A = physicalMatrix A * K) :
    U * Matrix.polarIso (physicalMatrix A) = Matrix.polarIso (physicalMatrix A) * K := by
  let M := physicalMatrix A
  let P := Matrix.polarPos M
  let V := Matrix.polarIso M
  have hP : P.PosDef := Matrix.posDef_polarPos_of_injective M
    (injective_physicalMatrix_mulVec_of_isInjective hA)
  have hPK := polarPos_commute_of_unitary_covariance A U K hU hK hCov
  apply Matrix.mul_left_injective_of_inv P P⁻¹
    (Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hP.isUnit))
  calc
    (U * V) * P = U * M := by rw [Matrix.mul_assoc, Matrix.polarIso_mul_polarPos]
    _ = M * K := hCov
    _ = (V * P) * K := by rw [Matrix.polarIso_mul_polarPos]
    _ = (V * K) * P := by
      rw [Matrix.mul_assoc, hPK.eq, ← Matrix.mul_assoc]

/-- The original on-site symmetry and virtual action are preserved at every
point of the injective polar path. Source: arXiv:1010.3732, Section II.C,
conclusion of “Isometric form and symmetries”. -/
theorem polarDeformation_covariance {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (U : Matrix (Fin d) (Fin d) ℂ)
    (K : Matrix (Fin D × Fin D) (Fin D × Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hK : K ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ)
    (hCov : U * physicalMatrix A = physicalMatrix A * K) (γ : ℝ) :
    U * physicalMatrix (polarDeformation A γ) = physicalMatrix (polarDeformation A γ) * K := by
  have hV := polarIso_covariance_of_isInjective hA U K hU hK hCov
  have hP := polarPos_commute_of_unitary_covariance A U K hU hK hCov
  change U * (Matrix.polarIso (physicalMatrix A) * polarDeformationPos A γ) =
    (Matrix.polarIso (physicalMatrix A) * polarDeformationPos A γ) * K
  rw [← Matrix.mul_assoc, hV, Matrix.mul_assoc, Matrix.mul_assoc]
  congr 1
  simp only [polarDeformationPos, Matrix.mul_add, Matrix.add_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul, hP.eq]

/-- Conjugation of the bond matrices acts on the virtual pair index by
`Xᵀ ⊗ Y`. Source: arXiv:1010.3732, Section II.C, virtual gauge action. -/
theorem physicalMatrix_mul_left_right (A : MPSTensor d D)
    (X Y : Matrix (Fin D) (Fin D) ℂ) :
    physicalMatrix (fun i => X * A i * Y) = physicalMatrix A * (Xᵀ ⊗ₖ Y) := by
  ext i ⟨a, b⟩
  simp only [physicalMatrix, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_comm, mul_left_comm]

/-- A unitary physical covariance by unitary bond conjugation is preserved
throughout the polar deformation. Source: arXiv:1010.3732, Section II.C,
“Isometric form and symmetries”. -/
theorem rotatePhysical_polarDeformation_of_unitary_covariance
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (U : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : rotatePhysical U A = fun i => X * A i * Xᴴ) (γ : ℝ) :
    rotatePhysical U (polarDeformation A γ) =
      fun i => X * polarDeformation A γ i * Xᴴ := by
  have hCovM : U * physicalMatrix A = physicalMatrix A * (Xᵀ ⊗ₖ Xᴴ) := by
    rw [← physicalMatrix_rotatePhysical, hCov, physicalMatrix_mul_left_right]
  have hK : (Xᵀ ⊗ₖ Xᴴ) ∈ Matrix.unitaryGroup (Fin D × Fin D) ℂ :=
    Matrix.kronecker_mem_unitary (Matrix.transpose_mem_unitaryGroup_iff.mpr hX)
      (Unitary.star_mem hX)
  apply physicalMatrix_injective
  rw [physicalMatrix_rotatePhysical, physicalMatrix_mul_left_right]
  exact polarDeformation_covariance hA U _ hU hK hCovM γ

/-- The same virtual unitary gives gauge covariance at every point of
the polar deformation. Source: arXiv:1010.3732, Section II.C,
“Isometric form and symmetries”. -/
theorem gaugeEquiv_polarDeformation_of_unitary_covariance
    {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    (U : Matrix (Fin d) (Fin d) ℂ) (X : Matrix (Fin D) (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hCov : rotatePhysical U A = fun i => X * A i * Xᴴ) (γ : ℝ) :
    GaugeEquiv (polarDeformation A γ) (rotatePhysical U (polarDeformation A γ)) := by
  refine ⟨⟨X, Xᴴ, (Matrix.mem_unitaryGroup_iff).mp hX,
    (Matrix.mem_unitaryGroup_iff').mp hX⟩, fun i => ?_⟩
  exact congrFun (rotatePhysical_polarDeformation_of_unitary_covariance
    hA U X hU hX hCov γ) i

end MPSTensor
