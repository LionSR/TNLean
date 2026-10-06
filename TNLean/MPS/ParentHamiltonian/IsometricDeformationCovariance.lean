/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TNLean.MPS.ParentHamiltonian.IsometricDeformation

/-!
# Covariance of the constructed isometric deformation

If a physical unitary \(U\) and a virtual unitary \(X\) satisfy
\(UP=PX\), then \(U\) commutes with the positive left polar factor,
including its identity extension outside the physical support. The left
partial isometry and the affine deformation obey the same covariance.

Source: arXiv:1010.3732, `paper_v3.tex`, lines 645--676.
This is the polar-decomposition step of the symmetry argument. The virtual
unitary is supplied here; deriving it from a symmetry of the matrix product
state is a separate assertion.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- A unitary physical--virtual intertwining relation makes the physical
Gram matrix commute with the physical action. Source: arXiv:1010.3732,
lines 658--671. -/
theorem commute_mul_conjTranspose_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (P * Pᴴ) := by
  have hAdj := congrArg conjTranspose hCov
  simp only [conjTranspose_mul] at hAdj
  have hXX : X * Xᴴ = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff.mp hX
  have hConj : U * (P * Pᴴ) * Uᴴ = P * Pᴴ := by
    calc
      U * (P * Pᴴ) * Uᴴ = (U * P) * (Pᴴ * Uᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = (P * X) * (Xᴴ * Pᴴ) := by rw [hCov, hAdj]
      _ = P * Pᴴ := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc X Xᴴ Pᴴ,
          hXX, Matrix.one_mul]
  have hUU : Uᴴ * U = 1 := by
    simpa only [star_eq_conjTranspose] using mem_unitaryGroup_iff'.mp hU
  calc
    U * (P * Pᴴ) = (U * (P * Pᴴ) * Uᴴ) * U := by
      rw [Matrix.mul_assoc, hUU, Matrix.mul_one]
    _ = (P * Pᴴ) * U := by rw [hConj]

/-- The physical support projection commutes with the physical unitary in
an exact unitary covariance. Source: arXiv:1010.3732, lines 645--676;
this also justifies extending the polar factor by the identity off support. -/
theorem commute_leftPolarSupport_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (polarSupport Pᴴ) := by
  have hGram := commute_mul_conjTranspose_of_unitary_covariance P U X hU hX hCov
  unfold polarSupport
  simp only [conjTranspose_conjTranspose]
  exact (hGram.symm.cfc_real _).symm

/-- The positive left polar factor commutes with a unitary physical action
intertwined with a virtual unitary. The assertion includes the identity
extension outside the physical support. Source: arXiv:1010.3732,
lines 658--676. -/
theorem commute_leftPolarPos_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : Commute U (leftPolarPos P) := by
  have hGram := commute_mul_conjTranspose_of_unitary_covariance P U X hU hX hCov
  have hPos : Commute U (polarPos Pᴴ) := by
    simpa only [polarPos, CFC.sqrt, conjTranspose_conjTranspose] using
      (hGram.symm.cfcₙ_nnreal NNReal.sqrt).symm
  exact hPos.add_right ((Commute.one_right U).sub_right
    (commute_leftPolarSupport_of_unitary_covariance P U X hU hX hCov))

/-- The left partial isometry has the same physical--virtual covariance
as the original matrix. Source: arXiv:1010.3732, lines 658--676. -/
theorem leftPolarIso_covariance_of_unitary_covariance
    (P : Matrix ι κ ℂ) (U : Matrix ι ι ℂ) (X : Matrix κ κ ℂ)
    (hU : U ∈ unitaryGroup ι ℂ) (hX : X ∈ unitaryGroup κ ℂ)
    (hCov : U * P = P * X) : U * leftPolarIso P = leftPolarIso P * X := by
  let := (posDef_leftPolarPos P).isUnit.invertible
  apply mul_right_injective_of_invertible (leftPolarPos P)
  have hComm := commute_leftPolarPos_of_unitary_covariance P U X hU hX hCov
  calc
    leftPolarPos P * (U * leftPolarIso P) = U * (leftPolarPos P * leftPolarIso P) := by
      rw [← Matrix.mul_assoc, ← hComm.eq, Matrix.mul_assoc]
    _ = U * P := by rw [leftPolarPos_mul_leftPolarIso]
    _ = P * X := hCov
    _ = (leftPolarPos P * leftPolarIso P) * X :=
      congrArg (· * X) (leftPolarPos_mul_leftPolarIso P).symm
    _ = leftPolarPos P * (leftPolarIso P * X) := Matrix.mul_assoc _ _ _

end Matrix

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

/-- Commutation with the positive factor persists along its affine path.
Source: arXiv:1010.3732, lines 672--676. -/
theorem commute_positivePhysicalDeformation
    (U Q : Matrix (Fin d) (Fin d) ℂ) (hComm : Commute U Q) (γ : unitInterval) :
    Commute U (positivePhysicalDeformation Q γ) := by
  exact (hComm.smul_right (γ : ℝ)).add_right
    ((Commute.one_right U).smul_right (1 - (γ : ℝ)))

/-- The constructed positive physical factor commutes with a physical
unitary when the original joint physical map intertwines it with a virtual
unitary. Source: arXiv:1010.3732, lines 658--676. -/
theorem commute_leftPolarPhysicalFactor_of_unitary_covariance
    (A : (j : Fin r) → MPSTensor d (dim j))
    (U : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ)
    (hCov : U * blockPhysicalMatrix A = blockPhysicalMatrix A * X) :
    Commute U (leftPolarPhysicalFactor A) := by
  exact Matrix.commute_leftPolarPos_of_unitary_covariance
    (blockPhysicalMatrix A) U X hU hX hCov

/-- Physical rotation acts on the joint tensor map by multiplication on
its physical index. Source: arXiv:1010.3732, lines 589--594 and 658--676. -/
theorem blockPhysicalMatrix_rotatePhysical
    (Λ : Matrix (Fin d) (Fin d) ℂ) (A : (j : Fin r) → MPSTensor d (dim j)) :
    blockPhysicalMatrix (fun j => rotatePhysical Λ (A j)) = Λ * blockPhysicalMatrix A := by
  ext i p
  simp [blockPhysicalMatrix, rotatePhysical, Matrix.mul_apply, Matrix.sum_apply]

/-- Every member of the constructed joint isometric deformation retains
an exact physical--virtual unitary covariance of its original physical map.
Source: arXiv:1010.3732, lines 672--676. -/
theorem blockPhysicalMatrix_isometricDeformationBlocks_covariance
    (A : (j : Fin r) → MPSTensor d (dim j))
    (U : Matrix (Fin d) (Fin d) ℂ)
    (X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin d) ℂ)
    (hX : X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ)
    (hCov : U * blockPhysicalMatrix A = blockPhysicalMatrix A * X) (γ : unitInterval) :
    U * blockPhysicalMatrix (isometricDeformationBlocks A γ) =
      blockPhysicalMatrix (isometricDeformationBlocks A γ) * X := by
  have hComm := commute_positivePhysicalDeformation U (leftPolarPhysicalFactor A)
    (commute_leftPolarPhysicalFactor_of_unitary_covariance A U X hU hX hCov) γ
  have hIso := Matrix.leftPolarIso_covariance_of_unitary_covariance
    (blockPhysicalMatrix A) U X hU hX hCov
  unfold isometricDeformationBlocks
  rw [blockPhysicalMatrix_rotatePhysical, blockPhysicalMatrix_leftPolarBlocks]
  calc
    U * (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ *
        Matrix.leftPolarIso (blockPhysicalMatrix A)) =
        (U * positivePhysicalDeformation (leftPolarPhysicalFactor A) γ) *
          Matrix.leftPolarIso (blockPhysicalMatrix A) := (Matrix.mul_assoc _ _ _).symm
    _ = (positivePhysicalDeformation (leftPolarPhysicalFactor A) γ * U) *
        Matrix.leftPolarIso (blockPhysicalMatrix A) := by rw [hComm.eq]
    _ = positivePhysicalDeformation (leftPolarPhysicalFactor A) γ *
        (Matrix.leftPolarIso (blockPhysicalMatrix A) * X) := by rw [Matrix.mul_assoc, hIso]
    _ = _ := (Matrix.mul_assoc _ _ _).symm

end MPSTensor
