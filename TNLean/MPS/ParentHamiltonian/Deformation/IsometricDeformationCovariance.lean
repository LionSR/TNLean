/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import TNLean.MPS.ParentHamiltonian.Deformation.IsometricDeformation
import QICLean.Analysis.FunctionalCalculus.LeftPolar

/-!
# Covariance of the constructed isometric deformation

If a physical unitary \(U\) and a virtual unitary \(X\) satisfy
\(UP=PX\), then \(U\) commutes with the positive left polar factor,
including its identity extension outside the physical support. The left
partial isometry and the affine deformation obey the same covariance.

Source: arXiv:1010.3732, paper_v3.tex, lines 645--676.
This is the polar-decomposition step of the symmetry argument. The virtual
unitary is supplied here; deriving it from a symmetry of the matrix product
state is a separate assertion.
-/

open scoped Matrix MatrixOrder ComplexOrder

namespace MPSTensor

variable {α : Type*} [Fintype α] [DecidableEq α] {r : ℕ} {dim : Fin r → ℕ}

/-- Commutation with the positive factor persists along its affine path.
Source: arXiv:1010.3732, lines 672--676. -/
theorem commute_positivePhysicalDeformation
    (U Q : Matrix α α ℂ) (hComm : Commute U Q) (γ : unitInterval) :
    Commute U (positivePhysicalDeformation Q γ) := by
  exact (hComm.smul_right (γ : ℝ)).add_right
    ((Commute.one_right U).smul_right (1 - (γ : ℝ)))

/-- The constructed positive physical factor commutes with a physical
unitary when the original joint physical map intertwines it with a virtual
unitary. Source: arXiv:1010.3732, lines 658--676. -/
theorem commute_leftPolarPhysicalFactor_of_unitary_covariance
    (A : (j : Fin r) → MPTensor α (Fin (dim j)))
    (U : Matrix α α ℂ)
    (X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ)
    (hU : U ∈ Matrix.unitaryGroup α ℂ)
    (hX : X ∈ Matrix.unitaryGroup (BlockEntryIndex dim) ℂ)
    (hCov : U * blockPhysicalMatrix A = blockPhysicalMatrix A * X) :
    Commute U (leftPolarPhysicalFactor A) := by
  exact Matrix.commute_leftPolarPos_of_unitary_covariance
    (blockPhysicalMatrix A) U X hU hX hCov

/-- Physical rotation acts on the joint tensor map by multiplication on
its physical index. Source: arXiv:1010.3732, lines 589--594 and 658--676. -/
theorem blockPhysicalMatrix_rotatePhysical
    (Λ : Matrix α α ℂ) (A : (j : Fin r) → MPTensor α (Fin (dim j))) :
    blockPhysicalMatrix (fun j => rotatePhysical Λ (A j)) = Λ * blockPhysicalMatrix A := by
  ext i p
  simp [blockPhysicalMatrix, rotatePhysical, Matrix.mul_apply, Matrix.sum_apply]

/-- Every member of the constructed joint isometric deformation retains
an exact physical--virtual unitary covariance of its original physical map.
Source: arXiv:1010.3732, lines 672--676. -/
theorem blockPhysicalMatrix_isometricDeformationBlocks_covariance
    (A : (j : Fin r) → MPTensor α (Fin (dim j)))
    (U : Matrix α α ℂ)
    (X : Matrix (BlockEntryIndex dim) (BlockEntryIndex dim) ℂ)
    (hU : U ∈ Matrix.unitaryGroup α ℂ)
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
