/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.SPTFixedPoint
import TNLean.MPS.Symmetry.PolarDeformation

/-!
# Physical matrix covariance under a unitary bond action

Vectorization turns adjoint conjugation of the tensor letters into an
intertwining identity between the physical matrix and the Kronecker bond
action. Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym.
-/

open scoped Matrix

namespace MPSTensor

/-- Unitary adjoint covariance of tensor letters gives the corresponding
physical-matrix intertwiner. The physical matrix need not be unitary.
Source context: arXiv:1010.3732, Section II.F.2,
equation eq:1d-sym:jointsym. -/
theorem physicalMatrix_mul_eq_sptKron_of_unitary_covariance
    {d D : ℕ} (A : MPSTensor d D) (u : Matrix (Fin d) (Fin d) ℂ)
    (X : GL (Fin D) ℂ)
    (hX : (X : Matrix (Fin D) (Fin D) ℂ) ∈ Matrix.unitaryGroup _ ℂ)
    (hCov : rotatePhysical u A =
      fun i => (X : Matrix (Fin D) (Fin D) ℂ) * A i *
        (X : Matrix (Fin D) (Fin D) ℂ)ᴴ) :
    u * physicalMatrix A = physicalMatrix A * sptKron X := by
  simpa only [sptKron,
    Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup X hX] using
    physicalMatrix_covariance_of_rotatePhysical A u X
      (X : Matrix (Fin D) (Fin D) ℂ)ᴴ hCov

end MPSTensor
