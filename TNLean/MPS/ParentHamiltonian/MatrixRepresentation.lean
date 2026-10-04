/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.Transport
import TNLean.MPS.MPDO.CommutingForm
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Matrix coordinates for canonical parent Hamiltonians

The canonical local projection and its cyclic translates admit identical
matrix descriptions in the configuration basis and the Euclidean Hilbert
space. These identities connect the parent-Hamiltonian gap estimates to
the matrix formulation of local interactions used in arXiv:1010.3732,
Section II.B (`Papers/1010.3732/paper_v3.tex`, lines 357--390).
-/

open scoped Matrix.Norms.L2Operator

namespace MPSTensor

variable {d D : ℕ}

/-- The local parent matrix is the matrix of its Euclidean representative
in the canonical orthonormal basis. Source: arXiv:1010.3732, Section II.B,
the local term \(h\) of the parent Hamiltonian. -/
theorem parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix
    (A : MPSTensor d D) (L : ℕ) :
    LinearMap.toMatrix' (parentInteraction A L) =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Cfg d L) ℂ).toBasis
        (EuclideanSpace.basisFun (Cfg d L) ℂ).toBasis
        (parentInteractionES A L) := by
  classical
  ext i j
  simp [LinearMap.toMatrix'_apply, LinearMap.toMatrix_apply,
    EuclideanSpace.basisFun_toBasis, PiLp.basisFun_apply,
    parentInteraction, parentInteractionES]

/-- The canonical parent interaction is represented by the same matrix in
the function and Euclidean realizations of the finite configuration space.
Source: arXiv:1010.3732, Section II.D. -/
theorem parentInteractionES_eq_toEuclideanLin_parentMatrix
    (A : MPSTensor d D) (L : ℕ) :
    parentInteractionES A L = Matrix.toEuclideanLin
      (LinearMap.toMatrix' (parentInteraction A L)) := by
  rw [Matrix.toEuclideanLin_eq_toLin_orthonormal,
    parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix, Matrix.toLin_toMatrix]

/-- A cyclic parent term is the matrix embedding of its local interaction.
Source: arXiv:1010.3732, Section II.B, the local Hamiltonian sum. -/
theorem localTerm_eq_toLin'_embedLocalOperator (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTerm A L N i = Matrix.toLin'
      (MPOTensor.embedLocalOperator (d := d) L N hLN i
        (LinearMap.toMatrix' (parentInteraction A L))) := by
  classical
  apply LinearMap.ext
  intro v
  funext σ
  rw [localTerm_apply_of_le A L N hLN i, Matrix.toLin'_apply,
    MPOTensor.embedLocalOperator_mulVec_apply]
  symm
  exact congrFun (LinearMap.congr_fun
    (Matrix.toLin'_toMatrix' (parentInteraction A L))
    (fun τ ↦ v (replaceWindow L hLN i σ τ))) (extractWindow L i σ)

/-- Euclidean form of the embedded cyclic parent term. Source:
arXiv:1010.3732, Section II.B, the local Hamiltonian sum. -/
theorem localTermES_eq_toEuclideanLin_embedLocalOperator (A : MPSTensor d D)
    {L N : ℕ} (hLN : L ≤ N) (i : Fin N) :
    localTermES A L i = Matrix.toEuclideanLin
      (MPOTensor.embedLocalOperator L N hLN i
        (LinearMap.toMatrix' (parentInteraction A L))) := by
  rw [localTermES, localTerm_eq_toLin'_embedLocalOperator A hLN i]
  rfl

/-- The full periodic parent Hamiltonian is the Euclidean representative
of the sum of embedded local parent matrices. Source: arXiv:1010.3732,
Section II.B, the local Hamiltonian sum. -/
theorem parentHamiltonianES_eq_toEuclideanLin_sum_embedLocalOperator
    (A : MPSTensor d D) {L N : ℕ} (hLN : L ≤ N) :
    parentHamiltonianES A L N = Matrix.toEuclideanLin
      (∑ i : Fin N, MPOTensor.embedLocalOperator L N hLN i
        (LinearMap.toMatrix' (parentInteraction A L))) := by
  rw [parentHamiltonianES_eq_sum_localTermES, map_sum]
  simp_rw [localTermES_eq_toEuclideanLin_embedLocalOperator A hLN]

/-- The matrix of a canonical parent interaction is an orthogonal projection.
Source: arXiv:1010.3732, Section II.B, the choice of the local term as a projector. -/
theorem parentInteraction_toMatrix'_isStarProjection (A : MPSTensor d D) (L : ℕ) :
    IsStarProjection (LinearMap.toMatrix' (parentInteraction A L)) := by
  rw [parentInteraction_toMatrix'_eq_parentInteractionES_toMatrix]
  exact ((LinearMap.isStarProjection_iff_isSymmetricProjection).2
    (parentInteractionES_isSymmetricProjection A L)).map
    (LinearMap.toMatrixOrthonormal (EuclideanSpace.basisFun (Cfg d L) ℂ))

/-- Canonical parent interactions have Hilbert-space operator norm at most
one, as do the projector local terms of arXiv:1010.3732, Section II.B. -/
theorem parentInteraction_toMatrix'_norm_le_one (A : MPSTensor d D) (L : ℕ) :
    ‖LinearMap.toMatrix' (parentInteraction A L)‖ ≤ 1 :=
  (parentInteraction_toMatrix'_isStarProjection A L).norm_le _

end MPSTensor
