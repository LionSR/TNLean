/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.SubmoduleStarProjectionMatrix
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.Rank
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
# Regression checks for matrices of submodule projections

The matrix retains the linear-map definition used by rank and range proofs,
agrees with the continuous-linear-map coordinates, and covers the zero space.
The new declarations use only Lean's three standard axioms.
-/

variable {n : Type*} [Fintype n] [DecidableEq n]

example (W : Submodule ℂ (EuclideanSpace ℂ n)) :
    W.starProjectionMatrix = Matrix.toEuclideanLin.symm W.starProjection.toLinearMap := rfl

example (W : Submodule ℂ (EuclideanSpace ℂ n)) :
    W.starProjectionMatrix = (Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)).symm
      W.starProjection := rfl

example (W : Submodule ℂ (EuclideanSpace ℂ n)) :
    Matrix.toEuclideanLin W.starProjectionMatrix = W.starProjection.toLinearMap := by simp

example (W : Submodule ℂ (EuclideanSpace ℂ n)) :
    W.starProjectionMatrix * W.starProjectionMatrix = W.starProjectionMatrix :=
  W.isStarProjection_starProjectionMatrix.isIdempotentElem.eq

example (W : Submodule ℂ (EuclideanSpace ℂ n)) : W.starProjectionMatrix.IsHermitian :=
  W.isStarProjection_starProjectionMatrix.isSelfAdjoint

example : (⊥ : Submodule ℂ (EuclideanSpace ℂ n)).starProjectionMatrix = 0 := by
  apply Matrix.toEuclideanLin.injective
  simp

example (W : Submodule ℂ (EuclideanSpace ℂ n)) :
    W.starProjectionMatrix.rank = Module.finrank ℂ W := by
  rw [Matrix.rank_eq_finrank_range_toLin _
    (EuclideanSpace.basisFun n ℂ).toBasis (EuclideanSpace.basisFun n ℂ).toBasis,
    ← Matrix.toEuclideanLin_eq_toLin_orthonormal,
    Submodule.toEuclideanLin_starProjectionMatrix, Submodule.range_starProjection]

example (W : Submodule ℂ (EuclideanSpace ℂ (Fin 0))) :
    IsStarProjection W.starProjectionMatrix := W.isStarProjection_starProjectionMatrix

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``Submodule.starProjectionMatrix,
      ``Submodule.toEuclideanLin_starProjectionMatrix,
      ``Submodule.isStarProjection_starProjectionMatrix] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
