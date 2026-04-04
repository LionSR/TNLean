/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TNLean.Algebra.BurnsideMatrix
import Mathlib.Analysis.Matrix.Hermitian

/-!
# Irreducible tensor implies irreducible action

This file closes the missing direction

`IsIrreducibleTensor A → IsIrreducibleAction A`.

The key idea is classical: if `W ≤ ℂ^D` is a nontrivial invariant subspace, then the orthogonal
projection onto `W` (in the finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin D)`) is a
nontrivial Hermitian idempotent matrix `P` satisfying `(1 - P) * A i * P = 0` for all `i`.
This produces `HasInvariantProj A`, contradicting `IsIrreducibleTensor A`.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

noncomputable section

/-- `IsIrreducibleTensor` implies `IsIrreducibleAction`.

If a nontrivial `A`-invariant submodule `W` existed, its orthogonal projection would give a
nontrivial invariant orthogonal projection matrix, contradicting `IsIrreducibleTensor`. -/
theorem isIrreducibleAction_of_isIrreducibleTensor
    {d D : ℕ} (A : MPSTensor d D)
    (hIrrT : IsIrreducibleTensor (d := d) (D := D) A) :
    IsIrreducibleAction (d := d) (D := D) A := by
  classical
  intro W hW
  -- Assume `W` is a nontrivial proper invariant submodule; derive a contradiction.
  by_contra hWT
  push Not at hWT
  obtain ⟨hW_ne_bot, hW_ne_top⟩ := hWT
  -- Work in the finite-dimensional Hilbert space `EuclideanSpace ℂ (Fin D)`.
  let E := EuclideanSpace ℂ (Fin D)
  let e : (Fin D → ℂ) ≃ₗ[ℂ] E :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℂ) (V := (Fin D → ℂ))).symm
  let W' : Submodule ℂ E := W.map e.toLinearMap
  have hW'_ne_bot : W' ≠ ⊥ := by
    intro h
    have : W = ⊥ :=
      (Submodule.map_eq_bot_iff (p := W) (e := e)).1 (by simpa [W'] using h)
    exact hW_ne_bot this
  have hW'_ne_top : W' ≠ ⊤ := by
    intro h
    have : W = ⊤ :=
      (Submodule.map_eq_top_iff (p := W) (e := e)).1 (by simpa [W'] using h)
    exact hW_ne_top this
  haveI : W'.HasOrthogonalProjection := by infer_instance
  let p' : E →L[ℂ] E := W'.starProjection
  -- Convert the orthogonal projection to a matrix via `Matrix.toEuclideanLin.symm`.
  let P : Matrix (Fin D) (Fin D) ℂ :=
    (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).symm p'.toLinearMap
  -- `W'` is invariant under `A i` (transported to `EuclideanSpace`).
  have hW' : ∀ i : Fin d, ∀ v ∈ W', (Matrix.toEuclideanLin (A i)) v ∈ W' := by
    intro i v hv
    rcases (Submodule.mem_map).1 hv with ⟨u, huW, rfl⟩
    have huW' : (A i).mulVec u ∈ W := hW i u huW
    have : e.toLinearMap ((A i).mulVec u) ∈ W' :=
      Submodule.mem_map_of_mem (f := e.toLinearMap) huW'
    simpa [W', Matrix.toEuclideanLin, e] using this
  -- The matrix `P` is Hermitian.
  have hHerm : P.IsHermitian := by
    have hSymm : (Matrix.toEuclideanLin P).IsSymmetric := by
      simpa [P, p'] using (Submodule.starProjection_isSymmetric (K := W'))
    exact (Matrix.isHermitian_iff_isSymmetric (A := P) (𝕜 := ℂ) (n := Fin D)).2 hSymm
  -- The matrix `P` is idempotent.
  have hPP : P * P = P := by
    apply (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).injective
    apply LinearMap.ext
    intro x
    simp [Matrix.toEuclideanLin, P, p']
    have hx : W'.starProjection x ∈ W' := by
      simp
    have : W'.starProjection (W'.starProjection x) = W'.starProjection x :=
      (Submodule.starProjection_eq_self_iff (K := W') (v := W'.starProjection x)).2 hx
    simpa using this
  have horth : IsOrthogonalProjection (D := D) P := ⟨hHerm, hPP⟩
  -- `P` is nontrivial.
  have hP_ne0 : P ≠ 0 := by
    intro hP0
    have hp0 : p'.toLinearMap = 0 := by
      have : Matrix.toEuclideanLin P = 0 := by
        simp [hP0]
      simpa [P] using this
    have : W' = (⊥ : Submodule ℂ E) := by
      have : (p' : E →L[ℂ] E).range = (⊥ : Submodule ℂ E) := by
        simp [p', hp0]
      simpa [p'] using this
    exact hW'_ne_bot this
  have hP_ne1 : P ≠ 1 := by
    intro hP1
    have hp1 : p'.toLinearMap = (LinearMap.id : E →ₗ[ℂ] E) := by
      have : Matrix.toEuclideanLin P = Matrix.toEuclideanLin (1 : Matrix (Fin D) (Fin D) ℂ) := by
        simp [hP1]
      simpa [Matrix.toEuclideanLin, P] using this
    have : W' = (⊤ : Submodule ℂ E) := by
      have : (p' : E →L[ℂ] E).range = (⊤ : Submodule ℂ E) := by
        -- `p'` is the identity map.
        have hp1' : (p' : E →L[ℂ] E) = ContinuousLinearMap.id ℂ E := by
          -- Avoid `ext` (which would unfold `EuclideanSpace` to pointwise goals).
          apply ContinuousLinearMap.ext
          intro x
          simpa using congrArg (fun f : E →ₗ[ℂ] E => f x) hp1
        simp [hp1']
      simpa [p'] using this
    exact hW'_ne_top this
  -- Invariance: `(1 - P) * A i * P = 0` for all `i`.
  have hPinv : ∀ i : Fin d, (1 - P) * A i * P = 0 := by
    intro i
    apply (Matrix.toEuclideanLin : Matrix (Fin D) (Fin D) ℂ ≃ₗ[ℂ] E →ₗ[ℂ] E).injective
    apply LinearMap.ext
    intro x
    -- Expand the triple product using the `Matrix.toLpLin` API.
    simp [Matrix.toEuclideanLin]
    -- Show the intermediate vector lies in `W'`.
    have hP_lin : Matrix.toEuclideanLin P = p'.toLinearMap := by
      simp [P]
    have hy : (Matrix.toEuclideanLin P) x ∈ W' := by
      -- The orthogonal projection always lands in the submodule.
      rw [hP_lin]
      change p' x ∈ W'
      simp [p']
    have hz : (Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x) ∈ W' :=
      hW' i ((Matrix.toEuclideanLin P) x) hy
    -- `P` fixes vectors in `W'`.
    have hfix : (Matrix.toEuclideanLin P)
        ((Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x)) =
        (Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x) := by
      have : W'.starProjection
          ((Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x)) =
          (Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x) :=
        (Submodule.starProjection_eq_self_iff (K := W')
          (v := (Matrix.toEuclideanLin (A i)) ((Matrix.toEuclideanLin P) x))).2 hz
      simpa [P, p'] using this
    -- Now `toEuclideanLin (1 - P)` kills vectors in `W'`.
    simp [Matrix.toEuclideanLin, hfix]
  -- Build `HasInvariantProj A`, contradicting `IsIrreducibleTensor A`.
  have : HasInvariantProj (d := d) (D := D) A :=
    ⟨P, horth, hP_ne0, hP_ne1, hPinv⟩
  exact hIrrT this

end

end MPSTensor
