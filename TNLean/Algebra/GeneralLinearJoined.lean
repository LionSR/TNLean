/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Paths of invertible complex matrices

Every invertible complex square matrix is joined to the identity by a path of
invertible matrices. The path follows a curve in the complex line
\(z\mapsto(1-z)I+zX\) that avoids the finitely many singular points, which
are the numbers \(-w^{-1}\) for eigenvalues \(w\) of \(X-I\); the complement
of a countable subset of \(\mathbb C\) is path connected.

This supplies the gauge interpolation used to connect a matrix product unitary
tensor to its canonical form II along tensors generating the same periodic
operators, in the proof of arXiv:1703.09188, Theorem `IndexTh` (iv),
lines 857--865.
-/

open scoped Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The points of the complex line through `1` and `X` where the line is singular. -/
private theorem finite_singular_line (X : Matrix n n ℂ) :
    {z : ℂ | ¬ IsUnit ((1 - z) • (1 : Matrix n n ℂ) + z • X).det}.Finite := by
  refine ((Matrix.finite_spectrum (X - 1)).image fun w : ℂ ↦ -w⁻¹).subset ?_
  intro z hz
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  refine ⟨-z⁻¹, ?_, by simp⟩
  rw [spectrum.mem_iff]
  intro hunit
  apply hz
  have hEq : (1 - z) • (1 : Matrix n n ℂ) + z • X =
      (-z) • (algebraMap ℂ (Matrix n n ℂ) (-z⁻¹) - (X - 1)) := by
    rw [Algebra.algebraMap_eq_smul_one, smul_sub, smul_smul]
    rw [show -z * -z⁻¹ = 1 by field_simp]
    module
  rw [hEq, Matrix.det_smul]
  exact (((isUnit_iff_ne_zero.mpr (pow_ne_zero _ (neg_ne_zero.mpr hz0))).mul
    ((Matrix.isUnit_iff_isUnit_det _).mp hunit)))

/-- Every invertible complex square matrix is joined to the identity by a path of
invertible matrices. -/
theorem joinedIn_isUnit_det_one {X : Matrix n n ℂ} (hX : IsUnit X.det) :
    JoinedIn {Y : Matrix n n ℂ | IsUnit Y.det} 1 X := by
  let S := {z : ℂ | ¬ IsUnit ((1 - z) • (1 : Matrix n n ℂ) + z • X).det}
  have hconn : IsPathConnected Sᶜ :=
    (finite_singular_line X).countable.isPathConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; exact Nat.one_lt_ofNat)
  have h0 : (0 : ℂ) ∈ Sᶜ := by simp [S]
  have h1 : (1 : ℂ) ∈ Sᶜ := by simpa [S] using hX
  obtain ⟨γ, hγ⟩ := hconn.joinedIn 0 h0 1 h1
  let f : ℂ → Matrix n n ℂ := fun z ↦ (1 - z) • (1 : Matrix n n ℂ) + z • X
  have hf : Continuous f := by fun_prop
  refine ⟨(γ.map hf).cast (by simp [f]) (by simp [f]), fun t ↦ ?_⟩
  have := hγ t
  simpa [S, f] using this

end Matrix
