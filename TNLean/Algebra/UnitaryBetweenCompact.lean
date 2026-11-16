/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Complex.Basic
import QICLean.Algebra.MatrixUnitaryBetween

/-!
# Compactness of the unitaries between two coordinate spaces

The rectangular complex matrices that are unitary between two finite coordinate
spaces, `Aᴴ A = 1` and `A Aᴴ = 1`, form a compact set. Each entry has modulus at
most one, and both equations are closed conditions.

This is the compactness used in the first step of the proof of Corollary
`coruvSF` of arXiv:1703.09188, lines 877--939, for the standard-form gates.
-/

open scoped Matrix

namespace Matrix

/-- The rectangular unitaries between two finite coordinate spaces form a
compact set. -/
theorem isCompact_setOf_isUnitaryBetween {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] :
    IsCompact {A : Matrix m n ℂ | A.IsUnitaryBetween} := by
  have hbox : IsCompact (Set.univ.pi fun _ : m ↦ Set.univ.pi fun _ : n ↦
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ ↦ isCompact_univ_pi fun _ ↦ isCompact_closedBall _ _
  refine hbox.of_isClosed_subset ?_ ?_
  · have h1 : IsClosed {A : Matrix m n ℂ | Aᴴ * A = 1} :=
      isClosed_eq (continuous_id.matrix_conjTranspose.matrix_mul continuous_id)
        continuous_const
    have h2 : IsClosed {A : Matrix m n ℂ | A * Aᴴ = 1} :=
      isClosed_eq (continuous_id.matrix_mul continuous_id.matrix_conjTranspose)
        continuous_const
    exact h1.inter h2
  · rintro (A : Matrix m n ℂ) hA
    have hAA : A * Aᴴ = 1 := hA.2
    refine Set.mem_univ_pi.mpr fun i ↦ Set.mem_univ_pi.mpr fun j ↦ ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    have hrow : ∑ k, A i k * star (A i k) = 1 := by
      have := congrFun (congrFun hAA i) i
      rwa [Matrix.mul_apply, Matrix.one_apply_eq] at this
    have hsum : ∑ k, ‖A i k‖ ^ 2 = 1 := by
      have : ∑ k, (A i k * star (A i k)) = ((∑ k, ‖A i k‖ ^ 2 : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
        push_cast; ring
      rw [this] at hrow
      exact_mod_cast hrow
    have hle : ‖A i j‖ ^ 2 ≤ 1 := by
      rw [← hsum]
      exact Finset.single_le_sum (f := fun k ↦ ‖A i k‖ ^ 2) (fun k _ ↦ by positivity)
        (Finset.mem_univ j)
    nlinarith [norm_nonneg (A i j)]

end Matrix
