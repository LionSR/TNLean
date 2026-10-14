/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RegularizedPatchCoordinate
import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import QICLean.Analysis.DensitySimplex

/-!
# Diagonal variation of an ordered regularized patch objective

A diagonal change of one density leaves the other densities and the order of
all filters fixed. The scalar objective is the square of the norm of that
same ordered product applied to the original vector.

Source: OpenAI, polynomial PEPS manuscript, proof of Proposition 4.1,
`03-patches.tex`, lines 170–200, `eq:patch-simplex-derivative` and
`eq:patch-kkt`, revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Out : V → Type*} [∀ v, Fintype (Out v)]
variable {m : ℕ} (regions : Fin m → Finset V)

open Classical in
/-- Replace one density by a real diagonal matrix in a fixed orthonormal basis.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178. -/
noncomputable def regularizedPatchDiagonalUpdate
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (y : ((v : regions j) → Out v.1) → ℝ) :=
  Function.update x j
    ((U : Matrix _ _ ℂ) * diagonal (fun i ↦ (y i : ℂ)) * star (U : Matrix _ _ ℂ))

open Classical in
/-- The squared norm of the original ordered product after one diagonal change.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–178. -/
noncomputable def regularizedPatchDiagonalObjective (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    (x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (y : ((v : regions j) → Out v.1) → ℝ) : ℝ :=
  regularizedPatchObjective regions a b Ω (regularizedPatchDiagonalUpdate regions x j U y) ^ 2

open Classical in
/-- A minimum of the full ordered objective restricts to a minimum on the
probability simplex in any eigenbasis of the selected density.
Source: polynomial-PEPS Proposition 4.1, `03-patches.tex`, lines 170–191.
Neither commutation of filters nor nonsingularity of a density is needed. -/
theorem isMinOn_regularizedPatchDiagonalObjective
    (a : Fin m → ℝ) (b : ℝ)
    (Ω : EuclideanSpace ℂ ((v : (Finset.univ : Finset V)) → Out v.1))
    {x : ∀ j, Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ}
    (hx : x ∈ regularizedPatchDomain regions)
    (hmin : IsMinOn (regularizedPatchObjective regions a b Ω)
      (regularizedPatchDomain regions) x)
    (j : Fin m)
    (U : unitary (Matrix ((v : regions j) → Out v.1) ((v : regions j) → Out v.1) ℂ))
    (s : ((v : regions j) → Out v.1) → ℝ)
    (hxs : x j =
      (U : Matrix _ _ ℂ) * diagonal (fun i ↦ (s i : ℂ)) * star (U : Matrix _ _ ℂ)) :
    IsMinOn (regularizedPatchDiagonalObjective regions a b Ω x j U)
      {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i = 1} s := by
  classical
  intro y hy
  have hfeas : regularizedPatchDiagonalUpdate regions x j U y ∈
      regularizedPatchDomain regions := by
    intro k
    by_cases h : k = j
    · subst k
      simp only [regularizedPatchDiagonalUpdate, Function.update_self]
      refine ⟨(Matrix.PosSemidef.diagonal
        (fun i ↦ Complex.zero_le_real.mpr (hy.1 i))).mul_mul_conjTranspose_same _, ?_⟩
      rw [Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul, Matrix.trace_diagonal]
      exact_mod_cast hy.2
    · simpa only [regularizedPatchDiagonalUpdate, Function.update_of_ne h] using hx k
  have hself : regularizedPatchDiagonalUpdate regions x j U s = x :=
    (congrArg (Function.update x j) hxs.symm).trans (Function.update_eq_self j x)
  simpa only [Set.mem_ofPred_eq, regularizedPatchDiagonalObjective, hself,
    regularizedPatchObjective] using
    pow_le_pow_left₀ (norm_nonneg _) (hmin hfeas) 2

end TNLean.PEPS
