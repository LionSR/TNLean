/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixAux
import TNLean.Algebra.MatrixTracePairing
import TNLean.Channel.Schwarz.TwoPositive

/-!
# Density representation of positive matrix functionals

A positive normalized complex-linear functional on a finite matrix algebra is the trace
pairing with a density matrix.  The representing density is obtained by applying the
trace-pairing adjoint of the associated scalar-range positive map to the faithful uniform
density.

## Main results

* `Matrix.exists_density_of_positive_functional`: a positive normalized linear functional
  on a finite matrix algebra is represented by a density matrix.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 1, the discussion
  following Proposition 1.5 and Equation (1.40)][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-- A positive normalized complex-linear functional on a finite matrix algebra is the
trace pairing with a density matrix.

This is the finite-dimensional representation of positive functionals used in Wolf,
Chapter 1, in the discussion following Proposition 1.5 and Equation (1.40). -/
theorem exists_density_of_positive_functional
    (f : Matrix n n ℂ →ₗ[ℂ] ℂ)
    (hpos : ∀ X : Matrix n n ℂ, X.PosSemidef → (0 : ℂ) ≤ f X)
    (hone : f 1 = 1) :
    ∃ ρ : Matrix n n ℂ, ρ.PosSemidef ∧ ρ.trace = 1 ∧
      ∀ X : Matrix n n ℂ, f X = (ρ * X).trace := by
  classical
  let F : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ :=
    { toFun := fun X ↦ f X • (1 : Matrix n n ℂ)
      map_add' := by
        intro X Y
        simp [add_smul]
      map_smul' := by
        intro c X
        simp [smul_smul] }
  have hF : IsPositiveMap F := by
    intro X hX
    exact Matrix.PosSemidef.one.smul (hpos X hX)
  let σ : Matrix n n ℂ := Matrix.faithfulDensity n
  let ρ : Matrix n n ℂ := Matrix.traceAdjointMap F σ
  have hσ : σ.PosSemidef := (Matrix.faithfulDensity_posDef n).posSemidef
  have hρ : ρ.PosSemidef := hF.traceAdjointMap σ hσ
  have hpair (X : Matrix n n ℂ) : (ρ * X).trace = f X := by
    rw [show ρ = Matrix.traceAdjointMap F σ from rfl,
      Matrix.trace_traceAdjointMap_mul]
    simp [F, σ, Matrix.trace_smul, Matrix.faithfulDensity_trace]
  refine ⟨ρ, hρ, ?_, fun X ↦ (hpair X).symm⟩
  simpa [hone] using hpair (1 : Matrix n n ℂ)

end Matrix
