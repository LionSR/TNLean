/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus

/-!
# Covariance of the matrix continuous functional calculus under unitary conjugation

This file records the single fact that, for a Hermitian matrix $A$, a real
function $f$, and a unitary $U$, the continuous functional calculus satisfies
$$f(U A U^\dagger) = U\,f(A)\,U^\dagger.$$
This is the matrix instance of the general statement that a continuous
star-algebra automorphism commutes with the continuous functional calculus,
specialized to the conjugation automorphism $x \mapsto U x U^\dagger$.

The result is purely a property of the functional calculus and unitary
conjugation, with no quantum-information content. It is isolated in this
low-level analysis module so that consumers such as the operator-monotone and
operator-concave machinery can use it without pulling in the quantum
relative-entropy stack.

## Main results

* `Matrix.cfc_conj_unitary` — covariance of the continuous functional calculus
  under conjugation by a unitary: $f(U A U^\dagger) = U\,f(A)\,U^\dagger$.
-/

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Covariance of the continuous functional calculus under unitary
conjugation.** For a Hermitian matrix $A$, a real function $f$, and a unitary
$U$, the continuous functional calculus satisfies
$f(U A U^\dagger) = U\,f(A)\,U^\dagger$.

This is the matrix instance of the general fact that the continuous functional
calculus commutes with the continuous star-algebra automorphism
$x \mapsto U x U^\dagger$ (`Unitary.conjStarAlgAut`). -/
theorem cfc_conj_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ)
    (U : unitary (Matrix n n ℂ)) :
    cfc f ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * cfc f A * star (U : Matrix n n ℂ) := by
  set φ := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) U with hφ
  have hcont : ContinuousOn f (spectrum ℝ A) := A.finite_real_spectrum |>.continuousOn f
  have hcontφ : Continuous φ :=
    LinearMap.continuous_of_finiteDimensional ((φ : Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ))
  have hsa : IsSelfAdjoint A := hA
  have happ : ∀ x, φ x = (U : Matrix n n ℂ) * x * star (U : Matrix n n ℂ) :=
    fun x => Unitary.conjStarAlgAut_apply U x
  have hsa' : IsSelfAdjoint (φ A) := by rw [happ]; exact hsa.conjugate (U : Matrix n n ℂ)
  have hconj := StarAlgHomClass.map_cfc φ f A hcont hcontφ hsa hsa'
  rw [happ, happ] at hconj
  exact hconj.symm

end Matrix
