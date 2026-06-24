/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Analysis.KleinInequality

/-!
# Unitary invariance of the quantum relative entropy

This file proves the **unitary invariance** of the quantum relative entropy
$D(\rho\|\sigma) = \operatorname{Re}\operatorname{tr}(\rho(\log\rho - \log\sigma))$:
for every unitary $U$,
$D(U\rho U^\dagger \,\|\, U\sigma U^\dagger) = D(\rho\|\sigma)$.

Unitary invariance is one of the three ingredients of the data-processing
inequality under the partial trace (layer 5 of the route note), alongside joint
convexity (layer 4, `convexOn_quantumRelativeEntropy`) and ancilla additivity.

## Main results

* `Matrix.cfc_conj_unitary` — covariance of the continuous functional calculus
  under conjugation by a unitary: $f(U A U^\dagger) = U\,f(A)\,U^\dagger$. This is
  the matrix instance of the fact that the continuous functional calculus
  commutes with the star-algebra automorphism $x \mapsto U x U^\dagger$.
* `Matrix.log_conj_unitary` — the special case $f = \log$:
  $\log(U A U^\dagger) = U\,(\log A)\,U^\dagger$.
* `quantumRelativeEntropy_conj_unitary` — unitary invariance of the relative
  entropy: $D(U\rho U^\dagger \,\|\, U\sigma U^\dagger) = D(\rho\|\sigma)$.

## Proof outline

The functional calculus covariance is the general lemma that a continuous
star-algebra homomorphism commutes with the continuous functional calculus,
specialized to the conjugation automorphism $x \mapsto U x U^\dagger$ on the
finite-dimensional matrix algebra; the four side conditions (continuity of $f$
on the finite spectrum, continuity of the automorphism on a finite-dimensional
space, and self-adjointness of $A$ and of its conjugate) are all dispatched
directly. The relative-entropy invariance then follows by applying the
covariance to $\log\rho$ and $\log\sigma$ and using trace cyclicity to cancel the
conjugating unitaries.

## References

* Layer 5 (data processing) of the relative-entropy elimination route for strong
  subadditivity, `docs/paper-gaps/cpsv16_ssa_from_lieb_route.tex`.
* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 8
  (Distance Measures)][Wolf2012QChannels].
-/

open scoped Matrix ComplexOrder Matrix.Norms.L2Operator
open Matrix Finset

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

/-- **The matrix logarithm is covariant under unitary conjugation.** For a
Hermitian matrix $A$ and a unitary $U$,
$\log(U A U^\dagger) = U\,(\log A)\,U^\dagger$. The special case $f = \log$ of
`cfc_conj_unitary`. -/
theorem log_conj_unitary {A : Matrix n n ℂ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℂ)) :
    CFC.log ((U : Matrix n n ℂ) * A * star (U : Matrix n n ℂ))
      = (U : Matrix n n ℂ) * CFC.log A * star (U : Matrix n n ℂ) := by
  rw [CFC.log, CFC.log, cfc_conj_unitary hA Real.log U]

end Matrix

/-- **Unitary invariance of the quantum relative entropy.** For Hermitian
matrices $\rho, \sigma$ and a unitary $U$,
$D(U\rho U^\dagger \,\|\, U\sigma U^\dagger) = D(\rho\|\sigma)$.

The logarithms are carried through the conjugation by `Matrix.log_conj_unitary`,
and the conjugating unitaries cancel under trace cyclicity. This is one of the
three ingredients of the data-processing inequality under the partial trace
(layer 5 of `docs/paper-gaps/cpsv16_ssa_from_lieb_route.tex`). -/
theorem quantumRelativeEntropy_conj_unitary {n : Type*} [Fintype n] [DecidableEq n]
    {ρ σ : Matrix n n ℂ} (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian)
    (U : unitary (Matrix n n ℂ)) :
    quantumRelativeEntropy ((U : Matrix n n ℂ) * ρ * star (U : Matrix n n ℂ))
        ((U : Matrix n n ℂ) * σ * star (U : Matrix n n ℂ))
      = quantumRelativeEntropy ρ σ := by
  set Um : Matrix n n ℂ := (U : Matrix n n ℂ) with hUm
  have hUstarU : star Um * Um = 1 := Unitary.star_mul_self_of_mem U.prop
  rw [quantumRelativeEntropy, quantumRelativeEntropy,
    Matrix.log_conj_unitary hρ U, Matrix.log_conj_unitary hσ U]
  congr 1
  have key : Um * ρ * star Um * (Um * CFC.log ρ * star Um - Um * CFC.log σ * star Um)
      = Um * (ρ * (CFC.log ρ - CFC.log σ)) * star Um := by
    rw [Matrix.mul_sub, Matrix.mul_sub,
      show Um * ρ * star Um * (Um * CFC.log ρ * star Um)
          = Um * ρ * (star Um * Um) * CFC.log ρ * star Um by noncomm_ring,
      show Um * ρ * star Um * (Um * CFC.log σ * star Um)
          = Um * ρ * (star Um * Um) * CFC.log σ * star Um by noncomm_ring,
      hUstarU]
    noncomm_ring
  rw [key, Matrix.trace_mul_cycle, ← Matrix.mul_assoc, hUstarU, Matrix.one_mul]
