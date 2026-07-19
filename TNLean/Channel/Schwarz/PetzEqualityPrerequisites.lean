/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.PetzRecoverySupport
import TNLean.Channel.Schwarz.SSAEqualityDPI

/-!
# Singular-support prerequisites for equality in data processing

This file records analytic identities needed to study equality in the
relative-entropy data-processing inequality without imposing invertibility on
the positive semidefinite matrices.

## Main result

* `quantumRelativeEntropy_kronecker_support` proves ancilla additivity on the
  finite-relative-entropy support domain.

## References

* P. Hayden, R. Jozsa, D. Petz, and A. Winter, *Structure of States Which
  Satisfy Strong Subadditivity of Quantum Entropy with Equality*, Theorem 3,
  arXiv:quant-ph/0304007v2.
-/

open scoped Matrix Kronecker ComplexOrder Matrix.Norms.L2Operator
open Matrix

/-- **Ancilla additivity on the singular support domain.** Let `ρ` and `σ` be
positive semidefinite matrices with `ker σ ⊆ ker ρ`, and let `τ` be a positive
semidefinite matrix of unit trace. Then
`D(ρ ⊗ τ ‖ σ ⊗ τ) = D(ρ ‖ σ)`.

The singular tensor-logarithm formula introduces the support projections of
`ρ`, `σ`, and `τ`. The common ancilla-logarithm contribution cancels because
the kernel inclusion makes both system support projections absorb `ρ`; the
remaining factor is multiplied by `trace τ = 1`.

This removes the positive-definite scope restriction from the ancilla identity
used in the Weyl-twirl route to partial-trace data processing. It is an analytic
prerequisite for the equality implication in Hayden--Jozsa--Petz--Winter,
arXiv:quant-ph/0304007v2, Theorem 3; it does not itself assert recovery. -/
theorem quantumRelativeEntropy_kronecker_support
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    {ρ σ : Matrix m m ℂ} {τ : Matrix n n ℂ}
    (hρ : ρ.PosSemidef) (hσ : σ.PosSemidef) (hτ : τ.PosSemidef)
    (hτtrace : τ.trace = 1)
    (hsupp : ∀ v : m → ℂ, σ.mulVec v = 0 → ρ.mulVec v = 0) :
    quantumRelativeEntropy (ρ ⊗ₖ τ) (σ ⊗ₖ τ) =
      quantumRelativeEntropy ρ σ := by
  have hσabsorb :
      hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj = ρ :=
    Matrix.IsHermitian.supportProj_mul_mul_supportProj_of_mulVec_kernel_le
      hσ.isHermitian hρ.isHermitian hsupp
  have hρPσ : ρ * hσ.isHermitian.supportProj = ρ := by
    calc
      ρ * hσ.isHermitian.supportProj =
          (hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj) *
            hσ.isHermitian.supportProj := by rw [hσabsorb]
      _ = hσ.isHermitian.supportProj * ρ *
          (hσ.isHermitian.supportProj * hσ.isHermitian.supportProj) := by
            simp only [Matrix.mul_assoc]
      _ = hσ.isHermitian.supportProj * ρ * hσ.isHermitian.supportProj := by
            rw [hσ.isHermitian.supportProj_idem]
      _ = ρ := hσabsorb
  have hρPρ : ρ * hρ.isHermitian.supportProj = ρ :=
    hρ.isHermitian.mul_supportProj_self
  have hτPτ : τ * hτ.isHermitian.supportProj = τ :=
    hτ.isHermitian.mul_supportProj_self
  rw [quantumRelativeEntropy, quantumRelativeEntropy,
    Matrix.log_kronecker_posSemidef hρ hτ,
    Matrix.log_kronecker_posSemidef hσ hτ]
  simp only [Matrix.mul_sub, Matrix.mul_add, ← Matrix.mul_kronecker_mul,
    Matrix.trace_sub, Matrix.trace_add, Matrix.trace_kronecker,
    Complex.sub_re, Complex.add_re]
  rw [hρPρ, hρPσ, hτPτ, hτtrace]
  ring_nf
