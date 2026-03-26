/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.LindbladForm.Basic
import TNLean.Channel.ChoiJamiolkowski

/-!
# Lindblad Form — Uniqueness of traceless GKSL decompositions

This file formalizes the uniqueness direction of Wolf Proposition 7.4 (item 2):
if two Lindblad / generator decompositions define the same generator and both
use traceless Kraus operators, then

* the dissipative CP parts coincide, and
* the drift matrices agree up to an imaginary scalar multiple of the identity.
-/

open scoped Matrix ComplexOrder BigOperators NNReal MatrixOrder
open Matrix

noncomputable section

-- Local instances needed for NormedAddCommGroup on Matrix (for CLM infrastructure)
attribute [local instance] Matrix.linftyOpNormedRing
attribute [local instance] Matrix.linftyOpNormedAlgebra

variable {D : ℕ}

section LindbladForms

/-- Predicate: all Kraus operators in a Lindblad form are traceless. -/
def LindbladForm.HasTracelessKraus (F : LindbladForm D) : Prop :=
  ∀ j : Fin F.r, trace (F.L j) = 0

/--
If two Lindblad forms induce the same generator and both Kraus families are
traceless, then their CP parts in Wolf's `(φ, κ)` decomposition agree.

This is the Choi-projection uniqueness step in Wolf Prop. 7.4 (item 2).

**Status**: `sorry` — needs projected Choi matrix orthogonality argument. -/
theorem generatorDecomp_traceless_unique_phi
    (F F' : LindbladForm D)
    (hL : F.toLinearMap = F'.toLinearMap)
    (htr : F.HasTracelessKraus)
    (htr' : F'.HasTracelessKraus) :
    F.toGeneratorDecomp.φ = F'.toGeneratorDecomp.φ := by
  -- Proof strategy (Wolf): compare projected Choi matrices and use Choi injectivity.
  -- Infrastructure for the final projection/orthogonality argument is developed in
  -- `ChoiJamiolkowski` and related Lindblad files.
  sorry

/--
If two Lindblad forms induce the same generator and both Kraus families are
traceless, then their drift matrices differ only by an imaginary scalar:
`κ' = κ + i λ 𝟙` for some `λ : ℝ`.

This is the Hamiltonian uniqueness modulo global energy shift in Wolf Prop. 7.4
(item 2).

**Status**: `sorry` — needs residual-map analysis after φ-uniqueness. -/
theorem generatorDecomp_traceless_unique_kappa_modPhase
    (F F' : LindbladForm D)
    (hL : F.toLinearMap = F'.toLinearMap)
    (htr : F.HasTracelessKraus)
    (htr' : F'.HasTracelessKraus) :
    ∃ l : ℝ,
      F'.toGeneratorDecomp.κ =
        F.toGeneratorDecomp.κ + (Complex.I * (l : ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  -- Proof strategy (Wolf): after identifying `φ = φ'`, the residual map is
  -- `ρ ↦ -(Δκ)ρ - ρ(Δκ)†`; equality to zero forces `Δκ` to be a scalar multiple
  -- of identity, and trace/Hermiticity constraints force that scalar to be purely
  -- imaginary.
  sorry

/-- Combined uniqueness statement for traceless Lindblad decompositions. -/
theorem generatorDecomp_traceless_unique
    (F F' : LindbladForm D)
    (hL : F.toLinearMap = F'.toLinearMap)
    (htr : F.HasTracelessKraus)
    (htr' : F'.HasTracelessKraus) :
    F.toGeneratorDecomp.φ = F'.toGeneratorDecomp.φ ∧
    ∃ l : ℝ,
      F'.toGeneratorDecomp.κ =
        F.toGeneratorDecomp.κ + (Complex.I * (l : ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  refine ⟨generatorDecomp_traceless_unique_phi F F' hL htr htr', ?_⟩
  exact generatorDecomp_traceless_unique_kappa_modPhase F F' hL htr htr'

end LindbladForms

end -- noncomputable section
