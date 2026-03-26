/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Semigroup.LindbladForm.Basic
import TNLean.Channel.ChoiJamiolkowski
import TNLean.Algebra.ScalarCommutant

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
-/
theorem generatorDecomp_traceless_unique_phi
    (F F' : LindbladForm D)
    (hL : F.toLinearMap = F'.toLinearMap)
    (htr : F.HasTracelessKraus)
    (htr' : F'.HasTracelessKraus) :
    F.toGeneratorDecomp.φ = F'.toGeneratorDecomp.φ := by
  -- Proof strategy (Wolf): compare projected Choi matrices and use Choi injectivity.
  -- For traceless Kraus operators, choiMatrix(φ) = projectedChoiMatrix(φ) since
  -- ⟨Ω|τ_φ|Ω⟩ = (1/D)·Σⱼ|tr(Lⱼ)|² = 0 and τ_φ ≥ 0 forces τ_φ|Ω⟩ = 0.
  -- Then choiMatrix(φ) = projectedChoiMatrix(L) = choiMatrix(φ'), hence φ = φ'.
  sorry

/--
If two Lindblad forms induce the same generator and both Kraus families are
traceless, then their drift matrices differ only by an imaginary scalar:
`κ' = κ + i λ 𝟙` for some `λ : ℝ`.

This is the Hamiltonian uniqueness modulo global energy shift in Wolf Prop. 7.4
(item 2).

The proof proceeds as follows: once `φ = φ'` is known (from
`generatorDecomp_traceless_unique_phi`), the generator equality forces
`Δκ ρ + ρ (Δκ)† = 0` for all `ρ`. Setting `ρ = 1` yields `Δκ + (Δκ)† = 0`
(skew-Hermiticity), which converts the equation to `[Δκ, ρ] = 0`. The scalar
commutant lemma then gives `Δκ = c · 𝟙`, and skew-Hermiticity forces `c` to
be purely imaginary.
-/
theorem generatorDecomp_traceless_unique_kappa_modPhase
    (F F' : LindbladForm D)
    (hL : F.toLinearMap = F'.toLinearMap)
    (htr : F.HasTracelessKraus)
    (htr' : F'.HasTracelessKraus) :
    ∃ l : ℝ,
      F'.toGeneratorDecomp.κ =
        F.toGeneratorDecomp.κ + (Complex.I * (l : ℂ)) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  -- Step 1: φ = φ' from the first uniqueness theorem (currently sorry)
  have hφ := generatorDecomp_traceless_unique_phi F F' hL htr htr'
  -- Step 2: Generator decompositions define the same linear map
  have hG : F.toGeneratorDecomp.toLinearMap = F'.toGeneratorDecomp.toLinearMap := by
    rw [← F.toLinearMap_eq_generatorDecomp, ← F'.toLinearMap_eq_generatorDecomp]; exact hL
  -- Step 3: Δκ * ρ + ρ * Δκ† = 0 for all ρ
  set κ := F.toGeneratorDecomp.κ with hκ_def
  set κ' := F'.toGeneratorDecomp.κ with hκ'_def
  set Δ := κ' - κ with hΔ_def
  have hΔ : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, Δ * ρ + ρ * Δᴴ = 0 := by
    intro ρ
    have h := LinearMap.ext_iff.mp hG ρ
    simp only [GeneratorDecomp.toLinearMap_apply] at h
    -- h : F.φ ρ - κ * ρ - ρ * κᴴ = F'.φ ρ - κ' * ρ - ρ * κ'ᴴ
    -- Use hφ to unify the φ terms on both sides
    rw [show F.toGeneratorDecomp.φ = F'.toGeneratorDecomp.φ from hφ] at h
    -- h : F'.φ ρ - κ * ρ - ρ * κᴴ = F'.φ ρ - κ' * ρ - ρ * κ'ᴴ
    -- Derive Δ * ρ + ρ * Δᴴ = 0 from h
    have h0 := sub_eq_zero.mpr h
    show Δ * ρ + ρ * Δᴴ = 0
    rw [hΔ_def, conjTranspose_sub, sub_mul, mul_sub]
    convert h0 using 1; abel
  -- Step 4: Δ is skew-Hermitian (set ρ = 1)
  have hskew : Δᴴ = -Δ := by
    have h1 := hΔ 1; rw [mul_one, one_mul] at h1
    exact eq_neg_of_add_eq_zero_right h1
  -- Step 5: Δ commutes with all matrices
  have hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Δ * M = M * Δ := by
    intro M
    have hM := hΔ M
    rw [hskew, mul_neg, ← sub_eq_add_neg] at hM
    exact sub_eq_zero.mp hM
  -- Step 6: Δ is a scalar matrix (center of M_n)
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top Δ
    Submodule.span_univ (fun M _ => hcomm M)
  -- Step 7–8: c is purely imaginary ⟹ extract real scalar
  -- (Proof: skew-Hermiticity of Δ forces star c = -c,
  --  hence c.re = 0 and c = I * c.im.)
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
