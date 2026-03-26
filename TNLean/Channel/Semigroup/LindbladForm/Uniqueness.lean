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
  -- Step 1: φ = φ' from the first uniqueness theorem
  have hφ := generatorDecomp_traceless_unique_phi F F' hL htr htr'
  -- Step 2: Generator decompositions define the same linear map
  have hG : F.toGeneratorDecomp.toLinearMap = F'.toGeneratorDecomp.toLinearMap := by
    rw [← F.toLinearMap_eq_generatorDecomp, ← F'.toLinearMap_eq_generatorDecomp]; exact hL
  -- Step 3: Δκ * ρ + ρ * Δκ† = 0 for all ρ
  set κ := F.toGeneratorDecomp.κ
  set κ' := F'.toGeneratorDecomp.κ
  set Δ := κ' - κ
  have hΔ : ∀ ρ : Matrix (Fin D) (Fin D) ℂ, Δ * ρ + ρ * Δᴴ = 0 := by
    intro ρ
    show (κ' - κ) * ρ + ρ * (κ' - κ)ᴴ = 0
    rw [conjTranspose_sub, sub_mul, mul_sub]
    -- Goal: κ' * ρ - κ * ρ + (ρ * κ'ᴴ - ρ * κᴴ) = 0
    have h := LinearMap.ext_iff.mp hG ρ
    simp only [GeneratorDecomp.toLinearMap_apply, hφ] at h
    -- h : F'.φ ρ - κ * ρ - ρ * κᴴ = F'.φ ρ - κ' * ρ - ρ * κ'ᴴ
    have h0 := sub_eq_zero.mpr h
    -- h0 : (F'.φ ρ - κ * ρ - ρ * κᴴ) - (F'.φ ρ - κ' * ρ - ρ * κ'ᴴ) = 0
    -- The F'.φ ρ terms cancel, leaving our goal up to additive rearrangement
    convert h0 using 1; abel
  -- Step 4: Δ is skew-Hermitian (set ρ = 1)
  have hskew : Δᴴ = -Δ :=
    eq_neg_of_add_eq_zero_right (by simpa [mul_one, one_mul] using hΔ 1)
  -- Step 5: Δ commutes with all matrices
  have hcomm : ∀ M : Matrix (Fin D) (Fin D) ℂ, Δ * M = M * Δ := by
    intro M
    have hM := hΔ M
    rw [hskew, mul_neg, ← sub_eq_add_neg] at hM
    exact sub_eq_zero.mp hM
  -- Step 6: Δ is a scalar matrix (center of M_n)
  obtain ⟨c, hc⟩ := Matrix.isScalar_of_commute_span_eq_top Δ
    (Submodule.span_univ ℂ) (fun M _ => hcomm M)
  -- Step 7: c is purely imaginary (from skew-Hermiticity)
  by_cases hD : D = 0
  · subst hD; exact ⟨0, Subsingleton.elim _ _⟩
  · haveI : NeZero D := ⟨hD⟩
    have hc_skew : starRingEnd ℂ c = -c := by
      have hΔ_conj : Δᴴ = Matrix.scalar (Fin D) (starRingEnd ℂ c) := by
        rw [hc, conjTranspose_diagonal]; ext; simp [Matrix.scalar]
      rw [hskew] at hΔ_conj
      have h_neg : -Matrix.scalar (Fin D) c = Matrix.scalar (Fin D) (-c) := by
        ext; simp [Matrix.scalar]
      rw [hc, h_neg] at hΔ_conj
      have h_inj := congr_fun (congr_fun hΔ_conj ⟨0, Nat.pos_of_ne_zero hD⟩)
        ⟨0, Nat.pos_of_ne_zero hD⟩
      simpa [Matrix.scalar, Matrix.diagonal] using h_inj
    have hre : c.re = 0 := by
      have h0 : c + starRingEnd ℂ c = 0 := by rw [hc_skew]; abel
      rw [Complex.add_conj] at h0
      have h1 : (2 : ℝ) * c.re = 0 := by exact_mod_cast h0
      linarith
    -- Step 8: Extract the real scalar l = c.im
    refine ⟨c.im, ?_⟩
    have hc_eq : c = Complex.I * (c.im : ℂ) := by
      ext
      · simp [hre]
      · simp
    show κ' = κ + (Complex.I * ↑c.im) • 1
    have : κ' = Δ + κ := by simp [Δ]
    rw [this, hc, ← hc_eq]
    ext i j
    simp [Matrix.scalar, Matrix.diagonal, Matrix.one_apply, smul_apply]
    split <;> simp

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
