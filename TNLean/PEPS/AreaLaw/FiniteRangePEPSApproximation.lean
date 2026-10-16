/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularSpecialization
import TNLean.PEPS.Approximation.ExactFiniteException

/-!
# Polynomial PEPS approximation for finite-range interactions

The approximation target of the polynomial-PEPS manuscript is stated for
nearest-neighbor site and edge terms on the open square. The area-law model
admits one bounded Hermitian term per nonempty support of bounded
induced-graph diameter. This module states the uniform polynomial
approximation for those finite-range interactions on the integer domain of
the open square, with the ground vector read in domain coordinates, and proves
the parts that do not depend on the interaction class: the removal of finitely
many exceptional sizes, the equivalence with the sufficiently-large-size form,
and the specialization at range one to the manuscript's nearest-neighbor
target.

The finite-range target is a generalization made in this library of the
manuscript's Theorem 1.1. The manuscript does not state it, and no proof of
either target is asserted here.

## Main definitions

* `FiniteRangePolynomialPEPSApproximation`: the finite-range uniform target.

## Main results

* `exists_uniform_finiteRange_approximation_of_sufficiently_large`: finitely
  many exceptional sizes are removed with one enlarged prefactor.
* `finiteRangePolynomialPEPSApproximation_iff_sufficiently_large`: the target
  is equivalent to its sufficiently-large-size form.
* `FiniteRangePolynomialPEPSApproximation.polynomialPEPSApproximation`: the
  finite-range target implies the nearest-neighbor target.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Theorem 1.1 (`thm:main`), `eq:model`, `eq:global-gap`,
  and `07-assembly.tex`, lines 203–214.
* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, `eq:hamiltonian` and Corollary 1.2.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscripts; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.AreaLaw

/-- The removal of finitely many exceptional sizes for the gapped ground vectors
of finite-range interactions on the open square, read in area-law coordinates.
The exponent is unchanged, and the enlarged prefactor is chosen before the size,
interaction family, energy, and ground vector. Source: polynomial-PEPS
`07-assembly.tex`, lines 203–214, whose small-size step uses the unit norm alone,
for the interaction class of area-law `eq:hamiltonian`. -/
theorem exists_uniform_finiteRange_approximation_of_sufficiently_large {q R L₀ : ℕ}
    {J Δ C c : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (hlarge : ∀ L : ℕ, 2 ≤ L → L₀ ≤ L →
      ∀ h : LocalHamiltonian (rectangularDomain L L) q R J, ∀ E₀ : ℝ,
        ∀ Ω : RectangleStateSpace L L q,
          IsGappedGroundState (rectangularDomain L L) q h.operator E₀
            (rectangleAreaLawState Ω) Δ →
          Approximation.HasPEPSApproximation C c L q Ω) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : LocalHamiltonian (rectangularDomain L L) q R J, ∀ E₀ : ℝ,
        ∀ Ω : RectangleStateSpace L L q,
          IsGappedGroundState (rectangularDomain L L) q h.operator E₀
            (rectangleAreaLawState Ω) Δ →
          Approximation.HasPEPSApproximation C' c L q Ω := by
  obtain ⟨C', hC', hCC', hall⟩ :=
    Approximation.exists_uniform_approximation_of_sufficiently_large_of_norm_eq_one
      (fun L (Ω : RectangleStateSpace L L q) ↦
        ∃ h : LocalHamiltonian (rectangularDomain L L) q R J, ∃ E₀ : ℝ,
          IsGappedGroundState (rectangularDomain L L) q h.operator E₀
            (rectangleAreaLawState Ω) Δ)
      hq hc
      (by
        rintro _ Ω ⟨_, _, hΩ⟩
        have hunit := hΩ.1
        rwa [norm_rectangleAreaLawState] at hunit)
      (by
        rintro L hL hL₀ Ω ⟨h, E₀, hΩ⟩
        exact hlarge L hL hL₀ h E₀ Ω hΩ)
  exact ⟨C', hC', hCC', fun L hL h E₀ Ω hΩ ↦ hall L hL Ω ⟨h, E₀, hΩ⟩⟩

/-- **Finite-range uniform polynomial PEPS approximation.** For every local
dimension `q ≥ 2`, every interaction range `R`, and all `J, Δ > 0`, there are
`C, c > 0`, chosen before the size, interaction family, energy, and ground
vector, such that every gapped unit ground vector of every interaction family
of range `R` and term bound `J` on the integer domain of the open `L × L`
square, `L ≥ 2`, has a nonzero native PEPS approximation on the square with
bond dimensions at most `C L ^ c` and phase-normalized error at most `L⁻¹`.
The ground vector is read in domain coordinates through
`rectangleAreaLawState`.

This is a generalization made in this library of polynomial-PEPS Theorem 1.1
(`thm:main`) to the interaction class of area-law `eq:hamiltonian`. At range
one it contains the nearest-neighbor target
`Approximation.PolynomialPEPSApproximation`, by
`FiniteRangePolynomialPEPSApproximation.polynomialPEPSApproximation`. The
manuscript states only the nearest-neighbor case, and no proof of either
target is asserted here. -/
def FiniteRangePolynomialPEPSApproximation : Prop :=
  ∀ q : ℕ, 2 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : LocalHamiltonian (rectangularDomain L L) q R J,
        ∀ E₀ : ℝ, ∀ Ω : RectangleStateSpace L L q,
          IsGappedGroundState (rectangularDomain L L) q h.operator E₀
            (rectangleAreaLawState Ω) Δ →
          Approximation.HasPEPSApproximation C c L q Ω

/-- The finite-range uniform target is equivalent to the same statement for all
sufficiently large squares, with the constants and the threshold chosen before
the size, interaction family, energy, and ground vector. The
sufficiently-large-size existence statement remains an open hypothesis.
Source: polynomial-PEPS `07-assembly.tex`, lines 203–214, for the interaction
class of area-law `eq:hamiltonian`. -/
theorem finiteRangePolynomialPEPSApproximation_iff_sufficiently_large :
    FiniteRangePolynomialPEPSApproximation ↔
      ∀ q : ℕ, 2 ≤ q → ∀ R : ℕ, ∀ J Δ : ℝ, 0 < J → 0 < Δ →
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ L₀ : ℕ,
          ∀ L : ℕ, 2 ≤ L → L₀ ≤ L →
            ∀ h : LocalHamiltonian (rectangularDomain L L) q R J, ∀ E₀ : ℝ,
              ∀ Ω : RectangleStateSpace L L q,
                IsGappedGroundState (rectangularDomain L L) q h.operator E₀
                  (rectangleAreaLawState Ω) Δ →
                Approximation.HasPEPSApproximation C c L q Ω := by
  constructor
  · intro happ q hq R J Δ hJ hΔ
    obtain ⟨C, c, hC, hc, hall⟩ := happ q hq R J Δ hJ hΔ
    exact ⟨C, c, hC, hc, 0, fun L hL _ h E₀ Ω hΩ ↦ hall L hL h E₀ Ω hΩ⟩
  · intro hlarge q hq R J Δ hJ hΔ
    obtain ⟨C, c, _, hc, L₀, htail⟩ := hlarge q hq R J Δ hJ hΔ
    obtain ⟨C', hC', _, hall⟩ :=
      exists_uniform_finiteRange_approximation_of_sufficiently_large (q := q) (by omega)
        hc.le htail
    exact ⟨C', c, hC', hc, hall⟩

/-- The finite-range target contains the manuscript's nearest-neighbor target: a
square Hamiltonian is a range-one interaction family on the integer domain of
the square, with the same gapped unit ground vector in domain coordinates.
Source: polynomial-PEPS Theorem 1.1 and `eq:model`, with the conversion of
area-law Corollary 1.2. -/
theorem FiniteRangePolynomialPEPSApproximation.polynomialPEPSApproximation
    (happ : FiniteRangePolynomialPEPSApproximation) :
    Approximation.PolynomialPEPSApproximation := by
  intro q hq J Δ hJ hΔ
  obtain ⟨C, c, hC, hc, hall⟩ := happ q hq 1 J Δ hJ hΔ
  refine ⟨C, c, hC, hc, fun L hL h E₀ Ω hΩ ↦ ?_⟩
  exact hall L hL (h.toRectangularHamiltonian.toAreaLawHamiltonian hJ.le) E₀ Ω
    (h.toRectangularHamiltonian.isGappedGroundState_toAreaLawHamiltonian hJ.le hΩ)

end TNLean.PEPS.AreaLaw
