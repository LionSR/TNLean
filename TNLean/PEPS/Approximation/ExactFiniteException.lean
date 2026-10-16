/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ExactSmallSizeApproximation

/-!
# Removing finitely many exceptional square sizes

Increasing the prefactor preserves a native PEPS approximation. The exact
small-size construction therefore extends a uniform approximation for all
sufficiently large squares to every square of side length at least two.
The exponent is unchanged, and the enlarged prefactor is chosen before the
size, Hamiltonian, energy, and ground vector.

The equivalence below leaves the sufficiently-large-size existence statement
unproved. It does not assert the polynomial approximation theorem.

Source: *Polynomial PEPS approximation of gapped square-grid ground states*,
September 24, 2026, `07-assembly.tex`, lines 203–214, at immutable manuscript
revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.Approximation

/-- Increasing the prefactor preserves the same PEPS, phase, and error bound.
No sign condition on the exponent is needed. Source: manuscript, assembly,
lines 203–214, the enlargement of the polynomial-bond prefactor. -/
theorem HasPEPSApproximation.mono_prefactor {C C' c : ℝ} {L q : ℕ}
    {Ω : StateSpace L q} (h : HasPEPSApproximation C c L q Ω) (hC : C ≤ C') :
    HasPEPSApproximation C' c L q Ω := by
  obtain ⟨A, hpos, hbound, hne, herr⟩ := h
  refine ⟨A, hpos, ?_, hne, herr⟩
  intro e
  exact (hbound e).trans
    (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg (Nat.cast_nonneg L) c))

/-- The finite-size enlargement for an arbitrary class of unit vectors, one class
for each side length. Only the unit norm of an admissible vector enters, so the
class may consist of the gapped ground vectors of any family of Hamiltonians,
such as the finite-range interactions of the area-law model. Source: manuscript,
assembly, lines 203–214, whose small-size step uses the unit norm of the ground
vector alone. -/
theorem exists_uniform_approximation_of_sufficiently_large_of_norm_eq_one {q L₀ : ℕ}
    {C c : ℝ} (P : (L : ℕ) → StateSpace L q → Prop) (hq : 0 < q) (hc : 0 ≤ c)
    (hunit : ∀ L : ℕ, ∀ Ω : StateSpace L q, P L Ω → ‖Ω‖ = 1)
    (hlarge : ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ Ω : StateSpace L q, P L Ω →
      HasPEPSApproximation C c L q Ω) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → ∀ Ω : StateSpace L q, P L Ω → HasPEPSApproximation C' c L q Ω := by
  obtain ⟨C', hC', hCC', hsmall⟩ :=
    exists_uniform_small_size_approximation (L₀ := L₀) hq C c hc
  refine ⟨C', hC', hCC', ?_⟩
  intro L hL Ω hΩ
  by_cases hsize : L < L₀
  · exact hsmall L hL hsize Ω (hunit L Ω hΩ)
  · exact (hlarge L hL (Nat.le_of_not_gt hsize) Ω hΩ).mono_prefactor hCC'

/-- A uniform approximation above a fixed threshold extends to every square
of side length at least two, with the same exponent and a single positive
enlarged prefactor. Source: manuscript, assembly, lines 203–214. -/
theorem exists_uniform_approximation_of_sufficiently_large {q L₀ : ℕ}
    {J Δ C c : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (hlarge : ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C' c L q Ω := by
  obtain ⟨C', hC', hCC', hall⟩ :=
    exists_uniform_approximation_of_sufficiently_large_of_norm_eq_one
      (fun L Ω ↦ ∃ h : SquareHamiltonian L q J, ∃ E₀ : ℝ, h.IsGappedGroundState E₀ Ω Δ)
      hq hc
      (by
        rintro _ _ ⟨_, _, hΩ⟩
        exact hΩ.1)
      (by
        rintro L hL hL₀ Ω ⟨h, E₀, hΩ⟩
        exact hlarge L hL hL₀ h E₀ Ω hΩ)
  exact ⟨C', hC', hCC', fun L hL h E₀ Ω hΩ ↦ hall L hL Ω ⟨h, E₀, hΩ⟩⟩

/-- The uniform polynomial approximation statement is equivalent to the same
statement for all sufficiently large squares. Both constants and the threshold
are chosen before the size, Hamiltonian, energy, and ground vector. The
sufficiently-large-size existence statement remains an open hypothesis, not a
conclusion proved here. Source: manuscript, assembly, lines 203–214. -/
theorem polynomialPEPSApproximation_iff_sufficiently_large :
    PolynomialPEPSApproximation ↔
      ∀ q : ℕ, 2 ≤ q → ∀ J Δ : ℝ, 0 < J → 0 < Δ →
        ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ L₀ : ℕ,
          ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
            ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
              h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω := by
  constructor
  · intro happ q hq J Δ hJ hΔ
    obtain ⟨C, c, hC, hc, hall⟩ := happ q hq J Δ hJ hΔ
    exact ⟨C, c, hC, hc, 0, fun L hL _ h E₀ Ω hΩ ↦ hall L hL h E₀ Ω hΩ⟩
  · intro hlarge q hq J Δ hJ hΔ
    obtain ⟨C, c, _, hc, L₀, htail⟩ := hlarge q hq J Δ hJ hΔ
    obtain ⟨C', hC', _, hall⟩ :=
      exists_uniform_approximation_of_sufficiently_large (q := q) (by omega) hc.le htail
    exact ⟨C', c, hC', hc, hall⟩

end TNLean.PEPS.Approximation
