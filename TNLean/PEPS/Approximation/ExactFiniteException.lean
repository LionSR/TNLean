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

/-- **Removing the small sizes at a named prefactor.** If a unit vector on a square of side
`L ≥ 2` has a PEPS approximation with prefactor `C` whenever `L₀ ≤ L`, then it has one with
prefactor `max C (q ^ (L₀ * L₀))` and the same exponent `c ≥ 0`: below `L₀` the exact
representation of `hasPEPSApproximation_of_small_size` applies. Source: manuscript, assembly,
lines 203–214. -/
theorem hasPEPSApproximation_of_sufficiently_large_le {q L L₀ : ℕ} {C c : ℝ}
    (hq : 0 < q) (hL : 2 ≤ L) (hc : 0 ≤ c) {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1)
    (hlarge : L₀ ≤ L → HasPEPSApproximation C c L q Ω) :
    HasPEPSApproximation (max C (q ^ (L₀ * L₀) : ℕ)) c L q Ω := by
  by_cases hsize : L < L₀
  · exact hasPEPSApproximation_of_small_size hq (by omega) hsize.le C c hc Ω hΩ
  · exact (hlarge (Nat.le_of_not_gt hsize)).mono_prefactor (le_max_left _ _)

/-- A uniform approximation above a fixed threshold extends to every square
of side length at least two, with the same exponent and the single positive
enlarged prefactor `max C (q ^ (L₀ * L₀))` of
`hasPEPSApproximation_of_sufficiently_large_le`. Source: manuscript, assembly,
lines 203–214. -/
theorem exists_uniform_approximation_of_sufficiently_large {q L₀ : ℕ}
    {J Δ C c : ℝ} (hq : 0 < q) (hc : 0 ≤ c)
    (hlarge : ∀ L : ℕ, 2 ≤ L → L₀ ≤ L → ∀ h : SquareHamiltonian L q J,
      ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
        h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C c L q Ω) :
    ∃ C' : ℝ, 0 < C' ∧ C ≤ C' ∧
      ∀ L : ℕ, 2 ≤ L → ∀ h : SquareHamiltonian L q J,
        ∀ E₀ : ℝ, ∀ Ω : StateSpace L q,
          h.IsGappedGroundState E₀ Ω Δ → HasPEPSApproximation C' c L q Ω := by
  refine ⟨max C (q ^ (L₀ * L₀) : ℕ), ?_, le_max_left _ _, fun L hL h E₀ Ω hΩ ↦
    hasPEPSApproximation_of_sufficiently_large_le hq hL hc hΩ.1
      (fun hL₀ ↦ hlarge L hL hL₀ h E₀ Ω hΩ)⟩
  exact (show (0 : ℝ) < (q ^ (L₀ * L₀) : ℕ) by exact_mod_cast pow_pos hq _).trans_le
    (le_max_right _ _)

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
