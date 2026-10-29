/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Hastings.LemmaOneConstant
import TNLean.Circuit.LiebRobinson.TimeScaling

/-!
# The Lieb–Robinson velocity and length in Hastings' factorization

For a range-`R` chain Hamiltonian, write `v₀ = chainLRVelocity R J`. The numerical
graph estimate gives `4 |X| ‖A‖ ‖B‖ exp(2(v₀ - 1)|t| - d)` for arbitrary finite
supports at distance at least `d`. It follows that `(8v₀, 8)` is an admissible velocity
and length pair. Raising either constant preserves the estimate.

After rescaling by the gap `Δ`, the physical velocities are
`8Δ chainLRVelocity R (J/Δ)` and `10Δ chainLRVelocity R (J/Δ)`. Their associated
lengths `max(2v/Δ, 8)` are exactly the two lengths used in the factorization.

**Local fix (length convention):** the commutator decays as `exp(-d/ξ_C)` on
`|t| ≤ d/v`. The printed equation multiplies `d` by `ξ_C` and uses an undefined
`l` in the time bound. The convention is recorded in
`docs/paper-gaps/hastings07_lemma1_decay_length.tex`.

Source: Hastings, arXiv:0705.2024v4, eq. `lrb` and the definition of `ξ`,
lines 96–112 and 139–142.
-/

open QuantumCircuit
open scoped Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

variable {L q R : ℕ} {J : ℝ}

/-- The numerical Lieb–Robinson estimate for two arbitrary finite supports on a chain.
The distance lower bound is vacuous when either support is empty; the commutator then
vanishes. Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112. -/
theorem ChainHamiltonian.norm_heisenberg_commutator_le_numeric
    (h : ChainHamiltonian L q R J) (X Y : Finset (Fin L))
    {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A X)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val) (t : ℝ) :
    ‖heisenbergEvolution h.operator t A * B - B * heisenbergEvolution h.operator t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ *
        Real.exp (2 * (chainLRVelocity R J - 1) * |t| - d) := by
  classical
  have hBound := norm_heisenberg_commutator_le_graphDistance_finsets_numeric
    (SimpleGraph.pathGraph L) (fun Z : ChainSupport L R ↦ Z.1)
    (fun Z ↦ Classical.choose Z.2.1) (fun Z ↦ Classical.choose_spec Z.2.1)
    h.term h.hermitian (fun Z ↦ mem_supportedOperators_of_isSupportedOn (h.supported Z))
    R (fun Z x hx y hy ↦ Z.edist_le x hx y hy)
    (R + 1) (by omega) (fun Z ↦ Z.2.card_le)
    (((2 ^ (2 * R + 1) : ℕ) : ℝ) * J) h.sum_norm_terms_containing_le X
    (mem_supportedOperators_of_isSupportedOn hA) Y
    (mem_supportedOperators_of_isSupportedOn hB) 1 (by norm_num) d
    (fun x hx y hy ↦ by
      simpa only [SimpleGraph.pathGraph_edist, ENat.natCast_le_natCast] using hd x hx y hy) t
  convert hBound using 1 <;>
    simp only [ChainHamiltonian.operator, chainLRVelocity, Nat.cast_add, Nat.cast_one,
      add_sub_cancel_right, mul_one, one_mul]
  ring_nf

/-- The time-cone form of Hastings' Lieb–Robinson bound, with numerical prefactor `4`.
Any positive velocity `v ≥ 8(v₀ - 1)` and length `ξ_C ≥ 8` are admissible. The distance
lower-bound formulation also includes empty supports. Hastings, arXiv:0705.2024v4,
eq. `lrb`, lines 96–112, in the length convention of the module docstring. -/
theorem ChainHamiltonian.norm_heisenberg_commutator_le_hastings
    (h : ChainHamiltonian L q R J) {v ξC : ℝ}
    (hvpos : 0 < v) (hv : 8 * (chainLRVelocity R J - 1) ≤ v) (hξC : 8 ≤ ξC)
    (X Y : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A X)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val)
    (t : ℝ) (ht : |t| ≤ d / v) :
    ‖heisenbergEvolution h.operator t A * B - B * heisenbergEvolution h.operator t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ * Real.exp (-(d / ξC)) := by
  have hcone : |t| * v ≤ (d : ℝ) := (le_div_iff₀ hvpos).mp ht
  have hspeed : 2 * (chainLRVelocity R J - 1) * |t| ≤ (d : ℝ) / 4 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hv) (abs_nonneg t)]
  have hdecay : (d : ℝ) / ξC ≤ d / 8 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg d) (by norm_num) hξC
  exact (h.norm_heisenberg_commutator_le_numeric X Y hA hB d hd t).trans
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by
      have := Nat.cast_nonneg (α := ℝ) d
      linarith)) (by positivity))

/-- The interaction-dependent part of the chain velocity is positive for `J > 0`.
Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112. -/
theorem chainLRVelocity_sub_one_pos (R : ℕ) {J : ℝ} (hJ : 0 < J) :
    0 < chainLRVelocity R J - 1 := by
  simp only [chainLRVelocity, add_sub_cancel_right]
  positivity

/-- An interaction-proportional velocity gives a source length large enough for the
printed entropy bound: the pair has velocity `40(v₀ - 1)` and length `80`.
Hastings, arXiv:0705.2024v4, lines 96–112 and 139–142. -/
theorem two_mul_lemmaOneEndpointLength_le_sourceLength (R : ℕ) {J Δ : ℝ}
    (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    2 * lemmaOneEndpointLength R J Δ ≤
      max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80 := by
  rw [lemmaOneEndpointLength_eq, lemmaOneLength_div R hJ hΔ]
  have hleft : 80 * ((chainLRVelocity R J - 1) / Δ) ≤
      max (2 * (40 * (chainLRVelocity R J - 1)) / Δ) 80 := by
    convert le_max_left (2 * (40 * (chainLRVelocity R J - 1)) / Δ) (80 : ℝ) using 1
    ring
  linarith [le_max_right (2 * (40 * (chainLRVelocity R J - 1)) / Δ) (80 : ℝ)]

/-- The factorization length in gap units is exactly `max(2v/Δ, 8)` with physical
velocity `v = 8Δ chainLRVelocity R (J/Δ)`. Hastings, arXiv:0705.2024v4,
lines 139–142. -/
theorem lemmaOneLength_eq_sourceLength (R : ℕ) (J : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    lemmaOneLength R (J / Δ) 1 =
      max (2 * (8 * Δ * chainLRVelocity R (J / Δ)) / Δ) 8 := by
  simp only [lemmaOneLength, div_one, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 8),
    mul_one]
  congr 1
  field_simp

/-- The enlarged factorization length is exactly `max(2v/Δ, 8)` with physical
velocity `v = 10Δ chainLRVelocity R (J/Δ)`. Hastings, arXiv:0705.2024v4,
lines 139–142. -/
theorem lemmaOneEndpointLength_eq_sourceLength (R : ℕ) (J : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    lemmaOneEndpointLength R J Δ =
      max (2 * (10 * Δ * chainLRVelocity R (J / Δ)) / Δ) 8 := by
  simp only [lemmaOneEndpointLength, mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 8),
    mul_one]
  congr 1
  field_simp
  ring

/-- Multiplying the rescaled interaction-dependent velocity by the gap restores the
physical velocity. Hastings, arXiv:0705.2024v4, lines 96–112 and 139–142. -/
theorem chainLRVelocity_gapRescaling (R : ℕ) (J : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) :
    Δ * (chainLRVelocity R (J / Δ) - 1) = chainLRVelocity R J - 1 := by
  simp only [chainLRVelocity, add_sub_cancel_right, abs_mul, abs_div, abs_of_pos hΔ]
  field_simp

/-- The rescaled factorization uses a physical velocity with the factor `Δ` restored.
For every `κ ≥ 8`, the pair `(κΔ chainLRVelocity R (J/Δ), 8)` satisfies Hastings'
time-cone estimate. Hastings, arXiv:0705.2024v4, eq. `lrb`, lines 96–112. -/
theorem ChainHamiltonian.norm_heisenberg_commutator_le_hastings_rescaled
    (h : ChainHamiltonian L q R J) {Δ κ : ℝ} (hΔ : 0 < Δ) (hκ : 8 ≤ κ)
    (X Y : Finset (Fin L)) {A B : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ}
    (hA : Entropy.IsSupportedOn (n := fun _ ↦ q) A X)
    (hB : Entropy.IsSupportedOn (n := fun _ ↦ q) B Y)
    (d : ℕ) (hd : ∀ x ∈ X, ∀ y ∈ Y, d ≤ Nat.dist x.val y.val)
    (t : ℝ) (ht : |t| ≤ d / (κ * Δ * chainLRVelocity R (J / Δ))) :
    ‖heisenbergEvolution h.operator t A * B - B * heisenbergEvolution h.operator t A‖ ≤
      4 * (X.card : ℝ) * ‖A‖ * ‖B‖ * Real.exp (-(d / (8 : ℝ))) := by
  have hu : 1 ≤ chainLRVelocity R (J / Δ) := by
    unfold chainLRVelocity
    exact le_add_of_nonneg_left (by positivity)
  have hvpos : 0 < κ * Δ * chainLRVelocity R (J / Δ) :=
    mul_pos (mul_pos (by linarith) hΔ) (by linarith)
  have hscale := chainLRVelocity_gapRescaling R J hΔ
  have hκ' := mul_le_mul_of_nonneg_right hκ
    (show 0 ≤ Δ * chainLRVelocity R (J / Δ) from mul_nonneg hΔ.le (by linarith))
  have hv : 8 * (chainLRVelocity R J - 1) ≤ κ * Δ * chainLRVelocity R (J / Δ) := by
    nlinarith only [hscale, hκ', hΔ]
  exact h.norm_heisenberg_commutator_le_hastings hvpos hv (by norm_num) X Y hA hB d hd t ht

end TNLean.MPS.AreaLaw
