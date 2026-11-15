/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.InteractionBudgetImaginaryTime
import TNLean.MPS.AreaLaw.InteractionBudget
import TNLean.Circuit.EntropySupport

/-!
# Imaginary-time conjugation for finite-range chain interactions

The existing chain support count supplies the per-site budget for the finite-site
commutator estimate. The generator is the actual chain Hamiltonian, with any scalar
energy shift. No gap, positivity or positive local dimension is required.
The use of `max J 0` retains the empty chain even when its vacuous norm bound is negative.

Source: AKL14, arXiv:1406.3898, Section 3, conservative auxiliary to Lemma 3.1;
the chain budget is the counting estimate for the one-dimensional note, `eq:ham`.
-/

open scoped BigOperators Matrix.Norms.L2Operator

namespace TNLean.MPS.AreaLaw

/-- The original finite-range chain Hamiltonian satisfies the finite-site
imaginary-time estimate with budget `2^(2R+1) * max J 0`. This also applies
to the empty chain; no separate sign assumption on `J` is imposed. -/
theorem ChainHamiltonian.norm_exp_conjugation_shift_le_two
    {L q R : ℕ} {J : ℝ} (h : ChainHamiltonian L q R J)
    (O : Matrix (Fin L → Fin q) (Fin L → Fin q) ℂ) (S : Finset (Fin L))
    (hO : Entropy.IsSupportedOn (n := fun _ ↦ q) O S) (hS : S.card ≤ R + 1)
    (z : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hsmall : (2 * ((2 ^ (2 * R + 1) : ℕ) : ℝ) * max J 0 * (R + 1)) * t ≤ 1 / 2) :
    ‖NormedSpace.exp ((t : ℂ) • (h.operator - z • 1)) * O *
      NormedSpace.exp (-((t : ℂ) • (h.operator - z • 1)))‖ ≤ 2 * ‖O‖ := by
  classical
  apply TNLean.Lattice.norm_exp_conjugation_interactionBudget_shift_le_two
    (fun X : ChainSupport L R ↦ X.1) h.term (R + 1)
    (((2 ^ (2 * R + 1) : ℕ) : ℝ) * max J 0) (by positivity)
    (fun X ↦ QuantumCircuit.mem_supportedOperators_of_isSupportedOn (h.supported X))
    (fun X ↦ X.2.card_le) ?_ O S
    (QuantumCircuit.mem_supportedOperators_of_isSupportedOn hO) hS z t ht ?_
  · intro x
    exact (h.sum_norm_terms_containing_le x).trans
      (mul_le_mul_of_nonneg_left (le_max_left J 0) (by positivity))
  · simpa only [Nat.cast_add, Nat.cast_one, mul_assoc] using hsmall

end TNLean.MPS.AreaLaw
