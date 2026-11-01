/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.FiniteRingGaussianFilter
import TNLean.Lattice.GaussianNegativeFrequencyLocality

/-!
# Uniform negative-frequency locality on the actual finite ring

The actual periodic nearest-neighbour Lieb–Robinson bound supplies the
short-time increment in the Gaussian/Cauchy frequency estimate. Its
cancellation at zero time makes the result independent of the positive
Cauchy regularizer, so the actual scalar frequency limit can be used.

Source: Hastings–Koma, arXiv:math-ph/0507008, Section 3 and Appendix A;
the finite physical input for the SPC11 Section II.F gap argument.
-/

open QuantumCircuit MPSPreparation GaussianFilter TNLean.Lattice
open scoped Matrix Matrix.Norms.L2Operator NNReal

namespace MPSTensor

/-- The actual local Hamiltonian supplies the Gaussian negative-frequency
commutator estimate, with no propagation or correlation premise. The
bound is uniform over positive regularizers, physical dimensions and
ring lengths. Source: Hastings–Koma, arXiv:math-ph/0507008,
Section 3 and Appendix A, specialized to the periodic nearest-neighbour
interaction used in SPC11, arXiv:1010.3732, Section II.F. -/
theorem norm_negativeFrequency_interactionHamiltonian_commutator_le
    {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (h : MPOTensor.ChainOperator d 2) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : MPOTensor.ChainOperator d N)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ supportedOperators d X) (hB : B ∈ supportedOperators d Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (s : ℝ≥0) {ε T a : ℝ} (hε : 0 < ε) (hT : 0 < T) (ha : 0 ≤ a) :
    ‖gaussianNegativeFrequencyOperator s ε (interactionHamiltonian h hN) A * B -
        B * gaussianNegativeFrequencyOperator s ε (interactionHamiltonian h hN) A‖ ≤
      kernel s⁻¹ 0 *
        ((2 * ‖A‖ * ‖B‖ * X.card *
            Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY)) *
            (8 * Real.exp a) * Real.exp ((8 * Real.exp a) * T) +
          (2 * ‖A‖ * ‖B‖ / T) * Real.exp (-T ^ 2 / (2 * (s : ℝ)))) := by
  apply norm_commutator_gaussianNegativeFrequencyOperator_le s
    (interactionHamiltonian_isHermitian hN hHerm) A B hε hT (by positivity) (by positivity)
  intro t
  exact norm_interactionHamiltonian_commutator_le_exp_abs_of_disjoint hN h hHerm hNorm
    A B X Y hX hY hA hB hXY a ha t

end MPSTensor
