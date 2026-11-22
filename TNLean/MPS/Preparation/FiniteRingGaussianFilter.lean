/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.FiniteRingLiebRobinson
import QICLean.ManyBody.Hamiltonian.GaussianFilterLocality

/-!
# Gaussian-filtered commutators on finite periodic chains

The periodic nearest-neighbor Lieb–Robinson bound supplies the short-time
input to the existing Gaussian locality estimate. The resulting bound has
constants independent of ring length and physical dimension, with arbitrary
ground energy and without frustration freedom.

This is a filtering estimate needed for the physical-gap route to the SPT
converse. A symmetric Gaussian filter by itself does not isolate the
positive-energy contribution to an ordinary connected correlation; this
module does not assert exponential clustering or a transfer spectral gap.

## References

* Hastings, arXiv:cond-mat/0508554v3, equation `lbnd`, lines 266–283 and
  its proof at lines 1419–1456: short-time propagation plus a Gaussian tail.
* Hastings–Koma, arXiv:math-ph/0507008, Appendix A, Theorem A.2: the
  propagation input specialized here to periodic nearest-neighbor chains.
* Schuch–Pérez-García–Cirac, arXiv:1010.3732, Section II.F, lines 929–953:
  the SPT converse whose physical-gap argument requires further assembly.
-/

open NormedSpace QuantumCircuit MPSPreparation
open scoped Matrix Matrix.Norms.L2Operator

namespace MPSTensor

/-- Gaussian averaging of the actual finite-ring dynamics gives the sum of
the short-time propagation error and the Gaussian tail, uniformly in ring
length and physical dimension. This is the periodic specialization of
Hastings, arXiv:cond-mat/0508554v3, equation `lbnd`, lines 266–283.
No clustering estimate is assumed. -/
theorem norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le
    {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (h : MPOTensor.ChainOperator d 2) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : MPOTensor.ChainOperator d N)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    (a : ℝ) (ha : 0 ≤ a) {q Δ T : ℝ} (hq : 0 ≤ q) (hT : 0 ≤ T) :
    ‖ManyBody.gaussianFilteredTerm q Δ
          (ManyBody.Interaction.translationInvariant hN h).hamiltonian A * B -
        B * ManyBody.gaussianFilteredTerm q Δ
          (ManyBody.Interaction.translationInvariant hN h).hamiltonian A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-a * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          (Real.exp ((8 * Real.exp a) * T) - 1) +
        2 * ‖A‖ * ‖B‖ * Real.exp (-(T * Δ) ^ 2 / (2 * q)) := by
  have hExp : 0 ≤ Real.exp ((8 * Real.exp a) * T) - 1 := by
    apply sub_nonneg.mpr
    exact Real.one_le_exp (by positivity)
  refine ManyBody.norm_commutator_gaussianFilteredTerm_le hq
    (ManyBody.Interaction.isHermitian_hamiltonian
      (ManyBody.Interaction.isHermitian_translates_term _ hHerm)) A B hT (by positivity) ?_
  intro t ht
  have htAbs : |t| ≤ T := abs_le.mpr ht
  change ‖(exp (t • (Complex.I • (ManyBody.Interaction.translationInvariant hN h).hamiltonian)) *
      A * exp ((-t) • (Complex.I •
        (ManyBody.Interaction.translationInvariant hN h).hamiltonian))) * B -
    B * (exp (t • (Complex.I • (ManyBody.Interaction.translationInvariant hN h).hamiltonian)) *
      A * exp ((-t) • (Complex.I •
        (ManyBody.Interaction.translationInvariant hN h).hamiltonian)))‖ ≤ _
  refine (norm_hamiltonian_translationInvariant_commutator_le_exp_abs_of_disjoint hN h hHerm hNorm
    A B X Y hX hY hA hB hXY a ha t).trans ?_
  gcongr

/-- A concrete Gaussian parameter gives exponential decay in the separation
of the supports. The spectral filtering error for this same parameter is
`exp (-ℓ * Δ / (32 * exp 1))`. This is the short-time/tail balance in
Hastings, arXiv:cond-mat/0508554v3, equation `lbnd`, with the actual periodic
velocity `8 * exp 1`. It is a filtered commutator bound, not an ordinary
connected-correlation estimate. -/
theorem norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le_exp
    {d N : ℕ} [NeZero N] (hN : 2 ≤ N)
    (h : MPOTensor.ChainOperator d 2) (hHerm : h.IsHermitian) (hNorm : ‖h‖ ≤ 1)
    (A B : MPOTensor.ChainOperator d N)
    (X Y : Finset (Fin N)) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hA : A ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) X)
    (hB : B ∈ ManyBody.supportedOperators (fun _ ↦ Fin d) Y)
    (hXY : Disjoint (X : Set (Fin N)) (Y : Set (Fin N)))
    {ℓ Δ : ℝ} (hℓ : 0 < ℓ) (hΔ : 0 < Δ)
    (hDist : ℓ ≤ ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) :
    let q := ℓ / (16 * Real.exp 1) * Δ
    ‖ManyBody.gaussianFilteredTerm q Δ
          (ManyBody.Interaction.translationInvariant hN h).hamiltonian A * B -
        B * ManyBody.gaussianFilteredTerm q Δ
          (ManyBody.Interaction.translationInvariant hN h).hamiltonian A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card * Real.exp (-ℓ / 2) +
        2 * ‖A‖ * ‖B‖ * Real.exp (-ℓ * Δ / (32 * Real.exp 1)) := by
  let T := ℓ / (16 * Real.exp 1)
  have hT : 0 < T := div_pos hℓ (by positivity)
  have hTime : (8 * Real.exp (1 : ℝ)) * T = ℓ / 2 := by
    dsimp [T]
    field_simp [ne_of_gt (Real.exp_pos (1 : ℝ))]
    ring
  have hTail : -(T * Δ) ^ 2 / (2 * (T * Δ)) =
      -ℓ * Δ / (32 * Real.exp 1) := by
    dsimp [T]
    field_simp [ne_of_gt hℓ, ne_of_gt hΔ, ne_of_gt (Real.exp_pos (1 : ℝ))]
    ring
  refine (norm_gaussianFilteredTerm_hamiltonian_translationInvariant_commutator_le hN h hHerm hNorm
    A B X Y hX hY hA hB hXY 1 (by norm_num) (mul_nonneg hT.le hΔ.le) hT.le).trans ?_
  rw [hTime, hTail]
  refine add_le_add ?_ le_rfl
  calc
    2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          (Real.exp (ℓ / 2) - 1) ≤
        2 * ‖A‖ * ‖B‖ * X.card *
          Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY) *
          Real.exp (ℓ / 2) := by gcongr; linarith
    _ = 2 * ‖A‖ * ‖B‖ * X.card *
        Real.exp (-1 * ringSupportDistance (X : Set (Fin N)) (Y : Set (Fin N)) hX hY +
          ℓ / 2) := by rw [mul_assoc, ← Real.exp_add]
    _ ≤ 2 * ‖A‖ * ‖B‖ * X.card * Real.exp (-ℓ / 2) := by
      gcongr
      linarith

end MPSTensor
