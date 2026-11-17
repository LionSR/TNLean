/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.BlockedNormalSectors
import TNLean.MPS.Preparation.OverlappingLogLogPreparation

/-!
# Measurement preparation of arbitrary tensors after fixed blocking

Starting with an arbitrary translation-invariant tensor, derive its normal sectors,
stationary matrices and mixed gaps, then apply the overlapping-sector preparation theorems.
The blocking length and depth constants are chosen before the chain length and accuracy.
There is no supplied canonical form, period, transfer gap or injectivity assumption.

**Scope restriction (grouped sites):** circuits act on sites of dimension `d ^ p`.
The target is `blockTensor A p` on `M` grouped sites. Thus the represented physical lengths are `p * M`.
Transport to circuits on the original sites and lengths not divisible by `p` remains open;
these results do not close the unrestricted source theorem. See
`docs/paper-gaps/mswc24_measurement_preparation_scope.tex`.

## References

* arXiv:2307.01696, "Long-range MPS using measurements", eqs. (S2)--(S4).
* arXiv:1606.00608, Section II.C and Appendix A, canonical reduction after blocking.
-/

open MPSTensor QuantumCircuit
open scoped BigOperators InnerProductSpace
open Kraus (blockPhysDim blockTensor)

namespace MPSPreparation

/-- Every tensor admits a fixed positive blocking with logarithmic measurement preparation
at every nonzero blocked length at least two. Only the tensor is supplied; the normal
sectors, multiplicities, faithful fixed points and mixed spectral gaps are derived.
Circuits and depths are measured on the grouped sites.
Source: arXiv:2307.01696, "Long-range MPS using measurements" (fixed-blocking restriction). -/
theorem exists_isPreparedWithMeasurementsAndCircuitInDepth_blockTensor_le_log
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ c : ℝ,
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (M : ℕ) [NeZero M], 2 ≤ M →
        mpvState (blockTensor A p) M ≠ 0 →
        ∃ (ψ : MPVSpace (blockPhysDim d p) M) (T : ℕ), ‖ψ‖ = 1 ∧
          (T : ℝ) ≤ c * Real.log (M / ε) ∧
          IsPreparedWithMeasurementsAndCircuitInDepth T (fun s => ψ s) ∧
          1 - ‖⟪ψ, normalizedMPVState (blockTensor A p) M⟫_ℂ‖ ≤ ε := by
  obtain ⟨p, hp, P, σ, heq, hnormal, hleft, hpos, htr, hfix, hmix⟩ :=
    exists_blockTensor_normal_sectors_fixedPoints A
  refine ⟨p, hp, ?_⟩
  apply exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpv_eq_sum
    (blockTensor A p) hnormal hleft hpos htr hfix hmix P.coeff
  intro M _ s
  exact (heq M (Nat.pos_of_ne_zero (NeZero.ne M)) s).trans (P.mpv_toTensor_eq_sum_coeff s)

/-- Every tensor admits a fixed positive blocking with double-logarithmic preparation
using measurement rounds at every nonzero blocked length at least two. The constants
are uniform in length, accuracy and the resulting sector amplitudes; vanishing individual
power sums are allowed. Circuits act on grouped sites, not the original physical sites.
Source: arXiv:2307.01696, "Long-range MPS using measurements" (fixed-blocking restriction). -/
theorem exists_isPreparedWithMeasurementRoundsInDepth_blockTensor_le_log_log
    {d D : ℕ} (A : MPSTensor d D) :
    ∃ p : ℕ, 0 < p ∧ ∃ c : ℝ,
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ (M : ℕ) [NeZero M], 2 ≤ M →
        mpvState (blockTensor A p) M ≠ 0 →
        ∃ (ψ : MPVSpace (blockPhysDim d p) M) (T : ℕ), ‖ψ‖ = 1 ∧
          (T : ℝ) ≤ c * Real.log (Real.log (M / ε) + 1) ∧
          IsPreparedWithMeasurementRoundsInDepth T (fun s => ψ s) ∧
          1 - ‖⟪ψ, normalizedMPVState (blockTensor A p) M⟫_ℂ‖ ≤ ε := by
  obtain ⟨p, hp, P, σ, heq, hnormal, hleft, hpos, htr, hfix, hmix⟩ :=
    exists_blockTensor_normal_sectors_fixedPoints A
  refine ⟨p, hp, ?_⟩
  apply exists_isPreparedWithMeasurementRoundsInDepth_le_log_log_of_mpv_eq_sum
    (blockTensor A p) hnormal hleft hpos htr hfix hmix P.coeff
  intro M _ s
  exact (heq M (Nat.pos_of_ne_zero (NeZero.ne M)) s).trans (P.mpv_toTensor_eq_sum_coeff s)

end MPSPreparation
