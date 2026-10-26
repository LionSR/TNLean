/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.CutReducedState
import QICLean.Entropy.RegionPureApproximationTail

/-!
# Spectral-tail lower bound for MPS approximation

At each internal cut, approximating a unit chain vector by an open-boundary
matrix product state costs at least the discarded ordered marginal spectrum.
The approximant need not be normalized, and the full trace error is unrestricted.

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2,
Eq. (eps-lower), lines 246–264.
-/

open scoped ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The discarded ordered spectrum at an internal cut is bounded by the full
pure-density trace error of any MPS approximant of bond dimension `D`.
No normalization of the approximant or small-error assumption is required.
Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower), lines 246–264. -/
theorem IsOpenMPS.sum_descEigenvalue_leftBlock_tail_le_traceNorm
    {L q D : ℕ} {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1)
    {k : ℕ} (hk0 : 0 < k) (hkL : k < L) :
    ∑ i ∈ Finset.Ico D (Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q)
      (leftBlock L k))),
      (Entropy.regionState_posSemidef (leftBlock L k) ψ).isHermitian.descEigenvalue i ≤
        Matrix.rectangularTraceNorm
          (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) := by
  classical
  by_cases hsmall : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) < 1
  · have ht := Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
      ψ φ hψ (leftBlock L k) (hφ.rank_regionState_leftBlock_le hk0 hkL) hsmall le_rfl
    exact ht.trans (half_le_self (Matrix.rectangularTraceNorm_nonneg _))
  · apply le_trans (b := (1 : ℝ)) ?_ (le_of_not_gt hsmall)
    have htotal : (Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q)
        (leftBlock L k) ψ).isHermitian.kyFanNorm
        (Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))) = 1 := by
      rw [Matrix.IsHermitian.kyFanNorm_card_eq_trace_re]
      simp [Entropy.trace_regionState, hψ]
    rw [← htotal]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact fun i hi ↦ Finset.mem_range.mpr (Finset.mem_Ico.mp hi).2
    · exact fun i _ _ ↦ (Entropy.regionState_posSemidef (leftBlock L k) ψ).descEigenvalue_nonneg i

end TNLean.MPS.AreaLaw
