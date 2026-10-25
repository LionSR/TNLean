/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.MPSApproximation
import QICLean.Analysis.SpectralTailTraceNorm

/-!
# Approximation from separately smoothed marginal states

Source: Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 539–559.
Each cut may use a different nearby density matrix. The smoothing radius is
measured in the full trace norm; it contributes half its value to the bound
on discarded spectral mass. This supplies the finite-chain estimate for the
smooth entropy family criterion. Only the individual marginal tails enter
this estimate; no common smoothing state is assumed.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace Matrix

private theorem IsHermitian.kyFanNorm_eq_trace_re_of_card_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) {D : ℕ} (hD : Fintype.card ι ≤ D) :
    hρ.kyFanNorm D = ρ.trace.re := by
  rw [← hρ.kyFanNorm_card_eq_trace_re, hρ.kyFanNorm_eq_sum_fin,
    hρ.kyFanNorm_eq_sum_fin]
  exact Finset.sum_congr rfl fun i _ ↦ by simp [i.isLt, i.isLt.trans_le hD]

private theorem IsHermitian.trace_sub_kyFanNorm_le_add_traceDistance
    {ι : Type*} [Fintype ι] [DecidableEq ι] {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.IsHermitian) (hσ : σ.IsHermitian) (htrace : ρ.trace = σ.trace) (D : ℕ) :
    ρ.trace.re - hρ.kyFanNorm D ≤
      σ.trace.re - hσ.kyFanNorm D + traceDistance ρ σ := by
  by_cases hD : D ≤ Fintype.card ι
  · have h := hρ.sum_descEigenvalue_tail_le_add_traceDistance hσ htrace D
    rw [Finset.sum_Ico_eq_sub _ hD, Finset.sum_Ico_eq_sub _ hD] at h
    change hρ.kyFanNorm (Fintype.card ι) - hρ.kyFanNorm D ≤
      hσ.kyFanNorm (Fintype.card ι) - hσ.kyFanNorm D + traceDistance ρ σ at h
    simpa only [hρ.kyFanNorm_card_eq_trace_re, hσ.kyFanNorm_card_eq_trace_re] using h
  · rw [hρ.kyFanNorm_eq_trace_re_of_card_le (by omega),
      hσ.kyFanNorm_eq_trace_re_of_card_le (by omega)]
    simpa using traceDistance_nonneg ρ σ

end Matrix

namespace TNLean.MPS.AreaLaw

/-- The squared truncation error is bounded by the tails of independently
smoothed marginal states and half the sum of their full trace-norm errors.
This is the finite-chain estimate in the smoothing argument of
Schuch–Wolf–Verstraete–Cirac, arXiv:0705.0292v2, lines 539–559. -/
theorem norm_sequentialTruncation_leadingEigenprojection_sub_sq_le_of_smoothing
    {L q D : ℕ} (ψ : EuclideanSpace ℂ (Fin L → Fin q)) (hψ : ‖ψ‖ = 1)
    (T η : ℕ → ℝ)
    (hσ : ∀ k ∈ Finset.Ico 1 L,
      ∃ (σ : Matrix (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))
          (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k)) ℂ)
        (hσ : σ.PosSemidef), σ.trace = 1 ∧
        rectangularTraceNorm (Entropy.regionState (leftBlock L k) ψ - σ) ≤ η k ∧
        1 - hσ.isHermitian.kyFanNorm D ≤ T k) :
    let P : ∀ k : ℕ, LeftBlockMatrix L q k := fun k ↦
      (Entropy.regionState_isHermitian (leftBlock L k) ψ).leadingEigenprojection D
    ‖sequentialTruncation P (L - 1) ψ - ψ‖ ^ 2 ≤
      ∑ k ∈ Finset.Ico 1 L, (T k + η k / 2) := by
  exact (norm_sequentialTruncation_leadingEigenprojection_sub_sq_le ψ hψ D).trans
    (Finset.sum_le_sum (fun k hk ↦ by
      obtain ⟨σ, hσ, htr, hη, hT⟩ := hσ k hk
      have h := Matrix.IsHermitian.trace_sub_kyFanNorm_le_add_traceDistance
        (Entropy.regionState_isHermitian (leftBlock L k) ψ) hσ.isHermitian
          ((Entropy.trace_regionState_eq_one hψ).trans htr.symm) D
      rw [Entropy.trace_regionState_eq_one hψ, htr, Complex.one_re,
        traceDistance_eq_rectangularTraceNorm
          (Entropy.regionState_isHermitian (leftBlock L k) ψ) hσ.isHermitian] at h
      linarith))

end TNLean.MPS.AreaLaw
