/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.CutReducedState
import TNLean.MPS.AreaLaw.EntropyScaling.VonNeumannSpectralTail
import QICLean.Entropy.RegionPureApproximationTail
import Mathlib.Analysis.SpecialFunctions.Log.PosLog

/-!
# Von Neumann entropy bounds from MPS approximation

A unit chain vector approximated by an open-boundary MPS in full pure-density
trace norm with error `δ < 1` has regional entropy bounded by the logarithm of
the approximant's regional rank, plus `δ / 2` times the logarithm of the regional
dimension, plus `log 2`. The approximating vector need not be normalized.
A prefix uses one bond; a general contiguous block uses two.

**Local fix (error range and interior rank):** these theorems establish the
small-error range `δ < 1`, repairing the unrestricted printed range discussed
in `docs/paper-gaps/swvc08_von_neumann_error_range.tex`. The interior-block bound
has `2 * log D`, as documented in
`docs/paper-gaps/swvc08_interior_block_bond_rank.tex`. They do not formalize the
unrestricted printed entropy statement. Source: SWVC08, arXiv:0705.0292v2,
`paper_v2.tex`, lines 269–305.
-/

namespace TNLean.MPS.AreaLaw

/-- The logarithm of an integer rank budget is unchanged by replacing zero by one,
with the convention `Real.log 0 = 0`. -/
private theorem log_max_one_nat (D : ℕ) : Real.log (max 1 D : ℕ) = Real.log D := by
  rw [Nat.cast_max, Nat.cast_one, ← Real.posLog_eq_log_max_one (Nat.cast_nonneg D)]
  exact max_eq_right (Real.log_natCast_nonneg D)

/-- The small-error von Neumann bound at a single chain boundary. This is the
corrected small-error form of SWVC08, arXiv:0705.0292v2, lines 278–305.
Empty and full prefixes and chains of length zero or one are included. -/
theorem IsOpenMPS.regionEntropy_leftBlock_le_log_add_half_error {L q D : ℕ}
    {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1) (k : ℕ)
    {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ ≤
      Real.log D + δ / 2 * ((leftBlock L k).card : ℝ) * Real.log q + Real.log 2 := by
  have ht := Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ φ hψ (leftBlock L k) (hφ.rank_regionState_leftBlock_le_max k) hδ herror
  have hb := regionEntropy_le_log_rank_add_spectral_tail ψ hψ (leftBlock L k) ht
  simpa only [log_max_one_nat] using hb

/-- The small-error von Neumann bound for a contiguous block. Two boundaries give
`2 * log D`. This is the corrected form of SWVC08, arXiv:0705.0292v2,
lines 269–305, including empty blocks, endpoints, and short chains. -/
theorem IsOpenMPS.regionEntropy_sdiff_leftBlock_le_two_log_add_half_error {L q D : ℕ}
    {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1)
    {a b : ℕ} (hab : a ≤ b) {δ : ℝ} (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    Entropy.regionEntropy (n := fun _ : Fin L ↦ q)
      (leftBlock L b \ leftBlock L a) ψ ≤
      2 * Real.log D + δ / 2 * ((leftBlock L b \ leftBlock L a).card : ℝ) *
        Real.log q + Real.log 2 := by
  have ht := Entropy.sum_descEigenvalue_regionState_tail_le_half_pure_trace_error
    ψ φ hψ (leftBlock L b \ leftBlock L a)
    (hφ.rank_regionState_sdiff_leftBlock_le_max_sq hab) hδ herror
  have hb := regionEntropy_le_log_rank_add_spectral_tail ψ hψ
    (leftBlock L b \ leftBlock L a) ht
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, log_max_one_nat] using hb

end TNLean.MPS.AreaLaw
