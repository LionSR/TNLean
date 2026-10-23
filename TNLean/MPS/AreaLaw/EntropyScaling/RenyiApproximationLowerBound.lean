/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.EntropyScaling.CutReducedState
import QICLean.Entropy.RenyiRankLowerBound
import QICLean.Entropy.FilterOptimizer
import QICLean.Entropy.RegionEntropy

/-!
# Rényi lower bounds for matrix product state approximation

Approximation by an open-boundary matrix product state forces Rényi bounds
on every contiguous block. A prefix cut gives a logarithmic bond bound; a
block with two boundary cuts gives twice the logarithm. Empty blocks, the
whole chain, and chains of length zero or one are included. Only the target
vector is normalized. Source: SWVC08, arXiv:0705.0292v2, Eq. (eps-lower),
lines 269–270 and 333–345.

**Local fix (error-term sign):** the corrected logarithmic term is documented
in `docs/paper-gaps/swvc08_renyi_bond_dimension_sign.tex`.
-/

open scoped ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The corrected Rényi lower bound at an internal chain cut. The approximating
MPS need not be normalized. Source: SWVC08, arXiv:0705.0292v2,
Eq. (eps-lower) and lines 333–345. -/
theorem IsOpenMPS.renyiEntropy_leftBlock_add_log_error_le_log
    {L q D : ℕ} {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1)
    {k : ℕ} (hk0 : 0 < k) (hkL : k < L)
    {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    renyiEntropy (Entropy.regionState (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ)
      (Entropy.regionState_posSemidef _ _).isHermitian α +
      α / (α - 1) * Real.log (1 - δ) ≤ Real.log D := by
  have hρ := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q) (leftBlock L k) ψ
  exact hρ.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm
    (by simp [Entropy.trace_regionState, hψ])
    (Entropy.regionState_posSemidef _ φ).isHermitian
    (hφ.rank_regionState_leftBlock_le hk0 hkL) hα hδ
    ((rectangularTraceNorm_regionState_leftBlock_sub_le ψ φ k).trans herror)

/-- The corrected Rényi lower bound for any contiguous block, including empty
blocks, the whole chain, and chains of length zero or one. The approximating
MPS need not be normalized.
Source: SWVC08, arXiv:0705.0292v2, lines 269–270 and 333–345.

**Local fix (interior-block rank):** the right side is twice the logarithm of
the bond dimension. The source's single-bond expression applies to a prefix
or suffix; see `docs/paper-gaps/swvc08_interior_block_bond_rank.tex`. -/
theorem IsOpenMPS.renyiEntropy_sdiff_leftBlock_add_log_error_le_two_log
    {L q D : ℕ} {ψ φ : EuclideanSpace ℂ (Fin L → Fin q)}
    (hφ : IsOpenMPS L q D (fun x ↦ φ x)) (hψ : ‖ψ‖ = 1)
    {a b : ℕ} (hab : a ≤ b)
    {α δ : ℝ} (hα : 1 < α) (hδ : δ < 1)
    (herror : Matrix.rectangularTraceNorm
      (Matrix.euclideanOuterProduct ψ ψ - Matrix.euclideanOuterProduct φ φ) ≤ δ) :
    renyiEntropy (Entropy.regionState (n := fun _ : Fin L ↦ q)
      (leftBlock L b \ leftBlock L a) ψ)
      (Entropy.regionState_posSemidef _ _).isHermitian α +
      α / (α - 1) * Real.log (1 - δ) ≤ 2 * Real.log D := by
  have hρ := Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q)
    (leftBlock L b \ leftBlock L a) ψ
  have hbound := hρ.renyiEntropy_add_log_error_le_log_rank_of_rectangularTraceNorm
    (by simp [Entropy.trace_regionState, hψ])
    (Entropy.regionState_posSemidef _ φ).isHermitian
    (hφ.rank_regionState_sdiff_leftBlock_le_max_sq hab) hα hδ
    ((Entropy.rectangularTraceNorm_regionState_sub_le ψ φ _).trans herror)
  have hlog : Real.log (max 1 D : ℕ) = Real.log D := by
    rcases Nat.eq_zero_or_pos D with rfl | hD
    · simp
    · rw [max_eq_right hD]
  simpa only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat, hlog] using hbound

end TNLean.MPS.AreaLaw
