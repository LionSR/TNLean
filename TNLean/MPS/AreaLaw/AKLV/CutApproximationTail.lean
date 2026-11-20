/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ViableSet.Basic
import QICLean.Channel.MaximalOverlap

/-!
# Schmidt tails from actual cut approximants

A unit vector within squared distance `rho` of a unit chain vector and of
cut rank at most `D` bounds the discarded mass beyond `D` by `rho`.
This is the variational passage used after the physical AKLV construction,
arXiv:1301.1162v1, lines 1503--1517. It uses only the bipartite overlap
inequality, and assumes no area law.
-/

open Matrix
open scoped InnerProductSpace ComplexOrder

namespace TNLean.MPS.AreaLaw

/-- The discarded mass at a cut is bounded by the squared distance to a
unit vector of bounded rank at that cut. -/
theorem one_sub_kyFanNorm_le_of_unit_cut_rank_approximation {L q D k : ℕ}
    (Ω y : EuclideanSpace ℂ (Fin L → Fin q)) (hΩ : ‖Ω‖ = 1) (hy : ‖y‖ = 1)
    {rho : ℝ} (herror : ‖y - Ω‖ ^ 2 ≤ rho) (hrank : (cutMatrix y k).rank ≤ D) :
    1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
      (leftBlock L k) Ω).kyFanNorm D ≤ rho := by
  classical
  let U := LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (Entropy.cutEquiv (fun _ : Fin L ↦ q) (leftBlock L k))
  let H := (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q)
    (leftBlock L k) Ω)
  have hoverlap : 1 - rho ≤ ‖⟪Ω, y⟫_ℂ‖ ^ 2 := by
    have hdist := norm_sub_sq (𝕜 := ℂ) y Ω
    rw [hy, hΩ] at hdist
    have hre : (⟪y, Ω⟫_ℂ).re ≤ ‖⟪y, Ω⟫_ℂ‖ := Complex.re_le_norm _
    rw [norm_inner_symm] at hre
    change ‖y - Ω‖ ^ 2 = 1 ^ 2 - 2 * (⟪y, Ω⟫_ℂ).re + 1 ^ 2 at hdist
    nlinarith [sq_nonneg (‖⟪Ω, y⟫_ℂ‖ - 1)]
  by_cases hD : D < Fintype.card (Entropy.RegionConfig (fun _ : Fin L ↦ q) (leftBlock L k))
  · have h := Matrix.normSq_inner_le_kyFanNorm_mul_normSq (U Ω) (U y) hD hrank
    rw [U.inner_map_map, U.norm_map, hy, one_pow, mul_one] at h
    have heq : H.kyFanNorm D =
        (posSemidef_self_mul_conjTranspose (cutMatrix Ω k)).isHermitian.kyFanNorm D := by
      congr 1
    change ‖⟪Ω, y⟫_ℂ‖ ^ 2 ≤
      (posSemidef_self_mul_conjTranspose (cutMatrix Ω k)).isHermitian.kyFanNorm D at h
    rw [← heq] at h
    linarith
  · have htrace : (Entropy.regionState (n := fun _ : Fin L ↦ q)
        (leftBlock L k) Ω).trace.re = 1 := by
      rw [Entropy.trace_regionState_eq_one hΩ, Complex.one_re]
    have hmass := (Entropy.regionState_posSemidef (n := fun _ : Fin L ↦ q)
      (leftBlock L k) Ω).kyFanNorm_mono (Nat.le_of_not_gt hD)
    rw [Matrix.IsHermitian.kyFanNorm_card_eq_trace_re, htrace] at hmass
    have hrho : 0 ≤ rho := (sq_nonneg _).trans herror
    linarith

end TNLean.MPS.AreaLaw
