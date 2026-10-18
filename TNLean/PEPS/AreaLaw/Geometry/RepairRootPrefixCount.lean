/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantScales
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth

/-!
# Counting descendants of one initial repair mark

For a fixed stopping scale greater than one, the number of descendants of
one actual initial mark in any finite sequence of generations is bounded
by a polynomial in its initial layer index. The constant is chosen before
the domain, the initial mark, the layer, and the number of generations.
The only condition on the layer is the corresponding upper bound for the
scale of the given mark. The initial mark family is unchanged.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:descendant-count`, lines 670–686.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

/-- **Descendant prefix count of one initial mark, with an explicit constant.**
The descendants of one actual initial mark through any finite number of
generations, whenever its scale is at most `2 ^ k`, number at most
`K (k + 1) ^ K` with `K = repairDescendantLayerConstant S_* 1`.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–686. -/
theorem repairMarkAncestor_prefix_layer_le {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
      (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
      RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
        (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
      ∀ (p : (repairStage o Λ A C k₀ hC h₀ Sstar 0).markIndex) (k : ℕ),
        (repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p ≤ (2 : ℝ) ^ k →
        ∀ N : ℕ,
          ∑ j ∈ Finset.range N,
              (Nat.card {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + j)).markIndex //
                repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ) ≤
            repairDescendantLayerConstant Sstar 1 *
              ((k : ℝ) + 1) ^ repairDescendantLayerConstant Sstar 1 := by
  intro o Λ A C k₀ hC h₀ a₀ h p k hpk N
  set K := repairDescendantLayerConstant Sstar 1
  have hK : 0 < K := repairDescendantLayerConstant_pos Sstar 1
  have hcount := sum_pow_le_repairDescendantLayerConstant hSstar (M := 1) zero_lt_one
  induction N with
  | zero =>
    simpa only [Finset.range_zero, Finset.sum_empty] using
      (show 0 ≤ K * ((k : ℝ) + 1) ^ K by positivity)
  | succ N ih =>
    by_cases hzero : Nat.card
        {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + N)).markIndex //
          repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 N q = p} = 0
    · simpa only [Finset.sum_range_succ, hzero, Nat.cast_zero, add_zero] using ih
    · obtain ⟨q⟩ := (Nat.card_ne_zero.mp hzero).1
      have hm : Sstar ≤ repairHalfSide^[N]
          ((repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p) := by
        simpa only [repairStage_scale_eq_iterate, q.property] using h.le_scale (0 + N) q.val
      refine (Finset.sum_le_sum fun j _ ↦ ?_).trans
        (hcount k _ (h.scale_pos 0 p) (by simpa only [one_mul] using hpk) N hm)
      exact_mod_cast card_repairMarkAncestor_fiber_le o Λ A C k₀ hC h₀ Sstar 0 j p

/-- A uniform bound for the descendants of one actual initial mark through
any finite number of generations, whenever its scale is at most `2 ^ k`.
The constant depends only on the stopping scale; it is
`repairDescendantLayerConstant S_* 1` (`repairMarkAncestor_prefix_layer_le`).
This is the per-mark estimate preceding the sum over the chosen initial family.
Source: area-law Section 11, `geometry:descendant-count`, lines 670–686. -/
theorem exists_repairMarkAncestor_prefix_layer_bound {Sstar : ℝ} (hSstar : 1 < Sstar) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (a₀ : ℝ),
        RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
          (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀ →
        ∀ (p : (repairStage o Λ A C k₀ hC h₀ Sstar 0).markIndex) (k : ℕ),
          (repairStage o Λ A C k₀ hC h₀ Sstar 0).scale p ≤ (2 : ℝ) ^ k →
          ∀ N : ℕ,
            ∑ j ∈ Finset.range N,
                (Nat.card {q : (repairStage o Λ A C k₀ hC h₀ Sstar (0 + j)).markIndex //
                  repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 j q = p} : ℝ) ≤
              K * ((k : ℝ) + 1) ^ K :=
  ⟨_, repairDescendantLayerConstant_pos Sstar 1, repairMarkAncestor_prefix_layer_le hSstar⟩

end TNLean.PEPS.AreaLaw.Geometry
