/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Set.Finite.Lattice
import TNLean.PEPS.AreaLaw.Geometry.RepairDescendantCounts
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# A common empty generation of the repair

The initial mark scales form a bounded finite set. Uniform halving of the
scales and a positive stopping scale therefore give a generation with no
marks. This stopping generation may depend on the initial family.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, initial marks, lines 325–363, and
`geometry:repair-induction`, termination argument, lines 538–541.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- A common generation has no actual mark occurrences. The initial finite
family is bounded uniformly before the contraction estimate is applied.
Source: area-law Section 11, initial marks, lines 325–363, and
`geometry:repair-induction`, lines 538–541. -/
theorem RepairMetricHypotheses.exists_isEmpty_markIndex {a₀ : ℝ}
    (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
      (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀) :
    ∃ N : ℕ, IsEmpty (𝔇 N).markIndex := by
  exact
    letI := finite_repairStage_markIndex o Λ A C k₀ hC h₀ Sstar 0
    let ⟨M, hB⟩ := (Set.finite_range (𝔇 0).scale).bddAbove
    let ⟨n, hn⟩ := pow_unbounded_of_one_lt (M / Sstar) (one_lt_two : (1 : ℝ) < 2)
    ⟨0 + n, ⟨fun q ↦
      (not_le_of_gt ((div_lt_iff₀ h.stop_pos).mp hn))
        (((mul_le_mul_of_nonneg_left (h.le_scale (0 + n) q)
          (pow_pos (two_pos : (0 : ℝ) < 2) n).le).trans_eq
            (mul_comm ((2 : ℝ) ^ n) ((𝔇 (0 + n)).scale q))).trans
          ((h.scale_mul_two_pow_le 0 n q).trans
            (hB (Set.mem_range_self (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar 0 n q)))))⟩⟩

/-- Once an actual mark family is empty, every later mark family is empty.
A later mark would have an ancestor in the empty generation.
Source: area-law Section 11, child marks, lines 404–409, and
`geometry:repair-induction`, termination argument, lines 538–541. -/
theorem isEmpty_repairStage_markIndex_add (j n : ℕ)
    (h : IsEmpty (𝔇 j).markIndex) : IsEmpty (𝔇 (j + n)).markIndex := by
  exact
    letI := h
    Function.isEmpty (repairMarkAncestor o Λ A C k₀ hC h₀ Sstar j n)

/-- The stopping-scale and lower-layer thresholds precede the finite domain
and cut; each resulting repair has a common empty generation.
Source: area-law Section 11, `geometry:trim-margins`, lines 380–394,
initial marks, lines 325–363, and `geometry:repair-induction`, lines 538–541. -/
theorem exists_uniform_isEmpty_repairStage_markIndex {a₀ : ℝ}
    (ha₀ : 0 < a₀) (ha₀' : a₀ ≤ 1 / 4) :
    ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          ∃ N : ℕ, IsEmpty (repairStage o Λ A C k₀ hC h₀ Sstar N).markIndex := by
  exact
    let ⟨T, hT⟩ := exists_repairMetricHypotheses ha₀ ha₀'
    ⟨T, fun Sstar hSstar C ↦
      let ⟨K, hK⟩ := hT Sstar hSstar C
      ⟨K, fun o Λ A k₀ hC h₀ hk ↦
        RepairMetricHypotheses.exists_isEmpty_markIndex o Λ A C k₀ hC h₀ Sstar
          (hK o Λ A k₀ hC h₀ hk)⟩⟩

end TNLean.PEPS.AreaLaw.Geometry
