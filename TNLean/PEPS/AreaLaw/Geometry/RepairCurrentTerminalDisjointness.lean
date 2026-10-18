/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# Current regions avoid earlier terminal squares

Under the metric hypotheses of the repair induction, each current region is
disjoint from the closed terminal squares of all earlier generations. Old
regions lose every closed removal square. A fresh region lies in its
nonterminal parent's square, which avoids earlier terminal squares by the
existing metric estimates and avoids current terminal squares by the
separation of distinct parents.

The assertion concerns the whole planar regions, at an arbitrary origin.
Its hypotheses are the existing metric hypotheses; no lattice arithmetic or
empty-generation assumption is imposed.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, replacement instructions, lines 393–417;
`geometry:repair-induction`, lines 474–478 and 526–536; and current actual
regions, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

noncomputable section

open TNLean.Lattice

namespace TNLean.PEPS.AreaLaw.Geometry

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

variable {o Λ A C k₀ hC h₀ Sstar}

namespace RepairMetricHypotheses

variable {a₀ : ℝ} (h : RepairMetricHypotheses (o := o) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
  (hC := hC) (h₀ := h₀) (Sstar := Sstar) a₀)

include h

/-- Every actual current region avoids all closed terminal squares from
strictly earlier generations.
Source: area-law Section 11, lines 393–417; `geometry:repair-induction`,
lines 474–478 and 526–536; and current actual regions, lines 558–561. -/
theorem current_disjoint_earlierTerminalSquares (j : ℕ) (i : (𝔇 j).regionIndex) :
    Disjoint ((𝔇 j).current i)
      (repairEarlierTerminalSquares o Λ A C k₀ hC h₀ Sstar j) := by
  classical
  induction j with
  | zero => simp [repairEarlierTerminalSquares]
  | succ j ih =>
    refine Set.disjoint_left.mpr fun x hx ht ↦ ?_
    simp only [repairEarlierTerminalSquares, Set.mem_iUnion] at ht
    obtain ⟨t, ht, q, hxq⟩ := ht
    have hxt : t < j → x ∈ repairEarlierTerminalSquares o Λ A C k₀ hC h₀ Sstar j :=
      fun htj ↦ Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr
        ⟨htj, Set.mem_iUnion.mpr ⟨q, hxq⟩⟩⟩
    rcases i with i | r
    · by_cases htj : t < j
      · exact Set.disjoint_left.mp (ih i) hx.1
          (hxt htj)
      · have ht_eq : t = j :=
          Nat.le_antisymm (Nat.le_of_lt_succ ht) (Nat.le_of_not_gt htj)
        subst t
        exact hx.2 (Set.mem_iUnion.mpr ⟨q.val, hxq⟩)
    · have hxp : x ∈ repairSquare ((𝔇 j).location r.2.1.val)
          ((𝔇 j).scale r.2.1.val) :=
        (interior_subset.trans
          (repairReplacementBirthRegion_subset_repairSquare _ _ _ _ r.2.2)) hx
      by_cases htj : t < j
      · have hd : repairHalfSide ((𝔇 j).scale r.2.1.val) ≤
            a₀ * (𝔇 j).scale r.2.1.val := by
          nlinarith [h.halfSide_le j r.2.1.val,
            mul_pos h.pos (h.scale_pos j r.2.1.val)]
        exact Set.disjoint_left.mp (h.disjoint_earlierTerminalSquares j r.2.1.val)
          (Metric.closedBall_subset_closedBall hd hxp)
          (hxt htj)
      · have ht_eq : t = j :=
          Nat.le_antisymm (Nat.le_of_lt_succ ht) (Nat.le_of_not_gt htj)
        subst t
        have hpq : r.2.1.val ≠ q.val := fun hpq ↦
          (not_lt_of_ge r.2.1.property) (hpq.symm ▸ q.property)
        exact Set.disjoint_left.mp
          (h.disjoint_repairSquare j r.2.1.val q.val hpq) hxp hxq

end RepairMetricHypotheses

end TNLean.PEPS.AreaLaw.Geometry
