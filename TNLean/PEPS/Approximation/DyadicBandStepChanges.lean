/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBulkFrames

/-!
# Births and deaths along an edge as changes of a treated sheet

Along an edge `e` of a square `S` repainted at scale `n > K₀ t`, the protocol of Proposition 7.1
of the polynomial-PEPS manuscript performs elementary births and deaths on a sheet whose guide is
`bandUpdate n e W g₀`, after homogenizing it to the surrounding label `P∘` on the squares of
radius `t` about the two endpoints of `e` (`06-geometry.tex`, lines 183–221 and 328–387). This
file proves that such a birth or death is a bounded change between the frames of the treated
guides before and after it, conditional on Proposition 3.4 through `IsAngularScale`:

* `BandOperation.treated_mem` : near the closed changed region the two treated guides take only
  the surrounding label and the inserted label, and the surrounding guide is `P∘`;
* `bandBirth_hasFrameChange` : a birth;
* `bandDeath_hasFrameChange` : a death.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: guides and sampling
  (lines 69–80), the holes and tags (lines 109–125), the edge construction (lines 183–221), the
  point treatment and the bulk operations (lines 328–387 and 440–445); Lemma 6.5 `lem:birth`,
  `05-frames.tex`.
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

section Values

variable {ι : Type*} {op : BandOperation ι} {Q : ι} {n t : ℝ} {e : SquareEdge}
  {g : ℝ × ℝ → ι}

/-- **Values near the change.** Near the closure of the remaining changed region of a treated
birth or death that inserts the single label `Q`, the treated guides before and after take only
the surrounding label `P∘` and `Q`, and the treated surrounding guide is `P∘`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 375–382. -/
theorem BandOperation.treated_mem (hop : op.InsertsOne Q) (htn : t ≤ n) {p : ℝ × ℝ}
    (hp : p ∈ thickening (angularConstant * t)
      {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p}) :
    homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ∈
        ({op.label, Q} : Set ι) ∧
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p ∈
        ({op.label, Q} : Set ι) ∧
      homogenize (edgeTreated n e t) op.label (bandUpdate n e op.surrounding g) p = op.label := by
  have hs := op.treated_surrounding_eq htn e g hp
  refine ⟨?_, ?_, hs⟩ <;>
  · by_cases hpR : homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p
    · have hpU : p ∉ edgeTreated n e t := fun h => hpR (by simp only [homogenize_of_mem h])
      have hpB : p ∈ edgeBand n e (-8) 2 := by
        by_contra hb
        exact hpR (by simp only [homogenize_of_notMem hpU, bandUpdate_of_notMem hb])
      have hne : op.before (bandCoord n e p) ≠ op.after (bandCoord n e p) := by
        simpa only [homogenize_of_notMem hpU, bandUpdate_of_mem hpB] using hpR
      simp only [homogenize_of_notMem hpU, bandUpdate_of_mem hpB]
      first
        | exact (hop.changed_mem _ hne).1
        | exact (hop.changed_mem _ hne).2
    · have heq := not_not.1 hpR
      rcases hop.surrounding_eq with h | h
      · rw [h] at hs
        first | exact Or.inl hs | exact Or.inl (heq ▸ hs)
      · rw [h] at hs
        first | exact Or.inl (heq.trans hs) | exact Or.inl hs

/-- The changed region of a treated birth or death lies in the band of its edge. -/
theorem BandOperation.treated_ne_subset (op : BandOperation ι) :
    {p | homogenize (edgeTreated n e t) op.label (bandUpdate n e op.before g) p ≠
        homogenize (edgeTreated n e t) op.label (bandUpdate n e op.after g) p} ⊆
      edgeBand n e (-8) 2 := by
  intro p hpR
  have hpU : p ∉ edgeTreated n e t := fun h => hpR (by simp only [homogenize_of_mem h])
  by_contra hb
  exact hpR (by simp only [homogenize_of_notMem hpU, bandUpdate_of_notMem hb])

end Values

end TNLean.PEPS.Approximation
