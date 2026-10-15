/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicResizeRewrite

/-!
# The true vertices of a level guide as a finite set

The holes of the main frame at the start and the end of a repainting are at the true vertices of
the reading of a guide uniform on the blocks of the level, which carries the placeholder outside
the root square (`levelLabels`). These true vertices are grid corners of the root square, or of
its first neighbours, so they form a finite set (`levelTrueVertices`,
`mem_levelTrueVertices`), the set of hole centers of the frame of the guide.

## Main definitions

* `Approximation.levelTrueVertices`.

## Main results

* `Approximation.mem_levelTrueVertices`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the root square and the
  placeholder outside it (lines 62–67 and 82–100), the holes at true vertices (lines 109–118).
-/

open Set Metric Filter Topology

noncomputable section

namespace TNLean.PEPS.Approximation

variable {κ : Type}

open Classical in
/-- The true vertices of a labelling among the grid corners `blockCorner n Q` with
`0 ≤ Q.1, Q.2 ≤ M + 1`. -/
def levelTrueVertices (n : ℝ) (M : ℤ) (g : ℝ × ℝ → κ) : Finset (ℝ × ℝ) :=
  ((Finset.Icc 0 (M + 1) ×ˢ Finset.Icc 0 (M + 1)).image (blockCorner n)).filter (IsTrueVertex g)

/-- **The true vertices of a level guide.** Let `g` be the reading along `v` of a guide uniform
on the `n`-blocks whose label is a fixed `ph` on every block outside the root square of `M × M`
blocks. Then the true vertices of `g` are exactly the points of `levelTrueVertices n M g`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 62–67, 82–100 and 109–118. -/
theorem mem_levelTrueVertices {n : ℝ} (hn : 0 < n) {M : ℤ} {lab : ℤ × ℤ → κ} {ph : κ}
    (hout : ∀ Q, ¬InRoot M Q → lab Q = ph) {v : ℝ × ℝ} {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v) {c : ℝ × ℝ} :
    c ∈ levelTrueVertices n M g ↔ IsTrueVertex g c := by
  classical
  simp only [levelTrueVertices, Finset.mem_filter, Finset.mem_image, Finset.mem_product,
    Finset.mem_Icc, and_iff_right_iff_imp]
  intro hc
  obtain ⟨Q, rfl⟩ := (hg.isTrueVertex hc).eq_blockCorner hn
  refine ⟨Q, ?_, rfl⟩
  by_contra hQ
  refine (hasTwoLabelsNear_of_eventuallyEq_const (c := ph) ?_).not_isTrueVertex hc
  filter_upwards [ball_mem_nhds (blockCorner n Q) hn] with p hp
  obtain ⟨Q', hQ', e⟩ := reading_mem_nineBlocks hn hg (blockCorner_mem_closedBlock_sub_one hn Q)
    (mem_ball.1 hp)
  rw [e]
  refine hout Q' fun hr => hQ ?_
  simp only [nineBlocks, Finset.mem_product, Finset.mem_Icc] at hQ'
  obtain ⟨h1, h2, h3, h4⟩ := hr
  omega

end TNLean.PEPS.Approximation
