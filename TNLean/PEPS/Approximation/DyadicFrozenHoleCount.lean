/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicFootprintScaling
import TNLean.PEPS.Approximation.DyadicProtocolSchedule
import TNLean.PEPS.Approximation.DyadicUnmodifiedVertices

/-!
# The holes of the frozen auxiliary sheets

Every true vertex of a guide carries one encoded hole (`06-geometry.tex`, lines 108–112), so the
holes of a sheet are counted by the true vertices of its guide. An auxiliary sheet is initialized
uniform, hence without holes (lines 129–130). It is used in one edge construction, returned from
the point treatment of its lens exchange to its final frame, and then retired and kept idle,
without resizing its holes (lines 130–133, 620–624). The final guide of the sheet of the edge `e`
is the auxiliary guide of `e` with the word left by the exchange, `auxWordExchanged`: it differs
from the uniform guide only in the band of one edge (lines 653–655).

This file proves the count of lines 653–656:

* every true vertex of an auxiliary guide is an endpoint of its edge, so each frozen auxiliary
  sheet has at most two holes, in the coordinates of the repainted square and after translating
  it to its block;
* summed over the auxiliary sheets initialized by the protocol schedule, one per edge of a
  large-scale repainting, the frozen sheets carry at most `8` holes for each square and junction
  of the hierarchy, which is `O(L ^ 2)` and in particular at most `214 L ^ 3` when `2 ^ k < 2 L`.

The schedule `protocolSchedule` does not carry the labels of the repaintings. The total count is
therefore stated for any assignment of a repainting, a block translation and an edge to each
change that initializes an auxiliary sheet; the bound does not depend on that assignment.

Distances are ambient sup distances: `ℝ × ℝ` carries the maximum metric.

## Main results

* `TNLean.PEPS.Approximation.RepaintingBaseline.isTrueVertex_auxGuide_subset`: the true vertices
  of an auxiliary guide lie at the two endpoints of its edge.
* `TNLean.PEPS.Approximation.RepaintingBaseline.ncard_isTrueVertex_shiftGuide_auxGuide_le`: at
  most two holes on each frozen auxiliary sheet.
* `TNLean.PEPS.Approximation.frozenAuxGuide`: the final guide of a frozen auxiliary sheet.
* `TNLean.PEPS.Approximation.sum_frozenHoles_le`: at most `8` frozen holes for each square and
  junction.
* `TNLean.PEPS.Approximation.sum_frozenHoles_le_cube`: at most `214 L ^ 3` frozen holes.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: holes at true vertices
  (lines 108–112), fresh and retired auxiliary sheets (lines 129–133), the auxiliary word and
  the lens exchange (lines 183–214), the separation of unmodified true vertices (lines 321–326),
  frozen auxiliary frames (lines 620–624), and the counts (lines 649–656, 676–678).

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.PEPS.Approximation

open Set

/-! ### Holes of one frozen auxiliary sheet -/

namespace RepaintingBaseline

variable {ι : Type*} (R : RepaintingBaseline ι)

/-- **True vertices of an auxiliary guide.** Every true vertex of the guide of the auxiliary
sheet of the edge `e`, with any auxiliary word, is one of the two endpoints of `e`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:321–326, 653–655`. -/
theorem isTrueVertex_auxGuide_subset (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e)) :
    {c | IsTrueVertex (R.auxGuide e W) c} ⊆ {e.point R.n 0 0, e.point R.n R.n 0} := by
  intro c hc
  by_contra h
  simp only [mem_insert_iff, mem_singleton_iff, not_or] at h
  exact (R.hasTwoLabelsNear_auxGuide e hW h.1 h.2).not_isTrueVertex hc

/-- **Two holes on an auxiliary sheet.** The guide of the auxiliary sheet of an edge, with any
auxiliary word, has at most two true vertices, hence carries at most two holes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:108–112, 653–655`. -/
theorem ncard_isTrueVertex_auxGuide_le (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e)) :
    {c | IsTrueVertex (R.auxGuide e W) c}.ncard ≤ 2 :=
  (ncard_le_ncard (R.isTrueVertex_auxGuide_subset e hW) (toFinite _)).trans
    ((ncard_insert_le _ _).trans (by rw [ncard_singleton]))

/-- **Two holes on a frozen auxiliary sheet.** The guide of the auxiliary sheet of an edge,
translated to its block, has at most two true vertices. In particular the final guide of a
frozen auxiliary sheet, with the word left by the lens exchange, carries at most two holes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:108–112, 620–624, 653–655`. -/
theorem ncard_isTrueVertex_shiftGuide_auxGuide_le (o : ℝ × ℝ) (e : SquareEdge) {W : ℝ → ι}
    (hW : W ∈ auxWords R.oldLabel R.finalLabel (R.nbrLabel e)) :
    {c | IsTrueVertex (shiftGuide o (R.auxGuide e W)) c}.ncard ≤ 2 := by
  have h : {c | IsTrueVertex (shiftGuide o (R.auxGuide e W)) c} =
      (Homeomorph.subRight o) ⁻¹' {c | IsTrueVertex (R.auxGuide e W) c} := by
    ext c
    exact isTrueVertex_comp_homeomorph (f := R.auxGuide e W) (Homeomorph.subRight o)
  rw [h, ncard_preimage_of_injective_subset_range (Homeomorph.subRight o).injective
    (by rw [(Homeomorph.subRight o).surjective.range_eq]; exact subset_univ _)]
  exact R.ncard_isTrueVertex_auxGuide_le e hW

end RepaintingBaseline

/-! ### All frozen auxiliary sheets of the schedule -/

/-- The final guide of a frozen auxiliary sheet: the auxiliary guide of the edge `e` of a
repainting `R`, with the word left by the lens exchange, translated by `o` to the block.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:193–214, 620–624`. -/
noncomputable def frozenAuxGuide {ι : Type*} (R : RepaintingBaseline ι) (o : ℝ × ℝ)
    (e : SquareEdge) : ℝ × ℝ → ι :=
  shiftGuide o (R.auxGuide e (auxWordExchanged R.oldLabel R.finalLabel (R.nbrLabel e)))

/-- A frozen auxiliary sheet carries at most two holes. -/
theorem ncard_isTrueVertex_frozenAuxGuide_le {ι : Type*} (R : RepaintingBaseline ι)
    (o : ℝ × ℝ) (e : SquareEdge) : {c | IsTrueVertex (frozenAuxGuide R o e) c}.ncard ≤ 2 :=
  R.ncard_isTrueVertex_shiftGuide_auxGuide_le o e (by simp [auxWords])

/-- **Frozen holes per square and junction.** Let `F` assign to each change of the schedule that
initializes an auxiliary sheet the repainting, block translation and edge of that sheet. The
frozen sheets carry at most `8` holes for each square and junction of the hierarchy: at most two
holes on each, and at most four sheets for each event.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:576, 649–656`: “Each frozen
auxiliary has only a fixed number of holes”. -/
theorem sum_frozenHoles_le {ι : Type*} (k : ℕ) (large : DyadicSquare k → Bool)
    (F : ProtocolEvent k × RepaintOp → RepaintingBaseline ι × (ℝ × ℝ) × SquareEdge) :
    (((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map
        fun x => {c | IsTrueVertex (frozenAuxGuide (F x).1 (F x).2.1 (F x).2.2) c}.ncard).sum ≤
      8 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)) := by
  refine (List.sum_le_length_nsmul _ 2 fun m hm => ?_).trans ?_
  · obtain ⟨x, -, rfl⟩ := List.mem_map.1 hm
    exact ncard_isTrueVertex_frozenAuxGuide_le _ _ _
  · rw [List.length_map, ← List.countP_eq_length_filter, smul_eq_mul]
    have := countP_isAuxInit_protocolSchedule_le k large
    omega

/-- **At most `C L ³` frozen holes.** With `2 ^ k < 2 L`, the frozen auxiliary sheets of the
schedule carry at most `214 L ^ 3` holes in all, the count used for the final reference vector.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex:653–656`: “Even the weaker
total bound `C L ^ 3` on frozen auxiliary holes will suffice”, used at lines 676–678. -/
theorem sum_frozenHoles_le_cube {ι : Type*} {k L : ℕ} (hk : 2 ^ k < 2 * L)
    (large : DyadicSquare k → Bool)
    (F : ProtocolEvent k × RepaintOp → RepaintingBaseline ι × (ℝ × ℝ) × SquareEdge) :
    (((protocolSchedule k large).filter fun x => x.2.IsAuxInit).map
        fun x => {c | IsTrueVertex (frozenAuxGuide (F x).1 (F x).2.1 (F x).2.2) c}.ncard).sum ≤
      214 * L ^ 3 := by
  have h1 := sum_frozenHoles_le k large F
  have h2 := three_mul_schedule_le_cube hk 8
  omega

end TNLean.PEPS.Approximation
