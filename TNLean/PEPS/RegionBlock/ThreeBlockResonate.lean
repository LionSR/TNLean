import TNLean.PEPS.RegionBlock.Recovery11
import TNLean.PEPS.NormalEdgeBlockingData

/-!
# The three-block resonate engine for the normal PEPS Fundamental Theorem

This file ports the edge-level resonate engine of `TNLean.PEPS.InsertionRealization`
(`resonate_middle_inverted`, `resonate_invert_right_endpoint`,
`resonate_invert_left_endpoint`, `resonate_endpoint_coeff_reconcile`) to the
**three injective region blocks** of a `NormalEdgeBlockingData`: the red region `B₁`
(one endpoint of the crossing edge `f`), the blue region `B₂` (the other endpoint),
and the complementary region `B₃` (the middle).

The source argument (arXiv:1804.04964, Section 3, Lemma `inj_isomorph`,
`eq:resonate`--`eq:O->X`, lines 355--486 of `Papers/1804.04964/paper_normal.tex`)
inserts a physical operator on a particle adjacent to the crossing edge `f`. The
state-equality `eq:resonate` is read three ways:

* inverting `B₂` and `B₃` reads the left operator off as a one-bond matrix action
  `W` on the red endpoint;
* inverting `B₁` and `B₃` reads the right operator off as a one-bond matrix action
  `V` on the blue endpoint;
* injectivity of all three blocks (and in particular the *shared* middle block
  `B₃`) forces `V = W`.

The middle block `B₃` is the new structural ingredient: it is a third, separately
invertible block disjoint from both endpoints. The two-block frame (region `R`
against its set complement `univ \ R`) cannot state the middle-strip step
(`threeBlock_middle_strip`), which strips the middle block while keeping the red
and blue endpoint residual configurations quantified independently.

## Structure

* `threeBlockComplPhysical` fuses the blue and complement physical legs into the
  single complement leg over `univ \ red` consumed by the two-block backbone
  (`regionInsertedCoeff`, `regionBlockedWeight`, the blocked left inverses).
* `threeBlockInsertedCoeff` (Target 1) is the region analogue of
  `regionInsertedCoeff` keeping the three physical legs `σred`, `σblue`, `σcompl`
  open.
* `threeBlockInsertedCoeff_eq_regionInsertedCoeff` (Target 2, the bridge) reads the
  three-block coefficient as the two-block `regionInsertedCoeff` with `R := red`,
  unlocking the entire two-block backbone.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 355--486 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d} {e : Edge G}

/-! ### Fusing the blue and complement physical legs

The two-block backbone contracts the region `red` against its set complement
`univ \ red`, with a single complement physical leg `τ : RegionPhysicalConfig
(univ \ red)`. The three-block engine keeps the blue and complement legs separate.
Since `red`, `blue`, `complement` are pairwise disjoint and cover the vertex set,
every vertex outside `red` lies in `blue` or in `complement`, so the two legs fuse
into the single complement leg over `univ \ red`. -/

/-- The complement physical leg over `univ \ red`, fused from a blue physical leg
and a complement physical leg.

A vertex `w ∉ red` lies in `blue` (then read `σblue`) or, failing that, in
`complement` (then read `σcompl`); the cover and disjointness of the three blocks
make this well defined.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
def threeBlockComplPhysical
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red) :=
  fun w =>
    if hb : w.1 ∈ D.blue then σblue ⟨w.1, hb⟩
    else σcompl ⟨w.1, by
      have hwnotred : w.1 ∉ D.red := (Finset.mem_sdiff.mp w.2).2
      have hcover : w.1 ∈ D.red ∪ D.blue ∪ D.complement := by
        rw [D.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact absurd hr hwnotred
        · exact absurd hbl hb
      · exact hc⟩

/-- The fused complement leg reads a blue vertex off the blue physical leg. -/
@[simp] theorem threeBlockComplPhysical_apply_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (w : {w : V // w ∈ Finset.univ \ D.red}) (hb : w.1 ∈ D.blue) :
    threeBlockComplPhysical (A := A) (e := e) D σblue σcompl w = σblue ⟨w.1, hb⟩ := by
  rw [threeBlockComplPhysical, dif_pos hb]

/-- The fused complement leg reads a non-blue vertex off the complement physical
leg. -/
@[simp] theorem threeBlockComplPhysical_apply_not_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (w : {w : V // w ∈ Finset.univ \ D.red}) (hb : w.1 ∉ D.blue)
    (hc : w.1 ∈ D.complement) :
    threeBlockComplPhysical (A := A) (e := e) D σblue σcompl w = σcompl ⟨w.1, hc⟩ := by
  rw [threeBlockComplPhysical, dif_neg hb]

/-! ### The boundary edge of red carrying the inserted matrix

The crossing edge `f` of a `NormalEdgeBlockingData` has its left endpoint in the red
block and its right endpoint in the blue block (`left_mem_red`, `right_mem_blue`), so
it crosses the boundary of `red`: exactly one endpoint lies in `red`. The inserted
matrix is placed on this edge. -/

/-- The crossing edge `e` of a `NormalEdgeBlockingData` is a boundary edge of the
red block: its left endpoint lies in `red` and (since `red` and `blue` are disjoint
and its right endpoint lies in `blue`) its right endpoint does not.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isRegionBoundaryEdge_red_edge
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    IsRegionBoundaryEdge (G := G) D.red e := by
  refine Or.inl ⟨D.left_mem_red, ?_⟩
  intro hr
  exact (Finset.disjoint_left.mp D.red_disjoint_blue) hr D.right_mem_blue

/-- The crossing edge of a `NormalEdgeBlockingData`, packaged as a boundary edge of
the red block. -/
def redBoundaryEdge (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f} :=
  ⟨e, isRegionBoundaryEdge_red_edge (A := A) (e := e) D⟩

@[simp] theorem redBoundaryEdge_coe
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    (redBoundaryEdge (A := A) (e := e) D : Edge G) = e := rfl

/-! ### The three-block inserted coefficient

Insert a matrix `M` on the crossing edge `f` (a boundary edge of the red block) and
contract the three blocks `red`, `blue`, `complement` with three open physical legs.
The blue and complement legs are fused into the single complement leg over
`univ \ red` consumed by the two-block backbone, so the three-block coefficient is the
two-block `regionInsertedCoeff` with `R := red`. -/

/-- **The three-block inserted coefficient.** Insert `M` on the boundary edge `f` of
the red block, contract `red` on one side and the fused `blue ∪ complement` on the
other, keeping the three physical legs `σred`, `σblue`, `σcompl` open.

This is the region analogue of `regionInsertedCoeff` (`TNLean.PEPS.RegionBlock.Insertion`)
with the complement leg split along the blue/complement decomposition of `univ \ red`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def threeBlockInsertedCoeff
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) : ℂ :=
  regionInsertedCoeff (G := G) A D.red f M σred
    (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)

/-- **The three-block bridge.** The three-block inserted coefficient is the two-block
`regionInsertedCoeff` of the red region against its set complement `univ \ red`, with
the blue and complement physical legs fused into the single complement leg. This
unlocks the entire two-block backbone for the three-block engine.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockInsertedCoeff_eq_regionInsertedCoeff
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl =
      regionInsertedCoeff (G := G) A D.red f M σred
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) :=
  rfl

end PEPS
end TNLean
