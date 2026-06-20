import TNLean.PEPS.RegionBlock.Recovery11
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
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

/-! ### The disjoint cover of `univ \ red` by blue and complement

The set complement of the red block decomposes as the disjoint union of the blue
and complement blocks. This is the geometric fact underlying the weight
factorization: contracting over `univ \ red` is contracting over `blue` and then
over `complement`. -/

/-- The set complement of the red block is the disjoint union of the blue and
complement blocks.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem sdiff_red_eq_blue_union_complement
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    Finset.univ \ D.red = D.blue ∪ D.complement := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hwnotred
    have hcover : w ∈ D.red ∪ D.blue ∪ D.complement := by
      rw [D.cover_univ]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hcover with hrb | hc
    · rcases Finset.mem_union.mp hrb with hr | hbl
      · exact absurd hr hwnotred
      · exact Or.inl hbl
    · exact Or.inr hc
  · intro hbc hr
    rcases hbc with hbl | hc
    · exact (Finset.disjoint_left.mp D.red_disjoint_blue) hr hbl
    · exact (Finset.disjoint_left.mp D.red_disjoint_complement) hr hc

/-- **The vertex-product split over `univ \ red`.** For any global virtual
configuration `ζ`, the product of the vertex tensors over `univ \ red`, read with
the fused blue/complement physical leg, factors as the blue product (read with
`σblue`) times the complement product (read with `σcompl`). This is the disjoint
decomposition `univ \ red = blue ⊔ complement` applied to the contraction.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_sdiff_red_eq_blue_mul_complement
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (ζ : VirtualConfig A) :
    (∏ w : {w : V // w ∈ Finset.univ \ D.red},
        A.component w.1 (fun ie => ζ ie.1)
          (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl w)) =
      (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  classical
  -- A total physical leg agreeing with `σblue` on blue and `σcompl` on complement.
  -- The value on red vertices is never read by the products below.
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · -- With no physical index, a vertex in any block forces a contradiction.
    have hblue : IsEmpty {w : V // w ∈ D.blue} := by
      constructor; intro w; exact hd.elim (σblue w)
    have hcompl : IsEmpty {w : V // w ∈ D.complement} := by
      constructor; intro w; exact hd.elim (σcompl w)
    have hsdiff : IsEmpty {w : V // w ∈ Finset.univ \ D.red} := by
      constructor; intro w
      exact hd.elim (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl w)
    rw [Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, one_mul]
  · set g : V → Fin d := fun w =>
      if hb : w ∈ D.blue then σblue ⟨w, hb⟩
      else if hc : w ∈ D.complement then σcompl ⟨w, hc⟩
      else Classical.arbitrary (Fin d) with hg
    -- The fused leg on `univ \ red` agrees with `g`.
    have hsdiff : (∏ w : {w : V // w ∈ Finset.univ \ D.red},
          A.component w.1 (fun ie => ζ ie.1)
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl w)) =
        ∏ w : {w : V // w ∈ Finset.univ \ D.red},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      by_cases hb : w.1 ∈ D.blue
      · rw [threeBlockComplPhysical_apply_blue (A := A) (e := e) D σblue σcompl w hb,
          hg]
        simp only [dif_pos hb]
      · have hwnotred : w.1 ∉ D.red := (Finset.mem_sdiff.mp w.2).2
        have hc : w.1 ∈ D.complement := by
          have hcover : w.1 ∈ D.red ∪ D.blue ∪ D.complement := by
            rw [D.cover_univ]; exact Finset.mem_univ _
          rcases Finset.mem_union.mp hcover with hrb | hc
          · rcases Finset.mem_union.mp hrb with hr | hbl
            · exact absurd hr hwnotred
            · exact absurd hbl hb
          · exact hc
        rw [threeBlockComplPhysical_apply_not_blue (A := A) (e := e) D σblue σcompl w hb hc,
          hg]
        simp only [dif_neg hb, dif_pos hc]
    -- The blue and complement subtype products read `g` on their vertices.
    have hblue : (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => ζ ie.1) (σblue w)) =
        ∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      rw [hg]; simp only [dif_pos w.2]
    have hcompl : (∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
        ∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      have hb : w.1 ∉ D.blue := fun h =>
        (Finset.disjoint_left.mp D.blue_disjoint_complement) h w.2
      rw [hg]; simp only [dif_neg hb, dif_pos w.2]
    rw [hsdiff, hblue, hcompl]
    -- Convert the three subtype products to `Finset.prod` and split the union.
    rw [← Finset.prod_subtype (Finset.univ \ D.red) (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      ← Finset.prod_subtype D.blue (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      ← Finset.prod_subtype D.complement (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      sdiff_red_eq_blue_union_complement (A := A) (e := e) D,
      Finset.prod_union D.blue_disjoint_complement]

/-- **The fused complement weight as a blue/complement double product sum.** The
blocked-region weight of `univ \ red` at the fused blue/complement physical leg
unfolds to the single constrained sum over global virtual configurations of the
blue product (read with `σblue`) times the complement product (read with
`σcompl`). This is `regionBlockedWeight` for `univ \ red` with the vertex product
split along `univ \ red = blue ⊔ complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_threeBlockComplPhysical_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
        (∏ w : {w : V // w ∈ D.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  rw [regionBlockedWeight]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  exact prod_sdiff_red_eq_blue_mul_complement (A := A) (e := e) D σblue σcompl ζ

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

/-! ### The three blocked-tensor injectivity engines

The three blocks of a `NormalEdgeBlockingData` are each injective. Under the
concrete region-injectivity predicate `regionInjectivityDataOf A`, this means each
block is blocked-tensor injective (`RegionBlockedTensorInjective`), which is exactly
injectivity of the corresponding blocked tensor map and so supplies the chosen
left inverse `regionBlockedLeftInverse`. These are the three contraction-inverse
engines the middle-strip step (inverting the complement block `B₃`) and the two
endpoint inversions (inverting the blue block `B₂`, then the red block `B₁`) consume.

This is the region analogue of the three edge-level inverses
`edgeMiddleLeftInverse` / `localLeftInverseAt` of
`TNLean.PEPS.InsertionRealization`, now at region-block granularity. -/

/-- The red block `B₁` of a `NormalEdgeBlockingData` is blocked-tensor injective.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_red
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    RegionBlockedTensorInjective (G := G) A D.red := by
  have h := D.red_injective
  rwa [regionInjectivityDataOf_isInjective] at h

/-- The blue block `B₂` of a `NormalEdgeBlockingData` is blocked-tensor injective.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    RegionBlockedTensorInjective (G := G) A D.blue := by
  have h := D.blue_injective
  rwa [regionInjectivityDataOf_isInjective] at h

/-- The complement block `B₃` of a `NormalEdgeBlockingData` is blocked-tensor
injective. This is the separately invertible middle block disjoint from both edge
endpoints, the structural ingredient the two-block frame lacks.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedTensorInjective_complement
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e) :
    RegionBlockedTensorInjective (G := G) A D.complement := by
  have h := D.complement_injective
  rwa [regionInjectivityDataOf_isInjective] at h

/-! ### The core region-blocking associativity factorization

The blocked-region weight of the host `univ \ red` at the fused blue/complement
physical leg, read **as a function of the complement physical leg** `σcompl`, lies
in the range of the complement block's blocked-region tensor map. This is the
foundational factorization that strips the complement (middle) block while keeping
the red and blue residual configurations independent.

The route is the host-relative analogue of `stateCoeff_eq_regionComplement`. The
constrained global-configuration sum of the fused weight
(`regionBlockedWeight_threeBlockComplPhysical_eq`) is grouped by the complement
boundary configuration `bc'` a global configuration induces. On each fiber the blue
and complement vertex products **decouple**, because the free interior edges of the
blue block (blue-interior) and of the complement block (complement-interior) are
disjoint: the complement part becomes the complement blocked-region weight at `bc'`,
the blue part a `bc'`-coupled coefficient `blueCoeff`. The red tensors appear only
as bond multiplicity. The fiber multiplicity collapses to the complement interior
bond product, a nonzero constant, which is divided out to land the function in the
complement block image.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/

/-- The blue vertex product reads a global configuration only through the
blue-incident edges, so it agrees with the configuration merged along the
complement block, provided the two merged configurations agree on the complement
boundary. The blue-incident edges that are also complement-incident are exactly the
blue/complement crossing edges, which are boundary edges of the complement block,
where the agreement forces the two configurations to coincide.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem blueProd_eq_regionMerge_complement
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A D.complement p.1 =
      regionBoundaryLabel (G := G) A D.complement p.2) :
    (∏ w : {w : V // w ∈ D.blue}, A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∏ w : {w : V // w ∈ D.blue},
        A.component w.1 (fun ie => regionMerge (G := G) A D.complement p ie.1) (σblue w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  -- `ie` is incident to `w ∈ blue`, so `w ∉ complement`.
  have hwblue : w.1 ∈ D.blue := w.2
  have hwnotcompl : w.1 ∉ D.complement := fun hc =>
    (Finset.disjoint_left.mp D.blue_disjoint_complement) hwblue hc
  have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
  by_cases hinc : IsRegionIncidentEdge (G := G) D.complement ie.1
  · -- `ie` is complement-incident and touches `w ∉ complement`: a boundary edge of
    -- the complement, where `p.1` and `p.2` agree.
    have hbdry : IsRegionBoundaryEdge (G := G) D.complement ie.1 := by
      rcases hinc with h1 | h2
      · rcases hwinc with hw1 | hw2
        · exact absurd (by rw [← hw1]; exact h1) hwnotcompl
        · refine Or.inl ⟨h1, ?_⟩; rw [hw2]; exact hwnotcompl
      · rcases hwinc with hw1 | hw2
        · refine Or.inr ⟨?_, h2⟩; rw [hw1]; exact hwnotcompl
        · exact absurd (by rw [← hw2]; exact h2) hwnotcompl
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨ie.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]

/-- On a boundary edge of the host `univ \ red`, the blue-side global configuration
`p.2` agrees with the configuration merged along the complement block, provided the
pair agrees on the complement boundary. A host boundary edge has one endpoint in
`univ \ red` and one in `red`; if it is complement-incident it is a boundary edge of
the complement (the red endpoint lies outside the complement), where the agreement
pins it, and otherwise the merge reads it from `p.2` directly.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem hostLabel_p2_eq_hostLabel_regionMerge_complement
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A D.complement p.1 =
      regionBoundaryLabel (G := G) A D.complement p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 =
      regionBoundaryLabel (G := G) A (Finset.univ \ D.red)
        (regionMerge (G := G) A D.complement p) := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : IsRegionIncidentEdge (G := G) D.complement f.1
  · -- A complement-incident host boundary edge is a boundary edge of the complement.
    have hbdry : IsRegionBoundaryEdge (G := G) D.complement f.1 := by
      -- The host-side endpoint that lies in `univ \ red` is the complement endpoint;
      -- the red endpoint lies outside the complement.
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · -- `f.1.1 ∈ univ \ red`, `f.1.2 ∉ univ \ red` i.e. `f.1.2 ∈ red`.
        have h2red : f.1.1.2 ∈ D.red := by
          have := h2nothost; rw [Finset.mem_sdiff] at this; push Not at this
          exact this (Finset.mem_univ _)
        have h2notcompl : f.1.1.2 ∉ D.complement := fun hc =>
          (Finset.disjoint_left.mp D.red_disjoint_complement) h2red hc
        rcases hinc with hc1 | hc2
        · refine Or.inl ⟨hc1, h2notcompl⟩
        · exact absurd hc2 h2notcompl
      · have h1red : f.1.1.1 ∈ D.red := by
          have := h1nothost; rw [Finset.mem_sdiff] at this; push Not at this
          exact this (Finset.mem_univ _)
        have h1notcompl : f.1.1.1 ∉ D.complement := fun hc =>
          (Finset.disjoint_left.mp D.red_disjoint_complement) h1red hc
        rcases hinc with hc1 | hc2
        · exact absurd hc1 h1notcompl
        · refine Or.inr ⟨h1notcompl, hc2⟩
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨f.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]

open scoped Classical in
/-- **The host-relative fiber cardinality.** Among the boundary-agreeing pairs of
global configurations whose blue-side host label is `bdry`, the fiber over a merged
configuration `η` of the complement merge has cardinality the complement interior
bond product when `η` itself has host label `bdry`, and is empty otherwise.

The host constraint on the blue side is implied by the merge identity and the
complement-boundary agreement (`hostLabel_p2_eq_hostLabel_regionMerge_complement`),
so on the compatible fibers the count is the unconstrained complement fiber count
`regionFiber_card`; on the incompatible fibers the host constraint clashes with the
merge, emptying the fiber.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockFiber_card
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
          (regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2 ∧
            regionMerge (G := G) A D.complement p = η))).card =
      if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
        regionInteriorBondProd (G := G) A D.complement else 0 := by
  classical
  -- The host label of the blue side is the host label of the merge on this fiber.
  by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry
  · rw [if_pos hcompat]
    -- The host constraint is implied by the agreement and the merge identity.
    rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            (regionBoundaryLabel (G := G) A D.complement p.1 =
                regionBoundaryLabel (G := G) A D.complement p.2 ∧
              regionMerge (G := G) A D.complement p = η))) =
        Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          (regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2 ∧
            regionMerge (G := G) A D.complement p = η)) from ?_]
    · exact regionFiber_card (G := G) A D.complement η
    · refine Finset.filter_congr (fun p _ => ?_)
      constructor
      · rintro ⟨_, hagree, hmerge⟩; exact ⟨hagree, hmerge⟩
      · rintro ⟨hagree, hmerge⟩
        refine ⟨?_, hagree, hmerge⟩
        rw [hostLabel_p2_eq_hostLabel_regionMerge_complement (A := A) (e := e) D p hagree,
          hmerge, hcompat]
  · rw [if_neg hcompat]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hhost, hagree, hmerge⟩
    apply hcompat
    rw [← hmerge,
      ← hostLabel_p2_eq_hostLabel_regionMerge_complement (A := A) (e := e) D p hagree, hhost]

open scoped Classical in
/-- **The host-relative merge collapse.** The boundary-agreeing double sum of the
complement vertex product against the blue vertex product, with the blue side
constrained to the host label `bdry`, collapses to the complement interior bond
product times the single constrained sum of the complement against the blue product
over global configurations with host label `bdry`. This is the multiplicity collapse
behind the three-block factorization, mirroring `stateCoeff_eq_regionComplement` in
the host-relative frame.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockDoubleSum_eq_smul_single
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2),
      (∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      regionInteriorBondProd (G := G) A D.complement •
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
          (∏ w : {w : V // w ∈ D.complement},
              A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
            ∏ w : {w : V // w ∈ D.blue},
              A.component w.1 (fun ie => ζ ie.1) (σblue w) := by
  classical
  -- Read each agreeing summand through the merged configuration.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2),
      (∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2),
        (∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => regionMerge (G := G) A D.complement p ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ D.blue},
            A.component w.1
              (fun ie => regionMerge (G := G) A D.complement p ie.1) (σblue w) from ?_]
  · -- Group the agreeing pairs by their merged configuration.
    rw [← Finset.sum_fiberwise (Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2))
      (fun p => regionMerge (G := G) A D.complement p)
      (fun p =>
        (∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => regionMerge (G := G) A D.complement p ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ D.blue},
            A.component w.1
              (fun ie => regionMerge (G := G) A D.complement p ie.1) (σblue w))]
    -- Compare the η-indexed sums on both sides.
    rw [show (regionInteriorBondProd (G := G) A D.complement •
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig A =>
                regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
            (∏ w : {w : V // w ∈ D.complement},
                A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
              ∏ w : {w : V // w ∈ D.blue},
                A.component w.1 (fun ie => ζ ie.1) (σblue w)) =
        ∑ η : VirtualConfig A,
          regionInteriorBondProd (G := G) A D.complement •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
              (∏ w : {w : V // w ∈ D.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)) *
                ∏ w : {w : V // w ∈ D.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)
              else 0) from ?_]
    · refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [Finset.filter_filter,
        Finset.sum_congr rfl (g := fun _ =>
            (∏ w : {w : V // w ∈ D.complement},
                A.component w.1 (fun ie => η ie.1) (σcompl w)) *
              ∏ w : {w : V // w ∈ D.blue},
                A.component w.1 (fun ie => η ie.1) (σblue w))
          (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
        Finset.sum_const]
      -- The fiber count is the conditional complement interior bond product.
      rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
                regionBoundaryLabel (G := G) A D.complement p.1 =
                  regionBoundaryLabel (G := G) A D.complement p.2) ∧
              regionMerge (G := G) A D.complement p = η)) =
          Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
              (regionBoundaryLabel (G := G) A D.complement p.1 =
                  regionBoundaryLabel (G := G) A D.complement p.2 ∧
                regionMerge (G := G) A D.complement p = η)) from by
          refine Finset.filter_congr (fun p _ => ?_); tauto,
        threeBlockFiber_card (A := A) (e := e) D bdry η]
      by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry
      · rw [if_pos hcompat, if_pos hcompat]
      · rw [if_neg hcompat, if_neg hcompat, zero_smul, smul_zero]
    · rw [Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry)]
      rw [show (∑ η ∈ Finset.univ.filter
            (fun η : VirtualConfig A =>
              ¬ regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry),
          regionInteriorBondProd (G := G) A D.complement •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
              (∏ w : {w : V // w ∈ D.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)) *
                ∏ w : {w : V // w ∈ D.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)
              else 0)) = 0 from ?_,
        add_zero]
      · refine Finset.sum_congr rfl (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_pos hη.2]
      · refine Finset.sum_eq_zero (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_neg hη.2, smul_zero]
  · -- Each agreeing summand is the merged summand at the merged configuration.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [regionProd_eq_merge (G := G) A D.complement σcompl p,
      blueProd_eq_regionMerge_complement (A := A) (e := e) D σblue p hp.2.2]

open scoped Classical in
/-- **The blue coupling coefficient.** The blue vertex product summed over all global
configurations whose host label is `bdry` and whose complement boundary label is the
prescribed `bc'`. This is the blue-block contraction coupled to the complement
boundary configuration through the blue/complement crossing bonds, the coefficient of
the complement blocked-region weight in the three-block factorization.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def threeBlockBlueCoeff
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (bc' : RegionBoundaryConfig (G := G) A D.complement) : ℂ :=
  ∑ q ∈ Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
          regionBoundaryLabel (G := G) A D.complement q = bc'),
    ∏ w : {w : V // w ∈ D.blue}, A.component w.1 (fun ie => q ie.1) (σblue w)

open scoped Classical in
/-- **The host-relative decoupling.** The boundary-agreeing double sum of the
complement vertex product against the host-constrained blue vertex product decouples,
grouped by the complement boundary configuration `bc'`, into the complement
blocked-region weight at `bc'` against the blue coupling coefficient. The decoupling
holds because the complement product reads a global configuration only through the
complement-incident edges and the blue product only through the blue-incident edges,
which are coupled only through the shared blue/complement crossing bonds recorded by
`bc'`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockDoubleSum_eq_blueCoeff_sum
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.complement p.1 =
              regionBoundaryLabel (G := G) A D.complement p.2),
      (∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
        regionBlockedWeight (G := G) A D.complement bc' σcompl *
          threeBlockBlueCoeff (A := A) (e := e) D bdry σblue bc' := by
  classical
  -- Group the agreeing pairs by the complement boundary label of the complement side.
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
          regionBoundaryLabel (G := G) A D.complement p.1 =
            regionBoundaryLabel (G := G) A D.complement p.2))
    (fun p => regionBoundaryLabel (G := G) A D.complement p.1)
    (fun p =>
      (∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w))]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  -- On the `bc'` fiber the complement and blue constraints separate.
  rw [regionBlockedWeight, threeBlockBlueCoeff, Finset.sum_mul_sum]
  -- Reindex the product over `(p, q)` against the separated double sum.
  rw [Finset.filter_filter, ← Finset.sum_product']
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext x
  rcases x with ⟨p, q⟩
  constructor
  · intro hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hpq ⊢
    obtain ⟨⟨hhost, hagree⟩, hbc⟩ := hpq
    exact ⟨hbc, hhost, hbc ▸ hagree.symm⟩
  · intro hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hpq ⊢
    obtain ⟨hp, hhost, hq⟩ := hpq
    exact ⟨⟨hhost, hp.trans hq.symm⟩, hp⟩

open scoped Classical in
/-- **The core three-block smul-factorization (pointwise).** The complement interior
bond multiple of the fused host weight, at a fixed complement physical leg `σcompl`,
is the sum over complement boundary configurations of the blue coupling coefficient
times the complement blocked-region weight. Combines the merge collapse and the
decoupling, after splitting the fused host weight along `univ \ red = blue ⊔
complement` (`regionBlockedWeight_threeBlockComplPhysical_eq`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
          (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) =
      ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
        threeBlockBlueCoeff (A := A) (e := e) D bdry σblue bc' •
          regionBlockedWeight (G := G) A D.complement bc' σcompl := by
  classical
  -- Split the fused host weight along `univ \ red = blue ⊔ complement` and commute
  -- the blue/complement product order to match the merge-collapse convention.
  rw [regionBlockedWeight_threeBlockComplPhysical_eq (A := A) (e := e) D bdry σblue σcompl,
    show (∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
        (∏ w : {w : V // w ∈ D.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
        (∏ w : {w : V // w ∈ D.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ D.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w) from
      Finset.sum_congr rfl (fun ζ _ => mul_comm _ _)]
  -- The smul of the single sum is the boundary-agreeing double sum (merge collapse),
  -- which decouples into the blue coupling against the complement weight.
  rw [smul_eq_mul, ← nsmul_eq_mul,
    ← threeBlockDoubleSum_eq_smul_single (A := A) (e := e) D bdry σblue σcompl,
    threeBlockDoubleSum_eq_blueCoeff_sum (A := A) (e := e) D bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [smul_eq_mul, mul_comm]

open scoped Classical in
/-- **The core three-block smul-factorization (as functions of `σcompl`).** The
complement interior bond multiple of the fused host weight, read as a function of the
complement physical leg, is the blue-coupling combination of the complement
blocked-region weights. This is the function-level form of the pointwise factorization,
ready for the divide-out into the complement block image.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_threeBlockComplWeight_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue) :
    (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        (fun σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement =>
          regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
        threeBlockBlueCoeff (A := A) (e := e) D bdry σblue bc' •
          regionBlockedWeight (G := G) A D.complement bc' := by
  funext σcompl
  rw [Pi.smul_apply, Finset.sum_apply,
    regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
      (A := A) (e := e) D bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [Pi.smul_apply]

/-- **The core region-blocking associativity factorization.** The fused host weight
`regionBlockedWeight A (univ \ red) bdry (threeBlockComplPhysical D σblue σcompl)`,
read as a function of the complement physical leg `σcompl`, lies in the range of the
complement block's blocked-region tensor map. This is the foundational factorization
that strips the complement (middle) block while keeping the red and blue residual
configurations independent, unblocking the three-block middle strip for the normal
PEPS Fundamental Theorem.

The complement interior bond multiple of the function is the blue-coupling combination
of the complement blocked-region weights
(`regionInteriorBondProd_smul_threeBlockComplWeight_eq`), each of which lies in the
range (`range_regionBlockedTensorMap_eq_span`); dividing out the nonzero interior bond
multiplicity (positive bond dimensions) lands the function itself in the range.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_threeBlockComplPhysical_mem_range
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    (fun σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement =>
        regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
          (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) ∈
      LinearMap.range (regionBlockedTensorMap (G := G) A D.complement) := by
  classical
  rw [range_regionBlockedTensorMap_eq_span (G := G) A D.complement]
  have hne : (regionInteriorBondProd (G := G) A D.complement : ℂ) ≠ 0 := by
    have hpos' : 0 < regionInteriorBondProd (G := G) A D.complement :=
      regionInteriorBondProd_pos (G := G) A D.complement hpos
    exact_mod_cast hpos'.ne'
  rw [← Submodule.smul_mem_iff _ hne,
    regionInteriorBondProd_smul_threeBlockComplWeight_eq (A := A) (e := e) D bdry σblue]
  refine Submodule.sum_mem _ (fun bc' _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bc', rfl⟩)

end PEPS
end TNLean
