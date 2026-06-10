import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.RegionBlock.Recovery
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# The three-region merge collapse for the normal PEPS theorem

The coarse three-site tensor of `TNLean.PEPS.RegionBlock.CoarseThreeSite` has its
closed-state coefficient written, through the coherent bond models of
`TNLean.PEPS.RegionBlock.CoarseThreeSite2`, as a sum over coarse virtual
configurations of a product of three original blocked-region weights
(`stateCoeff_coarseTensor_eq_threeRegionSum`). This file collapses that triple
sum to a constant times the original closed-state coefficient, the merge collapse
that glues the coarse state to the original state.

The route fuses the blue and complement weights into the host weight over
`univ \ red` and then applies the landed two-block collapse
`stateCoeff_eq_regionComplement` of `TNLean.PEPS.RegionBlock.Recovery` for the red
region against its set complement. The constants are the interior bond products of
the three regions, all positive under positive bond dimensions.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1205--1210 (the one-region-against-complement gluing) and
  1449--1500 (the blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The partition hypothesis of a coarse blocking frame

The merge collapse needs the three regions to partition the vertex set: the red,
blue, and complement regions are pairwise disjoint and cover `V`. A
`CoarseBlockingFrame` records only the three region injectivities, so the
partition is supplied as a separate hypothesis bundle. It is the geometry of the
source's edge blocking (arXiv:1804.04964, Section 3, the three injective regions
of a `NormalEdgeBlockingData` partition the lattice), here detached from the
tensor construction so the collapse reads only the partition. -/

namespace CoarseBlockingFrame

variable {A : Tensor G d} (F : CoarseBlockingFrame (G := G) (d := d) A)

/-- **The partition of a coarse blocking frame.** The red, blue, and complement
regions are pairwise disjoint and cover the vertex set. This is the geometry of
the source's edge blocking (arXiv:1804.04964, Section 3, proof of Theorem 3, the
three injective regions partition the lattice).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
structure IsPartition : Prop where
  /-- The red and blue regions are disjoint. -/
  red_disjoint_blue : Disjoint F.red F.blue
  /-- The red and complement regions are disjoint. -/
  red_disjoint_complement : Disjoint F.red F.complement
  /-- The blue and complement regions are disjoint. -/
  blue_disjoint_complement : Disjoint F.blue F.complement
  /-- The three regions cover the vertex set. -/
  cover_univ : F.red ∪ F.blue ∪ F.complement = Finset.univ

namespace IsPartition

variable {F}

/-- The set complement of the red region is the union of the blue and complement
regions. -/
theorem sdiff_red (hP : F.IsPartition) :
    Finset.univ \ F.red = F.blue ∪ F.complement := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hwnotred
    have hcover : w ∈ F.red ∪ F.blue ∪ F.complement := by
      rw [hP.cover_univ]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hcover with hrb | hc
    · rcases Finset.mem_union.mp hrb with hr | hbl
      · exact absurd hr hwnotred
      · exact Or.inl hbl
    · exact Or.inr hc
  · intro hbc hr
    rcases hbc with hbl | hc
    · exact (Finset.disjoint_left.mp hP.red_disjoint_blue) hr hbl
    · exact (Finset.disjoint_left.mp hP.red_disjoint_complement) hr hc

end IsPartition

/-! ### The three-block geometry of a partitioned coarse frame

The red, blue, and complement regions of a partitioned coarse frame form a
`ThreeBlockGeometry`, unlocking the landed three-block factorization machinery of
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` for the coarse merge collapse:
the fused complement physical leg `complPhysical`, the host vertex-product split
`prod_sdiff_red_eq_blue_mul_complement`, and the host weight as a blue/complement
double-product sum. -/

/-- **The three-block geometry of a partitioned coarse frame.** The red, blue, and
complement regions, with their pairwise disjointness and cover, packaged as a
`ThreeBlockGeometry` so the landed three-block factorizations of
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` apply to the coarse blocking.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
def toThreeBlockGeometry (hP : F.IsPartition) : ThreeBlockGeometry V where
  red := F.red
  blue := F.blue
  complement := F.complement
  red_disjoint_blue := hP.red_disjoint_blue
  red_disjoint_complement := hP.red_disjoint_complement
  blue_disjoint_complement := hP.blue_disjoint_complement
  cover_univ := hP.cover_univ

@[simp] theorem toThreeBlockGeometry_red (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).red = F.red := rfl
@[simp] theorem toThreeBlockGeometry_blue (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).blue = F.blue := rfl
@[simp] theorem toThreeBlockGeometry_complement (hP : F.IsPartition) :
    (F.toThreeBlockGeometry hP).complement = F.complement := rfl

/-! ### Crossing classification of region boundary edges

Under the partition, every boundary edge of a region crosses to exactly one
partner region: a boundary edge of `red` has its out-of-`red` endpoint in `blue`
or in `complement`, so it is an `r-b` or an `r-c` crossing edge. This is the
geometric content the factoring fields of a coherent frame consume: the two
super-edges incident to a super-site carry exactly the two crossing bundles of
its region's boundary. -/

/-- A vertex outside `red` lies in `blue` or in `complement`. -/
theorem mem_blue_or_complement_of_not_mem_red (hP : F.IsPartition) {w : V}
    (hw : w ∉ F.red) : w ∈ F.blue ∨ w ∈ F.complement := by
  have hbc : w ∈ F.blue ∪ F.complement := by rw [← hP.sdiff_red]; simp [hw]
  exact Finset.mem_union.mp hbc

/-- **Crossing classification at the red super-site.** A boundary edge of `red`
is an `r-b` crossing edge or an `r-c` crossing edge: its out-of-`red` endpoint
lies in `blue` or in `complement`. -/
theorem isCrossingEdge_red_blue_or_red_complement (hP : F.IsPartition) {g : Edge G}
    (hg : IsRegionBoundaryEdge (G := G) F.red g) :
    IsCrossingEdge (G := G) A F.red F.blue g ∨
      IsCrossingEdge (G := G) A F.red F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ red` (h1), `g.1.2 ∉ red` (h2): classify the out-of-red endpoint `g.1.2`.
    have h1nb : g.1.1 ∉ F.blue := (Finset.disjoint_left.mp hP.red_disjoint_blue) h1
    have h1nc : g.1.1 ∉ F.complement :=
      (Finset.disjoint_left.mp hP.red_disjoint_complement) h1
    rcases F.mem_blue_or_complement_of_not_mem_red hP h2 with hb | hc
    · exact Or.inl ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nb, hb⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · -- `g.1.1 ∉ red` (h1), `g.1.2 ∈ red` (h2): classify the out-of-red endpoint `g.1.1`.
    have h2nb : g.1.2 ∉ F.blue := (Finset.disjoint_left.mp hP.red_disjoint_blue) h2
    have h2nc : g.1.2 ∉ F.complement :=
      (Finset.disjoint_left.mp hP.red_disjoint_complement) h2
    rcases F.mem_blue_or_complement_of_not_mem_red hP h1 with hb | hc
    · exact Or.inl ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hb, h2nb⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- **Crossing classification at the blue super-site.** A boundary edge of `blue`
is an `r-b` crossing edge or a `b-c` crossing edge. -/
theorem isCrossingEdge_red_blue_or_blue_complement (hP : F.IsPartition) {g : Edge G}
    (hg : IsRegionBoundaryEdge (G := G) F.blue g) :
    IsCrossingEdge (G := G) A F.red F.blue g ∨
      IsCrossingEdge (G := G) A F.blue F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ blue` (h1), `g.1.2 ∉ blue` (h2): classify `g.1.2` as red or complement.
    have h1nr : g.1.1 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_blue) hr h1
    have h1nc : g.1.1 ∉ F.complement := fun hc =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) h1 hc
    have hbc : g.1.2 ∈ F.red ∨ g.1.2 ∈ F.complement := by
      have hcover : g.1.2 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h2
      · exact Or.inr hc
    rcases hbc with hr | hc
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨h1, h2⟩, Or.inr ⟨h1nc, hc⟩⟩
  · -- `g.1.1 ∉ blue` (h1), `g.1.2 ∈ blue` (h2): classify `g.1.1` as red or complement.
    have h2nr : g.1.2 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_blue) hr h2
    have h2nc : g.1.2 ∉ F.complement := fun hc =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) h2 hc
    have hbc : g.1.1 ∈ F.red ∨ g.1.1 ∈ F.complement := by
      have hcover : g.1.1 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact absurd hbl h1
      · exact Or.inr hc
    rcases hbc with hr | hc
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1, h2⟩, Or.inl ⟨hc, h2nc⟩⟩

/-- **Crossing classification at the complement super-site.** A boundary edge of
`complement` is an `r-c` crossing edge or a `b-c` crossing edge. -/
theorem isCrossingEdge_red_complement_or_blue_complement (hP : F.IsPartition)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) F.complement g) :
    IsCrossingEdge (G := G) A F.red F.complement g ∨
      IsCrossingEdge (G := G) A F.blue F.complement g := by
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- `g.1.1 ∈ complement`, `g.1.2 ∉ complement`: classify `g.1.2` as red or blue.
    have hbc : g.1.2 ∈ F.red ∨ g.1.2 ∈ F.blue := by
      have hcover : g.1.2 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h2
    -- `g.1.1 ∈ complement` (h1), so `g.1.1 ∉ red` and `g.1.1 ∉ blue`.
    have h1nr : g.1.1 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_complement) hr h1
    have h1nb : g.1.1 ∉ F.blue := fun hb =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb h1
    rcases hbc with hr | hb
    · exact Or.inl ⟨Or.inr ⟨h1nr, hr⟩, Or.inl ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inr ⟨h1nb, hb⟩, Or.inl ⟨h1, h2⟩⟩
  · -- `g.1.1 ∉ complement`, `g.1.2 ∈ complement`: classify `g.1.1` as red or blue.
    have hbc : g.1.1 ∈ F.red ∨ g.1.1 ∈ F.blue := by
      have hcover : g.1.1 ∈ F.red ∪ F.blue ∪ F.complement := by
        rw [hP.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact Or.inl hr
        · exact Or.inr hbl
      · exact absurd hc h1
    -- `g.1.2 ∈ complement` (h2), so `g.1.2 ∉ red` and `g.1.2 ∉ blue`.
    have h2nr : g.1.2 ∉ F.red := fun hr =>
      (Finset.disjoint_left.mp hP.red_disjoint_complement) hr h2
    have h2nb : g.1.2 ∉ F.blue := fun hb =>
      (Finset.disjoint_left.mp hP.blue_disjoint_complement) hb h2
    rcases hbc with hr | hb
    · exact Or.inl ⟨Or.inl ⟨hr, h2nr⟩, Or.inr ⟨h1, h2⟩⟩
    · exact Or.inr ⟨Or.inl ⟨hb, h2nb⟩, Or.inr ⟨h1, h2⟩⟩

end CoarseBlockingFrame

/-! ### Incident super-edges of the coarse graph

Each coarse super-site has two incident super-edges. The red super-site `0` is
incident to `r-b` and `r-c`, the blue super-site `1` to `r-b` and `b-c`, the
complement super-site `2` to `r-c` and `b-c`. These named incident edges feed the
factoring fields of a coherent frame, which read a super-bond off the coarse leg
at the corresponding incident edge. -/

/-- The incident super-edge `r-b` at the red super-site `0`. -/
def incidentRB0 : IncidentEdge coarseGraph 0 := ⟨coarseEdgeRB, Or.inl rfl⟩

/-- The incident super-edge `r-c` at the red super-site `0`. -/
def incidentRC0 : IncidentEdge coarseGraph 0 := ⟨coarseEdgeRC, Or.inl rfl⟩

/-- The incident super-edge `r-b` at the blue super-site `1`. -/
def incidentRB1 : IncidentEdge coarseGraph 1 := ⟨coarseEdgeRB, Or.inr rfl⟩

/-- The incident super-edge `b-c` at the blue super-site `1`. -/
def incidentBC1 : IncidentEdge coarseGraph 1 := ⟨coarseEdgeBC, Or.inl rfl⟩

/-- The incident super-edge `r-c` at the complement super-site `2`. -/
def incidentRC2 : IncidentEdge coarseGraph 2 := ⟨coarseEdgeRC, Or.inr rfl⟩

/-- The incident super-edge `b-c` at the complement super-site `2`. -/
def incidentBC2 : IncidentEdge coarseGraph 2 := ⟨coarseEdgeBC, Or.inr rfl⟩

@[simp] theorem incidentRB0_fst : (incidentRB0).1 = coarseEdgeRB := rfl
@[simp] theorem incidentRC0_fst : (incidentRC0).1 = coarseEdgeRC := rfl
@[simp] theorem incidentRB1_fst : (incidentRB1).1 = coarseEdgeRB := rfl
@[simp] theorem incidentBC1_fst : (incidentBC1).1 = coarseEdgeBC := rfl
@[simp] theorem incidentRC2_fst : (incidentRC2).1 = coarseEdgeRC := rfl
@[simp] theorem incidentBC2_fst : (incidentBC2).1 = coarseEdgeBC := rfl

/-! ### Reading a region boundary leg off the bond models

Through the factoring fields, each super-site's leg identification of a coarse
virtual configuration `η` reads every boundary edge of its region off one of the
two bond models on its incident super-edges. The crossing classification selects
which model: a boundary edge of `red` crossing to `blue` is read off the `r-b`
bond model at `η`'s `r-b` value, a boundary edge crossing to `complement` off the
`r-c` bond model at `η`'s `r-c` value. These read-offs are the per-edge form of
the shared-super-bond agreement; they will express each coarse blocked-region
weight as a function of the original crossing configurations alone. -/

namespace CoherentCoarseBlockingFrame

variable {A : Tensor G d} (F : CoherentCoarseBlockingFrame (G := G) (d := d) A)

/-- **Red leg off the `r-b` bond model.** On a red boundary edge crossing to blue,
the red super-site reads the leg of a coarse virtual configuration `η` off the
`r-b` bond model at `η`'s `r-b` value. -/
theorem legEquivRed_eq_bondModel_rb
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_red (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentRB0 rfl

/-- **Red leg off the `r-c` bond model.** On a red boundary edge crossing to the
complement, the red super-site reads the leg of `η` off the `r-c` bond model at
`η`'s `r-c` value. -/
theorem legEquivRed_eq_bondModel_rc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_red_rc (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentRC0 rfl

/-- **Blue leg off the `r-b` bond model.** On a blue boundary edge crossing to red,
the blue super-site reads the leg of `η` off the `r-b` bond model. -/
theorem legEquivBlue_eq_bondModel_rb
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_blue_rb (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentRB1 rfl

/-- **Blue leg off the `b-c` bond model.** On a blue boundary edge crossing to the
complement, the blue super-site reads the leg of `η` off the `b-c` bond model. -/
theorem legEquivBlue_eq_bondModel_bc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeBC (η coarseEdgeBC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_blue_bc (fun ie => η ie.1) ⟨g, hf.1⟩ hf incidentBC1 rfl

/-- **Complement leg off the `r-c` bond model.** On a complement boundary edge
crossing to red, the complement super-site reads the leg of `η` off the `r-c`
bond model. -/
theorem legEquivComplement_eq_bondModel_rc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_compl_rc (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentRC2 rfl

/-- **Complement leg off the `b-c` bond model.** On a complement boundary edge
crossing to blue, the complement super-site reads the leg of `η` off the `b-c`
bond model. -/
theorem legEquivComplement_eq_bondModel_bc
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) =
      (F.bondModel coarseEdgeBC (η coarseEdgeBC) ⟨g, hf⟩ : Fin (A.bondDim g)) :=
  F.factor_compl_bc (fun ie => η ie.1) ⟨g, hf.2⟩ hf incidentBC2 rfl

/-! ### The region boundary configs as functions of the crossing configs

Assembling the per-edge read-offs with the crossing classification, each coarse
region weight's boundary configuration is a function of the three original
crossing configurations alone. The red boundary configuration reads each red
boundary edge off the `r-b` bond model (if it crosses to blue) or the `r-c` bond
model (if it crosses to complement); the classification is a genuine dichotomy
because blue and complement are disjoint. This expresses `legEquivRed (fun ie =>
η ie.1)` entirely through `bondModel rb (η rb)` and `bondModel rc (η rc)`, the
form the merge collapse contracts against the original crossing edges. -/

open scoped Classical in
/-- The red boundary configuration induced by a coarse virtual configuration `η`
is determined by the `r-b` and `r-c` bond models at `η`'s values: on a red
boundary edge crossing to blue it reads the `r-b` model, on one crossing to the
complement it reads the `r-c` model. Under the partition every red boundary edge
crosses to exactly one of blue or complement. -/
theorem legEquivRed_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.red b}) :
    (F.frame.legEquivRed (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1 then
        (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeRC (η coarseEdgeRC)
          ⟨b.1, (F.frame.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dif_pos hb]
    have := F.legEquivRed_eq_bondModel_rb η b.1 hb
    -- `⟨b.1, hb.1⟩ = b` as subtype elements (same edge, proof-irrelevant membership).
    simpa using this
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_red_complement hP b.2).resolve_left hb
    have := F.legEquivRed_eq_bondModel_rc η b.1 hc
    simpa using this

open scoped Classical in
/-- The blue boundary configuration induced by `η`: on a blue boundary edge
crossing to red it reads the `r-b` bond model, on one crossing to the complement
it reads the `b-c` bond model. -/
theorem legEquivBlue_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.blue b}) :
    (F.frame.legEquivBlue (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1 then
        (F.bondModel coarseEdgeRB (η coarseEdgeRB) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeBC (η coarseEdgeBC)
          ⟨b.1, (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.blue b.1
  · rw [dif_pos hb]
    have := F.legEquivBlue_eq_bondModel_rb η b.1 hb
    simpa using this
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_blue_or_blue_complement hP b.2).resolve_left hb
    have := F.legEquivBlue_eq_bondModel_bc η b.1 hc
    simpa using this

open scoped Classical in
/-- The complement boundary configuration induced by `η`: on a complement
boundary edge crossing to red it reads the `r-c` bond model, on one crossing to
blue it reads the `b-c` bond model. -/
theorem legEquivComplement_apply_eq (hP : F.frame.IsPartition)
    (η : VirtualConfig (F.frame.coarseTensor))
    (b : {b : Edge G // IsRegionBoundaryEdge (G := G) F.frame.complement b}) :
    (F.frame.legEquivComplement (fun ie => η ie.1) b : Fin (A.bondDim b.1)) =
      if hb : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1 then
        (F.bondModel coarseEdgeRC (η coarseEdgeRC) ⟨b.1, hb⟩ : Fin (A.bondDim b.1))
      else
        (F.bondModel coarseEdgeBC (η coarseEdgeBC)
          ⟨b.1, (F.frame.isCrossingEdge_red_complement_or_blue_complement hP
            b.2).resolve_left hb⟩ :
          Fin (A.bondDim b.1)) := by
  by_cases hb : IsCrossingEdge (G := G) A F.frame.red F.frame.complement b.1
  · rw [dif_pos hb]
    have := F.legEquivComplement_eq_bondModel_rc η b.1 hb
    simpa using this
  · rw [dif_neg hb]
    have hc : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement b.1 :=
      (F.frame.isCrossingEdge_red_complement_or_blue_complement hP b.2).resolve_left hb
    have := F.legEquivComplement_eq_bondModel_bc η b.1 hc
    simpa using this

/-! ### Single-configuration consistency

For a single coarse virtual configuration `η`, the three region boundary
configurations it induces agree on every shared crossing edge: the two super-sites
incident to a super-edge read the same super-bond value (the one in `η`) through
the same bond model. These are the agreement lemmas of
`TNLean.PEPS.RegionBlock.CoarseThreeSite2` specialized to a single `η`, the form
the three-region merge collapse consumes when summing the three weights' product
over one coarse configuration. -/

/-- For a single `η`, the red and blue boundary configurations agree on every
red-to-blue crossing edge. -/
theorem legEquivRed_eq_legEquivBlue_on_rb_single
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.blue g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) :=
  F.legEquivRed_eq_legEquivBlue_on_rb (fun ie => η ie.1) (fun ie => η ie.1)
    incidentRB0 rfl incidentRB1 rfl rfl g hf

/-- For a single `η`, the red and complement boundary configurations agree on
every red-to-complement crossing edge. -/
theorem legEquivRed_eq_legEquivComplement_on_rc_single
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.red F.frame.complement g) :
    (F.frame.legEquivRed (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) :=
  F.legEquivRed_eq_legEquivComplement_on_rc (fun ie => η ie.1) (fun ie => η ie.1)
    incidentRC0 rfl incidentRC2 rfl rfl g hf

/-- For a single `η`, the blue and complement boundary configurations agree on
every blue-to-complement crossing edge. -/
theorem legEquivBlue_eq_legEquivComplement_on_bc_single
    (η : VirtualConfig (F.frame.coarseTensor)) (g : Edge G)
    (hf : IsCrossingEdge (G := G) A F.frame.blue F.frame.complement g) :
    (F.frame.legEquivBlue (fun ie => η ie.1) ⟨g, hf.1⟩ : Fin (A.bondDim g)) =
      (F.frame.legEquivComplement (fun ie => η ie.1) ⟨g, hf.2⟩ : Fin (A.bondDim g)) :=
  F.legEquivBlue_eq_legEquivComplement_on_bc (fun ie => η ie.1) (fun ie => η ie.1)
    incidentBC1 rfl incidentBC2 rfl rfl g hf

end CoherentCoarseBlockingFrame

end PEPS
end TNLean
