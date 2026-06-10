import TNLean.PEPS.RegionBlock.Recovery11
import TNLean.PEPS.RegionBlock.BlockRangeCoincidence

/-!
# The general union-of-injective-regions lemma for normal PEPS

This file proves the union lemma of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`) in its source-faithful generality: for two
disjoint finite regions whose blocked tensors are injective, the blocked tensor of
their union is injective. The earlier
`TNLean.PEPS.RegionBlock.UnionInjectivity` proves the same conclusion only for the
edge-centred blue/complement triple of a `NormalEdgeBlockingData`, whose third
region (the red block) is additionally required to be injective and to carry the
endpoints of a distinguished edge. The source lemma asks for neither; this file
removes both restrictions by re-deriving the two-step inverse application over a
bare three-block geometry.

The geometry is recorded by `ThreeBlockGeometry`: three pairwise-disjoint finite
regions `red`, `blue`, `complement` covering the vertex set, with no injectivity
hypothesis and no distinguished edge. The host block whose injectivity is proved is
`univ \ red = blue ∪ complement`. Setting `blue := S`, `complement := T`, and
`red := univ \ (S ∪ T)` recovers the disjoint two-region statement.

The proof is the source's two-step inverse application, re-derived here for the
geometry without the red block's injectivity: a coefficient family annihilating the
host weights is stripped of the blue block by its left inverse, leaving a
complement-coupling combination; injectivity of the complement block then forces the
reconstructed host residual coefficients to vanish, and surjectivity of the host
boundary label (positive bond dimensions) makes every residual realized.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-- A geometry of three pairwise-disjoint finite regions covering the vertex set.

This carries only the set-theoretic data of the four-region decomposition used by
the source union-of-injective-regions lemma (arXiv:1804.04964, Section 3, Lemma
`injective_union`, lines 1324--1400 of `Papers/1804.04964/paper_normal.tex`): the
blocks `red`, `blue`, `complement` are disjoint and cover `V`. There is no
injectivity hypothesis on any block and no distinguished edge; the host block
`univ \ red = blue ∪ complement` is the union whose injectivity the lemma proves
from injectivity of `blue` and `complement`. -/
structure ThreeBlockGeometry (V : Type*) [Fintype V] [DecidableEq V] : Type _ where
  /-- The block playing the role of the source's `(A ∪ B)`-complement. -/
  red : Finset V
  /-- The first injective block of the union. -/
  blue : Finset V
  /-- The second injective block of the union. -/
  complement : Finset V
  /-- The red and blue blocks are disjoint. -/
  red_disjoint_blue : Disjoint red blue
  /-- The red and complementary blocks are disjoint. -/
  red_disjoint_complement : Disjoint red complement
  /-- The blue and complementary blocks are disjoint. -/
  blue_disjoint_complement : Disjoint blue complement
  /-- The three blocks cover the vertex set. -/
  cover_univ : red ∪ blue ∪ complement = Finset.univ

variable (g : ThreeBlockGeometry V)

/-- The set complement of the red block is the disjoint union of the blue and
complement blocks.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.sdiff_red_eq_blue_union_complement :
    Finset.univ \ g.red = g.blue ∪ g.complement := by
  ext w
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · intro hwnotred
    have hcover : w ∈ g.red ∪ g.blue ∪ g.complement := by
      rw [g.cover_univ]; exact Finset.mem_univ _
    rcases Finset.mem_union.mp hcover with hrb | hc
    · rcases Finset.mem_union.mp hrb with hr | hbl
      · exact absurd hr hwnotred
      · exact Or.inl hbl
    · exact Or.inr hc
  · intro hbc hr
    rcases hbc with hbl | hc
    · exact (Finset.disjoint_left.mp g.red_disjoint_blue) hr hbl
    · exact (Finset.disjoint_left.mp g.red_disjoint_complement) hr hc

/-- The complement physical leg over `univ \ red`, fused from a blue physical leg and
a complement physical leg: a vertex `w ∉ red` lies in `blue` (read `σblue`) or in
`complement` (read `σcompl`).

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
def ThreeBlockGeometry.complPhysical
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ g.red) :=
  fun w =>
    if hb : w.1 ∈ g.blue then σblue ⟨w.1, hb⟩
    else σcompl ⟨w.1, by
      have hwnotred : w.1 ∉ g.red := (Finset.mem_sdiff.mp w.2).2
      have hcover : w.1 ∈ g.red ∪ g.blue ∪ g.complement := by
        rw [g.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact absurd hr hwnotred
        · exact absurd hbl hb
      · exact hc⟩

@[simp] theorem ThreeBlockGeometry.complPhysical_apply_blue
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (w : {w : V // w ∈ Finset.univ \ g.red}) (hb : w.1 ∈ g.blue) :
    g.complPhysical (d := d) σblue σcompl w = σblue ⟨w.1, hb⟩ := by
  rw [ThreeBlockGeometry.complPhysical, dif_pos hb]

@[simp] theorem ThreeBlockGeometry.complPhysical_apply_not_blue
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (w : {w : V // w ∈ Finset.univ \ g.red}) (hb : w.1 ∉ g.blue) (hc : w.1 ∈ g.complement) :
    g.complPhysical (d := d) σblue σcompl w = σcompl ⟨w.1, hc⟩ := by
  rw [ThreeBlockGeometry.complPhysical, dif_neg hb]

/-- The product of the vertex tensors over `univ \ red`, read with the fused
blue/complement physical leg, factors as the blue product times the complement
product.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.prod_sdiff_red_eq_blue_mul_complement
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (ζ : VirtualConfig A) :
    (∏ w : {w : V // w ∈ Finset.univ \ g.red},
        A.component w.1 (fun ie => ζ ie.1) (g.complPhysical (d := d) σblue σcompl w)) =
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · have hblue : IsEmpty {w : V // w ∈ g.blue} := ⟨fun w => hd.elim (σblue w)⟩
    have hcompl : IsEmpty {w : V // w ∈ g.complement} := ⟨fun w => hd.elim (σcompl w)⟩
    have hsdiff : IsEmpty {w : V // w ∈ Finset.univ \ g.red} :=
      ⟨fun w => hd.elim (g.complPhysical (d := d) σblue σcompl w)⟩
    rw [Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, one_mul]
  · set gf : V → Fin d := fun w =>
      if hb : w ∈ g.blue then σblue ⟨w, hb⟩
      else if hc : w ∈ g.complement then σcompl ⟨w, hc⟩
      else Classical.arbitrary (Fin d) with hgf
    have hsdiff : (∏ w : {w : V // w ∈ Finset.univ \ g.red},
          A.component w.1 (fun ie => ζ ie.1)
            (g.complPhysical (d := d) σblue σcompl w)) =
        ∏ w : {w : V // w ∈ Finset.univ \ g.red},
          A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      by_cases hb : w.1 ∈ g.blue
      · rw [g.complPhysical_apply_blue (d := d) σblue σcompl w hb, hgf]; simp only [dif_pos hb]
      · have hwnotred : w.1 ∉ g.red := (Finset.mem_sdiff.mp w.2).2
        have hc : w.1 ∈ g.complement := by
          have hcover : w.1 ∈ g.red ∪ g.blue ∪ g.complement := by
            rw [g.cover_univ]; exact Finset.mem_univ _
          rcases Finset.mem_union.mp hcover with hrb | hc
          · rcases Finset.mem_union.mp hrb with hr | hbl
            · exact absurd hr hwnotred
            · exact absurd hbl hb
          · exact hc
        rw [g.complPhysical_apply_not_blue (d := d) σblue σcompl w hb hc, hgf]
        simp only [dif_neg hb, dif_pos hc]
    have hblue : (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => ζ ie.1) (σblue w)) =
        ∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1; rw [hgf]; simp only [dif_pos w.2]
    have hcompl : (∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => ζ ie.1) (gf w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      have hb : w.1 ∉ g.blue := fun h =>
        (Finset.disjoint_left.mp g.blue_disjoint_complement) h w.2
      rw [hgf]; simp only [dif_neg hb, dif_pos w.2]
    rw [hsdiff, hblue, hcompl]
    rw [← Finset.prod_subtype (Finset.univ \ g.red) (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      ← Finset.prod_subtype g.blue (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      ← Finset.prod_subtype g.complement (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (gf w)),
      g.sdiff_red_eq_blue_union_complement,
      Finset.prod_union g.blue_disjoint_complement]

/-- The blocked-region weight of `univ \ red` at the fused blue/complement physical
leg unfolds to the single constrained sum of the blue product times the complement
product.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.regionBlockedWeight_complPhysical_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
        (g.complPhysical (d := d) σblue σcompl) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
        (∏ w : {w : V // w ∈ g.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  rw [regionBlockedWeight]
  exact Finset.sum_congr rfl
    (fun ζ _ => g.prod_sdiff_red_eq_blue_mul_complement (A := A) σblue σcompl ζ)


/-! ### The blue and complement fiber-collapse factorizations

The two source factorizations stripping the blue and complement blocks, re-derived
over the bare geometry. -/

/-- The blue vertex product reads a global configuration only through the
blue-incident edges, so it agrees with the configuration merged along the
complement block, provided the two merged configurations agree on the complement
boundary. The blue-incident edges that are also complement-incident are exactly the
blue/complement crossing edges, which are boundary edges of the complement block,
where the agreement forces the two configurations to coincide.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.blueProd_eq_regionMerge_complement
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.complement p.1 =
      regionBoundaryLabel (G := G) A g.complement p.2) :
    (∏ w : {w : V // w ∈ g.blue}, A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∏ w : {w : V // w ∈ g.blue},
        A.component w.1 (fun ie => regionMerge (G := G) A g.complement p ie.1) (σblue w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  -- `ie` is incident to `w ∈ blue`, so `w ∉ complement`.
  have hwblue : w.1 ∈ g.blue := w.2
  have hwnotcompl : w.1 ∉ g.complement := fun hc =>
    (Finset.disjoint_left.mp g.blue_disjoint_complement) hwblue hc
  have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
  by_cases hinc : IsRegionIncidentEdge (G := G) g.complement ie.1
  · -- `ie` is complement-incident and touches `w ∉ complement`: a boundary edge of
    -- the complement, where `p.1` and `p.2` agree.
    have hbdry : IsRegionBoundaryEdge (G := G) g.complement ie.1 := by
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
theorem ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_complement
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.complement p.1 =
      regionBoundaryLabel (G := G) A g.complement p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 =
      regionBoundaryLabel (G := G) A (Finset.univ \ g.red)
        (regionMerge (G := G) A g.complement p) := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : IsRegionIncidentEdge (G := G) g.complement f.1
  · -- A complement-incident host boundary edge is a boundary edge of the complement.
    have hbdry : IsRegionBoundaryEdge (G := G) g.complement f.1 := by
      -- The host-side endpoint that lies in `univ \ red` is the complement endpoint;
      -- the red endpoint lies outside the complement.
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · -- `f.1.1 ∈ univ \ red`, `f.1.2 ∉ univ \ red` i.e. `f.1.2 ∈ red`.
        have h2red : f.1.1.2 ∈ g.red := by
          have := h2nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h2notcompl : f.1.1.2 ∉ g.complement := fun hc =>
          (Finset.disjoint_left.mp g.red_disjoint_complement) h2red hc
        rcases hinc with hc1 | hc2
        · refine Or.inl ⟨hc1, h2notcompl⟩
        · exact absurd hc2 h2notcompl
      · have h1red : f.1.1.1 ∈ g.red := by
          have := h1nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h1notcompl : f.1.1.1 ∉ g.complement := fun hc =>
          (Finset.disjoint_left.mp g.red_disjoint_complement) h1red hc
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
theorem ThreeBlockGeometry.threeBlockFiber_card
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
          (regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2 ∧
            regionMerge (G := G) A g.complement p = η))).card =
      if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
        regionInteriorBondProd (G := G) A g.complement else 0 := by
  classical
  -- The host label of the blue side is the host label of the merge on this fiber.
  by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry
  · rw [if_pos hcompat]
    -- The host constraint is implied by the agreement and the merge identity.
    rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            (regionBoundaryLabel (G := G) A g.complement p.1 =
                regionBoundaryLabel (G := G) A g.complement p.2 ∧
              regionMerge (G := G) A g.complement p = η))) =
        Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          (regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2 ∧
            regionMerge (G := G) A g.complement p = η)) from ?_]
    · exact regionFiber_card (G := G) A g.complement η
    · refine Finset.filter_congr (fun p _ => ?_)
      constructor
      · rintro ⟨_, hagree, hmerge⟩; exact ⟨hagree, hmerge⟩
      · rintro ⟨hagree, hmerge⟩
        refine ⟨?_, hagree, hmerge⟩
        rw [g.hostLabel_p2_eq_hostLabel_regionMerge_complement p hagree,
          hmerge, hcompat]
  · rw [if_neg hcompat]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hhost, hagree, hmerge⟩
    apply hcompat
    rw [← hmerge,
      ← g.hostLabel_p2_eq_hostLabel_regionMerge_complement p hagree, hhost]
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
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2),
      (∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      regionInteriorBondProd (G := G) A g.complement •
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
          (∏ w : {w : V // w ∈ g.complement},
              A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
            ∏ w : {w : V // w ∈ g.blue},
              A.component w.1 (fun ie => ζ ie.1) (σblue w) := by
  classical
  -- Read each agreeing summand through the merged configuration.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2),
      (∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2),
        (∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => regionMerge (G := G) A g.complement p ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ g.blue},
            A.component w.1
              (fun ie => regionMerge (G := G) A g.complement p ie.1) (σblue w) from ?_]
  · -- Group the agreeing pairs by their merged configuration.
    rw [← Finset.sum_fiberwise (Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2))
      (fun p => regionMerge (G := G) A g.complement p)
      (fun p =>
        (∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => regionMerge (G := G) A g.complement p ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ g.blue},
            A.component w.1
              (fun ie => regionMerge (G := G) A g.complement p ie.1) (σblue w))]
    -- Compare the η-indexed sums on both sides.
    rw [show (regionInteriorBondProd (G := G) A g.complement •
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig A =>
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
            (∏ w : {w : V // w ∈ g.complement},
                A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
              ∏ w : {w : V // w ∈ g.blue},
                A.component w.1 (fun ie => ζ ie.1) (σblue w)) =
        ∑ η : VirtualConfig A,
          regionInteriorBondProd (G := G) A g.complement •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
              (∏ w : {w : V // w ∈ g.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)) *
                ∏ w : {w : V // w ∈ g.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)
              else 0) from ?_]
    · refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [Finset.filter_filter,
        Finset.sum_congr rfl (g := fun _ =>
            (∏ w : {w : V // w ∈ g.complement},
                A.component w.1 (fun ie => η ie.1) (σcompl w)) *
              ∏ w : {w : V // w ∈ g.blue},
                A.component w.1 (fun ie => η ie.1) (σblue w))
          (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
        Finset.sum_const]
      -- The fiber count is the conditional complement interior bond product.
      rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
                regionBoundaryLabel (G := G) A g.complement p.1 =
                  regionBoundaryLabel (G := G) A g.complement p.2) ∧
              regionMerge (G := G) A g.complement p = η)) =
          Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
              (regionBoundaryLabel (G := G) A g.complement p.1 =
                  regionBoundaryLabel (G := G) A g.complement p.2 ∧
                regionMerge (G := G) A g.complement p = η)) from by
          refine Finset.filter_congr (fun p _ => ?_); tauto,
        g.threeBlockFiber_card bdry η]
      by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry
      · rw [if_pos hcompat, if_pos hcompat]
      · rw [if_neg hcompat, if_neg hcompat, zero_smul, smul_zero]
    · rw [Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry)]
      rw [show (∑ η ∈ Finset.univ.filter
            (fun η : VirtualConfig A =>
              ¬ regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry),
          regionInteriorBondProd (G := G) A g.complement •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
              (∏ w : {w : V // w ∈ g.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)) *
                ∏ w : {w : V // w ∈ g.blue},
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
    rw [regionProd_eq_merge (G := G) A g.complement σcompl p,
      g.blueProd_eq_regionMerge_complement σblue p hp.2.2]
open scoped Classical in
/-- **The blue coupling coefficient.** The blue vertex product summed over all global
configurations whose host label is `bdry` and whose complement boundary label is the
prescribed `bc'`. This is the blue-block contraction coupled to the complement
boundary configuration through the blue/complement crossing bonds, the coefficient of
the complement blocked-region weight in the three-block factorization.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def ThreeBlockGeometry.threeBlockBlueCoeff
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (bc' : RegionBoundaryConfig (G := G) A g.complement) : ℂ :=
  ∑ q ∈ Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
          regionBoundaryLabel (G := G) A g.complement q = bc'),
    ∏ w : {w : V // w ∈ g.blue}, A.component w.1 (fun ie => q ie.1) (σblue w)
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
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_blueCoeff_sum
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.complement p.1 =
              regionBoundaryLabel (G := G) A g.complement p.2),
      (∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w)) =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        regionBlockedWeight (G := G) A g.complement bc' σcompl *
          g.threeBlockBlueCoeff bdry σblue bc' := by
  classical
  -- Group the agreeing pairs by the complement boundary label of the complement side.
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
          regionBoundaryLabel (G := G) A g.complement p.1 =
            regionBoundaryLabel (G := G) A g.complement p.2))
    (fun p => regionBoundaryLabel (G := G) A g.complement p.1)
    (fun p =>
      (∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.1 ie.1) (σcompl w)) *
        ∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.2 ie.1) (σblue w))]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  -- On the `bc'` fiber the complement and blue constraints separate.
  rw [regionBlockedWeight, threeBlockBlueCoeff, Finset.sum_mul_sum]
  -- Reindex the product over `(p, q)` against the separated double sum.
  rw [Finset.filter_filter, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.1, p.2)) (fun p => (p.1, p.2)) ?_ ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · -- A `bc'`-fiber pair maps to the separated product index set.
    rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hpq ⊢
    obtain ⟨⟨hhost, hagree⟩, hbc⟩ := hpq
    exact ⟨hbc, hhost, hbc ▸ hagree.symm⟩
  · -- A separated product index maps back to a `bc'`-fiber pair.
    rintro ⟨p, q⟩ hpq
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
theorem ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (regionInteriorBondProd (G := G) A g.complement : ℂ) •
        regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
          (g.complPhysical σblue σcompl) =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        g.threeBlockBlueCoeff bdry σblue bc' •
          regionBlockedWeight (G := G) A g.complement bc' σcompl := by
  classical
  -- Split the fused host weight along `univ \ red = blue ⊔ complement` and commute
  -- the blue/complement product order to match the merge-collapse convention.
  rw [g.regionBlockedWeight_complPhysical_eq bdry σblue σcompl,
    show (∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
        (∏ w : {w : V // w ∈ g.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
        (∏ w : {w : V // w ∈ g.complement},
            A.component w.1 (fun ie => ζ ie.1) (σcompl w)) *
          ∏ w : {w : V // w ∈ g.blue},
            A.component w.1 (fun ie => ζ ie.1) (σblue w) from
      Finset.sum_congr rfl (fun ζ _ => mul_comm _ _)]
  -- The smul of the single sum is the boundary-agreeing double sum (merge collapse),
  -- which decouples into the blue coupling against the complement weight.
  rw [smul_eq_mul, ← nsmul_eq_mul,
    ← g.threeBlockDoubleSum_eq_smul_single bdry σblue σcompl,
    g.threeBlockDoubleSum_eq_blueCoeff_sum bdry σblue σcompl]
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
theorem ThreeBlockGeometry.regionInteriorBondProd_smul_threeBlockComplWeight_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue) :
    (regionInteriorBondProd (G := G) A g.complement : ℂ) •
        (fun σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement =>
          regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
            (g.complPhysical σblue σcompl)) =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        g.threeBlockBlueCoeff bdry σblue bc' •
          regionBlockedWeight (G := G) A g.complement bc' := by
  funext σcompl
  rw [Pi.smul_apply, Finset.sum_apply,
    g.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [Pi.smul_apply]

end PEPS
end TNLean
