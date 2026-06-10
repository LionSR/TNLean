import TNLean.PEPS.RegionBlock.CoarseThreeSite2
import TNLean.PEPS.RegionBlock.Recovery

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

/-! ### The fused complement physical leg

The two-block collapse `stateCoeff_eq_regionComplement` reads the host
`univ \ red` through a single physical leg over `univ \ red`. The blue and
complement super-sites carry two independent physical legs, over `blue` and over
`complement`. Under the partition `univ \ red = blue ∪ complement`, these fuse
into one leg over `univ \ red`. -/

/-- The fused complement physical leg over `univ \ red`, read from a blue physical
leg and a complement physical leg: a vertex outside `red` lies in `blue` (then
read `σblue`) or, failing that, in `complement` (then read `σcompl`). -/
noncomputable def complPhysical (hP : F.IsPartition)
    (σblue : RegionPhysicalConfig (V := V) (d := d) F.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) F.complement) :
    RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ F.red) :=
  fun w =>
    if hb : w.1 ∈ F.blue then σblue ⟨w.1, hb⟩
    else σcompl ⟨w.1, by
      have hbc : w.1 ∈ F.blue ∪ F.complement := by
        rw [← hP.sdiff_red]; exact w.2
      rcases Finset.mem_union.mp hbc with hbl | hc
      · exact absurd hbl hb
      · exact hc⟩

/-- The fused complement leg reads a blue vertex off the blue physical leg. -/
theorem complPhysical_apply_blue (hP : F.IsPartition)
    (σblue : RegionPhysicalConfig (V := V) (d := d) F.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) F.complement)
    (w : {w : V // w ∈ Finset.univ \ F.red}) (hb : w.1 ∈ F.blue) :
    F.complPhysical hP σblue σcompl w = σblue ⟨w.1, hb⟩ := by
  rw [complPhysical, dif_pos hb]

/-- The fused complement leg reads a non-blue vertex off the complement physical
leg. -/
theorem complPhysical_apply_not_blue (hP : F.IsPartition)
    (σblue : RegionPhysicalConfig (V := V) (d := d) F.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) F.complement)
    (w : {w : V // w ∈ Finset.univ \ F.red}) (hb : w.1 ∉ F.blue)
    (hc : w.1 ∈ F.complement) :
    F.complPhysical hP σblue σcompl w = σcompl ⟨w.1, hc⟩ := by
  rw [complPhysical, dif_neg hb]

/-- **The vertex-product split over `univ \ red`.** For any global virtual
configuration `ζ`, the product of the vertex tensors over `univ \ red`, read with
the fused blue/complement physical leg, factors as the blue product (read with
`σblue`) times the complement product (read with `σcompl`). This is the disjoint
decomposition `univ \ red = blue ⊔ complement` applied to the contraction. -/
theorem prod_sdiff_red_eq_blue_mul_complement (hP : F.IsPartition)
    (σblue : RegionPhysicalConfig (V := V) (d := d) F.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) F.complement)
    (ζ : VirtualConfig A) :
    (∏ w : {w : V // w ∈ Finset.univ \ F.red},
        A.component w.1 (fun ie => ζ ie.1) (F.complPhysical hP σblue σcompl w)) =
      (∏ w : {w : V // w ∈ F.blue}, A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ F.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  classical
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · -- With no physical index, every block subtype is empty.
    have hblue : IsEmpty {w : V // w ∈ F.blue} := ⟨fun w => hd.elim (σblue w)⟩
    have hcompl : IsEmpty {w : V // w ∈ F.complement} := ⟨fun w => hd.elim (σcompl w)⟩
    have hsdiff : IsEmpty {w : V // w ∈ Finset.univ \ F.red} :=
      ⟨fun w => hd.elim (F.complPhysical hP σblue σcompl w)⟩
    rw [Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, Finset.prod_of_isEmpty, one_mul]
  · -- A total physical leg agreeing with `σblue` on blue and `σcompl` on complement.
    set g : V → Fin d := fun w =>
      if hb : w ∈ F.blue then σblue ⟨w, hb⟩
      else if hc : w ∈ F.complement then σcompl ⟨w, hc⟩
      else Classical.arbitrary (Fin d) with hg
    -- The fused leg on `univ \ red` agrees with `g`.
    have hsdiff : (∏ w : {w : V // w ∈ Finset.univ \ F.red},
          A.component w.1 (fun ie => ζ ie.1) (F.complPhysical hP σblue σcompl w)) =
        ∏ w : {w : V // w ∈ Finset.univ \ F.red},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      by_cases hb : w.1 ∈ F.blue
      · rw [F.complPhysical_apply_blue hP σblue σcompl w hb, hg]
        simp only [dif_pos hb]
      · have hbc' : w.1 ∈ F.blue ∪ F.complement := by rw [← hP.sdiff_red]; exact w.2
        have hc : w.1 ∈ F.complement := by
          rcases Finset.mem_union.mp hbc' with h | h
          · exact absurd h hb
          · exact h
        rw [F.complPhysical_apply_not_blue hP σblue σcompl w hb hc, hg]
        simp only [dif_neg hb, dif_pos hc]
    -- The blue and complement subtype products read `g` on their vertices.
    have hblue : (∏ w : {w : V // w ∈ F.blue},
          A.component w.1 (fun ie => ζ ie.1) (σblue w)) =
        ∏ w : {w : V // w ∈ F.blue},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      rw [hg]; simp only [dif_pos w.2]
    have hcompl : (∏ w : {w : V // w ∈ F.complement},
          A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
        ∏ w : {w : V // w ∈ F.complement},
          A.component w.1 (fun ie => ζ ie.1) (g w.1) := by
      refine Finset.prod_congr rfl (fun w _ => ?_)
      congr 1
      have hb : w.1 ∉ F.blue := fun h =>
        (Finset.disjoint_left.mp hP.blue_disjoint_complement) h w.2
      rw [hg]; simp only [dif_neg hb, dif_pos w.2]
    rw [hsdiff, hblue, hcompl]
    -- Convert the three subtype products to `Finset.prod` and split the union.
    rw [← Finset.prod_subtype (Finset.univ \ F.red) (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      ← Finset.prod_subtype F.blue (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      ← Finset.prod_subtype F.complement (fun x => Iff.rfl)
        (fun w => A.component w (fun ie => ζ ie.1) (g w)),
      hP.sdiff_red,
      Finset.prod_union (Finset.disjoint_left.mpr (fun w hbl hc =>
        (Finset.disjoint_left.mp hP.blue_disjoint_complement) hbl hc))]

end CoarseBlockingFrame

end PEPS
end TNLean
