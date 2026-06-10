import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# The general union lemma: the blue-side fiber-collapse factorization

This file continues `TNLean.PEPS.RegionBlock.UnionInjectivityGeneral` with the
blue-side mirror of the complement-side fiber-collapse factorization, over a bare
`ThreeBlockGeometry`. Together with that file it supplies both factorizations the
two-step inverse application of Lemma `injective_union` (arXiv:1804.04964, Section 3,
lines 1324--1400 of `Papers/1804.04964/paper_normal.tex`) consumes.

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
variable (g : ThreeBlockGeometry V)

/-- The complement vertex product reads a global configuration only through the
complement-incident edges, so it agrees with the configuration merged along the blue
block, provided the two configurations agree on the blue boundary. This is the blue
mirror of `blueProd_eq_regionMerge_complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.complProd_eq_regionMerge_blue
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.blue p.1 =
      regionBoundaryLabel (G := G) A g.blue p.2) :
    (∏ w : {w : V // w ∈ g.complement}, A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∏ w : {w : V // w ∈ g.complement},
        A.component w.1 (fun ie => regionMerge (G := G) A g.blue p ie.1) (σcompl w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  -- `ie` is incident to `w ∈ complement`, so `w ∉ blue`.
  have hwcompl : w.1 ∈ g.complement := w.2
  have hwnotblue : w.1 ∉ g.blue := fun hb =>
    (Finset.disjoint_left.mp g.blue_disjoint_complement) hb hwcompl
  have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
  by_cases hinc : IsRegionIncidentEdge (G := G) g.blue ie.1
  · -- `ie` is blue-incident and touches `w ∉ blue`: a boundary edge of the blue block,
    -- where `p.1` and `p.2` agree.
    have hbdry : IsRegionBoundaryEdge (G := G) g.blue ie.1 := by
      rcases hinc with h1 | h2
      · rcases hwinc with hw1 | hw2
        · exact absurd (by rw [← hw1]; exact h1) hwnotblue
        · refine Or.inl ⟨h1, ?_⟩; rw [hw2]; exact hwnotblue
      · rcases hwinc with hw1 | hw2
        · refine Or.inr ⟨?_, h2⟩; rw [hw1]; exact hwnotblue
        · exact absurd (by rw [← hw2]; exact h2) hwnotblue
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨ie.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]

/-- On a boundary edge of the host `univ \ red`, the complement-side configuration
`p.2` agrees with the configuration merged along the blue block, provided the pair
agrees on the blue boundary. This is the blue mirror of
`hostLabel_p2_eq_hostLabel_regionMerge_complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.hostLabel_p2_eq_hostLabel_regionMerge_blue
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A g.blue p.1 =
      regionBoundaryLabel (G := G) A g.blue p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 =
      regionBoundaryLabel (G := G) A (Finset.univ \ g.red)
        (regionMerge (G := G) A g.blue p) := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : IsRegionIncidentEdge (G := G) g.blue f.1
  · -- A blue-incident host boundary edge is a boundary edge of the blue block.
    have hbdry : IsRegionBoundaryEdge (G := G) g.blue f.1 := by
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · have h2red : f.1.1.2 ∈ g.red := by
          have := h2nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h2notblue : f.1.1.2 ∉ g.blue := fun hb =>
          (Finset.disjoint_left.mp g.red_disjoint_blue) h2red hb
        rcases hinc with hb1 | hb2
        · refine Or.inl ⟨hb1, h2notblue⟩
        · exact absurd hb2 h2notblue
      · have h1red : f.1.1.1 ∈ g.red := by
          have := h1nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h1notblue : f.1.1.1 ∉ g.blue := fun hb =>
          (Finset.disjoint_left.mp g.red_disjoint_blue) h1red hb
        rcases hinc with hb1 | hb2
        · exact absurd hb1 h1notblue
        · refine Or.inr ⟨h1notblue, hb2⟩
    rw [regionMerge, if_pos hinc]
    have := congrFun hp ⟨f.1, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge, if_neg hinc]
open scoped Classical in
/-- **The host-relative blue fiber cardinality.** The blue mirror of
`threeBlockFiber_card`: among the blue-boundary-agreeing pairs whose complement-side
host label is `bdry`, the fiber over a blue merge `η` has cardinality the blue
interior bond product when `η` has host label `bdry`, and is empty otherwise.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockBlueFiber_card
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
          (regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2 ∧
            regionMerge (G := G) A g.blue p = η))).card =
      if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
        regionInteriorBondProd (G := G) A g.blue else 0 := by
  classical
  by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry
  · rw [if_pos hcompat]
    rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            (regionBoundaryLabel (G := G) A g.blue p.1 =
                regionBoundaryLabel (G := G) A g.blue p.2 ∧
              regionMerge (G := G) A g.blue p = η))) =
        Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          (regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2 ∧
            regionMerge (G := G) A g.blue p = η)) from ?_]
    · exact regionFiber_card (G := G) A g.blue η
    · refine Finset.filter_congr (fun p _ => ?_)
      constructor
      · rintro ⟨_, hagree, hmerge⟩; exact ⟨hagree, hmerge⟩
      · rintro ⟨hagree, hmerge⟩
        refine ⟨?_, hagree, hmerge⟩
        rw [g.hostLabel_p2_eq_hostLabel_regionMerge_blue p hagree,
          hmerge, hcompat]
  · rw [if_neg hcompat]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hhost, hagree, hmerge⟩
    apply hcompat
    rw [← hmerge,
      ← g.hostLabel_p2_eq_hostLabel_regionMerge_blue p hagree, hhost]
open scoped Classical in
/-- **The host-relative blue merge collapse.** The blue mirror of
`threeBlockDoubleSum_eq_smul_single`: the blue-boundary-agreeing double sum of the
blue vertex product against the complement vertex product, with the complement side
constrained to host label `bdry`, collapses to the blue interior bond product times
the single constrained sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_smul_single_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      regionInteriorBondProd (G := G) A g.blue •
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
          (∏ w : {w : V // w ∈ g.blue},
              A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
            ∏ w : {w : V // w ∈ g.complement},
              A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  classical
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
        (∏ w : {w : V // w ∈ g.blue},
            A.component w.1 (fun ie => regionMerge (G := G) A g.blue p ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ g.complement},
            A.component w.1
              (fun ie => regionMerge (G := G) A g.blue p ie.1) (σcompl w) from ?_]
  · rw [← Finset.sum_fiberwise (Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2))
      (fun p => regionMerge (G := G) A g.blue p)
      (fun p =>
        (∏ w : {w : V // w ∈ g.blue},
            A.component w.1 (fun ie => regionMerge (G := G) A g.blue p ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ g.complement},
            A.component w.1
              (fun ie => regionMerge (G := G) A g.blue p ie.1) (σcompl w))]
    rw [show (regionInteriorBondProd (G := G) A g.blue •
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig A =>
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) ζ = bdry),
            (∏ w : {w : V // w ∈ g.blue},
                A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
              ∏ w : {w : V // w ∈ g.complement},
                A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
        ∑ η : VirtualConfig A,
          regionInteriorBondProd (G := G) A g.blue •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
              (∏ w : {w : V // w ∈ g.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)) *
                ∏ w : {w : V // w ∈ g.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)
              else 0) from ?_]
    · refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [Finset.filter_filter,
        Finset.sum_congr rfl (g := fun _ =>
            (∏ w : {w : V // w ∈ g.blue},
                A.component w.1 (fun ie => η ie.1) (σblue w)) *
              ∏ w : {w : V // w ∈ g.complement},
                A.component w.1 (fun ie => η ie.1) (σcompl w))
          (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
        Finset.sum_const]
      rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
                regionBoundaryLabel (G := G) A g.blue p.1 =
                  regionBoundaryLabel (G := G) A g.blue p.2) ∧
              regionMerge (G := G) A g.blue p = η)) =
          Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
              (regionBoundaryLabel (G := G) A g.blue p.1 =
                  regionBoundaryLabel (G := G) A g.blue p.2 ∧
                regionMerge (G := G) A g.blue p = η)) from by
          refine Finset.filter_congr (fun p _ => ?_); tauto,
        g.threeBlockBlueFiber_card bdry η]
      by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry
      · rw [if_pos hcompat, if_pos hcompat]
      · rw [if_neg hcompat, if_neg hcompat, zero_smul, smul_zero]
    · rw [Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry)]
      rw [show (∑ η ∈ Finset.univ.filter
            (fun η : VirtualConfig A =>
              ¬ regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry),
          regionInteriorBondProd (G := G) A g.blue •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ g.red) η = bdry then
              (∏ w : {w : V // w ∈ g.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)) *
                ∏ w : {w : V // w ∈ g.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)
              else 0)) = 0 from ?_,
        add_zero]
      · refine Finset.sum_congr rfl (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_pos hη.2]
      · refine Finset.sum_eq_zero (fun η hη => ?_)
        rw [Finset.mem_filter] at hη
        rw [if_neg hη.2, smul_zero]
  · refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [regionProd_eq_merge (G := G) A g.blue σblue p,
      g.complProd_eq_regionMerge_blue σcompl p hp.2.2]
open scoped Classical in
/-- **The complement coupling coefficient.** The blue mirror of
`threeBlockBlueCoeff`: the complement vertex product summed over all global
configurations whose host label is `bdry` and whose blue boundary label is the
prescribed `bβ`. This is the complement-block contraction coupled to the blue
boundary configuration through the blue/complement crossing bonds.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def ThreeBlockGeometry.threeBlockComplCoeff
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement)
    (bβ : RegionBoundaryConfig (G := G) A g.blue) : ℂ :=
  ∑ q ∈ Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = bdry ∧
          regionBoundaryLabel (G := G) A g.blue q = bβ),
    ∏ w : {w : V // w ∈ g.complement}, A.component w.1 (fun ie => q ie.1) (σcompl w)

open scoped Classical in
/-- **The host-relative blue decoupling.** The blue mirror of
`threeBlockDoubleSum_eq_blueCoeff_sum`: the blue-boundary-agreeing double sum of the
blue vertex product against the host-constrained complement vertex product decouples,
grouped by the blue boundary configuration `bβ`, into the blue blocked-region weight
at `bβ` against the complement coupling coefficient.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.threeBlockDoubleSum_eq_complCoeff_sum_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A g.blue p.1 =
              regionBoundaryLabel (G := G) A g.blue p.2),
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        regionBlockedWeight (G := G) A g.blue bβ σblue *
          g.threeBlockComplCoeff bdry σcompl bβ := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ g.red) p.2 = bdry ∧
          regionBoundaryLabel (G := G) A g.blue p.1 =
            regionBoundaryLabel (G := G) A g.blue p.2))
    (fun p => regionBoundaryLabel (G := G) A g.blue p.1)
    (fun p =>
      (∏ w : {w : V // w ∈ g.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ g.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w))]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [regionBlockedWeight, threeBlockComplCoeff, Finset.sum_mul_sum]
  rw [Finset.filter_filter, ← Finset.sum_product']
  refine Finset.sum_nbij' (fun p => (p.1, p.2)) (fun p => (p.1, p.2)) ?_ ?_
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hpq ⊢
    obtain ⟨⟨hhost, hagree⟩, hbβ⟩ := hpq
    exact ⟨hbβ, hhost, hbβ ▸ hagree.symm⟩
  · rintro ⟨p, q⟩ hpq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hpq ⊢
    obtain ⟨hp, hhost, hq⟩ := hpq
    exact ⟨⟨hhost, hp.trans hq.symm⟩, hp⟩
open scoped Classical in
/-- **The core blue smul-factorization (pointwise).** The blue mirror of
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical`: the blue
interior bond multiple of the fused host weight, at a fixed blue physical leg, is the
sum over blue boundary configurations of the complement coupling coefficient times
the blue blocked-region weight.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (regionInteriorBondProd (G := G) A g.blue : ℂ) •
        regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
          (g.complPhysical σblue σcompl) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        g.threeBlockComplCoeff bdry σcompl bβ •
          regionBlockedWeight (G := G) A g.blue bβ σblue := by
  classical
  rw [g.regionBlockedWeight_complPhysical_eq bdry σblue σcompl]
  rw [smul_eq_mul, ← nsmul_eq_mul,
    ← g.threeBlockDoubleSum_eq_smul_single_blue bdry σblue σcompl,
    g.threeBlockDoubleSum_eq_complCoeff_sum_blue bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [smul_eq_mul, mul_comm]

open scoped Classical in
/-- **The core blue smul-factorization (as functions of `σblue`).** The blue
interior bond multiple of the fused host weight, read as a function of the blue
physical leg, is the complement-coupling combination of the blue blocked-region
weights.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_threeBlockBlueWeight_eq
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (regionInteriorBondProd (G := G) A g.blue : ℂ) •
        (fun σblue : RegionPhysicalConfig (V := V) (d := d) g.blue =>
          regionBlockedWeight (G := G) A (Finset.univ \ g.red) bdry
            (g.complPhysical σblue σcompl)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A g.blue,
        g.threeBlockComplCoeff bdry σcompl bβ •
          regionBlockedWeight (G := G) A g.blue bβ := by
  funext σblue
  rw [Pi.smul_apply, Finset.sum_apply,
    g.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [Pi.smul_apply]

end PEPS
end TNLean
