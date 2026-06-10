import TNLean.PEPS.RegionBlock.ThreeBlockResonate

/-!
# Three-block resonate engine: the middle strip and the endpoint inversions

This file continues `TNLean.PEPS.RegionBlock.ThreeBlockResonate`, building the
**middle strip** and the **two endpoint inversions** of the three-block resonate
engine for the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3,
Lemma `inj_isomorph`).

The previous file landed the core region-blocking associativity factorization:
the fused host weight `regionBlockedWeight A (univ \ red) bdry
(threeBlockComplPhysical D σblue σcompl)`, read as a function of the complement
physical leg, lies in the range of the complement block's blocked-region tensor
map (`regionBlockedWeight_threeBlockComplPhysical_mem_range`), with the explicit
complement-interior-bond multiple
`regionInteriorBondProd_smul_threeBlockComplWeight_eq`.

This file uses that factorization to:

* **strip the complement (middle) block** from the three-block inserted
  coefficient, reading it off through the complement block's chosen left inverse
  (`threeBlock_middle_strip`). This is the region analogue of
  `resonate_middle_inverted` (`TNLean.PEPS.InsertionRealization`): where the edge
  engine inverts the blocked middle tensor, the three-block engine inverts the
  complement block, keeping the red and blue residual configurations independent.

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

/-! ### The complement-block row of the three-block inserted coefficient

The three-block inserted coefficient `threeBlockInsertedCoeff D f M σred σblue
σcompl`, read as a function of the complement physical leg `σcompl`, lies in the
range of the complement block's blocked-region tensor map. The explicit preimage
(scaled by the complement interior bond product) is the **complement row**: the
host complement row of the two-block backbone, coupled through the blue block's
`threeBlockBlueCoeff`. -/

open scoped Classical in
/-- **The complement-block row of the three-block inserted coefficient.** For a
complement boundary configuration `bc'`, the host complement row of the two-block
backbone (`regionComplementRow` of the red region), coupled to `bc'` through the
blue block's `threeBlockBlueCoeff`.

This is the explicit preimage, scaled by the complement interior bond product, of
the σcompl-function of `threeBlockInsertedCoeff` under the complement block's
blocked-region tensor map (`regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def threeBlockComplRow
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue) :
    RegionBoundaryConfig (G := G) A D.complement → ℂ :=
  fun bc' =>
    ∑ w : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      regionComplementRow (G := G) A D.red f M σred w *
        threeBlockBlueCoeff (A := A) (e := e) D w σblue bc'

open scoped Classical in
/-- **The three-block inserted coefficient through the complement blocked map.** The
complement interior bond multiple of the three-block inserted coefficient, read as a
function of the complement physical leg, is the complement block's blocked-region
tensor map applied to the complement-block row `threeBlockComplRow`.

The three-block inserted coefficient is the two-block `regionInsertedCoeff` of the
red region against its set complement, with the blue and complement legs fused
(`threeBlockInsertedCoeff_eq_regionInsertedCoeff`); the host complement reading
(`regionInsertedCoeff_eq_complement_blockedMap`) writes it as the host complement
row contracted against the fused host weights. Multiplying by the complement interior
bond product and applying the core factorization
`regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical` to each
fused host weight replaces it by the blue-coupled complement blocked weights, which
reassemble into the complement blocked tensor map of `threeBlockComplRow`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue) :
    (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        (fun σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement =>
          threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl) =
      regionBlockedTensorMap (G := G) A D.complement
        (threeBlockComplRow (A := A) (e := e) D f M σred σblue) := by
  classical
  funext σcompl
  rw [Pi.smul_apply]
  -- The complement-blocked-map reading of the fused host inserted coefficient.
  rw [threeBlockInsertedCoeff_eq_regionInsertedCoeff,
    regionInsertedCoeff_eq_complement_blockedMap (G := G) A D.red f M σred,
    regionBlockedTensorMap_apply]
  -- Distribute the bond multiple across the host complement row sum, then apply the
  -- core factorization to each fused host weight.
  rw [Finset.smul_sum]
  rw [regionBlockedTensorMap_apply]
  simp only [threeBlockComplRow]
  -- Both sides are sums; relate them by swapping the `w`/`bc'` order on the right.
  rw [show (∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
        (∑ w : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            regionComplementRow (G := G) A D.red f M σred w *
              threeBlockBlueCoeff (A := A) (e := e) D w σblue bc') •
          regionBlockedWeight (G := G) A D.complement bc' σcompl) =
      ∑ w : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        ∑ bc' : RegionBoundaryConfig (G := G) A D.complement,
          (regionComplementRow (G := G) A D.red f M σred w *
              threeBlockBlueCoeff (A := A) (e := e) D w σblue bc') •
            regionBlockedWeight (G := G) A D.complement bc' σcompl from by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun bc' _ => ?_)
      rw [Finset.sum_smul]]
  refine Finset.sum_congr rfl (fun w _ => ?_)
  -- On each host complement configuration, the scaled fused host weight is the
  -- blue-coupled complement blocked weights.
  rw [smul_comm,
    regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical
      (A := A) (e := e) D w σblue σcompl,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [smul_smul, mul_comm, ← smul_smul, smul_eq_mul]

/-! ### The middle strip

Reading the σcompl-function of the three-block inserted coefficient through the
complement block's chosen left inverse strips the complement (middle) block,
recovering the complement-block row `threeBlockComplRow`, scaled by the complement
interior bond product. This is the region analogue of `resonate_middle_inverted`
(`TNLean.PEPS.InsertionRealization`): where the edge engine inverts the blocked
middle tensor to strip the middle block off the resonate identity, the three-block
engine inverts the complement block. The red and blue residual configurations
(`σred`, `σblue`) are kept quantified independently — the structural step the
two-block frame cannot state. -/

open scoped Classical in
/-- **The three-block middle strip.** The complement block's chosen left inverse,
applied to the three-block inserted coefficient read as a function of the complement
physical leg and scaled by the complement interior bond product, recovers the
complement-block row `threeBlockComplRow`. This strips the complement (middle) block
while keeping the red and blue residual physical legs `σred`, `σblue` independent.

The complement interior bond multiple of the σcompl-function is the complement
blocked tensor map of `threeBlockComplRow`
(`regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq`), and the complement
block's chosen left inverse recovers the row
(`regionBlockedLeftInverse_apply_regionBlockedTensorMap`); the bond multiple commutes
out through the linearity of the left inverse.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`--
`eq:inj_O->X_argument`, lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_middle_strip
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue) :
    (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        regionBlockedLeftInverse (G := G) A D.complement
          (regionBlockedTensorInjective_complement (A := A) (e := e) D)
          (fun σcompl => threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl) =
      threeBlockComplRow (A := A) (e := e) D f M σred σblue := by
  rw [← map_smul,
    regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq (A := A) (e := e) D f M σred σblue,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### The blue-block factorization of the fused host weight

The fused host weight, read as a function of the *blue* physical leg `σblue` (with
the complement leg `σcompl` fixed), lies in the range of the blue block's
blocked-region tensor map. This is the blue-block mirror of the core factorization
`regionBlockedWeight_threeBlockComplPhysical_mem_range`: the same host weight, now
inverted along the blue block rather than the complement block, with the complement
block supplying the coupling coefficient `threeBlockComplCoeff`.

The development mirrors the complement collapse of `ThreeBlockResonate.lean` with the
roles of the blue and complement blocks exchanged: the merge is taken along the blue
block, the coupling runs through the complement vertex products, and the fiber
multiplicity collapses to the blue interior bond product. -/

/-- The complement vertex product reads a global configuration only through the
complement-incident edges, so it agrees with the configuration merged along the blue
block, provided the two configurations agree on the blue boundary. This is the blue
mirror of `blueProd_eq_regionMerge_complement`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem complProd_eq_regionMerge_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A D.blue p.1 =
      regionBoundaryLabel (G := G) A D.blue p.2) :
    (∏ w : {w : V // w ∈ D.complement}, A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∏ w : {w : V // w ∈ D.complement},
        A.component w.1 (fun ie => regionMerge (G := G) A D.blue p ie.1) (σcompl w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  -- `ie` is incident to `w ∈ complement`, so `w ∉ blue`.
  have hwcompl : w.1 ∈ D.complement := w.2
  have hwnotblue : w.1 ∉ D.blue := fun hb =>
    (Finset.disjoint_left.mp D.blue_disjoint_complement) hb hwcompl
  have hwinc : ie.1.1.1 = w.1 ∨ ie.1.1.2 = w.1 := ie.2
  by_cases hinc : IsRegionIncidentEdge (G := G) D.blue ie.1
  · -- `ie` is blue-incident and touches `w ∉ blue`: a boundary edge of the blue block,
    -- where `p.1` and `p.2` agree.
    have hbdry : IsRegionBoundaryEdge (G := G) D.blue ie.1 := by
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
theorem hostLabel_p2_eq_hostLabel_regionMerge_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A D.blue p.1 =
      regionBoundaryLabel (G := G) A D.blue p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 =
      regionBoundaryLabel (G := G) A (Finset.univ \ D.red)
        (regionMerge (G := G) A D.blue p) := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : IsRegionIncidentEdge (G := G) D.blue f.1
  · -- A blue-incident host boundary edge is a boundary edge of the blue block.
    have hbdry : IsRegionBoundaryEdge (G := G) D.blue f.1 := by
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · have h2red : f.1.1.2 ∈ D.red := by
          have := h2nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h2notblue : f.1.1.2 ∉ D.blue := fun hb =>
          (Finset.disjoint_left.mp D.red_disjoint_blue) h2red hb
        rcases hinc with hb1 | hb2
        · refine Or.inl ⟨hb1, h2notblue⟩
        · exact absurd hb2 h2notblue
      · have h1red : f.1.1.1 ∈ D.red := by
          have := h1nothost; rw [Finset.mem_sdiff] at this; push_neg at this
          exact this (Finset.mem_univ _)
        have h1notblue : f.1.1.1 ∉ D.blue := fun hb =>
          (Finset.disjoint_left.mp D.red_disjoint_blue) h1red hb
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
theorem threeBlockBlueFiber_card
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
          (regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2 ∧
            regionMerge (G := G) A D.blue p = η))).card =
      if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
        regionInteriorBondProd (G := G) A D.blue else 0 := by
  classical
  by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry
  · rw [if_pos hcompat]
    rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            (regionBoundaryLabel (G := G) A D.blue p.1 =
                regionBoundaryLabel (G := G) A D.blue p.2 ∧
              regionMerge (G := G) A D.blue p = η))) =
        Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
          (regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2 ∧
            regionMerge (G := G) A D.blue p = η)) from ?_]
    · exact regionFiber_card (G := G) A D.blue η
    · refine Finset.filter_congr (fun p _ => ?_)
      constructor
      · rintro ⟨_, hagree, hmerge⟩; exact ⟨hagree, hmerge⟩
      · rintro ⟨hagree, hmerge⟩
        refine ⟨?_, hagree, hmerge⟩
        rw [hostLabel_p2_eq_hostLabel_regionMerge_blue (A := A) (e := e) D p hagree,
          hmerge, hcompat]
  · rw [if_neg hcompat]
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro p _ ⟨hhost, hagree, hmerge⟩
    apply hcompat
    rw [← hmerge,
      ← hostLabel_p2_eq_hostLabel_regionMerge_blue (A := A) (e := e) D p hagree, hhost]

open scoped Classical in
/-- **The host-relative blue merge collapse.** The blue mirror of
`threeBlockDoubleSum_eq_smul_single`: the blue-boundary-agreeing double sum of the
blue vertex product against the complement vertex product, with the complement side
constrained to host label `bdry`, collapses to the blue interior bond product times
the single constrained sum.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockDoubleSum_eq_smul_single_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2),
      (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      regionInteriorBondProd (G := G) A D.blue •
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
          (∏ w : {w : V // w ∈ D.blue},
              A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
            ∏ w : {w : V // w ∈ D.complement},
              A.component w.1 (fun ie => ζ ie.1) (σcompl w) := by
  classical
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2),
      (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2),
        (∏ w : {w : V // w ∈ D.blue},
            A.component w.1 (fun ie => regionMerge (G := G) A D.blue p ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1
              (fun ie => regionMerge (G := G) A D.blue p ie.1) (σcompl w) from ?_]
  · rw [← Finset.sum_fiberwise (Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2))
      (fun p => regionMerge (G := G) A D.blue p)
      (fun p =>
        (∏ w : {w : V // w ∈ D.blue},
            A.component w.1 (fun ie => regionMerge (G := G) A D.blue p ie.1) (σblue w)) *
          ∏ w : {w : V // w ∈ D.complement},
            A.component w.1
              (fun ie => regionMerge (G := G) A D.blue p ie.1) (σcompl w))]
    rw [show (regionInteriorBondProd (G := G) A D.blue •
          ∑ ζ ∈ Finset.univ.filter
              (fun ζ : VirtualConfig A =>
                regionBoundaryLabel (G := G) A (Finset.univ \ D.red) ζ = bdry),
            (∏ w : {w : V // w ∈ D.blue},
                A.component w.1 (fun ie => ζ ie.1) (σblue w)) *
              ∏ w : {w : V // w ∈ D.complement},
                A.component w.1 (fun ie => ζ ie.1) (σcompl w)) =
        ∑ η : VirtualConfig A,
          regionInteriorBondProd (G := G) A D.blue •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
              (∏ w : {w : V // w ∈ D.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)) *
                ∏ w : {w : V // w ∈ D.complement},
                  A.component w.1 (fun ie => η ie.1) (σcompl w)
              else 0) from ?_]
    · refine Finset.sum_congr rfl (fun η _ => ?_)
      rw [Finset.filter_filter,
        Finset.sum_congr rfl (g := fun _ =>
            (∏ w : {w : V // w ∈ D.blue},
                A.component w.1 (fun ie => η ie.1) (σblue w)) *
              ∏ w : {w : V // w ∈ D.complement},
                A.component w.1 (fun ie => η ie.1) (σcompl w))
          (fun p hp => by rw [Finset.mem_filter] at hp; rw [hp.2.2]),
        Finset.sum_const]
      rw [show (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            (regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
                regionBoundaryLabel (G := G) A D.blue p.1 =
                  regionBoundaryLabel (G := G) A D.blue p.2) ∧
              regionMerge (G := G) A D.blue p = η)) =
          Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
              (regionBoundaryLabel (G := G) A D.blue p.1 =
                  regionBoundaryLabel (G := G) A D.blue p.2 ∧
                regionMerge (G := G) A D.blue p = η)) from by
          refine Finset.filter_congr (fun p _ => ?_); tauto,
        threeBlockBlueFiber_card (A := A) (e := e) D bdry η]
      by_cases hcompat : regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry
      · rw [if_pos hcompat, if_pos hcompat]
      · rw [if_neg hcompat, if_neg hcompat, zero_smul, smul_zero]
    · rw [Finset.smul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ
          (fun η : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry)]
      rw [show (∑ η ∈ Finset.univ.filter
            (fun η : VirtualConfig A =>
              ¬ regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry),
          regionInteriorBondProd (G := G) A D.blue •
            (if regionBoundaryLabel (G := G) A (Finset.univ \ D.red) η = bdry then
              (∏ w : {w : V // w ∈ D.blue},
                  A.component w.1 (fun ie => η ie.1) (σblue w)) *
                ∏ w : {w : V // w ∈ D.complement},
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
    rw [regionProd_eq_merge (G := G) A D.blue σblue p,
      complProd_eq_regionMerge_blue (A := A) (e := e) D σcompl p hp.2.2]

open scoped Classical in
/-- **The complement coupling coefficient.** The blue mirror of
`threeBlockBlueCoeff`: the complement vertex product summed over all global
configurations whose host label is `bdry` and whose blue boundary label is the
prescribed `bβ`. This is the complement-block contraction coupled to the blue
boundary configuration through the blue/complement crossing bonds.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def threeBlockComplCoeff
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (bβ : RegionBoundaryConfig (G := G) A D.blue) : ℂ :=
  ∑ q ∈ Finset.univ.filter
      (fun q : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) q = bdry ∧
          regionBoundaryLabel (G := G) A D.blue q = bβ),
    ∏ w : {w : V // w ∈ D.complement}, A.component w.1 (fun ie => q ie.1) (σcompl w)

open scoped Classical in
/-- **The host-relative blue decoupling.** The blue mirror of
`threeBlockDoubleSum_eq_blueCoeff_sum`: the blue-boundary-agreeing double sum of the
blue vertex product against the host-constrained complement vertex product decouples,
grouped by the blue boundary configuration `bβ`, into the blue blocked-region weight
at `bβ` against the complement coupling coefficient.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockDoubleSum_eq_complCoeff_sum_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
            regionBoundaryLabel (G := G) A D.blue p.1 =
              regionBoundaryLabel (G := G) A D.blue p.2),
      (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ D.complement},
          A.component w.1 (fun ie => p.2 ie.1) (σcompl w)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A D.blue,
        regionBlockedWeight (G := G) A D.blue bβ σblue *
          threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun p : VirtualConfig A × VirtualConfig A =>
        regionBoundaryLabel (G := G) A (Finset.univ \ D.red) p.2 = bdry ∧
          regionBoundaryLabel (G := G) A D.blue p.1 =
            regionBoundaryLabel (G := G) A D.blue p.2))
    (fun p => regionBoundaryLabel (G := G) A D.blue p.1)
    (fun p =>
      (∏ w : {w : V // w ∈ D.blue},
          A.component w.1 (fun ie => p.1 ie.1) (σblue w)) *
        ∏ w : {w : V // w ∈ D.complement},
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
theorem regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
          (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) =
      ∑ bβ : RegionBoundaryConfig (G := G) A D.blue,
        threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ •
          regionBlockedWeight (G := G) A D.blue bβ σblue := by
  classical
  rw [regionBlockedWeight_threeBlockComplPhysical_eq (A := A) (e := e) D bdry σblue σcompl]
  rw [smul_eq_mul, ← nsmul_eq_mul,
    ← threeBlockDoubleSum_eq_smul_single_blue (A := A) (e := e) D bdry σblue σcompl,
    threeBlockDoubleSum_eq_complCoeff_sum_blue (A := A) (e := e) D bdry σblue σcompl]
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
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        (fun σblue : RegionPhysicalConfig (V := V) (d := d) D.blue =>
          regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      ∑ bβ : RegionBoundaryConfig (G := G) A D.blue,
        threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ •
          regionBlockedWeight (G := G) A D.blue bβ := by
  funext σblue
  rw [Pi.smul_apply, Finset.sum_apply,
    regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
      (A := A) (e := e) D bdry σblue σcompl]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [Pi.smul_apply]

/-- **The blue-block factorization of the fused host weight.** The fused host weight,
read as a function of the blue physical leg `σblue` (with the complement leg fixed),
lies in the range of the blue block's blocked-region tensor map. This is the
blue-block mirror of `regionBlockedWeight_threeBlockComplPhysical_mem_range`,
inverting along the blue block instead of the complement block.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_threeBlockBluePhysical_mem_range
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f) :
    (fun σblue : RegionPhysicalConfig (V := V) (d := d) D.blue =>
        regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
          (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) ∈
      LinearMap.range (regionBlockedTensorMap (G := G) A D.blue) := by
  classical
  rw [range_regionBlockedTensorMap_eq_span (G := G) A D.blue]
  have hne : (regionInteriorBondProd (G := G) A D.blue : ℂ) ≠ 0 := by
    have hpos' : 0 < regionInteriorBondProd (G := G) A D.blue :=
      regionInteriorBondProd_pos (G := G) A D.blue hpos
    exact_mod_cast hpos'.ne'
  rw [← Submodule.smul_mem_iff _ hne,
    regionInteriorBondProd_smul_threeBlockBlueWeight_eq (A := A) (e := e) D bdry σcompl]
  refine Submodule.sum_mem _ (fun bβ _ => ?_)
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨bβ, rfl⟩)

/-! ### The blue endpoint inversion

Reading the σblue-function of the fused host weight through the blue block's chosen
left inverse reads the complement coupling coefficient `threeBlockComplCoeff` off as
the blue inversion, at a fixed complement physical leg. This is the region analogue
of `resonate_invert_right_endpoint` (`TNLean.PEPS.InsertionRealization`) and the
single-block analogue of `transferCoeff_column_eq_regionBlockedLeftInverse_vSideRow`
(`TNLean.PEPS.RegionBlock.Recovery11`), now at the blue endpoint block. -/

open scoped Classical in
/-- **The fused host weight through the blue blocked map.** The blue interior bond
multiple of the σblue-function of the fused host weight is the blue blocked tensor
map applied to the complement coupling row `fun bβ => threeBlockComplCoeff D bdry
σcompl bβ`. This restates `regionInteriorBondProd_smul_threeBlockBlueWeight_eq` in
blocked-tensor-map form, ready for the blue left inverse. -/
theorem regionInteriorBondProd_smul_threeBlockBlueWeight_eq_blockedMap
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        (fun σblue : RegionPhysicalConfig (V := V) (d := d) D.blue =>
          regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      regionBlockedTensorMap (G := G) A D.blue
        (fun bβ => threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ) := by
  classical
  rw [regionInteriorBondProd_smul_threeBlockBlueWeight_eq (A := A) (e := e) D bdry σcompl]
  funext σblue
  rw [Finset.sum_apply, regionBlockedTensorMap_apply]
  refine Finset.sum_congr rfl (fun bβ _ => ?_)
  rw [Pi.smul_apply]

/-- **The blue endpoint inversion.** The blue block's chosen left inverse, applied to
the σblue-function of the fused host weight and scaled by the blue interior bond
product, recovers the complement coupling row `fun bβ => threeBlockComplCoeff D bdry
σcompl bβ`. This reads the complement-side contraction off through the blue block,
keeping the complement physical leg `σcompl` and host residual `bdry` fixed.

The blue interior bond multiple of the σblue-function is the blue blocked tensor map
of the complement coupling row
(`regionInteriorBondProd_smul_threeBlockBlueWeight_eq_blockedMap`), and the blue
block's chosen left inverse recovers the row
(`regionBlockedLeftInverse_apply_regionBlockedTensorMap`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_invert_blue
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        regionBlockedLeftInverse (G := G) A D.blue
          (regionBlockedTensorInjective_blue (A := A) (e := e) D)
          (fun σblue => regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      fun bβ => threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ := by
  rw [← map_smul,
    regionInteriorBondProd_smul_threeBlockBlueWeight_eq_blockedMap (A := A) (e := e) D bdry σcompl,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### The red endpoint inversion

Reading the σred-function of the three-block inserted coefficient through the red
block's chosen left inverse reads the blue-side operator off as a bond-`f` matrix
action, at a fixed fused blue/complement physical leg. This is the region analogue of
`resonate_invert_left_endpoint` (`TNLean.PEPS.InsertionRealization`), at the red
endpoint block. Unlike the blue inversion, the red block is the first block of the
two-block backbone, so no fiber collapse is needed: the σred-function factors through
the red blocked tensor map directly (`regionInsertedCoeff_eq_region_blockedMap`). -/

open scoped Classical in
/-- **The red endpoint inversion.** The red block's chosen left inverse, applied to
the σred-function of the three-block inserted coefficient, recovers the region row
function `regionRegionRow` at the fused blue/complement physical leg. This reads the
blue-side operator off as a bond-`f` matrix action against the fused host weight, at a
fixed blue and complement physical leg (`σblue`, `σcompl`).

The three-block inserted coefficient is the two-block `regionInsertedCoeff` of the red
region against its set complement, with the blue and complement legs fused
(`threeBlockInsertedCoeff_eq_regionInsertedCoeff`); the σred-function factors through
the red blocked tensor map of the region row (`regionInsertedCoeff_eq_region_blockedMap`),
and the red block's chosen left inverse recovers it
(`regionBlockedLeftInverse_region_regionInsertedCoeff`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_invert_red
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    regionBlockedLeftInverse (G := G) A D.red
        (regionBlockedTensorInjective_red (A := A) (e := e) D)
        (fun σred => threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl) =
      regionRegionRow (G := G) A D.red f M
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) := by
  simp only [threeBlockInsertedCoeff_eq_regionInsertedCoeff]
  exact regionBlockedLeftInverse_region_regionInsertedCoeff (G := G) A D.red
    (regionBlockedTensorInjective_red (A := A) (e := e) D) f M
    (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)

end PEPS
end TNLean
