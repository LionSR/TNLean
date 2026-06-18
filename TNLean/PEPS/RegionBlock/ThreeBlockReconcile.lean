import TNLean.PEPS.RegionBlock.ThreeBlockResonate2

/-!
# Three-block resonate engine: the V=W reconcile

This file completes `TNLean.PEPS.RegionBlock.ThreeBlockResonate2` with the **V=W
reconcile** of the three-block resonate engine for the normal PEPS Fundamental
Theorem (arXiv:1804.04964, Section 3, Lemma `inj_isomorph`). The previous two files
landed:

* the core region-blocking associativity factorization and the **middle strip**
  `threeBlock_middle_strip` (stripping the complement block while keeping the red
  and blue residual configurations independent);
* the **blue endpoint inversion** `threeBlock_invert_blue` (reading off the
  complement coupling row `threeBlockComplCoeff`);
* the **red endpoint inversion** `threeBlock_invert_red` (reading off the region row
  `regionRegionRow`).

This file ports the edge-level reconcile `resonate_endpoint_coeff_reconcile`
(`TNLean.PEPS.InsertionRealization`) to the three blocks. The edge reconcile forces
the matrix read by inverting one endpoint to equal the matrix read by inverting the
other: the residual independence is forced because both inversions reference the
**same** stripped (middle-inverted) identity. Here both endpoint inversions reference
the same `threeBlockComplRow` (the complement-stripped row produced by the middle
strip), so the two read-offs are pinned to the common middle-stripped reference.

## Structure

* `threeBlock_middle_strip_descent` descends an equality of three-block inserted
  coefficients through the complement block: equal coefficients (for all three legs)
  give equal `threeBlockComplRow`s.
* `threeBlock_red_readoff_eq_of_coeff_eq` reads the red endpoint off both sides: equal
  three-block coefficients give equal region rows `regionRegionRow` at the fused
  blue/complement leg.
* `threeBlock_blue_readoff_eq_of_coeff_eq` reads the blue endpoint off both sides:
  equal complement-stripped fused host weights give equal complement coupling rows
  `threeBlockComplCoeff`.

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

/-! ### Step 1: descending an equality of three-block coefficients through the strip

If two matrices `M`, `M'` inserted on the crossing edge produce the same three-block
inserted coefficient at every triple of physical legs `σred`, `σblue`, `σcompl`, then
they produce the same complement-stripped row `threeBlockComplRow` at every pair of
residual legs `σred`, `σblue`. This is the structural core of the reconcile: the
complement (middle) block is inverted on the common coefficient, pinning the two rows
to the same middle-stripped reference. It is the region analogue of the
middle-inversion step of `resonate_middle_inverted`
(`TNLean.PEPS.InsertionRealization`), now applied to two coefficient families at once
rather than the resonate identity. -/

/-- **Descending a coefficient equality through the complement strip.** If two
inserted matrices give the same three-block inserted coefficient at every physical
configuration, then their complement-stripped rows `threeBlockComplRow` agree at every
pair of red and blue residual legs.

The complement interior bond multiple of each σcompl-function is the complement blocked
tensor map of `threeBlockComplRow` (`regionInteriorBondProd_smul_threeBlockInsertedCoeff_eq`),
and the complement block's chosen left inverse recovers the row
(`threeBlock_middle_strip`). Equal coefficients give equal σcompl-functions, hence equal
left-inverse read-offs, hence equal rows after dividing out the positive interior bond
product.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`--
`eq:inj_O->X_argument`, lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_middle_strip_descent
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (hcoeff : ∀ σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement,
      threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl =
        threeBlockInsertedCoeff (A := A) (e := e) D f M' σred σblue σcompl) :
    threeBlockComplRow (A := A) (e := e) D f M σred σblue =
      threeBlockComplRow (A := A) (e := e) D f M' σred σblue := by
  have hposC : 0 < regionInteriorBondProd (G := G) A D.complement :=
    regionInteriorBondProd_pos (G := G) A D.complement hpos
  have hne : (regionInteriorBondProd (G := G) A D.complement : ℂ) ≠ 0 := by
    exact_mod_cast hposC.ne'
  -- The σcompl-functions agree, so their middle-strip read-offs agree.
  have hfun : (fun σcompl => threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl) =
      (fun σcompl => threeBlockInsertedCoeff (A := A) (e := e) D f M' σred σblue σcompl) :=
    funext hcoeff
  have hstrip := congrArg
    (fun g => regionBlockedLeftInverse (G := G) A D.complement
      (regionBlockedTensorInjective_complement (A := A) (e := e) D) g) hfun
  -- Multiply both middle-strip read-offs by the interior bond product to land on rows.
  have hM := threeBlock_middle_strip (A := A) (e := e) D f M σred σblue
  have hM' := threeBlock_middle_strip (A := A) (e := e) D f M' σred σblue
  have : (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        threeBlockComplRow (A := A) (e := e) D f M σred σblue =
      (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        threeBlockComplRow (A := A) (e := e) D f M' σred σblue := by
    rw [← hM, ← hM', hstrip]
  exact smul_right_injective _ hne this

/-! ### Step 2: the two endpoint read-offs

Inverting the two endpoint blocks reads two row functions off the three-block
inserted coefficient. Equal three-block coefficients give equal read-offs at the
respective endpoints, the residual independence forced by the common reference.

The **red read-off** inverts the σred-function and recovers the region row
`regionRegionRow` at the fused blue/complement leg (`threeBlock_invert_red`). The
**blue read-off** inverts the σblue-function of the complement-stripped fused host
weight and recovers the complement coupling row `threeBlockComplCoeff`
(`threeBlock_invert_blue`). The two read-offs live in different index spaces — the red
row is indexed by the host residual `bdry` and reads the complement physical leg as a
free residual, the blue row is indexed by the blue boundary configuration and reads the
complement physical leg through the coupling — and the reconcile routes both through the
common complement-stripped reference. -/

/-- **The red endpoint read-off from a coefficient equality.** If two inserted matrices
give the same three-block inserted coefficient at every physical configuration, then the
red block's chosen left inverse reads off the same region row `regionRegionRow` at the
fused blue/complement physical leg.

The red left inverse of the σred-function recovers `regionRegionRow A red f M
(threeBlockComplPhysical D σblue σcompl)` (`threeBlock_invert_red`); equal σred-functions
give the same read-off.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_red_readoff_eq_of_coeff_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (hcoeff : ∀ σred : RegionPhysicalConfig (V := V) (d := d) D.red,
      threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl =
        threeBlockInsertedCoeff (A := A) (e := e) D f M' σred σblue σcompl) :
    regionRegionRow (G := G) A D.red f M
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) =
      regionRegionRow (G := G) A D.red f M'
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) := by
  rw [← threeBlock_invert_red (A := A) (e := e) D f M σblue σcompl,
    ← threeBlock_invert_red (A := A) (e := e) D f M' σblue σcompl]
  exact congrArg
    (fun g => regionBlockedLeftInverse (G := G) A D.red
      (regionBlockedTensorInjective_red (A := A) (e := e) D) g) (funext hcoeff)

/-- **The blue endpoint read-off as a function of the host residual.** The blue
block's chosen left inverse, applied to the σblue-function of the complement-stripped
fused host weight and scaled by the blue interior bond product, recovers the complement
coupling row `threeBlockComplCoeff` at every host residual configuration `bdry`. This
is `threeBlock_invert_blue` packaged as the residual-quantified read-off the reconcile
references. The read-off is the same for any inserted matrix: the fused host weight is
`M`-independent, so the blue endpoint reads the complement physical leg off through the
coupling alone, providing the common reference frame against which the red read-off is
reconciled.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_blue_readoff
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red))
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement) :
    (regionInteriorBondProd (G := G) A D.blue : ℂ) •
        regionBlockedLeftInverse (G := G) A D.blue
          (regionBlockedTensorInjective_blue (A := A) (e := e) D)
          (fun σblue => regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
      fun bβ => threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ :=
  threeBlock_invert_blue (A := A) (e := e) D bdry σcompl

/-! ### The fused-leg bridge to the two-block region-inserted coefficient

The fused blue/complement physical leg `threeBlockComplPhysical D σblue σcompl`
ranges over **every** complement physical leg on `univ \ red` as `σblue`, `σcompl`
vary, because `univ \ red = blue ⊔ complement` (`sdiff_red_eq_blue_union_complement`).
Splitting a complement leg `τ` along this cover and reading the two halves recovers
`τ`, so the three-block inserted coefficient quantified over the three legs `σred`,
`σblue`, `σcompl` carries exactly the same information as the two-block
`regionInsertedCoeff` of the red region quantified over `σred`, `τ`. This bridges the
three-block engine to the block-frame coefficient transfer the per-edge gauge consumes
(`exists_regionEdgeGauge_of_coeffTransfer`,
`TNLean.PEPS.RegionBlock.RegionReconcile`). -/

/-- The blue half of a complement physical leg: read a complement leg `τ` on
`univ \ red` at its blue vertices. -/
def threeBlockBlueSplit
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)) :
    RegionPhysicalConfig (V := V) (d := d) D.blue :=
  fun w => τ ⟨w.1, by
    rw [sdiff_red_eq_blue_union_complement (A := A) (e := e) D]
    exact Finset.mem_union_left _ w.2⟩

/-- The complement half of a complement physical leg: read a complement leg `τ` on
`univ \ red` at its complement vertices. -/
def threeBlockComplSplit
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)) :
    RegionPhysicalConfig (V := V) (d := d) D.complement :=
  fun w => τ ⟨w.1, by
    rw [sdiff_red_eq_blue_union_complement (A := A) (e := e) D]
    exact Finset.mem_union_right _ w.2⟩

/-- **The fused leg recovers a split complement leg.** Fusing the blue and complement
halves of a complement physical leg `τ` recovers `τ`. The fused leg reads a blue vertex
off the blue half and a complement vertex off the complement half; on a vertex of
`univ \ red` (which lies in `blue` or `complement`) both halves read `τ` at that vertex.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockComplPhysical_split
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)) :
    threeBlockComplPhysical (A := A) (e := e) D
        (threeBlockBlueSplit (A := A) (e := e) D τ)
        (threeBlockComplSplit (A := A) (e := e) D τ) = τ := by
  funext w
  by_cases hb : w.1 ∈ D.blue
  · rw [threeBlockComplPhysical_apply_blue (A := A) (e := e) D _ _ w hb,
      threeBlockBlueSplit]
  · have hwnotred : w.1 ∉ D.red := (Finset.mem_sdiff.mp w.2).2
    have hc : w.1 ∈ D.complement := by
      have hcover : w.1 ∈ D.red ∪ D.blue ∪ D.complement := by
        rw [D.cover_univ]; exact Finset.mem_univ _
      rcases Finset.mem_union.mp hcover with hrb | hc
      · rcases Finset.mem_union.mp hrb with hr | hbl
        · exact absurd hr hwnotred
        · exact absurd hbl hb
      · exact hc
    rw [threeBlockComplPhysical_apply_not_blue (A := A) (e := e) D _ _ w hb hc,
      threeBlockComplSplit]

/-- **The three-block coefficient is the two-block region-inserted coefficient at the
split leg.** Reading a complement physical leg `τ` of the red region through the
blue/complement split, the two-block region-inserted coefficient of the red region at
`σred`, `τ` is the three-block inserted coefficient at `σred` and the two split halves
of `τ`. This is the bridge `threeBlockInsertedCoeff_eq_regionInsertedCoeff` with the
fused leg recovered from its split (`threeBlockComplPhysical_split`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_threeBlockInsertedCoeff_split
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)) :
    regionInsertedCoeff (G := G) A D.red f M σred τ =
      threeBlockInsertedCoeff (A := A) (e := e) D f M σred
        (threeBlockBlueSplit (A := A) (e := e) D τ)
        (threeBlockComplSplit (A := A) (e := e) D τ) := by
  rw [threeBlockInsertedCoeff_eq_regionInsertedCoeff,
    threeBlockComplPhysical_split (A := A) (e := e) D τ]

/-- **The three-block coefficient transfer is the two-block coefficient transfer
(single tensor).** Two inserted matrices `M`, `M'` on the red crossing edge give the
same three-block inserted coefficient at every triple of physical legs if and only if
they give the same two-block region-inserted coefficient of the red region at every
region and complement leg. The forward direction splits a complement leg along the
blue/complement cover; the reverse direction fuses the blue and complement legs through
the bridge `threeBlockInsertedCoeff_eq_regionInsertedCoeff`.

This identifies the three-block engine's resonate hypothesis with the two-block
inserted-coefficient frame `regionInsertedCoeff` of the red region, the frame the
block-frame coefficient transfer `exists_regionEdgeGauge_of_coeffTransfer`
(`TNLean.PEPS.RegionBlock.RegionReconcile`) consumes, with no single-vertex
injectivity.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlockInsertedCoeff_eq_iff_regionInsertedCoeff_eq
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    (∀ (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
        (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
        (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement),
      threeBlockInsertedCoeff (A := A) (e := e) D f M σred σblue σcompl =
        threeBlockInsertedCoeff (A := A) (e := e) D f M' σred σblue σcompl) ↔
      (∀ (σ : RegionPhysicalConfig (V := V) (d := d) D.red)
          (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)),
        regionInsertedCoeff (G := G) A D.red f M σ τ =
          regionInsertedCoeff (G := G) A D.red f M' σ τ) := by
  constructor
  · intro h σ τ
    rw [regionInsertedCoeff_eq_threeBlockInsertedCoeff_split (A := A) (e := e) D f M σ τ,
      regionInsertedCoeff_eq_threeBlockInsertedCoeff_split (A := A) (e := e) D f M' σ τ]
    exact h σ _ _
  · intro h σred σblue σcompl
    rw [threeBlockInsertedCoeff_eq_regionInsertedCoeff,
      threeBlockInsertedCoeff_eq_regionInsertedCoeff]
    exact h σred (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)

/-! ### The three-block reconcile

Packaging the middle strip and the two endpoint read-offs into the single
residual-independence statement of the reconcile. A two-block coefficient equality of
the red region (the frame the bridge `threeBlockInsertedCoeff_eq_iff_regionInsertedCoeff_eq`
identifies with the three-block resonate hypothesis) forces, simultaneously,

* the complement-stripped rows `threeBlockComplRow` to agree at every red and blue
  residual (the middle strip descent), and
* the region rows `regionRegionRow` to agree at every fused blue/complement leg (the red
  endpoint read-off).

Both read-offs are pinned to the same middle-stripped reference, the residual
independence the edge reconcile `resonate_endpoint_coeff_reconcile`
(`TNLean.PEPS.InsertionRealization`) supplies at edge granularity. -/

/-- **The three-block reconcile.** A two-block region-inserted coefficient equality of
the red region forces both the complement-stripped rows `threeBlockComplRow` and the
region rows `regionRegionRow` (at the fused blue/complement leg) of the two inserted
matrices to agree, at every residual configuration.

The hypothesis is read three ways: through the bridge
`threeBlockInsertedCoeff_eq_iff_regionInsertedCoeff_eq` it is the three-block resonate
equality, which the middle strip descends to equal complement-stripped rows
(`threeBlock_middle_strip_descent`) and the red endpoint reads off to equal region rows
(`threeBlock_red_readoff_eq_of_coeff_eq`). This is the residual-independent reconcile of
the two endpoint read-offs, the region port of the edge step `V=W`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:inj_O->X_argument`,
lines 355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem threeBlock_reconcile
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) D.red f})
    (M M' : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (hpos : ∀ g : Edge G, 0 < A.bondDim g)
    (hcoeff : ∀ (σ : RegionPhysicalConfig (V := V) (d := d) D.red)
        (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ D.red)),
      regionInsertedCoeff (G := G) A D.red f M σ τ =
        regionInsertedCoeff (G := G) A D.red f M' σ τ) :
    (∀ (σred : RegionPhysicalConfig (V := V) (d := d) D.red)
        (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue),
      threeBlockComplRow (A := A) (e := e) D f M σred σblue =
        threeBlockComplRow (A := A) (e := e) D f M' σred σblue) ∧
      (∀ (σblue : RegionPhysicalConfig (V := V) (d := d) D.blue)
          (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement),
        regionRegionRow (G := G) A D.red f M
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) =
          regionRegionRow (G := G) A D.red f M'
            (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) := by
  have hthree := (threeBlockInsertedCoeff_eq_iff_regionInsertedCoeff_eq
    (A := A) (e := e) D f M M').mpr hcoeff
  refine ⟨fun σred σblue => ?_, fun σblue σcompl => ?_⟩
  · exact threeBlock_middle_strip_descent (A := A) (e := e) D f M M' σred σblue hpos
      (fun σcompl => hthree σred σblue σcompl)
  · exact threeBlock_red_readoff_eq_of_coeff_eq (A := A) (e := e) D f M M' σblue σcompl
      (fun σred => hthree σred σblue σcompl)

end PEPS
end TNLean
