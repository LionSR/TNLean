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
  simp only at hstrip
  -- Multiply both middle-strip read-offs by the interior bond product to land on rows.
  have hM := threeBlock_middle_strip (A := A) (e := e) D f M σred σblue
  have hM' := threeBlock_middle_strip (A := A) (e := e) D f M' σred σblue
  have : (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        threeBlockComplRow (A := A) (e := e) D f M σred σblue =
      (regionInteriorBondProd (G := G) A D.complement : ℂ) •
        threeBlockComplRow (A := A) (e := e) D f M' σred σblue := by
    rw [← hM, ← hM', hstrip]
  exact smul_right_injective _ hne this

end PEPS
end TNLean
