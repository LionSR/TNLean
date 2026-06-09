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

end PEPS
end TNLean
