import TNLean.PEPS.RegionBlock.Recovery6

/-!
# Region physical-to-virtual recovery: the region resonate identity and endpoint pin

This file assembles the two endpoint readings of the region-inserted coefficient
(the in-region endpoint reading of `TNLean.PEPS.RegionBlock.Recovery2` and the
out-of-region endpoint reading of `TNLean.PEPS.RegionBlock.Recovery6`) into the
**region resonate identity**: the two endpoint operators built from the first
tensor `A`, applied to the *second* tensor `B`'s closed state vectors, agree at the
endpoint physical legs. This is the region analogue of the resonate identity
`hEqB` that `edgeRightInsertionOp_realizes_edgeTransferMatrix`
(`TNLean.PEPS.InsertionAlgebra`) derives at the edge level and feeds into
`physical_to_virtual_insertion` (`TNLean.PEPS.InsertionRealization`).

Both endpoint readings collapse, across `SameState`, to the same
`SameState`-invariant closed-state realization sum
(`regionInsertionOp_regionStateVec_pin`, `TNLean.PEPS.RegionBlock.Recovery3`), so
the two readings agree. The in-region endpoint operator carries `M` through the
in-region endpoint `v`; the out-of-region endpoint operator carries `M` through
the out-of-region endpoint `vout`, which is the in-region endpoint of `f` viewed as
a boundary edge of the set complement `univ \ R`
(`regionBoundaryEdgeInVertex_compl_eq_outVertex`).

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The out-of-region-endpoint pin

The in-region endpoint pin `regionInsertionOp_regionStateVec_pin` applied to the
set complement `univ \ R` of `R`, with the inserted matrix transposed and the
region/complement physical arguments exchanged, recovers the first tensor's
region-inserted coefficient through the out-of-region endpoint `vout`. The cast
identity `regionInsertedCoeff_eq_compl` (`TNLean.PEPS.RegionBlock.Recovery6`) turns
the complement-side coefficient back into the original region-inserted coefficient. -/

/-- **The out-of-region-endpoint pin.** The out-of-region endpoint operator of the
first tensor from `M`, applied to the *second* tensor's closed state vector on the
set complement `univ \ R` and evaluated at the out-of-region endpoint physical leg,
recovers the first tensor's region-inserted coefficient of `M`, up to the interior
bond product over the non-boundary edges of `univ \ R`.

This is `regionInsertionOp_regionStateVec_pin` instanced at the set complement
`univ \ R`, with the inserted matrix transposed and the region/complement physical
arguments exchanged, read back through the complement-side cast identity
`regionInsertedCoeff_eq_compl`. Together with the in-region-endpoint pin it is the
doubled boundary-edge reading the region resonate identity equates.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertionOp_regionStateVec_pin_compl (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInteriorBondProd (G := G) A (Finset.univ \ R) •
        (regionInsertionOp (G := G) A (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f) hvAout M.transpose.transpose
          (regionStateVec (G := G) B (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f) τ
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)))
          (τ ⟨regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f),
            regionBoundaryEdgeInVertex_mem (G := G) (Finset.univ \ R)
              (regionBoundaryEdgeToCompl (G := G) R f)⟩) =
      regionInsertedCoeff (G := G) A R f M σ τ := by
  rw [regionInsertedCoeff_eq_compl A R f M σ τ]
  exact regionInsertionOp_regionStateVec_pin A B (Finset.univ \ R)
    (regionBoundaryEdgeToCompl (G := G) R f) hvAout hAB M.transpose τ
    (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)

/-! ### The region resonate identity

Equating the in-region-endpoint pin and the out-of-region-endpoint pin gives the
**region resonate identity**: the in-region and out-of-region endpoint operators of
the first tensor, applied to the second tensor's closed state vectors at the two
endpoints, agree (up to their respective interior bond products). This is the
region analogue of the resonate identity `hEqB` that
`edgeRightInsertionOp_realizes_edgeTransferMatrix` feeds into
`physical_to_virtual_insertion`. It reads the two tensors only through the
`SameState`-invariant closed state vectors. -/

/-- **The region resonate identity.** The in-region-endpoint operator of the first
tensor from `M`, applied to the second tensor's closed state vector and evaluated at
the in-region endpoint leg, agrees with the out-of-region-endpoint operator from `M`,
applied to the second tensor's complement-side closed state vector and evaluated at
the out-of-region endpoint leg, each scaled by the interior bond product of the
respective block.

Both sides equal the first tensor's region-inserted coefficient of `M`: the left
side by the in-region-endpoint pin `regionInsertionOp_regionStateVec_pin`, the right
side by the out-of-region-endpoint pin
`regionInsertionOp_regionStateVec_pin_compl`. This is the doubled boundary-edge
reading the region resonate step equates.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem region_resonate_identity (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex (G := G) R f)))
    (hvAout : LinearIndependent ℂ
      (A.component (regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f))))
    (hAB : SameState A B)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInteriorBondProd (G := G) A R •
        (regionInsertionOp (G := G) A R f hvA M.transpose
          (regionStateVec (G := G) B R f σ τ))
          (σ ⟨regionBoundaryEdgeInVertex (G := G) R f,
            regionBoundaryEdgeInVertex_mem (G := G) R f⟩) =
      regionInteriorBondProd (G := G) A (Finset.univ \ R) •
        (regionInsertionOp (G := G) A (Finset.univ \ R)
          (regionBoundaryEdgeToCompl (G := G) R f) hvAout M.transpose.transpose
          (regionStateVec (G := G) B (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f) τ
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)))
          (τ ⟨regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
            (regionBoundaryEdgeToCompl (G := G) R f),
            regionBoundaryEdgeInVertex_mem (G := G) (Finset.univ \ R)
              (regionBoundaryEdgeToCompl (G := G) R f)⟩) := by
  rw [regionInsertionOp_regionStateVec_pin A B R f hvA hAB M σ τ,
    regionInsertionOp_regionStateVec_pin_compl A B R f hvAout hAB M σ τ]

/-! ### Factoring the region-inserted coefficient through the complement blocked map

Fixing the region physical configuration `σ`, the region-inserted coefficient is a
function of the complement physical configuration `τ` that factors through the
blocked-region tensor map of the set complement `univ \ R`. Reindexing the inner
boundary-configuration sum by the complement boundary-configuration equivalence
`regionComplementBoundaryConfigEquiv` exposes the τ-dependence as the complement
blocked tensor map applied to the **complement row function**: the
boundary-edge-coupled contraction of the region block against the inserted matrix.
This lets the chosen left inverse of the complement block
(`regionBlockedLeftInverse`) read off the row function, isolating the boundary-edge
matrix entries. -/

open scoped Classical in
/-- The complement row function: for a boundary configuration `w` of `univ \ R`,
the inserted matrix entry on the boundary edge `f` coupling `w` (reindexed back to
`R`) to the region boundary configuration, contracted against the region block at
`σ`. This is the coefficient of the complement block in the region-inserted
coefficient, viewed as a function of the complement physical configuration. -/
noncomputable def regionComplementRow (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ R) → ℂ :=
  fun w =>
    ∑ μ : RegionBoundaryConfig (G := G) A R,
      (if SameAwayFromBond f μ
            ((regionComplementBoundaryConfigEquiv (G := G) A R).symm w) then
          M (μ f) (((regionComplementBoundaryConfigEquiv (G := G) A R).symm w) f) else 0) *
        regionBlockedWeight (G := G) A R μ σ

open scoped Classical in
/-- **Factoring through the complement blocked map.** The region-inserted
coefficient, as a function of the complement physical configuration `τ`, is the
blocked-region tensor map of the set complement `univ \ R` applied to the complement
row function.

Reindexing the outer boundary-configuration sum of `regionInsertedCoeff` by the
complement boundary-configuration equivalence turns the complement blocked weights
into the standard blocked tensor map summands, with the row function carrying the
inserted-matrix coupling and the region block. This is the factoring the complement
left inverse acts on.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_complement_blockedMap (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionBlockedTensorMap (G := G) A (Finset.univ \ R)
        (regionComplementRow (G := G) A R f M σ) τ := by
  classical
  set E := regionComplementBoundaryConfigEquiv (G := G) A R with hE
  rw [regionInsertedCoeff_eq, regionBlockedTensorMap_apply]
  -- Swap the order of summation: outer over `ν`, inner over `μ`.
  rw [Finset.sum_comm]
  -- Reindex the right `w`-sum over complement configs by `E` to the `ν`-sum.
  rw [← Equiv.sum_comp E
    (fun w : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
      regionComplementRow (G := G) A R f M σ w •
        regionBlockedWeight (G := G) A (Finset.univ \ R) w τ)]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [regionComplementRow, smul_eq_mul, Finset.sum_mul, hE,
    regionComplementBoundaryConfigEquiv_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [← regionComplementBoundaryConfigEquiv_apply (G := G) A R ν, Equiv.symm_apply_apply,
    regionComplementBoundaryConfigEquiv_apply]

/-! ### Factoring the region-inserted coefficient through the region blocked map

Fixing the complement physical configuration `τ`, the region-inserted coefficient is
a function of the region physical configuration `σ` that factors through the
blocked-region tensor map of `R`. The outer boundary-configuration sum of
`regionInsertedCoeff` is already indexed by the region boundary configurations, so
no reindexing is needed: the row function carries the inserted-matrix coupling and
the complement block. This is the σ-analogue of the complement factoring, used to
read the region-inserted coefficient off the region block via its left inverse. -/

open scoped Classical in
/-- The region row function: for a region boundary configuration `μ`, the inserted
matrix entry on the boundary edge `f` coupling `μ` to the complement boundary
configuration, contracted against the complement block at `τ`. This is the
coefficient of the region block in the region-inserted coefficient, viewed as a
function of the region physical configuration. -/
noncomputable def regionRegionRow (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) A R → ℂ :=
  fun μ =>
    ∑ ν : RegionBoundaryConfig (G := G) A R,
      (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
        regionBlockedWeight (G := G) A (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R ν) τ

open scoped Classical in
/-- **Factoring through the region blocked map.** The region-inserted coefficient,
as a function of the region physical configuration `σ`, is the blocked-region tensor
map of `R` applied to the region row function.

The outer boundary-configuration sum of `regionInsertedCoeff` is indexed by the
region boundary configurations, so it is already the blocked tensor map summand form
with the row function carrying the inserted-matrix coupling and the complement block.
This is the factoring the region left inverse acts on.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_region_blockedMap (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionBlockedTensorMap (G := G) A R
        (regionRegionRow (G := G) A R f M τ) σ := by
  classical
  rw [regionInsertedCoeff_eq, regionBlockedTensorMap_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [regionRegionRow, smul_eq_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  ring

/-! ### Reading off the row functions through the blocked left inverses

Each blocked left inverse recovers the corresponding row function from the
region-inserted coefficient viewed as a function of the matching physical
configuration. These are the read-off lemmas the region resonate step uses:
the region-inserted coefficient, as a function of the complement (resp. region)
physical configuration, lies in the image of the complement (resp. region) blocked
tensor map, so the chosen left inverse reads off the row function. -/

/-- **Complement read-off.** The chosen left inverse of the complement blocked tensor
map, applied to the region-inserted coefficient viewed as a function of the
complement physical configuration, recovers the complement row function. -/
theorem regionBlockedLeftInverse_complement_regionInsertedCoeff (A : Tensor G d)
    (R : Finset V) (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedLeftInverse (G := G) A (Finset.univ \ R) hC
        (fun τ => regionInsertedCoeff (G := G) A R f M σ τ) =
      regionComplementRow (G := G) A R f M σ := by
  have hfun : (fun τ => regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) A (Finset.univ \ R)
        (regionComplementRow (G := G) A R f M σ) :=
    funext (fun τ => regionInsertedCoeff_eq_complement_blockedMap A R f M σ τ)
  rw [hfun, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-- **Region read-off.** The chosen left inverse of the region blocked tensor map,
applied to the region-inserted coefficient viewed as a function of the region
physical configuration, recovers the region row function. -/
theorem regionBlockedLeftInverse_region_regionInsertedCoeff (A : Tensor G d)
    (R : Finset V) (hR : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedLeftInverse (G := G) A R hR
        (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
      regionRegionRow (G := G) A R f M τ := by
  have hfun : (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
      regionBlockedTensorMap (G := G) A R (regionRegionRow (G := G) A R f M τ) :=
    funext (fun σ => regionInsertedCoeff_eq_region_blockedMap A R f M σ τ)
  rw [hfun, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

end PEPS
end TNLean
