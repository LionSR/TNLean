import TNLean.PEPS.RegionBlock.ThreeBlockTransfer

/-!
# The block realization operator for the cross-tensor transfer kernel

This file builds the **block realization operator** behind the cross-tensor
transfer kernel of the normal PEPS Fundamental Theorem (arXiv:1804.04964,
Section 3, the step `V=W`). It is the block-granularity port of the edge-level
realization `edgeRightInsertionOp_realizes_edgeTransferMatrix`
(`TNLean.PEPS.InsertionAlgebra`), replacing the single-vertex insertion operator
by the blocked region operator that inverts the whole region block instead of one
vertex.

The transfer kernel `transferCoeff A B R hRB hCB f M`
(`TNLean.PEPS.RegionBlock.Recovery10`) is the doubly-blocked read-off of the first
tensor's region-inserted coefficient through the second tensor's region and
complement blocks. Its bond locality — the residual content `V=W` isolated as the
predicate `IsBondLocalTransferKernel`
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) — is what closes the per-edge gauge.

## The row-insertion operator

The M-dependence of the first tensor's region-inserted coefficient runs entirely
through one linear operator on the region boundary-configuration coefficients: the
**row insertion** `rowInsertF`. It couples the boundary legs on the boundary edge
`f` through the matrix `M` and contracts the residual legs by the identity
(`SameAwayFromBond`). Factoring the region row `regionRegionRow`
(`TNLean.PEPS.RegionBlock.Recovery7`) as `rowInsertF M` applied to the
M-independent **complement weight row** exposes the insertion as a single bond-`f`
matrix action on the boundary configurations.

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

/-! ### The row-insertion operator

The first tensor's region-inserted coefficient of `M`, read as a function of the
region physical configuration, is the region blocked tensor map of the region row
`regionRegionRow A R f M τ` (`regionInsertedCoeff_eq_region_blockedMap`,
`TNLean.PEPS.RegionBlock.Recovery7`). The region row is, in turn, the **row
insertion** of `M` applied to the M-independent complement weight row: the M
dependence is exactly a left multiplication by the incident-matrix coupling on the
boundary edge `f`. -/

open scoped Classical in
/-- The **row-insertion operator** of a matrix `M` on the boundary edge `f`: it
couples the boundary legs `μ f`, `ν f` of two region boundary configurations
through `M` and contracts the residual legs by the identity (`SameAwayFromBond`).
This is the M-dependent part of the region row `regionRegionRow`
(`TNLean.PEPS.RegionBlock.Recovery7`), isolated as a linear endomorphism of the
boundary-configuration coefficients.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def rowInsertF (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    (RegionBoundaryConfig (G := G) A R → ℂ) →ₗ[ℂ]
      (RegionBoundaryConfig (G := G) A R → ℂ) where
  toFun c := fun μ =>
    ∑ ν : RegionBoundaryConfig (G := G) A R,
      (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) * c ν
  map_add' c c' := by
    funext μ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' z c := by
    funext μ
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl (fun ν _ => ?_)
    ring

open scoped Classical in
@[simp] theorem rowInsertF_apply (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (c : RegionBoundaryConfig (G := G) A R → ℂ)
    (μ : RegionBoundaryConfig (G := G) A R) :
    rowInsertF (G := G) A R f M c μ =
      ∑ ν : RegionBoundaryConfig (G := G) A R,
        (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) * c ν := rfl

open scoped Classical in
/-- The row insertion of two region boundary configurations is the standard basis at
the boundary configuration: the incident-matrix coupling vanishes unless the two
configurations agree on the boundary edge `f` as well as off it, that is, unless they
are equal. -/
theorem rowInsertF_coupling_eq_single (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ ν : RegionBoundaryConfig (G := G) A R) :
    (if SameAwayFromBond f μ ν then (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
        (μ f) (ν f) else 0) =
      (if μ = ν then (1 : ℂ) else 0) := by
  classical
  by_cases hμν : μ = ν
  · subst hμν
    have hsame : SameAwayFromBond f μ μ := fun c _ => rfl
    rw [if_pos hsame, Matrix.one_apply_eq, if_pos rfl]
  · rw [if_neg hμν]
    by_cases hsame : SameAwayFromBond f μ ν
    · rw [if_pos hsame, Matrix.one_apply]
      by_cases hbond : μ f = ν f
      · exact absurd (funext (fun c => by
          by_cases hc : c = f
          · subst hc; exact hbond
          · exact hsame c hc)) hμν
      · rw [if_neg hbond]
    · rw [if_neg hsame]

open scoped Classical in
/-- **The row insertion of the identity is the identity.** Inserting the identity
matrix on the boundary edge `f` couples the boundary legs trivially, contracting all
legs by the identity, so the row insertion is the identity endomorphism. This is the
anchor `M = 1` of the row insertion. -/
@[simp] theorem rowInsertF_one (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    rowInsertF (G := G) A R f (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) =
      LinearMap.id := by
  classical
  refine LinearMap.ext (fun c => funext (fun μ => ?_))
  rw [rowInsertF_apply, LinearMap.id_apply]
  rw [Finset.sum_eq_single μ]
  · rw [rowInsertF_coupling_eq_single A R f μ μ, if_pos rfl, one_mul]
  · intro ν _ hν
    rw [rowInsertF_coupling_eq_single A R f μ ν, if_neg (Ne.symm hν), zero_mul]
  · intro hμ; exact absurd (Finset.mem_univ μ) hμ

/-- The **complement weight row**: the M-independent boundary-configuration
coefficient family the row insertion acts on. At a region boundary configuration
`ν`, it is the complement blocked weight of the complement boundary configuration
of `ν` at the complement physical configuration `τ`. This is the part of the
region row `regionRegionRow` that does not depend on `M`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionComplementWeightRow (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) A R → ℂ :=
  fun ν =>
    regionBlockedWeight (G := G) A (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) A R ν) τ

open scoped Classical in
/-- The region row `regionRegionRow` is the row insertion of `M` applied to the
complement weight row. This isolates the M-dependence of `regionRegionRow`
(`TNLean.PEPS.RegionBlock.Recovery7`) as a left multiplication by the
incident-matrix coupling on the boundary edge `f`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionRegionRow_eq_rowInsertF (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionRegionRow (G := G) A R f M τ =
      rowInsertF (G := G) A R f M (regionComplementWeightRow (G := G) A R τ) := by
  classical
  funext μ
  rw [regionRegionRow, rowInsertF_apply]
  rfl

/-! ### The complement weight row is the region left inverse of the partial state

The interior bond multiple of the partial state across the region cut is the region
blocked tensor map of the complement weight row
(`regionInteriorBondProd_smul_regionPartialState`,
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`). So the chosen region left inverse
reads the complement weight row off the interior bond multiple of the partial state.
This connects the M-independent complement weight row to the `SameState`-invariant
partial state. -/

/-- The interior bond multiple of the partial state across the region cut is the
region blocked tensor map of the complement weight row. This restates
`regionInteriorBondProd_smul_regionPartialState`
(`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`) with the complement weight row
named.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInteriorBondProd_smul_regionPartialState_eq_blockedMap (A : Tensor G d)
    (R : Finset V) (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ =
      regionBlockedTensorMap (G := G) A R (regionComplementWeightRow (G := G) A R τ) := by
  classical
  rw [regionInteriorBondProd_smul_regionPartialState (G := G) A R τ]
  funext σ
  rw [regionBlockedTensorMap_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [regionComplementWeightRow, Pi.smul_apply]

/-- The chosen region left inverse reads the complement weight row off the interior
bond multiple of the partial state across the region cut. -/
theorem regionBlockedLeftInverse_regionInteriorBondProd_smul_regionPartialState
    (A : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedLeftInverse (G := G) A R hRA
        ((regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ) =
      regionComplementWeightRow (G := G) A R τ := by
  rw [regionInteriorBondProd_smul_regionPartialState_eq_blockedMap (G := G) A R τ,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### The block realization operator

The M-insertion on the boundary edge `f`, realized as a linear endomorphism of the
region physical functions through the first tensor's region block: invert the
region block, apply the row insertion of `M`, reblock. This is the block-granularity
port of the edge insertion operator `edgeRightInsertionOp`
(`TNLean.PEPS.InsertionAlgebra`), inverting the whole region block instead of one
vertex. -/

/-- The **block realization operator** of a matrix `M` on the boundary edge `f`: the
region blocked tensor map of the row insertion of `M` of the region left inverse.
Applied to a region physical function lying in the range of the region blocked
tensor map, it realizes the M-insertion on the boundary edge `f`. This is the
block-granularity port of the edge insertion operator `edgeRightInsertionOp`,
inverting the whole region block rather than a single vertex.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def blockRealizeOp (A : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ) :=
  (regionBlockedTensorMap (G := G) A R).comp
    ((rowInsertF (G := G) A R f M).comp (regionBlockedLeftInverse (G := G) A R hRA))

theorem blockRealizeOp_apply (A : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (g : RegionPhysicalConfig (V := V) (d := d) R → ℂ) :
    blockRealizeOp (G := G) A R hRA f M g =
      regionBlockedTensorMap (G := G) A R
        (rowInsertF (G := G) A R f M
          (regionBlockedLeftInverse (G := G) A R hRA g)) := rfl

/-- **The block realization operator on the region blocked tensor map.** On the
region blocked tensor map of any boundary-configuration coefficient `c`, the block
realization operator reblocks the row insertion of `M` of `c`. This is the operator
acting on the region block image, where the region left inverse cancels the region
blocked tensor map. -/
theorem blockRealizeOp_regionBlockedTensorMap (A : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (c : RegionBoundaryConfig (G := G) A R → ℂ) :
    blockRealizeOp (G := G) A R hRA f M (regionBlockedTensorMap (G := G) A R c) =
      regionBlockedTensorMap (G := G) A R (rowInsertF (G := G) A R f M c) := by
  rw [blockRealizeOp_apply, regionBlockedLeftInverse_apply_regionBlockedTensorMap]

/-! ### KEY IDENTITY 1: the realization operator recovers the M-inserted coefficient

Applied to the interior bond multiple of the partial state across the region cut,
the block realization operator recovers the interior bond multiple of the first
tensor's region-inserted coefficient of `M`, read as a function of the region
physical configuration. The partial state is the `SameState`-invariant object
through which the realization transports across the comparison. -/

/-- **KEY IDENTITY 1.** The block realization operator of `M`, applied to the interior
bond multiple of the partial state across the region cut, recovers the first tensor's
region-inserted coefficient of `M`, read as a function of the region physical
configuration. The region left inverse reads the complement weight row off the
partial state (`regionBlockedLeftInverse_regionInteriorBondProd_smul_regionPartialState`),
the row insertion turns it into the region row
(`regionRegionRow_eq_rowInsertF`), and the region blocked tensor map of the region row
is the coefficient (`regionInsertedCoeff_eq_region_blockedMap`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem blockRealizeOp_regionPartialState_eq_regionInsertedCoeff (A : Tensor G d)
    (R : Finset V) (hRA : RegionBlockedTensorInjective (G := G) A R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    blockRealizeOp (G := G) A R hRA f M
        ((regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) A R τ) =
      fun σ => regionInsertedCoeff (G := G) A R f M σ τ := by
  rw [blockRealizeOp_apply,
    regionBlockedLeftInverse_regionInteriorBondProd_smul_regionPartialState (G := G) A R hRA τ,
    ← regionRegionRow_eq_rowInsertF (G := G) A R f M τ]
  funext σ
  rw [← regionInsertedCoeff_eq_region_blockedMap A R f M σ τ]

/-! ### Step 2: the M-inserted coefficient through the second tensor's partial state

The partial state across the region cut is `SameState`-invariant
(`regionPartialState_sameState`,
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`), so KEY IDENTITY 1 also reads the
first tensor's region-inserted coefficient of `M` off the *second* tensor's partial
state. This is the transport across the comparison: the realization operator built
from the first tensor acts on the second tensor's `SameState`-invariant column. -/

/-- **The M-inserted coefficient through the second tensor's partial state.** The
block realization operator of `M`, applied to the interior bond multiple of the
second tensor's partial state across the region cut, recovers the first tensor's
region-inserted coefficient of `M` as a function of the region physical
configuration. The partial state is `SameState`-invariant, so the second tensor's
column feeds the first tensor's realization operator (KEY IDENTITY 1).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem blockRealizeOp_regionPartialState_B_eq_regionInsertedCoeff (A B : Tensor G d)
    (R : Finset V) (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hAB : SameState A B)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    blockRealizeOp (G := G) A R hRA f M
        ((regionInteriorBondProd (G := G) A R : ℂ) • regionPartialState (G := G) B R τ) =
      fun σ => regionInsertedCoeff (G := G) A R f M σ τ := by
  rw [← regionPartialState_sameState hAB R τ,
    blockRealizeOp_regionPartialState_eq_regionInsertedCoeff (G := G) A R hRA f M τ]

/-! ### Step 3: expanding the second tensor's partial state through its region block

The second tensor's partial state across the region cut lies in the range of the
second tensor's region blocked tensor map
(`regionPartialState_mem_span_regionBlockedWeight`,
`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`). Writing it as the second tensor's
region blocked tensor map of a boundary-configuration row exposes the **A↔B basis
change** `Φ := regionBlockedLeftInverse A R hRA ∘ regionBlockedTensorMap B R` inside
the realization operator: the first tensor's realization of the second tensor's block
image is the first tensor's region block of the row insertion of the basis-changed
row. This is the cross-tensor expansion the bond-locality reconcile acts on. -/

/-- The second tensor's partial state across the region cut lies in the range of the
second tensor's region blocked tensor map. By
`regionPartialState_mem_span_regionBlockedWeight`
(`TNLean.PEPS.RegionBlock.BlockRangeCoincidence`), it lies in the span of the second
tensor's region blocked weights, which is the range of the region blocked tensor map
(`range_regionBlockedTensorMap_eq_span`). -/
theorem regionPartialState_mem_range_regionBlockedTensorMap (B : Tensor G d)
    (R : Finset V) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionPartialState (G := G) B R τ ∈
      LinearMap.range (regionBlockedTensorMap (G := G) B R) := by
  rw [range_regionBlockedTensorMap_eq_span (G := G) B R]
  exact regionPartialState_mem_span_regionBlockedWeight (G := G) B R hposB τ

/-- The chosen second-tensor region boundary-configuration row whose region blocked
tensor map is the second tensor's partial state across the region cut. -/
noncomputable def partialStateRowB (B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionBoundaryConfig (G := G) B R → ℂ :=
  regionBlockedLeftInverse (G := G) B R hRB (regionPartialState (G := G) B R τ)

/-- The second tensor's region blocked tensor map of `partialStateRowB` is the second
tensor's partial state across the region cut. -/
theorem regionBlockedTensorMap_partialStateRowB (B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedTensorMap (G := G) B R (partialStateRowB (G := G) B R hRB τ) =
      regionPartialState (G := G) B R τ := by
  obtain ⟨c, hc⟩ := regionPartialState_mem_range_regionBlockedTensorMap (G := G) B R hposB τ
  rw [partialStateRowB, ← hc, regionBlockedLeftInverse_apply_regionBlockedTensorMap, hc]

/-- The **A↔B region basis change**: the first tensor's region left inverse of the
second tensor's region blocked tensor map. It conjugates the row insertion inside the
cross-tensor realization. -/
noncomputable def regionBasisChange (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R) :
    (RegionBoundaryConfig (G := G) B R → ℂ) →ₗ[ℂ]
      (RegionBoundaryConfig (G := G) A R → ℂ) :=
  (regionBlockedLeftInverse (G := G) A R hRA).comp (regionBlockedTensorMap (G := G) B R)

theorem regionBasisChange_apply (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (c : RegionBoundaryConfig (G := G) B R → ℂ) :
    regionBasisChange (G := G) A B R hRA c =
      regionBlockedLeftInverse (G := G) A R hRA
        (regionBlockedTensorMap (G := G) B R c) := rfl

/-- **The realization operator on the second tensor's expanded partial state.** The
block realization operator of `M`, applied to the second tensor's partial state
across the region cut, is the first tensor's region blocked tensor map of the row
insertion of `M` of the basis-changed second-tensor partial-state row. The
realization operator's region left inverse meets the second tensor's region blocked
tensor map exactly at the A↔B basis change `regionBasisChange`. -/
theorem blockRealizeOp_regionPartialState_B_eq_basisChange (A B : Tensor G d)
    (R : Finset V) (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    blockRealizeOp (G := G) A R hRA f M (regionPartialState (G := G) B R τ) =
      regionBlockedTensorMap (G := G) A R
        (rowInsertF (G := G) A R f M
          (regionBasisChange (G := G) A B R hRA
            (partialStateRowB (G := G) B R hRB τ))) := by
  rw [blockRealizeOp_apply, regionBasisChange_apply,
    regionBlockedTensorMap_partialStateRowB (G := G) B R hRB hposB τ]

open scoped Classical in
/-- **Step 3: the cross-tensor expansion.** The first tensor's region-inserted
coefficient of `M`, read as a function of the region physical configuration, is the
interior bond multiple of the first tensor's region blocked tensor map of the row
insertion of `M` of the basis-changed second-tensor partial-state row.

This is KEY IDENTITY 1 (through the second tensor's partial state, Step 2) with the
second tensor's partial state expanded through its region block (Step 3): the
realization operator's region left inverse meets the second tensor's region blocked
tensor map exactly at the A↔B basis change `regionBasisChange`. The interior bond
product appears because KEY IDENTITY 1 reads the realization operator on the interior
bond multiple of the partial state.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_crossExpansion (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hAB : SameState A B) (hposB : ∀ e : Edge G, 0 < B.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (fun σ => regionInsertedCoeff (G := G) A R f M σ τ) =
      (regionInteriorBondProd (G := G) A R : ℂ) •
        regionBlockedTensorMap (G := G) A R
          (rowInsertF (G := G) A R f M
            (regionBasisChange (G := G) A B R hRA
              (partialStateRowB (G := G) B R hRB τ))) := by
  rw [← blockRealizeOp_regionPartialState_B_eq_regionInsertedCoeff A B R hRA hAB f M τ,
    map_smul, blockRealizeOp_regionPartialState_B_eq_basisChange A B R hRA hRB hposB f M τ]

end PEPS
end TNLean
