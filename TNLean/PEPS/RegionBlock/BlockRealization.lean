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

end PEPS
end TNLean
