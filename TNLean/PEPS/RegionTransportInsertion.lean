import TNLean.PEPS.RegionTransport
import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap5

/-!
# Covariance of the region-inserted coefficient under a graph isomorphism

A graph isomorphism `φ : G ≃g G'` carries the region-inserted coefficient of a tensor `A`
over a region `R` to the region-inserted coefficient of the transported tensor `A.transport φ`
over the image region `Region.map φ R`, with the inserted matrix carried to the image bond, the
boundary edge to its image, and the region/complement physical configurations relabelled by the
vertex bijection (`regionInsertedCoeff_transport`).

The region-inserted coefficient is the double boundary-configuration sum coupling `R` and its
set complement through a single matrix inserted on one boundary edge `f`.  The blocked-region
weight transports (`regionBlockedWeight_transport`), the boundary configurations reindex by the
edge action (`regionBoundaryConfigMapEquiv`), and the `SameAwayFromBond` coupling is preserved by
that reindex, so the whole double sum carries across.  No endpoint orientation enters: the
coefficient inserts the matrix between the two boundary configurations' single values on the
boundary edge, with no reference to which endpoint lies in `R`.

This is the missing covariance of obligation 6 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`: together with the transport of the blocked
weights it makes the per-edge transfer maps covariant under translation on the torus.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V W : Type*} [Fintype V] [LinearOrder V]
  [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-! ### The image boundary edge -/

/-- The image of a boundary edge of `R` under the edge action of `φ`: a boundary edge of the
image region whose underlying edge is `Edge.map φ f.1`.  This is the inverse direction of the
boundary-edge reindexing `regionBoundaryEdgeMapEquiv`. -/
def boundaryEdgeMap (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    {f : Edge G' // IsRegionBoundaryEdge (G := G') (Region.map φ R) f} :=
  (regionBoundaryEdgeMapEquiv φ R).symm f

omit [Fintype V] [Fintype W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
@[simp] theorem boundaryEdgeMap_coe (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (boundaryEdgeMap φ R f).1 = Edge.map φ f.1 := rfl

omit [Fintype V] [Fintype W] in
/-- The bond dimension of `A.transport φ` at the image boundary edge equals the bond dimension of
`A` at the original boundary edge. -/
theorem transport_bondDim_boundaryEdgeMap (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    (A.transport φ).bondDim (boundaryEdgeMap φ R f).1 = A.bondDim f.1 := by
  rw [boundaryEdgeMap_coe, Tensor.transport_bondDim, Edge.map_symm_map]

omit [Fintype V] [Fintype W] in
/-- The image boundary configuration, read on the image of the distinguished boundary edge,
recovers the original value through the bond-dimension cast. -/
theorem regionBoundaryConfigMap_boundaryEdgeMap (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (g : RegionBoundaryConfig (G := G) A R) :
    (regionBoundaryConfigMap A φ R g) (boundaryEdgeMap φ R f) =
      Fin.cast (transport_bondDim_boundaryEdgeMap A φ R f).symm (g f) := by
  have hrt : regionBoundaryEdgeMapEquiv φ R (boundaryEdgeMap φ R f) = f := by
    rw [boundaryEdgeMap, Equiv.apply_symm_apply]
  change g (regionBoundaryEdgeMapEquiv φ R (boundaryEdgeMap φ R f)) = _
  -- The argument equals `f`, so the value equals `g f` up to the bond-dimension cast: the cast
  -- preserves the underlying natural-number value, which is `(g ·).val` evaluated at equal points.
  apply Fin.eq_of_val_eq
  rw [Fin.val_cast]
  exact congrArg (fun x => (g x).val) hrt

/-! ### Transport of the complement-side blocked weight

The region-inserted coefficient contracts the set complement `univ \ R` on the second factor.
Under transport, the image coefficient contracts `univ \ Region.map φ R`, while the transport of
the original complement weight lives over `Region.map φ (univ \ R)`.  These two regions agree
(`Region_map_compl`), and the complement boundary configurations match across the region equality,
so the image complement weight equals the original complement weight. -/


/-- The image complement boundary configuration, read on `univ \ Region.map φ R`, agrees across
the region equality `Region.map φ (univ \ R) = univ \ Region.map φ R` with the transport of the
original complement boundary configuration on `Region.map φ (univ \ R)`. -/
theorem regionComplementBoundaryConfig_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (ν : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R)
        (regionBoundaryConfigMap A φ R ν) =
      regionBoundaryConfigCongr (A := A.transport φ) (Region_map_compl φ R)
        (regionBoundaryConfigMap A φ (Finset.univ \ R)
          (regionComplementBoundaryConfig (G := G) A R ν)) := by
  funext f
  rw [regionBoundaryConfigCongr_apply]
  -- After the congr rewrite both sides read `ν` on the same reindexed boundary edge.
  rfl

/-- **Transport of the complement-side blocked weight.**

The blocked weight of `A.transport φ` over the set complement `univ \ Region.map φ R`, at the
image complement boundary configuration and the image complement physical configuration, equals
the blocked weight of `A` over `univ \ R`.  This bridges the region equality
`Region.map φ (univ \ R) = univ \ Region.map φ R` (`Region_map_compl`) and then applies the
blocked-weight transport (`regionBlockedWeight_transport`). -/
theorem regionComplementWeight_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (ν : RegionBoundaryConfig (G := G) A R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedWeight (G := G') (A.transport φ) (Finset.univ \ Region.map φ R)
        (regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R)
          (regionBoundaryConfigMap A φ R ν))
        (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
          (regionPhysicalConfigMap φ (Finset.univ \ R) τ)) =
      regionBlockedWeight (G := G) A (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R ν) τ := by
  -- Bridge the region equality, then apply the blocked-weight transport for `univ \ R`.
  rw [regionComplementBoundaryConfig_transport,
    ← regionBlockedWeight_congr (A := A.transport φ) (Region_map_compl φ R)
      (regionBoundaryConfigMap A φ (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R ν))
      (regionPhysicalConfigMap φ (Finset.univ \ R) τ),
    regionBlockedWeight_transport A φ (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) A R ν) τ]

/-! ### Transport of the `SameAwayFromBond` coupling

The boundary configurations of the image region reindex to those of `R` by the edge action
(`regionBoundaryConfigMap`).  The coupling `SameAwayFromBond` on the image boundary edge is
preserved by this reindex, since the reindex is a bijection on the boundary edges fixing the
distinguished edge. -/

omit [Fintype V] [Fintype W] in
/-- The `SameAwayFromBond` coupling on the image boundary edge transports along the
boundary-configuration reindex: the image configurations agree away from `boundaryEdgeMap φ R f`
iff the original configurations agree away from `f`.  The values are compared at the image bond
type `Fin ((A.transport φ).bondDim c'.1)`, which matches the original bond type definitionally
through the edge action. -/
theorem sameAwayFromBond_regionBoundaryConfigMap (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ ν : RegionBoundaryConfig (G := G) A R) :
    SameAwayFromBond (boundaryEdgeMap φ R f)
        (regionBoundaryConfigMap A φ R μ) (regionBoundaryConfigMap A φ R ν) ↔
      SameAwayFromBond f μ ν := by
  constructor
  · intro h c hc
    -- Push `c` forward to the image edge `boundaryEdgeMap φ R c`, which differs from
    -- `boundaryEdgeMap φ R f` by injectivity of the reindex.
    have hkey := h (boundaryEdgeMap φ R c) (fun hcontra =>
      hc ((regionBoundaryEdgeMapEquiv φ R).symm.injective hcontra))
    -- The two sides are, by definition of `regionBoundaryConfigMap`, `μ` and `ν` read on
    -- `regionBoundaryEdgeMapEquiv φ R (boundaryEdgeMap φ R c) = c`.
    have hcc : regionBoundaryEdgeMapEquiv φ R (boundaryEdgeMap φ R c) = c := by
      rw [boundaryEdgeMap, Equiv.apply_symm_apply]
    -- Rewrite the goal `μ c = ν c` to the roundtrip edge, where `hkey` closes it definitionally.
    rw [← hcc]
    exact hkey
  · intro h c hc
    -- Pull `c` back along the reindex; the preimage differs from `f`.
    have hpre : regionBoundaryEdgeMapEquiv φ R c ≠ f := fun hcontra =>
      hc (by rw [← hcontra, boundaryEdgeMap, Equiv.symm_apply_apply])
    have := h (regionBoundaryEdgeMapEquiv φ R c) hpre
    exact this

/-! ### Covariance of the region-inserted coefficient -/

open scoped Classical in
/-- **Covariance of the region-inserted coefficient under a graph isomorphism.**

For a graph isomorphism `φ : G ≃g G'`, the region-inserted coefficient of the transported tensor
`A.transport φ` over the image region `Region.map φ R`, with a matrix `M` inserted on the image
boundary edge `boundaryEdgeMap φ R f` and the region/complement physical configurations
relabelled by the vertex bijection, equals the region-inserted coefficient of `A` over `R`, with
`M` carried back to `A`'s bond on `f` through the bond-dimension equality.

The double boundary-configuration sum reindexes by the edge action
(`regionBoundaryConfigMapEquiv`), the `SameAwayFromBond` coupling is preserved
(`sameAwayFromBond_regionBoundaryConfigMap`), and the two blocked weights transport
(`regionBlockedWeight_transport`, `regionComplementWeight_transport`).  No endpoint orientation
enters: the matrix is inserted between the two single boundary values on the edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1572 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin ((A.transport φ).bondDim (boundaryEdgeMap φ R f).1))
      (Fin ((A.transport φ).bondDim (boundaryEdgeMap φ R f).1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G') (A.transport φ) (Region.map φ R) (boundaryEdgeMap φ R f) M
        (regionPhysicalConfigMap φ R σ)
        (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
          (regionPhysicalConfigMap φ (Finset.univ \ R) τ)) =
      regionInsertedCoeff (G := G) A R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (transport_bondDim_boundaryEdgeMap A φ R f)) M)
        σ τ := by
  classical
  rw [regionInsertedCoeff_eq, regionInsertedCoeff_eq]
  -- Reindex the outer `μ` sum by the boundary-configuration equivalence.
  rw [← Equiv.sum_comp (regionBoundaryConfigMapEquiv A φ R)
    (fun μ' => ∑ ν' : RegionBoundaryConfig (G := G') (A.transport φ) (Region.map φ R),
      (if SameAwayFromBond (boundaryEdgeMap φ R f) μ' ν' then M (μ' (boundaryEdgeMap φ R f))
          (ν' (boundaryEdgeMap φ R f)) else 0) *
        regionBlockedWeight (G := G') (A.transport φ) (Region.map φ R) μ'
          (regionPhysicalConfigMap φ R σ) *
        regionBlockedWeight (G := G') (A.transport φ) (Finset.univ \ Region.map φ R)
          (regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R) ν')
          (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
            (regionPhysicalConfigMap φ (Finset.univ \ R) τ)))]
  refine Finset.sum_congr rfl fun μ _ => ?_
  -- Reindex the inner `ν` sum by the same equivalence.
  rw [← Equiv.sum_comp (regionBoundaryConfigMapEquiv A φ R)
    (fun ν' => (if SameAwayFromBond (boundaryEdgeMap φ R f)
          (regionBoundaryConfigMapEquiv A φ R μ) ν' then
          M ((regionBoundaryConfigMapEquiv A φ R μ) (boundaryEdgeMap φ R f))
            (ν' (boundaryEdgeMap φ R f)) else 0) *
        regionBlockedWeight (G := G') (A.transport φ) (Region.map φ R)
          (regionBoundaryConfigMapEquiv A φ R μ) (regionPhysicalConfigMap φ R σ) *
        regionBlockedWeight (G := G') (A.transport φ) (Finset.univ \ Region.map φ R)
          (regionComplementBoundaryConfig (G := G') (A.transport φ) (Region.map φ R) ν')
          (regionPhysicalConfigCongr (d := d) (Region_map_compl φ R)
            (regionPhysicalConfigMap φ (Finset.univ \ R) τ)))]
  refine Finset.sum_congr rfl fun ν _ => ?_
  -- `regionBoundaryConfigMapEquiv A φ R μ = regionBoundaryConfigMap A φ R μ`.
  rw [regionBoundaryConfigMapEquiv_apply, regionBoundaryConfigMapEquiv_apply]
  -- The region weight on the `μ`-side transports.
  rw [regionBlockedWeight_transport A φ R μ σ]
  -- The complement weight on the `ν`-side transports.
  rw [regionComplementWeight_transport A φ R ν τ]
  -- Match the matrix factor and the `SameAwayFromBond` predicate.
  refine congr_arg₂ (· * ·) (congr_arg₂ (· * ·) ?_ rfl) rfl
  rw [show SameAwayFromBond (boundaryEdgeMap φ R f)
        (regionBoundaryConfigMap A φ R μ) (regionBoundaryConfigMap A φ R ν) =
      SameAwayFromBond f μ ν from
    propext (sameAwayFromBond_regionBoundaryConfigMap A φ R f μ ν)]
  split_ifs with hsame
  · -- The matrix entries agree: `M` read at the image-bond values equals the reindexed `M`
    -- read at the original-bond values, by the bond-dimension cast.
    rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply,
      regionBoundaryConfigMap_boundaryEdgeMap A φ R f μ,
      regionBoundaryConfigMap_boundaryEdgeMap A φ R f ν]
    simp only [finCongr_symm, finCongr_apply, Fin.cast_eq_cast]
  · rfl

end PEPS
end TNLean
