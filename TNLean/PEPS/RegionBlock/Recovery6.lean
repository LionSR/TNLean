import TNLean.PEPS.RegionBlock.Recovery5

/-!
# Region physical-to-virtual recovery: the out-of-region-endpoint realization

This file produces the complement-side realization of the region-inserted
coefficient, the second reading the region resonate step behind the normal PEPS
Fundamental Theorem equates (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

The v-side realizations `regionInsertedCoeff_eq_regionRealizationSum` and
`regionInsertedCoeff_eq_smul_op_regionStateVec`
(`TNLean.PEPS.RegionBlock.Recovery2`) carry the inserted matrix through the
in-region endpoint `regionBoundaryEdgeInVertex R f`. Since both lemmas are stated
for an arbitrary region, applying them to the set complement `univ \ R` realizes
the inserted matrix through that region's in-region endpoint, which is the
out-of-region endpoint `regionBoundaryEdgeOutVertex R f` of the original boundary
edge (`regionBoundaryEdgeInVertex_compl_eq_outVertex`,
`TNLean.PEPS.RegionBlock.Recovery5`).

The bridge is the **cast identity**

```
regionInsertedCoeff A R f M σ τ = regionInsertedCoeff A (univ \ R) f' M.transpose τ σ̃
```

where `f' := regionBoundaryEdgeToCompl R f` is the boundary edge `f` reread on the
complement, and `σ̃` transports `σ` across `univ \ (univ \ R) = R`. The
region-inserted coefficient contracts the region against its complement
symmetrically up to transposing the inserted matrix on the boundary edge; the
double sum of the right side is the double sum of the left side reindexed by the
boundary-edge identification `regionBoundaryEdgeComplEquiv` and the
physical-configuration transport across `univ \ (univ \ R) = R`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 and 1205--1210 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Transport of a region physical configuration across the double complement

The set complement of the set complement of `R` is `R` itself. A physical
configuration on `R` transports to one on `univ \ (univ \ R)` through the
membership equivalence of the two regions, and back. This isolates the dependent
reindexing `univ \ (univ \ R) = R` into a single equivalence of vertex subtypes,
so that it never threads through the realization argument. -/

/-- A vertex lies in `univ \ (univ \ R)` exactly when it lies in `R`. -/
theorem mem_compl_compl_iff (R : Finset V) (w : V) :
    w ∈ Finset.univ \ (Finset.univ \ R) ↔ w ∈ R := by
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

/-- The vertices of `univ \ (univ \ R)` are the vertices of `R`. -/
def regionDoubleComplVertexEquiv (R : Finset V) :
    {w : V // w ∈ Finset.univ \ (Finset.univ \ R)} ≃ {w : V // w ∈ R} :=
  Equiv.subtypeEquivRight (mem_compl_compl_iff (V := V) R)

/-- Transport of a region physical configuration on `R` to one on
`univ \ (univ \ R)` along the double-complement vertex equivalence. -/
def regionDoubleComplPhysicalConfig (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ (Finset.univ \ R)) :=
  fun w => σ (regionDoubleComplVertexEquiv (V := V) R w)

omit [DecidableRel G.Adj] in
/-- An edge crosses the boundary of `univ \ (univ \ R)` exactly when it crosses
the boundary of `R`. -/
theorem isRegionBoundaryEdge_compl_compl_iff (R : Finset V) (e : Edge G) :
    IsRegionBoundaryEdge (G := G) (Finset.univ \ (Finset.univ \ R)) e ↔
      IsRegionBoundaryEdge (G := G) R e := by
  rw [isRegionBoundaryEdge_compl_iff, isRegionBoundaryEdge_compl_iff]

/-- The edges crossing the boundary of `univ \ (univ \ R)` are the edges crossing
the boundary of `R`. -/
def regionBoundaryEdgeDoubleComplEquiv (R : Finset V) :
    {e : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ \ (Finset.univ \ R)) e} ≃
      {e : Edge G // IsRegionBoundaryEdge (G := G) R e} :=
  Equiv.subtypeEquivRight (fun e => isRegionBoundaryEdge_compl_compl_iff (G := G) R e)

omit [DecidableRel G.Adj] in
@[simp] theorem regionBoundaryEdgeDoubleComplEquiv_apply_coe (R : Finset V)
    (e : {e : Edge G // IsRegionBoundaryEdge (G := G) (Finset.univ \ (Finset.univ \ R)) e}) :
    ((regionBoundaryEdgeDoubleComplEquiv (G := G) R e) : Edge G) = e.1 := rfl

/-- Transport of a boundary configuration on `R` to one on `univ \ (univ \ R)`
along the double-complement boundary-edge equivalence. -/
def regionDoubleComplBoundaryConfig (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    RegionBoundaryConfig (G := G) A (Finset.univ \ (Finset.univ \ R)) :=
  fun e => bdry (regionBoundaryEdgeDoubleComplEquiv (G := G) R e)

/-! ### Double-complement invariance of the blocked-region weight

The blocked-region weight of `univ \ (univ \ R)` at the transported configurations
equals the blocked-region weight of `R`: the open boundary edges of the two
regions coincide, and so do their vertices, so the constrained virtual-configuration
sum and the contracted vertex product agree term by term. This is the cast that the
complement-side realization carries, isolated to a single weight identity. -/

/-- **Double-complement invariance of the blocked-region weight.** The blocked
weight of `univ \ (univ \ R)` at the double-complement transports of `bdry` and `σ`
equals the blocked weight of `R` at `bdry` and `σ`. The contraction runs over the
same global virtual configurations; the boundary-edge filter and the contracted
vertex product transport along the double-complement boundary-edge and vertex
equivalences. -/
theorem regionBlockedWeight_doubleCompl (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedWeight (G := G) A (Finset.univ \ (Finset.univ \ R))
        (regionDoubleComplBoundaryConfig (G := G) A R bdry)
        (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ) =
      regionBlockedWeight (G := G) A R bdry σ := by
  classical
  rw [regionBlockedWeight, regionBlockedWeight]
  -- The two filtered sums are over the same global virtual configurations.
  have hfilter : (Finset.univ.filter
        (fun ζ : VirtualConfig A =>
          regionBoundaryLabel (G := G) A (Finset.univ \ (Finset.univ \ R)) ζ =
            regionDoubleComplBoundaryConfig (G := G) A R bdry)) =
      (Finset.univ.filter
        (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = bdry)) := by
    ext ζ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    -- Both filter conditions say `ζ` restricted to the (shared) boundary edges is `bdry`,
    -- read through the double-complement boundary-edge equivalence.
    rw [funext_iff, funext_iff]
    refine (Equiv.forall_congr (regionBoundaryEdgeDoubleComplEquiv (G := G) R) ?_)
    intro g
    rw [regionBoundaryLabel_apply, regionBoundaryLabel_apply, regionDoubleComplBoundaryConfig]
    rfl
  rw [hfilter]
  -- For each global configuration the vertex products agree along the vertex equiv.
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  refine Fintype.prod_equiv (regionDoubleComplVertexEquiv (V := V) R) _ _ (fun w => ?_)
  rw [regionDoubleComplPhysicalConfig]
  rfl

/-! ### The complement boundary-configuration reindexing as an equivalence

The complement boundary-configuration map `regionComplementBoundaryConfig`
precomposes a boundary configuration with the boundary-edge identification of `R`
and its complement, so it is a bijection of boundary configurations. Recording it
as an equivalence lets the cast identity reindex the double sum of the
complement-side reading. -/

/-- The complement boundary-configuration reindexing as an equivalence: a boundary
configuration on `R` corresponds to one on `univ \ R` by reading each crossing edge
under the boundary-edge identification. -/
def regionComplementBoundaryConfigEquiv (A : Tensor G d) (R : Finset V) :
    RegionBoundaryConfig (G := G) A R ≃ RegionBoundaryConfig (G := G) A (Finset.univ \ R) where
  toFun := regionComplementBoundaryConfig (G := G) A R
  invFun bdry' := fun f => bdry' (regionBoundaryEdgeComplEquiv (G := G) R f)
  left_inv bdry := by
    funext f
    show regionComplementBoundaryConfig (G := G) A R bdry
      (regionBoundaryEdgeComplEquiv (G := G) R f) = bdry f
    rw [regionComplementBoundaryConfig]
    congr 1
  right_inv bdry' := by
    funext g
    show regionComplementBoundaryConfig (G := G) A R
      (fun f => bdry' (regionBoundaryEdgeComplEquiv (G := G) R f)) g = bdry' g
    rw [regionComplementBoundaryConfig]
    congr 1

@[simp] theorem regionComplementBoundaryConfigEquiv_apply (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfigEquiv (G := G) A R bdry =
      regionComplementBoundaryConfig (G := G) A R bdry := rfl

/-- The complement boundary configuration reads the boundary edge `f` of `R`,
viewed on the complement as `regionBoundaryEdgeToCompl R f`, off the original
boundary value at `f`. -/
theorem regionComplementBoundaryConfig_apply_toCompl (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G) A R bdry (regionBoundaryEdgeToCompl (G := G) R f) =
      bdry f := by
  rw [regionComplementBoundaryConfig]
  congr 1

/-- Applying the complement boundary-configuration reindexing twice (for `R` and
then for `univ \ R`) is the double-complement boundary-configuration transport. -/
theorem regionComplementBoundaryConfig_compl_compl (A : Tensor G d) (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionComplementBoundaryConfig (G := G) A (Finset.univ \ R)
        (regionComplementBoundaryConfig (G := G) A R bdry) =
      regionDoubleComplBoundaryConfig (G := G) A R bdry := by
  funext g
  rw [regionComplementBoundaryConfig, regionComplementBoundaryConfig,
    regionDoubleComplBoundaryConfig]
  rfl

end PEPS
end TNLean
