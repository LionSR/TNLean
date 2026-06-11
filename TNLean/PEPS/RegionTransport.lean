import TNLean.PEPS.IsoTransport
import TNLean.PEPS.RegionBlock.Basic

/-!
# Transport of blocked-region injectivity along a graph isomorphism

A graph isomorphism `φ : G ≃g G'` carries a finite vertex region `R` of `G` to its
image region `R.map φ.toEquiv.toEmbedding` of `G'`.  The blocked-region weight of the
transported tensor `A.transport φ` over that image region is a relabelling of the
blocked-region weight of `A` over `R`: the boundary edges, the open virtual legs, and
the physical legs on the region all carry across by the edge action `Edge.map φ` and
the vertex bijection `φ` (`regionBlockedWeight_transport`).  Linear independence is a
relabelling invariant, so blocked-region injectivity transports
(`regionBlockedTensorInjective_transport`).

This is the geometric covariance that turns one reference blocking datum on the torus
into blocking data at every translate of the reference edge: a translation-invariant
tensor satisfies `A.transport (translate a b) = A`, so the transported region datum is
a datum for the *same* tensor at the translated edge
(`TNLean/PEPS/TorusTranslationInvariant.lean`).

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V W : Type*} [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  {G : SimpleGraph V} {G' : SimpleGraph W} {d : ℕ}
variable [DecidableRel G.Adj] [DecidableRel G'.Adj]

/-! ### The image region of a graph isomorphism -/

/-- The image of a finite region `R` of `G` under the vertex bijection of `φ`. -/
def Region.map (φ : G ≃g G') (R : Finset V) : Finset W :=
  R.map φ.toEquiv.toEmbedding

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
@[simp] theorem mem_Region_map (φ : G ≃g G') (R : Finset V) (w : W) :
    w ∈ Region.map φ R ↔ φ.symm w ∈ R := by
  simp only [Region.map, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [show (φ.toEquiv : V → W) v = φ v from rfl,
      show φ.symm (φ v) = v from φ.symm_apply_apply v]; exact hv
  · intro h
    refine ⟨φ.symm w, h, ?_⟩
    rw [show (φ.toEquiv : V → W) (φ.symm w) = φ (φ.symm w) from rfl, φ.apply_symm_apply w]

omit [Fintype V] [LinearOrder V] [Fintype W] [LinearOrder W]
  [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- A vertex `v` lies in `R` iff `φ v` lies in the image region. -/
theorem mem_Region_map_apply (φ : G ≃g G') (R : Finset V) (v : V) :
    φ v ∈ Region.map φ R ↔ v ∈ R := by
  rw [mem_Region_map]
  rw [show φ.symm (φ v) = v from φ.symm_apply_apply v]

/-! ### Covariance of the region boundary -/

omit [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- An edge `f` of `G` crosses the boundary of `R` iff its image `Edge.map φ f`
crosses the boundary of the image region.  The endpoints carry across by `φ`, which
preserves membership in `R`. -/
theorem isRegionBoundaryEdge_map (φ : G ≃g G') (R : Finset V) (f : Edge G) :
    IsRegionBoundaryEdge (G := G') (Region.map φ R) (Edge.map φ f) ↔
      IsRegionBoundaryEdge (G := G) R f := by
  have key : ∀ x : V, x ∈ R ↔ φ x ∈ Region.map φ R := fun x =>
    (mem_Region_map_apply φ R x).symm
  rw [IsRegionBoundaryEdge, IsRegionBoundaryEdge]
  rcases Edge.map_endpoints φ f with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, ← key, ← key]
  · rw [h1, h2, ← key, ← key]; tauto

/-! ### Reindexing equivalences of region index types -/

/-- The boundary edges of the image region correspond to the boundary edges of `R`
by the inverse edge action `Edge.map φ.symm`. -/
def regionBoundaryEdgeMapEquiv (φ : G ≃g G') (R : Finset V) :
    {f : Edge G' // IsRegionBoundaryEdge (G := G') (Region.map φ R) f} ≃
      {f : Edge G // IsRegionBoundaryEdge (G := G) R f} where
  toFun f := ⟨Edge.map φ.symm f.1, by
    have h := isRegionBoundaryEdge_map φ R (Edge.map φ.symm f.1)
    rw [Edge.map_map_symm] at h
    exact h.mp f.2⟩
  invFun f := ⟨Edge.map φ f.1, (isRegionBoundaryEdge_map φ R f.1).mpr f.2⟩
  left_inv f := by apply Subtype.ext; simp [Edge.map_map_symm]
  right_inv f := by apply Subtype.ext; simp [Edge.map_symm_map]

/-- The vertices of the image region correspond to the vertices of `R` by `φ`. -/
def regionVertexMapEquiv (φ : G ≃g G') (R : Finset V) :
    {w : W // w ∈ Region.map φ R} ≃ {w : V // w ∈ R} where
  toFun w := ⟨φ.symm w.1, (mem_Region_map φ R w.1).mp w.2⟩
  invFun w := ⟨φ w.1, (mem_Region_map_apply φ R w.1).mpr w.2⟩
  left_inv w := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

/-! ### Transport of the blocked-region weight

The blocked-region weight of `A.transport φ` over the image region is the blocked-region
weight of `A` over `R`, after relabelling the open boundary legs by `Edge.map φ` and the
physical legs by `φ`.  The bond dimension of `A.transport φ` at a boundary edge `f'` of the
image region is, by definition, `A.bondDim (Edge.map φ.symm f')`, so the boundary index types
match definitionally under `regionBoundaryEdgeMapEquiv`. -/

/-- The boundary-configuration equivalence induced by the edge action: relabel the open
boundary legs along `regionBoundaryEdgeMapEquiv`.  Built as a `piCongrLeft'`, so it is an
honest equivalence; the bond dimensions match because
`(A.transport φ).bondDim f' = A.bondDim (Edge.map φ.symm f')` by definition. -/
def regionBoundaryConfigMapEquiv (A : Tensor G d) (φ : G ≃g G') (R : Finset V) :
    RegionBoundaryConfig (G := G) A R ≃
      RegionBoundaryConfig (G := G') (A.transport φ) (Region.map φ R) :=
  Equiv.piCongrLeft' (fun f => Fin (A.bondDim f.1)) (regionBoundaryEdgeMapEquiv φ R).symm

/-- The boundary configuration on the image region induced from one on `R` by the edge
action.  The bond dimensions match definitionally:
`(A.transport φ).bondDim f' = A.bondDim (Edge.map φ.symm f')`. -/
def regionBoundaryConfigMap (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    RegionBoundaryConfig (G := G') (A.transport φ) (Region.map φ R) :=
  fun f => bdry (regionBoundaryEdgeMapEquiv φ R f)

omit [Fintype V] [Fintype W] in
/-- The boundary-configuration map is the forward direction of its equivalence. -/
theorem regionBoundaryConfigMapEquiv_apply (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (bdry : RegionBoundaryConfig (G := G) A R) :
    regionBoundaryConfigMapEquiv A φ R bdry = regionBoundaryConfigMap A φ R bdry :=
  rfl

/-- The physical configuration on the image region induced from one on `R` by `φ`. -/
def regionPhysicalConfigMap (φ : G ≃g G') (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    RegionPhysicalConfig (V := W) (d := d) (Region.map φ R) :=
  fun w => τ (regionVertexMapEquiv φ R w)

omit [Fintype V] [Fintype W] in
/-- The boundary-configuration map is injective. -/
theorem regionBoundaryConfigMap_injective (A : Tensor G d) (φ : G ≃g G') (R : Finset V) :
    Function.Injective (regionBoundaryConfigMap A φ R) := by
  have h : regionBoundaryConfigMap A φ R = regionBoundaryConfigMapEquiv A φ R := by
    funext bdry; rw [regionBoundaryConfigMapEquiv_apply]
  rw [h]; exact (regionBoundaryConfigMapEquiv A φ R).injective

omit [Fintype V] [Fintype W] in
/-- The boundary label that `(vcEquiv A φ).symm η` reads on the image region is the
forward boundary-configuration map of the boundary label that `η` reads on `R`. -/
theorem regionBoundaryLabel_transport (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (η : VirtualConfig A) :
    regionBoundaryLabel (G := G') (A.transport φ) (Region.map φ R) ((vcEquiv A φ).symm η) =
      regionBoundaryConfigMap A φ R (regionBoundaryLabel (G := G) A R η) := by
  funext f
  simp only [regionBoundaryLabel_apply, regionBoundaryConfigMap, vcEquiv_symm_apply]
  rfl

omit [Fintype V] [Fintype W] in
/-- The transported virtual configuration carries the boundary label `bdry'` iff the
original configuration carries the preimage boundary label.  Used to reindex the
filtered sum in the blocked-region weight. -/
theorem regionBoundaryLabel_transport_iff (A : Tensor G d) (φ : G ≃g G') (R : Finset V)
    (η : VirtualConfig A) (bdry : RegionBoundaryConfig (G := G) A R) :
    regionBoundaryLabel (G := G') (A.transport φ) (Region.map φ R) ((vcEquiv A φ).symm η) =
        regionBoundaryConfigMap A φ R bdry ↔
      regionBoundaryLabel (G := G) A R η = bdry := by
  rw [regionBoundaryLabel_transport]
  exact (regionBoundaryConfigMap_injective A φ R).eq_iff

end PEPS
end TNLean
