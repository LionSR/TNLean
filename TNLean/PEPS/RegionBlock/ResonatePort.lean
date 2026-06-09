import TNLean.PEPS.RegionBlock.OpenLegsResonate

/-!
# Block-granularity port of the edge resonate engine

This file ports the **edge resonate engine** of `TNLean.PEPS.InsertionRealization`
(the construction `physical_to_virtual_insertion`, lines 501--963) to the
granularity of the three injective region blocks, closing the residual open fact of
the general normal PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964,
Section 3, Lemma `inj_isomorph`, the step `V=W`).

The block-frame foundation (`TNLean.PEPS.RegionBlock.OpenLegsResonate`,
`TNLean.PEPS.RegionBlock.BasisChangeIntertwine`) has reduced the predicate
`TransferRowIsRegionRow` — equivalently `IsBondLocalTransferKernel`, equivalently the
basis-change intertwining — to the single **coefficient transfer**: for every
inserted matrix `M` on the boundary edge `f` of the red region there is a matrix `N`
on the second tensor's bond with `regionInsertedCoeff A R f M = regionInsertedCoeff
B R f N` at every physical configuration. Every reformulation is an unconditional
repackaging of this one fact.

This file supplies the port that produces that `N`. The mapping from the edge engine
to the block frame is:

* the two endpoints of the chosen edge map to the **red region** `R` and its **host**
  `univ \ R` (the two blocked endpoints of the single boundary edge `f`);
* the residual local configuration on an endpoint maps to the boundary configuration
  away from the `f`-leg (the **residual boundary configuration**);
* the per-vertex left inverse `localLeftInverseAt` maps to the **region blocked left
  inverse** `regionBlockedLeftInverse` (`TNLean.PEPS.RegionBlock.Recovery5`);
* the row insertion of `M` on the bond maps to `rowInsertF`
  (`TNLean.PEPS.RegionBlock.BlockRealization`).

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, the step `V=W`, lines 355--486 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The `f`-leg split of a region boundary configuration

A region boundary configuration `μ : RegionBoundaryConfig A R` assigns a virtual
index to every edge crossing the boundary of `R`. Splitting off the distinguished
boundary edge `f` leaves the **residual boundary configuration**: the assignment on
the remaining boundary edges. This is the block-frame analogue of the edge engine's
`localVirtualConfigSplitAt` (`TNLean.PEPS.VirtualInsertion`), which splits a local
virtual configuration into the coordinate on one distinguished incident edge and the
coordinates on the rest.

Two boundary configurations agree away from `f` (`SameAwayFromBond f μ ν`) exactly
when their residual boundary configurations coincide, so the residual configuration
is the natural index for the residual-independence the resonate inversion supplies. -/

/-- The **residual boundary configuration** of `R` at the boundary edge `f`: an
assignment of virtual indices to every boundary edge of `R` other than `f`. This is
the boundary-configuration analogue of the edge engine's residual local
configuration `ResidualLocalConfig` (`TNLean.PEPS.VirtualInsertion`), which assigns
indices to the incident edges other than the distinguished one. -/
abbrev RegionResidualBoundaryConfig (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : Type _ :=
  (g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) →
    Fin (A.bondDim g.1.1)

instance instFintypeRegionResidualBoundaryConfig (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    Fintype (RegionResidualBoundaryConfig (G := G) A R f) :=
  inferInstance

/-- **The `f`-leg split of a region boundary configuration.** A region boundary
configuration corresponds to its index on the distinguished boundary edge `f`
together with its residual boundary configuration on the remaining boundary edges.
This is the block-frame port of `localVirtualConfigSplitAt`
(`TNLean.PEPS.VirtualInsertion`, line 73). -/
noncomputable def regionBoundaryConfigSplitAt (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    RegionBoundaryConfig (G := G) A R ≃
      Fin (A.bondDim f.1) × RegionResidualBoundaryConfig (G := G) A R f := by
  classical
  exact Equiv.piSplitAt f (fun g => Fin (A.bondDim g.1))

omit [Fintype V] in
@[simp] theorem regionBoundaryConfigSplitAt_apply_fst (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R) :
    (regionBoundaryConfigSplitAt (G := G) A R f μ).1 = μ f := by
  classical
  simp [regionBoundaryConfigSplitAt]

omit [Fintype V] in
@[simp] theorem regionBoundaryConfigSplitAt_apply_snd (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ : RegionBoundaryConfig (G := G) A R)
    (g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) :
    (regionBoundaryConfigSplitAt (G := G) A R f μ).2 g = μ g.1 := by
  classical
  simp [regionBoundaryConfigSplitAt]

omit [Fintype V] in
@[simp] theorem regionBoundaryConfigSplitAt_symm_apply_self (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (x : Fin (A.bondDim f.1) × RegionResidualBoundaryConfig (G := G) A R f) :
    (regionBoundaryConfigSplitAt (G := G) A R f).symm x f = x.1 := by
  classical
  simp [regionBoundaryConfigSplitAt]

omit [Fintype V] in
@[simp] theorem regionBoundaryConfigSplitAt_symm_apply_other (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (x : Fin (A.bondDim f.1) × RegionResidualBoundaryConfig (G := G) A R f)
    (g : {g : {g : Edge G // IsRegionBoundaryEdge (G := G) R g} // g ≠ f}) :
    (regionBoundaryConfigSplitAt (G := G) A R f).symm x g.1 = x.2 g := by
  classical
  simp [regionBoundaryConfigSplitAt, g.2]

omit [Fintype V] in
/-- **The `f`-leg split characterizes `SameAwayFromBond`.** Two region boundary
configurations agree away from the boundary edge `f` exactly when their residual
boundary configurations — the second components of the `f`-leg split — coincide.
This is the block-frame port of the edge engine's identification of the residual
local configuration with the agreement away from the distinguished incident edge. -/
theorem sameAwayFromBond_iff_split_snd_eq (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (μ ν : RegionBoundaryConfig (G := G) A R) :
    SameAwayFromBond f μ ν ↔
      (regionBoundaryConfigSplitAt (G := G) A R f μ).2 =
        (regionBoundaryConfigSplitAt (G := G) A R f ν).2 := by
  classical
  constructor
  · intro h
    funext g
    rw [regionBoundaryConfigSplitAt_apply_snd, regionBoundaryConfigSplitAt_apply_snd]
    exact h g.1 g.2
  · intro h g hg
    have := congrFun h ⟨g, hg⟩
    rwa [regionBoundaryConfigSplitAt_apply_snd, regionBoundaryConfigSplitAt_apply_snd] at this

end PEPS
end TNLean
