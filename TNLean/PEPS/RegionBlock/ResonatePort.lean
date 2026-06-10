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

/-! ### The `f`-leg reading of the region row

The first tensor's own region row `regionRegionRow A R f M τ` is, by construction, the
row insertion of `M` on the boundary edge `f` of the complement weight row
(`regionRegionRow_eq_rowInsertF`, `TNLean.PEPS.RegionBlock.BlockRealization`): it
couples the boundary configurations only through their `f`-legs, through the single
matrix `M`. Read through the `f`-leg split, the region row at a boundary configuration
`μ` depends on `μ` only through its `f`-leg `μ f` and its residual boundary
configuration, with `M` coupling the `f`-leg. This is the block-frame port of the
edge engine's residual factoring of the boundary contraction. -/

open scoped Classical in
/-- **The region row through the `f`-leg split.** The first tensor's region row at a
boundary configuration `μ`, written through the `f`-leg split, is the sum over bond
indices `b` on `f` of `M (μ f) b` against the complement weight row of the boundary
configuration with `f`-leg `b` and the residual of `μ`. This exposes the region row's
`f`-locality: `μ` enters only through its `f`-leg and its residual boundary
configuration.

This is the block-frame port of the edge engine's residual reading of the boundary
contraction (`edgeLeftLocalConfig`/`edgeRightLocalConfig` against the residual), with
the single distinguished incident edge `f` and the residual boundary configuration in
place of the residual local configuration.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionRegionRow_split (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (μ : RegionBoundaryConfig (G := G) A R) :
    regionRegionRow (G := G) A R f M τ μ =
      ∑ b : Fin (A.bondDim f.1),
        M (μ f) b *
          regionComplementWeightRow (G := G) A R τ
            ((regionBoundaryConfigSplitAt (G := G) A R f).symm
              (b, (regionBoundaryConfigSplitAt (G := G) A R f μ).2)) := by
  classical
  rw [regionRegionRow_eq_rowInsertF, rowInsertF_apply]
  -- Reindex the `ν`-sum by the `f`-leg split: `ν ↔ (ν f, residual ν)`.
  rw [← Equiv.sum_comp (regionBoundaryConfigSplitAt (G := G) A R f).symm
    (fun ν : RegionBoundaryConfig (G := G) A R =>
      (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
        regionComplementWeightRow (G := G) A R τ ν)]
  -- Split the product index over `(b, residual)`; only `residual = residual μ` survives.
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_eq_single (regionBoundaryConfigSplitAt (G := G) A R f μ).2]
  · rw [regionBoundaryConfigSplitAt_symm_apply_self]
    have hsame : SameAwayFromBond f μ
        ((regionBoundaryConfigSplitAt (G := G) A R f).symm
          (b, (regionBoundaryConfigSplitAt (G := G) A R f μ).2)) := by
      rw [sameAwayFromBond_iff_split_snd_eq, Equiv.apply_symm_apply]
    rw [if_pos hsame]
  · intro res _ hres
    have hne : ¬ SameAwayFromBond f μ
        ((regionBoundaryConfigSplitAt (G := G) A R f).symm (b, res)) := by
      rw [sameAwayFromBond_iff_split_snd_eq, Equiv.apply_symm_apply]
      exact fun h => hres h.symm
    rw [if_neg hne, zero_mul]
  · intro hres; exact absurd (Finset.mem_univ _) hres

/-! ### The complement-side block realization operator (the blue endpoint)

The block realization operator is region-polymorphic, so instantiating it at the
**host** region `univ \ R` and the boundary edge `f' := regionBoundaryEdgeToCompl R f`
(the same underlying edge reread on the complement) with the transposed matrix
`Mᵀ` gives the **complement-side realization**. This is the block-frame port of the
edge engine's left-endpoint insertion operator: where the edge engine builds the
left-endpoint operator from the transposed matrix on the same bond, the block frame
builds the host-block realization from `Mᵀ` on the same boundary edge.

Applied to the host interior-bond multiple of the second tensor's partial state
across the host cut at the double-complement transport of a region physical
configuration `σ`, it recovers the first tensor's region-inserted coefficient of `M`,
read as a function of the complement physical leg `τ`. This is the complement-side
reading the region resonate step equates with the region-side reading
`regionInsertedCoeff_eq_blockRealizeOp_regionPartialState_B`
(`TNLean.PEPS.RegionBlock.OpenLegsResonate`). -/

/-- **The complement-side reading of the first tensor's coefficient.** The first
tensor's region-inserted coefficient of `M`, read as a function of the complement
physical leg `τ`, is the host-block realization operator of `Mᵀ` (the block
realization operator at the region `univ \ R` and the boundary edge
`regionBoundaryEdgeToCompl R f`) applied to the host interior-bond multiple of the
**second** tensor's partial state across the host cut at the double-complement
transport of `σ`.

This is the complement-side companion of
`regionInsertedCoeff_eq_blockRealizeOp_regionPartialState_B`
(`TNLean.PEPS.RegionBlock.OpenLegsResonate`): the same landed open-legs transport,
instanced at the host region through the cast identity
`regionInsertedCoeff_eq_compl` (`TNLean.PEPS.RegionBlock.Recovery6`). It supplies the
blue-endpoint reading the two-endpoint reconcile equates with the red-endpoint
reading.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, `eq:resonate`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem regionInsertedCoeff_eq_blockRealizeOp_complementPartialState_B (A B : Tensor G d)
    (R : Finset V) (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hAB : SameState A B) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    (fun τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R) =>
        regionInsertedCoeff (G := G) A R f M σ τ) =
      blockRealizeOp (G := G) A (Finset.univ \ R) hCA
        (regionBoundaryEdgeToCompl (G := G) R f) M.transpose
        ((regionInteriorBondProd (G := G) B (Finset.univ \ R) : ℂ) •
          regionPartialState (G := G) B (Finset.univ \ R)
            (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)) := by
  have h := regionInsertedCoeff_eq_blockRealizeOp_regionPartialState_B A B (Finset.univ \ R)
    hCA hAB hDim (regionBoundaryEdgeToCompl (G := G) R f) M.transpose
    (regionDoubleComplPhysicalConfig (V := V) (d := d) R σ)
  -- The host-region reading of the coefficient through the cast identity.
  funext τ
  rw [regionInsertedCoeff_eq_compl A R f M σ τ]
  exact congrFun h τ

/-! ### The incident kernel as the region row through the `f`-leg split

The incident-matrix kernel `incidentKernel B R f N`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) and the second tensor's region row
`regionRegionRow B R f N` are
the same `f`-coupling read on the two boundary-configuration index sets — the
complement boundary configuration of `R` versus the boundary configuration of
`univ \ R` — bridged by the complement boundary-configuration equivalence. This pins
the bond-locality predicate to the region-row predicate: the transfer kernel is the
incident kernel of `N` exactly when the transferred row is the region row of `N`. -/

open scoped Classical in
/-- **The incident kernel is the complement blocked map of the region row.** The
boundary-configuration sum of the incident-matrix kernel of `N` against the second
tensor's complement blocked weights, at a region boundary configuration `μ`, is the
second tensor's region row of `N` at `μ`, read as a function of the complement
physical leg. This identifies the incident kernel with the region row through the
complement block, the bridge between the bond-locality predicate and the region-row
predicate.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem incidentKernel_complement_blockedMap_eq_regionRegionRow (B : Tensor G d)
    (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionBlockedTensorMap (G := G) B (Finset.univ \ R)
        (incidentKernel (G := G) B R f N μ) τ =
      regionRegionRow (G := G) B R f N τ μ := by
  classical
  rw [regionBlockedTensorMap_apply, regionRegionRow]
  -- Reindex the complement-boundary `ν'`-sum of the left side by the complement
  -- boundary-configuration equivalence to the region-boundary `ν`-sum of the region row.
  set E := regionComplementBoundaryConfigEquiv (G := G) B R with hE
  rw [← Equiv.sum_comp E
    (fun ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R) =>
      incidentKernel (G := G) B R f N μ ν' •
        regionBlockedWeight (G := G) B (Finset.univ \ R) ν' τ)]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [incidentKernel, smul_eq_mul, hE, Equiv.symm_apply_apply,
    regionComplementBoundaryConfigEquiv_apply]

/-! ### The region-row predicate is the bond-locality of the transfer kernel

The transferred row `blockTransferRow A B R f M`, as a function of the complement
physical leg at a region boundary configuration `μ`, is the second tensor's
complement blocked tensor map of the transfer kernel `transferCoeff … M μ`
(`blockTransferRow_eq_complement_blockedMap`,
`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`). The second tensor's region row
`regionRegionRow B R f N`, as a function of the complement physical leg at `μ`, is the
complement blocked tensor map of the incident kernel `incidentKernel B R f N μ`
(`incidentKernel_complement_blockedMap_eq_regionRegionRow`). Since the second tensor's
complement block is injective, the transferred row equals the region row of `N` at
every complement leg if and only if the transfer kernel of `M` equals the incident
kernel of `N`. This identifies the region-row predicate `TransferRowIsRegionRow` with
the bond-locality predicate `IsBondLocalTransferKernel`, both reading the same `N`. -/

/-- **The transferred row is the region row of `N` exactly when the transfer kernel is
the incident kernel of `N`.** For a fixed bond matrix `N`, the transferred row
`blockTransferRow A B R f M` equals the second tensor's region row
`regionRegionRow B R f N` at every complement physical leg if and only if the transfer
kernel `transferCoeff … M` equals the incident kernel `incidentKernel B R f N`.

The transferred row, as a function of the complement physical leg at a region boundary
configuration `μ`, is the complement blocked tensor map of `transferCoeff … M μ`; the
region row is the complement blocked tensor map of `incidentKernel B R f N μ`. The
second tensor's complement block is injective (`hCB`), so the two rows coincide at
every leg if and only if the two kernels coincide.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem blockTransferRow_eq_regionRegionRow_iff_transferCoeff_eq_incidentKernel
    (A B : Tensor G d) (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    (∀ τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R),
        blockTransferRow A B R hRB f M τ = regionRegionRow (G := G) B R f N τ) ↔
      transferCoeff (G := G) A B R hRB hCB f M = incidentKernel (G := G) B R f N := by
  constructor
  · -- Equal rows reblock through the complement block to equal kernels.
    intro hrow
    funext μ
    refine regionBlockedTensorMap_injective_of_injective (G := G) B (Finset.univ \ R) hCB ?_
    funext τ
    rw [← blockTransferRow_eq_complement_blockedMap A B R hRA hRB hCB hAB hposA hposB hDim f M μ,
      incidentKernel_complement_blockedMap_eq_regionRegionRow B R f N μ τ]
    exact congrFun (hrow τ) μ
  · -- Equal kernels reblock through the complement block to equal rows.
    intro hker τ
    funext μ
    have hμ := congrFun hker μ
    have hcompl := congrFun
      (blockTransferRow_eq_complement_blockedMap A B R hRA hRB hCB hAB hposA hposB hDim f M μ) τ
    rw [hμ] at hcompl
    rw [hcompl, incidentKernel_complement_blockedMap_eq_regionRegionRow B R f N μ τ]

/-- **The region-row predicate is the bond-locality predicate (kernel route).** The
transferred-row region-row predicate `TransferRowIsRegionRow` holds if and only if the
transfer kernel is bond-local (`IsBondLocalTransferKernel`). Both quantify, over every
inserted matrix `M`, the existence of a bond matrix `N`; per `N` the equivalence is the
per-leg complement-block reblocking
`blockTransferRow_eq_regionRegionRow_iff_transferCoeff_eq_incidentKernel`.

This is a direct kernel-level proof of the equivalence
`isBondLocalTransferKernel_iff_transferRowIsRegionRow`
(`TNLean.PEPS.RegionBlock.OpenLegsResonate`), reading both predicates against the same
witness `N` through the complement block, without passing through the coefficient
transfer.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem transferRowIsRegionRow_iff_isBondLocalTransferKernel (A B : Tensor G d)
    (R : Finset V)
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (hAB : SameState A B) (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hposB : ∀ e : Edge G, 0 < B.bondDim e) (hDim : A.bondDim = B.bondDim)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    TransferRowIsRegionRow (G := G) A B R hRB f ↔
      IsBondLocalTransferKernel (G := G) A B R hRB hCB f := by
  unfold TransferRowIsRegionRow IsBondLocalTransferKernel
  refine forall_congr' (fun M => exists_congr (fun N => ?_))
  exact blockTransferRow_eq_regionRegionRow_iff_transferCoeff_eq_incidentKernel A B R hRA hRB
    hCB hAB hposA hposB hDim f M N

end PEPS
end TNLean
