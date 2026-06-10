import TNLean.PEPS.RegionBlock.ThreeBlockResonateAB2

/-!
# The witness extraction for the cross-tensor three-block normal PEPS V=W

This file performs the **witness extraction** that closes the residual open content of
the general normal PEPS Fundamental Theorem per-edge gauge (arXiv:1804.04964, Section 3,
Lemma `inj_isomorph`, the step `V=W`), given the blue-collapse frame
`TNLean.PEPS.RegionBlock.ThreeBlockResonateAB2`.

The landed block-frame foundation has reduced the per-edge gauge to a single predicate,
`IsBondLocalTransferKernel` (`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`): for every
inserted matrix `M` on the boundary edge `f` of the shared red region, the cross-tensor
transfer kernel `transferCoeff A B red f M` is the incident-matrix kernel
`incidentKernel B red f N` of some bond matrix `N` on `f`. By the `f`-leg split
criterion `transferCoeff_eq_incidentKernel_iff_split`
(`TNLean.PEPS.RegionBlock.ResonatePort2`), this holds with a given `N` exactly when the
transfer kernel, read through the `f`-leg split, couples the two boundary configurations
only through their `f`-legs through `N` — that is, it vanishes off the diagonal of the
two residual boundary configurations and reads `N` on the matching `f`-leg.

## The witness

This file constructs the candidate witness `N` directly from `M`: a **reference residual
boundary configuration** is fixed (the all-zero residual, available because every bond
dimension is positive), and `N a b` is read off as the transfer-kernel value at the two
boundary configurations whose `f`-legs are `a`, `b` and whose residual is the reference.
This is the read-off the resonate inversion produces: the `f`-leg matrix entries of the
collapsed coupling at the reference residual.

The **residual-independence** equation — that the transfer kernel at *any* residual
equals the reference value on the `f`-legs and vanishes off the residual diagonal — is
the remaining content. With it, the witness `N` realizes the bond locality and the
per-edge gauge follows mechanically.

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

/-! ### The reference residual boundary configuration

A residual boundary configuration of `R` at the boundary edge `f` assigns a virtual
index to every boundary edge other than `f`. Reading the all-zero index on each (legal
because every bond dimension is positive) gives a distinguished **reference residual**,
the frame at which the witness matrix is read off. This is the block-frame analogue of
the edge engine's reference residual local configuration. -/

/-- **The reference residual boundary configuration.** The residual boundary
configuration of `R` at `f` that reads the zero index on every boundary edge other than
`f`. The zero index is legal because every bond dimension is positive (`hpos`).

This is the distinguished residual frame at which the witness matrix is read off, the
block-frame port of the edge engine's reference residual local configuration.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
def referenceResidualBoundaryConfig (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hpos : ∀ g : Edge G, 0 < B.bondDim g) :
    RegionResidualBoundaryConfig (G := G) B R f :=
  fun g => ⟨0, hpos g.1.1⟩

/-- The region boundary configuration with `f`-leg `a` and the reference residual. -/
noncomputable def referenceBoundaryConfigAt (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hpos : ∀ g : Edge G, 0 < B.bondDim g) (a : Fin (B.bondDim f.1)) :
    RegionBoundaryConfig (G := G) B R :=
  (regionBoundaryConfigSplitAt (G := G) B R f).symm
    (a, referenceResidualBoundaryConfig (G := G) B R f hpos)

omit [Fintype V] in
@[simp] theorem referenceBoundaryConfigAt_fLeg (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hpos : ∀ g : Edge G, 0 < B.bondDim g) (a : Fin (B.bondDim f.1)) :
    referenceBoundaryConfigAt (G := G) B R f hpos a f = a := by
  rw [referenceBoundaryConfigAt, regionBoundaryConfigSplitAt_symm_apply_self]

omit [Fintype V] in
@[simp] theorem referenceBoundaryConfigAt_residual (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hpos : ∀ g : Edge G, 0 < B.bondDim g) (a : Fin (B.bondDim f.1)) :
    (regionBoundaryConfigSplitAt (G := G) B R f
        (referenceBoundaryConfigAt (G := G) B R f hpos a)).2 =
      referenceResidualBoundaryConfig (G := G) B R f hpos := by
  rw [referenceBoundaryConfigAt, Equiv.apply_symm_apply]

/-! ### The witness matrix

The witness matrix `N` of `M` is read off the cross-tensor transfer kernel
`transferCoeff A B red f M` at the reference residual: its `(a, b)` entry is the
transfer-kernel value at the region boundary configuration with `f`-leg `a` and
reference residual, against the complement boundary configuration whose underlying
region boundary configuration has `f`-leg `b` and reference residual. This is the
`f`-leg matrix entry the resonate inversion produces. -/

/-- **The witness matrix.** The bond matrix on `f` read off the cross-tensor transfer
kernel of `M` at the reference residual: `N a b` is the transfer-kernel value at the
region boundary configuration with `f`-leg `a` and reference residual, against the
complement boundary configuration of the region boundary configuration with `f`-leg `b`
and reference residual.

This is the explicit candidate witness of the step `V=W`: the `f`-leg matrix entries of
the collapsed coupling at the reference residual frame. The residual-independence of the
transfer kernel — that its value at any residual is read by this same `N` — is the
remaining content the resonate inversion supplies.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def witnessMatrix (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ :=
  fun a b =>
    transferCoeff (G := G) A B R hRB hCB f M
      (referenceBoundaryConfigAt (G := G) B R f hposB a)
      (regionComplementBoundaryConfigEquiv (G := G) B R
        (referenceBoundaryConfigAt (G := G) B R f hposB b))

/-! ### The residual-independence equation

The remaining content of the step `V=W` is the **residual-independence** of the
cross-tensor transfer kernel: at every pair of boundary configurations, the kernel value
is the reference-frame matrix entry `witnessMatrix … M` on the `f`-legs, gated by the
agreement of the two residual boundary configurations. This is the `f`-leg-split form of
the bond-locality target `transferCoeff M = incidentKernel N` of
`transferCoeff_eq_incidentKernel_iff_split` (`TNLean.PEPS.RegionBlock.ResonatePort2`),
specialized to the explicit witness `witnessMatrix`. -/

/-- **The residual-independence predicate.** The cross-tensor transfer kernel of `M`, at
every pair `(μ, ν')`, equals the witness-matrix entry on the `f`-legs of `μ` and of the
underlying region boundary configuration of `ν'`, when the residual boundary
configurations of `μ` and of that underlying configuration agree, and `0` otherwise.

This is the `f`-leg-split bond-locality condition of `transferCoeff_eq_incidentKernel_iff_split`
(`TNLean.PEPS.RegionBlock.ResonatePort2`) at the explicit witness `witnessMatrix`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
def TransferKernelResidualIndependent (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) : Prop :=
  ∀ (μ : RegionBoundaryConfig (G := G) B R)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)),
    transferCoeff (G := G) A B R hRB hCB f M μ ν' =
      (if (regionBoundaryConfigSplitAt (G := G) B R f μ).2 =
            (regionBoundaryConfigSplitAt (G := G) B R f
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν')).2 then
          witnessMatrix (G := G) A B R hRB hCB f hposB M (μ f)
            (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f)
        else 0)

/-- **The residual-independence equation gives the bond locality at the witness.** If the
cross-tensor transfer kernel of `M` is residual-independent, then it is the
incident-matrix kernel of the witness matrix `witnessMatrix … M`.

This is the `f`-leg-split criterion `transferCoeff_eq_incidentKernel_iff_split`
(`TNLean.PEPS.RegionBlock.ResonatePort2`) read in the reverse direction at the explicit
witness `N := witnessMatrix … M`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_eq_incidentKernel_witnessMatrix_of_residualIndependent
    (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (hM : TransferKernelResidualIndependent (G := G) A B R hRB hCB f hposB M) :
    transferCoeff (G := G) A B R hRB hCB f M =
      incidentKernel (G := G) B R f (witnessMatrix (G := G) A B R hRB hCB f hposB M) :=
  (transferCoeff_eq_incidentKernel_iff_split A B R hRB hCB f M
    (witnessMatrix (G := G) A B R hRB hCB f hposB M)).mpr hM

/-! ### Bond locality from residual independence in both directions

Residual independence of every transfer kernel is exactly the bond locality predicate
`IsBondLocalTransferKernel` (`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`), with the
witness carried by `witnessMatrix`. Supplying it in both directions feeds the per-edge
gauge `SharedNormalEdgeBlockingData.exists_regionEdgeGauge`
(`TNLean.PEPS.RegionBlock.ThreeBlockTransfer`) unconditionally. -/

/-- **Bond locality from residual independence.** If every cross-tensor transfer kernel
of an inserted matrix `M` on the boundary edge `f` is residual-independent, then the
transfer kernel is bond-local (`IsBondLocalTransferKernel`), with the witness the
explicit `witnessMatrix … M`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem isBondLocalTransferKernel_of_residualIndependent (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (hposB : ∀ g : Edge G, 0 < B.bondDim g)
    (hres : ∀ M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ,
      TransferKernelResidualIndependent (G := G) A B R hRB hCB f hposB M) :
    IsBondLocalTransferKernel (G := G) A B R hRB hCB f :=
  fun M =>
    ⟨witnessMatrix (G := G) A B R hRB hCB f hposB M,
      transferCoeff_eq_incidentKernel_witnessMatrix_of_residualIndependent A B R hRB hCB f
        hposB M (hres M)⟩

end PEPS
end TNLean
