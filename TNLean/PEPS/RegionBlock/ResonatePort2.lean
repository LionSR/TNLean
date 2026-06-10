import TNLean.PEPS.RegionBlock.ResonatePort

/-!
# Block-granularity port of the edge resonate inversion (the bond matrix `N`)

This file continues `TNLean.PEPS.RegionBlock.ResonatePort`, porting the **endpoint
inversions** and the **reconcile** of the edge resonate engine of
`TNLean.PEPS.InsertionRealization` (the construction `physical_to_virtual_insertion`,
lines 579--963) to the granularity of the three injective region blocks.

The landed reductions (`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`,
`TNLean.PEPS.RegionBlock.BasisChangeIntertwine`) have isolated the single residual
open fact of the general normal PEPS Fundamental Theorem per-edge gauge
(arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`) as the **coefficient
transfer**: for every inserted matrix `M` on the boundary edge `f` of the red region
there is a matrix `N` on the second tensor's bond with
`regionInsertedCoeff A R f M = regionInsertedCoeff B R f N` at every physical
configuration. By `coeffTransfer_iff_transferCoeff_incidentForm`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) this is equivalent to the transfer kernel
`transferCoeff A B R f M` (`TNLean.PEPS.RegionBlock.Recovery10`) having the
**incident-matrix coupling form** of a single bond matrix `N` on `f` — coupling the two
boundary configurations only through their `f`-legs, contracting the residual legs by the
identity.

This file supplies that incident-matrix form, ported from the edge engine: the two
endpoints of the chosen edge map to the **red region** `R` and its **host**
`univ \ R`; the residual local configuration on an endpoint maps to the residual
boundary configuration; the per-vertex left inverse `localLeftInverseAt` maps to the
region blocked left inverse `regionBlockedLeftInverse`
(`TNLean.PEPS.RegionBlock.Recovery5`); and the `f`-leg split
`regionBoundaryConfigSplitAt` (`TNLean.PEPS.RegionBlock.ResonatePort`) replaces the
edge engine's `localVirtualConfigSplitAt`.

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

/-! ### The incident kernel through the `f`-leg split

The incident-matrix kernel `incidentKernel B R f N`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) couples the two boundary configurations
`μ` and `(complement equiv).symm ν'` through their `f`-legs via `N`, contracting the
residual legs by the identity (`SameAwayFromBond`). Read through the `f`-leg split
`regionBoundaryConfigSplitAt` (`TNLean.PEPS.RegionBlock.ResonatePort`), the kernel
`incidentKernel B R f N μ ν'` depends on `μ` only through its `f`-leg `μ f` and its
residual boundary configuration, with `N` coupling the `f`-leg. -/

open scoped Classical in
/-- **The incident kernel is bond-`f` local in `μ`.** The incident-matrix kernel of `N`
at the complement boundary configuration `ν'`, read as a function of the region boundary
configuration `μ`, vanishes unless `μ` has the residual boundary configuration of
`(complement equiv).symm ν'`; on that residual it is `N (μ f)` against the `f`-leg of
`(complement equiv).symm ν'`. This exposes the kernel's `f`-locality in the first index.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--582 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem incidentKernel_eq_split (B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (μ : RegionBoundaryConfig (G := G) B R)
    (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)) :
    incidentKernel (G := G) B R f N μ ν' =
      (if (regionBoundaryConfigSplitAt (G := G) B R f μ).2 =
            (regionBoundaryConfigSplitAt (G := G) B R f
              ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν')).2 then
          N (μ f)
            (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f)
        else 0) := by
  classical
  rw [incidentKernel]
  by_cases hsame : SameAwayFromBond f μ
      ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν')
  · rw [if_pos hsame,
      if_pos ((sameAwayFromBond_iff_split_snd_eq B R f μ _).mp hsame)]
  · rw [if_neg hsame,
      if_neg (fun h => hsame ((sameAwayFromBond_iff_split_snd_eq B R f μ _).mpr h))]

/-! ### The incident-form criterion through the `f`-leg split

The transfer kernel `transferCoeff A B R f M`
(`TNLean.PEPS.RegionBlock.Recovery10`) is the incident-matrix kernel of a bond matrix
`N` exactly when, read through the `f`-leg split, it couples the two boundary
configurations only through their `f`-legs. This packages the bond-locality target
`transferCoeff M = incidentKernel N` as the two conditions the resonate inversion
must establish: residual independence (the kernel vanishes off the diagonal of the two
residual boundary configurations) and the `f`-leg value being read by `N`. -/

open scoped Classical in
/-- **The incident-form criterion.** For a bond matrix `N`, the transfer kernel of `M`
is the incident-matrix kernel of `N` if and only if, at every pair of boundary
configurations `(μ, ν')`, the transfer-kernel value is `N (μ f)` against the `f`-leg of
`(complement equiv).symm ν'` when the residual boundary configurations of `μ` and of
`(complement equiv).symm ν'` agree, and is `0` otherwise. This is the `f`-leg-split
reading of the bond-locality target `transferCoeff M = incidentKernel N`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem transferCoeff_eq_incidentKernel_iff_split (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (N : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    transferCoeff (G := G) A B R hRB hCB f M = incidentKernel (G := G) B R f N ↔
      ∀ (μ : RegionBoundaryConfig (G := G) B R)
        (ν' : RegionBoundaryConfig (G := G) B (Finset.univ \ R)),
        transferCoeff (G := G) A B R hRB hCB f M μ ν' =
          (if (regionBoundaryConfigSplitAt (G := G) B R f μ).2 =
                (regionBoundaryConfigSplitAt (G := G) B R f
                  ((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν')).2 then
              N (μ f)
                (((regionComplementBoundaryConfigEquiv (G := G) B R).symm ν') f)
            else 0) := by
  classical
  constructor
  · intro hker μ ν'
    rw [← incidentKernel_eq_split B R f N μ ν', ← hker]
  · intro hsplit
    funext μ ν'
    rw [hsplit μ ν', incidentKernel_eq_split B R f N μ ν']

/-! ### The transferred row through the A↔B region basis change

The block-frame transferred row `blockTransferRow A B R f M`
(`TNLean.PEPS.RegionBlock.BlockCoeffTransfer`) is the second tensor's region blocked
left inverse of the first tensor's region-inserted coefficient of `M`, read as a
function of the region physical configuration. The coefficient is the first tensor's
region blocked tensor map of the first tensor's own bond-`f`-local region row
(`regionInsertedCoeff_eq_region_blockedMap`,
`TNLean.PEPS.RegionBlock.Recovery7`), so the transferred row is the A↔B region basis
change `regionBasisChange B A R hRB` (`TNLean.PEPS.RegionBlock.BlockRealization`)
applied to that region row. This presents the transferred row — the source of the
transfer kernel `transferCoeff` — as the basis change of a bond-`f`-local row, with no
single-vertex injectivity. -/

/-- **The transferred row is the basis change of the region row.** The block-frame
transferred row `blockTransferRow A B R f M τ` is the A↔B region basis change
`regionBasisChange B A R hRB` applied to the first tensor's own region row
`regionRegionRow A R f M τ`.

The transferred row is the second tensor's region blocked left inverse of the first
tensor's coefficient (definition of `blockTransferRow`); the coefficient, as a
function of `σ`, is the first tensor's region blocked tensor map of its region row
(`regionInsertedCoeff_eq_region_blockedMap`), and the basis change is exactly the
second tensor's region blocked left inverse composed with the first tensor's region
blocked tensor map (`regionBasisChange_apply`,
`TNLean.PEPS.RegionBlock.BlockRealization`).

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem blockTransferRow_eq_basisChange_regionRegionRow (A B : Tensor G d) (R : Finset V)
    (hRB : RegionBlockedTensorInjective (G := G) B R)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    blockTransferRow A B R hRB f M τ =
      regionBasisChange (G := G) B A R hRB (regionRegionRow (G := G) A R f M τ) := by
  rw [blockTransferRow, regionBasisChange_apply]
  congr 1
  funext σ
  rw [regionInsertedCoeff_eq_region_blockedMap A R f M σ τ]

/-! ### The complement-side transferred row through the basis change

The symmetric companion of `blockTransferRow_eq_basisChange_regionRegionRow`. The
**complement-side transferred row** is the second tensor's complement blocked left
inverse of the first tensor's region-inserted coefficient of `M`, read as a function
of the complement physical configuration. The coefficient is the first tensor's
complement blocked tensor map of the first tensor's own bond-`f`-local complement row
`regionComplementRow A R f M σ` (`regionInsertedCoeff_eq_complement_blockedMap`,
`TNLean.PEPS.RegionBlock.Recovery7`), so the complement-side transferred row is the
A↔B complement basis change `regionBasisChange B A (univ \ R)`
(`TNLean.PEPS.RegionBlock.BlockRealization`) applied to that complement row. Both
transferred rows are basis changes of bond-`f`-local first-tensor rows, with no
single-vertex injectivity. -/

/-- **The complement-side transferred row.** The second tensor's complement blocked
left inverse of the first tensor's region-inserted coefficient of `M`, read as a
function of the complement physical configuration `τ` at a fixed region physical
configuration `σ`. This is the complement-block read-off of the coefficient — the
read the symmetric (complement-endpoint) inversion consumes, dual to the
region-block read-off `blockTransferRow`. -/
noncomputable def complBlockTransferRow (A B : Tensor G d) (R : Finset V)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    RegionBoundaryConfig (G := G) B (Finset.univ \ R) → ℂ :=
  regionBlockedLeftInverse (G := G) B (Finset.univ \ R) hCB
    (fun τ => regionInsertedCoeff (G := G) A R f M σ τ)

/-- **The complement-side transferred row is the basis change of the complement row.**
The complement-side transferred row `complBlockTransferRow A B R f M σ` is the A↔B
complement basis change `regionBasisChange B A (univ \ R) hCB` applied to the first
tensor's own complement row `regionComplementRow A R f M σ`.

The complement-side transferred row is the second tensor's complement blocked left
inverse of the first tensor's coefficient (definition); the coefficient, as a function
of `τ`, is the first tensor's complement blocked tensor map of its complement row
(`regionInsertedCoeff_eq_complement_blockedMap`,
`TNLean.PEPS.RegionBlock.Recovery7`), and the complement basis change is exactly the
second tensor's complement blocked left inverse composed with the first tensor's
complement blocked tensor map. No single-vertex injectivity is used.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, the step `V=W`, lines
355--486 of `Papers/1804.04964/paper_normal.tex`. -/
theorem complBlockTransferRow_eq_basisChange_regionComplementRow (A B : Tensor G d)
    (R : Finset V)
    (hCB : RegionBlockedTensorInjective (G := G) B (Finset.univ \ R))
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    complBlockTransferRow A B R hCB f M σ =
      regionBasisChange (G := G) B A (Finset.univ \ R) hCB
        (regionComplementRow (G := G) A R f M σ) := by
  rw [complBlockTransferRow, regionBasisChange_apply]
  congr 1
  funext τ
  rw [regionInsertedCoeff_eq_complement_blockedMap A R f M σ τ]

end PEPS
end TNLean
