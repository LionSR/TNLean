/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.Recovery5
import TNLean.PEPS.TorusDeformedWindow

/-!
# Physical realization of a region insert

Let `R` be an injective region.  Its genuine blocked tensors, indexed by the virtual boundary
configuration, are linearly independent.  Consequently, any insert `C` with the same virtual
boundary and physical spaces is obtained by applying one linear operator to the physical leg of
the genuine block.  A chosen left inverse of the blocked-tensor map gives this operator explicitly.

This is the linear-algebraic meaning of the paper's phrase that a virtual operation on the
highlighted bond is a physical operation on an injective window.  Unlike equality after closing the
window against its complement, the theorem below is an open-boundary identity for every boundary
configuration.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair
  states generating the same state*, arXiv:1804.04964, the virtual/physical operation
  correspondence at lines 2320--2321 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964).
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The physical operator on an injective region realizing a prescribed region insert.

First use the chosen left inverse of the genuine blocked-tensor map to read a physical vector as
virtual-boundary coefficients.  Then take the corresponding linear combination of the prescribed
insert family.

Source: arXiv:1804.04964, the virtual/physical operation correspondence at lines 2320--2321 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def physicalOpOfRegionInsert (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (C : RegionInsert (G := G) (d := d) A R) :
    (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ) :=
  (Fintype.linearCombination ℂ C).comp (regionBlockedLeftInverse (G := G) A R hR)

/-- The physical operator of an insert sends every genuine open-boundary block to the
corresponding member of the insert family:
\[
  O_C\bigl(T_{A,R}(\mu)\bigr)=C(\mu).
\]

Thus the realization holds before contracting the window with its complement.

Source: arXiv:1804.04964, the virtual/physical operation correspondence at lines 2320--2321 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem physicalOpOfRegionInsert_realizes (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R)
    (C : RegionInsert (G := G) (d := d) A R)
    (μ : RegionBoundaryConfig (G := G) A R) :
    physicalOpOfRegionInsert (G := G) A R hR C
        (regionBlockedWeight (G := G) A R μ) = C μ := by
  classical
  rw [physicalOpOfRegionInsert, LinearMap.comp_apply,
    regionBlockedLeftInverse_regionBlockedWeight,
    Fintype.linearCombination_apply_single, one_smul]

end PEPS
end TNLean
