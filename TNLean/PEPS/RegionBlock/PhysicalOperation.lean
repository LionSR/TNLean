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

In the other direction, any physical operation defines an insert by applying it to every genuine
open-boundary block.  Closing this insert against the complement is the operation applied to the
partial state, up to the region's interior-bond multiplicity.  Since partial states depend only on
the closed state, this gives the direct `SameState` transfer used in the common-state comparison of
the two-dimensional converse.

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

/-- The region insert obtained by applying a physical operation to every genuine
open-boundary block of the region.

Source: arXiv:1804.04964, the four physical operations on the staircase windows at lines
2320--2415 of `Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionInsertOfPhysicalOp (A : Tensor G d) (R : Finset V)
    (O : Module.End ℂ (RegionPhysicalConfig (V := V) (d := d) R → ℂ)) :
    RegionInsert (G := G) (d := d) A R :=
  fun μ => O (regionBlockedWeight (G := G) A R μ)

/-- Applying a physical operation to every genuine open-boundary block and then closing the
region against its complement is the same as applying that operation to the corresponding
partial state, with the interior-bond multiplicity of the region.

This is the coefficient form of the common-state comparison for the four physical operations in
the two-dimensional proof: the operation is applied before the window is contracted with the
rest of the network.

Source: arXiv:1804.04964, the four physical operations and their common closed state at lines
2368--2415 of `Papers/1804.04964/paper_normal.tex`. -/
theorem deformedRegionState_regionInsertOfPhysicalOp (A : Tensor G d) (R : Finset V)
    (O : Module.End ℂ (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    deformedRegionState (G := G) A R (regionInsertOfPhysicalOp (G := G) A R O) σ τ =
      O ((regionInteriorBondProd (G := G) A R : ℂ) •
        regionPartialState (G := G) A R τ) σ := by
  classical
  unfold deformedRegionState regionInsertOfPhysicalOp
  rw [regionInteriorBondProd_smul_regionPartialState (G := G) A R τ]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun μ _ => mul_comm _ _

/-- The same physical operation, applied to the genuine blocks of two tensors with the same
closed state, produces deformed states equal after cross-multiplication by the two interior-bond
products.

No identification of the two virtual boundary spaces is used: the two boundary sums are first
read as the same partial state, and the only tensor-dependent factors left are the two
interior-bond multiplicities.  This is the source-faithful bridge from `SameState` to the common
physical-operation states compared in the two-dimensional converse.

Source: arXiv:1804.04964, the common-state comparison at lines 2368--2415 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem deformedRegionState_regionInsertOfPhysicalOp_sameState (A B : Tensor G d)
    (hAB : SameState A B) (R : Finset V)
    (O : Module.End ℂ (RegionPhysicalConfig (V := V) (d := d) R → ℂ))
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (regionInteriorBondProd (G := G) B R : ℂ) •
        deformedRegionState (G := G) A R
          (regionInsertOfPhysicalOp (G := G) A R O) σ τ =
      (regionInteriorBondProd (G := G) A R : ℂ) •
        deformedRegionState (G := G) B R
          (regionInsertOfPhysicalOp (G := G) B R O) σ τ := by
  rw [deformedRegionState_regionInsertOfPhysicalOp,
    deformedRegionState_regionInsertOfPhysicalOp,
    regionPartialState_sameState hAB R τ]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  ring

end PEPS
end TNLean
