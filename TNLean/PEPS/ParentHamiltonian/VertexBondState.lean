/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.VertexBondCoordinates
import TNLean.PEPS.ParentHamiltonian.RegionFullGroundSpace

/-!
# The closed PEPS vector as the image of the virtual Bell product

In endpoint-pair coordinates, the product of the site tensor maps sends
the product of virtual Bell vectors to the actual closed PEPS vector.
Its image of the common virtual Bell ground space is the full-region
physical range. Ordinary site injectivity identifies these two spaces
and makes the closed state nonzero precisely when every bond dimension
is positive.

Source: CPGSV21, arXiv:2011.12127, Section IV.C.1, the product of virtual
entangled pairs and its physical image, lines 2017–2044. These are global
contraction identities; no assertion about a smaller-region physical
parent Hamiltonian is made here.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The product of all site tensor maps, with its domain written as
independent endpoint pairs of the actual graph edges.
Source: CPGSV21, Section IV.C.1, lines 2017–2028. -/
noncomputable def fullRegionVertexTensorMapEdgePairs (A : Tensor Γ d) :
    (EdgePairVirtualConfig A → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (d := d) (Finset.univ : Finset V) → ℂ) :=
  regionVertexTensorMap A Finset.univ ∘ₗ
    (fullRegionVertexVectorEquivEdgePair A).symm.toLinearMap

/-- The actual closed PEPS vector is the image of the product Bell vector
under the product of the site maps. No injectivity is required.
Source: CPGSV21, Section IV.C.1, lines 2017–2028. -/
theorem fullRegionVertexTensorMapEdgePairs_virtualBondProduct (A : Tensor Γ d) :
    fullRegionVertexTensorMapEdgePairs A (virtualBondProduct A.bondDim) =
      fullRegionPhysicalEquiv d (stateCoeff A) := by
  let μ : RegionBoundaryConfig A Finset.univ :=
    fun e => False.elim (not_isRegionBoundaryEdge_univ e.1 e.2)
  change regionVertexTensorMap A Finset.univ
    ((fullRegionVertexVectorEquivEdgePair A).symm (virtualBondProduct A.bondDim)) = _
  rw [← fullRegionVertexVectorEquivEdgePair_virtualBondWeight A μ,
    LinearEquiv.symm_apply_apply, regionVertexTensorMap_regionVirtualBondWeight,
    openRegionWeight_univ]

/-- The common virtual Bell ground space maps exactly onto the actual
full-region physical range, including the zero-dimensional case.
Source: the virtual-pair physical image in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem map_virtualBondGroundSpace_fullRegionVertexTensorMapEdgePairs (A : Tensor Γ d) :
    (virtualBondGroundSpace A.bondDim).map (fullRegionVertexTensorMapEdgePairs A) =
      regionGroundSpace A Finset.univ := by
  rw [virtualBondGroundSpace_eq_span, Submodule.map_span, Set.image_singleton,
    fullRegionVertexTensorMapEdgePairs_virtualBondProduct, regionGroundSpace_univ]

/-- Ordinary site injectivity makes the global product site map injective
also in endpoint-pair coordinates.
Source: tensoring the site inverses in CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem fullRegionVertexTensorMapEdgePairs_injective (A : Tensor Γ d)
    (hA : IsVertexInjective A) : Function.Injective (fullRegionVertexTensorMapEdgePairs A) :=
  (regionVertexTensorMap_injective A hA Finset.univ).comp
    (fullRegionVertexVectorEquivEdgePair A).symm.injective

/-- Under ordinary site injectivity, the independent virtual vectors
whose physical images belong to the full-region range are exactly the
common virtual Bell ground space.
Source: the inverse-and-reconstruction argument of CPGSV21,
Section IV.C.1, lines 2017–2044. -/
theorem comap_regionGroundSpace_fullRegionVertexTensorMapEdgePairs (A : Tensor Γ d)
    (hA : IsVertexInjective A) :
    (regionGroundSpace A Finset.univ).comap (fullRegionVertexTensorMapEdgePairs A) =
      virtualBondGroundSpace A.bondDim := by
  rw [← map_virtualBondGroundSpace_fullRegionVertexTensorMapEdgePairs,
    Submodule.comap_map_eq_of_injective (fullRegionVertexTensorMapEdgePairs_injective A hA)]

/-- An ordinarily site-injective closed PEPS vector is nonzero exactly
when every virtual bond dimension is positive. This includes isolated
vertices and the empty graph.
Source: consequence of the virtual-pair construction and site inverses
in CPGSV21, Section IV.C.1, lines 2017–2044. -/
theorem stateCoeff_ne_zero_iff_bondDim_pos_of_isVertexInjective (A : Tensor Γ d)
    (hA : IsVertexInjective A) :
    stateCoeff A ≠ 0 ↔ ∀ e, 0 < A.bondDim e := by
  have hF := fullRegionVertexTensorMapEdgePairs_injective A hA
  have hE := (fullRegionPhysicalEquiv (V := V) d).injective
  have hzero : stateCoeff A = 0 ↔ virtualBondProduct A.bondDim = 0 := by
    constructor
    · intro h
      apply hF
      rw [fullRegionVertexTensorMapEdgePairs_virtualBondProduct, h, map_zero, map_zero]
    · intro h
      apply hE
      rw [← fullRegionVertexTensorMapEdgePairs_virtualBondProduct, h, map_zero, map_zero]
  rw [← virtualBondProduct_ne_zero_iff, ne_eq, ne_eq, hzero]

end TNLean.PEPS
