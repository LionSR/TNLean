/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Region.RegionBlock
import QICLean.ManyBody.Sites.Placement.Basic

/-!
# Splitting physical configurations at a region

A physical configuration on all vertices is the same as a pair of configurations, one on a
finite region `R` and one on its set complement `univ \ R`. This file gives the gluing map
`assembleRegionσ`, the resulting equivalence `regionConfigEquiv`, and the linear map
`regionSliceMap` that reads a global vector with the complementary configuration fixed.

In these coordinates the placement of an operator on `R`, extended by the identity on the
complement, is the Kronecker product of the operator with the identity
(`place_eq_regionConfigEquiv`). On a fixed complementary configuration it acts as the
regional operator itself (`place_mulVec_assemble`).

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section IV.C.1, local-versus-complement factorization, local source lines 2003–2011.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators Kronecker Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V] {d : ℕ}

/-- Glue a physical configuration on the region `R` and a physical configuration
on the set complement `univ \ R` into a global physical configuration on all
vertices. -/
def assembleRegionσ (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : V → Fin d :=
  fun w => if h : w ∈ R then σ ⟨w, h⟩ else τ ⟨w, by simp [h]⟩

@[simp] theorem assembleRegionσ_mem (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (w : {w : V // w ∈ R}) :
    assembleRegionσ (V := V) (d := d) R σ τ w.1 = σ w := by
  simp [assembleRegionσ, w.2]

@[simp] theorem assembleRegionσ_notMem (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (w : {w : V // w ∈ Finset.univ \ R}) :
    assembleRegionσ (V := V) (d := d) R σ τ w.1 = τ w := by
  have hw : w.1 ∉ R := by
    have := w.2
    rw [Finset.mem_sdiff] at this
    exact this.2
  rw [assembleRegionσ, dite_eq_right hw]

/-- Splitting a physical configuration into its region and complement.
Source: arXiv:2011.12127, local-versus-complement factorization, lines 2003–2011. -/
def regionConfigEquiv (R : Finset V) :
    (V → Fin d) ≃ RegionPhysicalConfig (d := d) R ×
      RegionPhysicalConfig (d := d) (Finset.univ \ R) where
  toFun σ := (fun v => σ v.1, fun v => σ v.1)
  invFun p := assembleRegionσ R p.1 p.2
  left_inv σ := by
    funext v
    simp [assembleRegionσ]
  right_inv p := by
    apply Prod.ext <;> funext v
    · exact assembleRegionσ_mem R p.1 p.2 v
    · exact assembleRegionσ_notMem R p.1 p.2 v

/-- The placement of a regional operator, extended by the identity on its complement, in the
coordinates of the region and of `univ \ R`.
Source: arXiv:2011.12127, parent Hamiltonian construction, lines 2003–2011. -/
theorem place_eq_regionConfigEquiv (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) :
    ManyBody.place (X := fun _ ↦ Fin d) R h =
      (h ⊗ₖ (1 : Matrix (RegionPhysicalConfig (d := d) (Finset.univ \ R))
        (RegionPhysicalConfig (d := d) (Finset.univ \ R)) ℂ)).submatrix
          (regionConfigEquiv R) (regionConfigEquiv R) := by
  ext σ τ
  simp only [ManyBody.place_apply, Matrix.submatrix_apply, Matrix.kroneckerMap_apply,
    Matrix.one_apply, regionConfigEquiv, Equiv.coe_fn_mk, funext_iff, Subtype.forall,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  split_ifs <;> simp_all

/-- On a fixed complementary configuration the global interaction is exactly
the original regional interaction. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem place_mulVec_assemble (R : Finset V)
    (h : Matrix (RegionPhysicalConfig (d := d) R)
      (RegionPhysicalConfig (d := d) R) ℂ) (ψ : (V → Fin d) → ℂ)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (ManyBody.place (X := fun _ ↦ Fin _) R h *ᵥ ψ) (assembleRegionσ R σ τ) =
      (h *ᵥ (fun ν => ψ (assembleRegionσ R ν τ))) σ := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp (regionConfigEquiv (d := d) R).symm,
    Fintype.sum_prod_type]
  simp [place_eq_regionConfigEquiv, Matrix.submatrix_apply,
    regionConfigEquiv, Matrix.one_apply]

/-- A physical slice with the complementary configuration fixed.
Source: arXiv:2011.12127, local ground-space conditions, lines 2003–2011. -/
def regionSliceMap (R : Finset V)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    ((V → Fin d) → ℂ) →ₗ[ℂ] (RegionPhysicalConfig (d := d) R → ℂ) where
  toFun ψ σ := ψ (assembleRegionσ R σ τ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end PEPS
end TNLean
