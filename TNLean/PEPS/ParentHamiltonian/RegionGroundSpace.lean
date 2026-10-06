/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.OpenRegionContraction
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Ground spaces of finite PEPS regions

For a finite region, the local ground space consists of all physical vectors
obtained by contracting its internal virtual bonds with arbitrary boundary
conditions on the crossing bonds. Equivalently, it is the span of the
open-region tensors. The definition uses the genuine open contraction, so
edges wholly outside the region contribute no multiplicity.

Every slice of the closed PEPS vector, with the complementary physical
configuration fixed, belongs to this space. Consequently any local linear
operator whose kernel contains this space annihilates all such slices.
No injectivity, translation invariance, or positivity of the bond dimensions
is required.

Source: Cirac, Pérez-García, Schuch, and Verstraete, arXiv:2011.12127,
Section IV.C.1, local source lines 2003–2011.
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

/-- The local ground space of a finite region, obtained by contracting its
internal bonds with arbitrary virtual boundary conditions.
Source: arXiv:2011.12127, Section IV.C.1, lines 2003–2008. -/
noncomputable def regionGroundSpace (A : Tensor Γ d) (R : Finset V) :
    Submodule ℂ (RegionPhysicalConfig (d := d) R → ℂ) :=
  (openRegionMap A R).range

/-- The local ground space is the span of the open-region tensors indexed by
crossing-bond configurations. Source: arXiv:2011.12127, lines 2003–2008. -/
theorem regionGroundSpace_eq_span (A : Tensor Γ d) (R : Finset V) :
    regionGroundSpace A R = Submodule.span ℂ (Set.range (openRegionWeight A R)) := by
  exact Fintype.range_linearCombination ℂ (openRegionWeight A R)

/-- A subspace contains the regional ground space exactly when it contains
every actual open-region tensor. Source: arXiv:2011.12127, the boundary
condition construction in Section IV.C.1, lines 2003–2008. -/
theorem regionGroundSpace_le_iff (A : Tensor Γ d) (R : Finset V)
    (S : Submodule ℂ (RegionPhysicalConfig (d := d) R → ℂ)) :
    regionGroundSpace A R ≤ S ↔ ∀ μ, openRegionWeight A R μ ∈ S := by
  rw [regionGroundSpace_eq_span, Submodule.span_le, Set.range_subset_iff]
  rfl

/-- Membership means that a virtual boundary condition produces the physical
vector. Source: arXiv:2011.12127, lines 2003–2008. -/
theorem mem_regionGroundSpace_iff (A : Tensor Γ d) (R : Finset V)
    (ψ : RegionPhysicalConfig (d := d) R → ℂ) :
    ψ ∈ regionGroundSpace A R ↔ ∃ x, openRegionMap A R x = ψ := Iff.rfl

/-- Every open-region tensor belongs to the local ground space.
Source: arXiv:2011.12127, lines 2003–2008. -/
theorem openRegionWeight_mem_regionGroundSpace (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) : openRegionWeight A R μ ∈ regionGroundSpace A R := by
  classical
  exact ⟨Pi.single μ 1, openRegionMap_single A R μ⟩

/-- The dimension of a local ground space is at most the product of the
crossing-bond dimensions. Source: arXiv:2011.12127, the boundary-condition
construction at lines 2003–2008. -/
theorem finrank_regionGroundSpace_le (A : Tensor Γ d) (R : Finset V) :
    Module.finrank ℂ (regionGroundSpace A R) ≤
      ∏ e : {e : Edge Γ // IsRegionBoundaryEdge R e}, A.bondDim e.1 := by
  classical
  calc
    Module.finrank ℂ (regionGroundSpace A R) ≤
        Fintype.card (RegionBoundaryConfig A R) := by
      change Module.finrank ℂ (openRegionMap A R).range ≤ _
      rw [← Module.finrank_pi ℂ]
      exact (openRegionMap A R).finrank_range_le
    _ = _ := by
      rw [Fintype.card_pi]
      exact Finset.prod_congr rfl fun e _ => Fintype.card_fin _

/-- Fixing all physical indices outside a region yields a vector in its local
ground space. This is the local contraction identity underlying frustration
freeness. Source: arXiv:2011.12127, lines 2003–2011. -/
theorem stateCoeff_slice_mem_regionGroundSpace (A : Tensor Γ d) (R : Finset V)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (fun σ => stateCoeff A (assembleRegionσ R σ τ)) ∈ regionGroundSpace A R := by
  classical
  by_cases h : Nonempty (VirtualConfig A)
  · obtain ⟨ζ⟩ := h
    have hA (e : Edge Γ) : A.bondDim e ≠ 0 := by
      exact Nat.ne_zero_of_lt (lt_of_le_of_lt (Nat.zero_le (ζ e).val) (ζ e).isLt)
    refine ⟨fun μ => openRegionWeight A (Finset.univ \ R)
      (regionComplementBoundaryConfig A R μ) τ, ?_⟩
    funext σ
    rw [openRegionMap_apply, stateCoeff_eq_openRegionComplement A R hA σ τ]
    apply Finset.sum_congr rfl
    intro μ _
    exact mul_comm _ _
  · let : IsEmpty (VirtualConfig A) := not_nonempty_iff.mp h
    have hzero : (fun σ => stateCoeff A (assembleRegionσ R σ τ)) = 0 := by
      funext σ
      simp [stateCoeff]
    rw [hzero]
    exact Submodule.zero_mem _

/-- Every linear operator vanishing on the local ground space annihilates
all slices of the closed PEPS vector. Source: arXiv:2011.12127,
frustration freeness at lines 2008–2011. -/
theorem localOperator_stateCoeff_slice_eq_zero (A : Tensor Γ d) (R : Finset V)
    (h : Module.End ℂ (RegionPhysicalConfig (d := d) R → ℂ))
    (hh : regionGroundSpace A R ≤ h.ker)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    h (fun σ => stateCoeff A (assembleRegionσ R σ τ)) = 0 := by
  exact hh (stateCoeff_slice_mem_regionGroundSpace A R τ)

end TNLean.PEPS
