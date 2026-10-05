/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularConstraintProjectors

/-!
# Fixed spaces of the elementary regular constraints

The vertex and shared-edge averages fix exactly the corresponding invariant
functions; the diagonal regional constraint fixes exactly the functions
supported on the flat locus. These identities connect the commuting product
to the actual regional range characterization in SCP10, Theorem 6.12.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

attribute [local instance] Representation.invertibleFintypeCardComplex

private theorem matrix_average_mulVec_eq_self_iff {H ι : Type*}
    [Group H] [Fintype H] [Fintype ι] [DecidableEq ι]
    (ρ : H →* Matrix ι ι ℂ) (x : ι → ℂ) :
    ((Fintype.card H : ℂ)⁻¹ • ∑ g, ρ g) *ᵥ x = x ↔ ∀ g, ρ g *ᵥ x = x := by
  let σ : Representation ℂ H (ι → ℂ) := Matrix.toLinAlgEquiv'.toMonoidHom.comp ρ
  have havg : σ.averageMap x = ((Fintype.card H : ℂ)⁻¹ • ∑ g, ρ g) *ᵥ x := by
    rw [Representation.averageMap_apply_eq_sum]
    change (⅟(Fintype.card H : ℂ)) • ∑ g, ρ g *ᵥ x = _
    rw [invOf_eq_inv, Matrix.smul_mulVec, Matrix.sum_mulVec]
  rw [← havg]
  constructor
  · intro h g
    have hfixed := σ.averageMap_invariant x g
    rw [h] at hfixed
    exact hfixed
  · intro h
    exact σ.averageMap_id x h

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- A vertex average fixes exactly the functions invariant under every
left multiplication at that vertex. -/
theorem regularGlobalVertexAverage_mulVec_eq_self_iff (v : V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    regularGlobalVertexAverage (Γ := Γ) (G := G) v *ᵥ x = x ↔
      ∀ g : G, ∀ α, x (regularRegionGaugePhysicalLabels Finset.univ
        (fun w => if w.1 = v then g else 1) α) = x α := by
  let ρ := (Matrix.permMatrixHom (R := ℂ)).comp
    (regularGlobalVertexPermutation (Γ := Γ) (G := G) v)
  change ((Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g) *ᵥ x = x ↔ _
  rw [matrix_average_mulVec_eq_self_iff]
  have hact (g : G) : ρ g *ᵥ x = fun α =>
      x (regularRegionGaugePhysicalLabels Finset.univ
        (fun w => if w.1 = v then g else 1) α) := by
    change (Equiv.Perm.permMatrix ℂ (regularGlobalVertexPermutation v g)⁻¹) *ᵥ x = _
    rw [Matrix.permMatrix_mulVec]
    funext α
    apply congrArg x
    funext w e
    change ((if w.1 = v then g else 1)⁻¹)⁻¹⁻¹ * α w e = _
    rw [inv_inv]
    rfl
  simp only [hact, funext_iff]

/-- Inverse right multiplication on one shared edge is a group representation. -/
def regularRegionEdgePermutation (R : Finset V) (e : Edge Γ) :
    G →* Equiv.Perm (RegionHalfEdgeConfig (Γ := Γ) G R) where
  toFun g := regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g⁻¹ else 1)
  map_one' := by
    ext α v f
    simp only [regularRegionHalfEdgeRightEquiv_apply, regularRegionHalfEdgeRightMul,
      inv_one, ite_self, mul_one, Equiv.Perm.one_apply]
  map_mul' g h := by
    ext α v f
    change α v f * (if f.1 = e then (g * h)⁻¹ else 1) =
      (α v f * (if f.1 = e then h⁻¹ else 1)) * (if f.1 = e then g⁻¹ else 1)
    split_ifs <;> simp only [mul_inv_rev, mul_assoc, mul_one]

/-- An edge average fixes exactly the functions invariant under every shared
right multiplication on that original edge. -/
theorem regularRegionEdgeAverage_mulVec_eq_self_iff (R : Finset V) (e : Edge Γ)
    (x : RegionHalfEdgeConfig (Γ := Γ) G R → ℂ) :
    regularRegionEdgeAverage (G := G) R e *ᵥ x = x ↔
      ∀ g : G, ∀ α, x (regularRegionHalfEdgeRightMul R
        (fun f => if f = e then g else 1) α) = x α := by
  let ρ := (Matrix.permMatrixHom (R := ℂ)).comp
    (regularRegionEdgePermutation (G := G) R e)
  have havg : regularRegionEdgeAverage (G := G) R e =
      (Fintype.card G : ℂ)⁻¹ • ∑ g, ρ g := by
    unfold regularRegionEdgeAverage
    congr 1
    exact (Equiv.sum_comp (Equiv.inv G) (fun g => Matrix.permMatrixHom (R := ℂ)
      (regularRegionHalfEdgeRightEquiv R (fun f => if f = e then g else 1)))).symm
  rw [havg, matrix_average_mulVec_eq_self_iff]
  have hact (g : G) : ρ g *ᵥ x = fun α =>
      x (regularRegionHalfEdgeRightMul R (fun f => if f = e then g else 1) α) := by
    change (Equiv.Perm.permMatrix ℂ (regularRegionEdgePermutation R e g)⁻¹) *ᵥ x = _
    rw [Matrix.permMatrix_mulVec]
    funext α
    apply congrArg x
    funext v f
    change α v f * (if f.1 = e then g⁻¹ else 1)⁻¹ = _
    split_ifs <;> simp [regularRegionHalfEdgeRightMul, *]
  simp only [hact, funext_iff]

/-- The diagonal regional projector fixes exactly the functions with flat support. -/
theorem regularGlobalRegionFlatProjector_mulVec_eq_self_iff (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    regularGlobalRegionFlatProjector (Γ := Γ) (G := G) R *ᵥ x = x ↔
      ∀ α, ¬ IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) →
        x α = 0 := by
  classical
  simp only [regularGlobalRegionFlatProjector, Matrix.mulVec_diagonal, funext_iff]
  constructor
  · intro h α hα
    simpa [hα] using (h α).symm
  · intro h α
    split_ifs with hα
    · exact one_mul _
    · simp only [zero_mul, h α hα]

end TNLean.PEPS
