/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenSemiRegularSupport
import TNLean.PEPS.SemiRegularBoundaryTransport
import TNLean.PEPS.MixedPhysicalProductMap
import TNLean.PEPS.ParentHamiltonian.RegionOperatorBlocks

/-!
# Regional blocks of the actual graph bond transformation

The product of bond maps, in the numbered physical coordinates of the graph,
has regional blocks that factor into exterior scalars, one-ended crossing
maps, and full internal maps. For multiplicity restoration, the crossing maps
are scalar multiples of the boundary filters. All these statements follow
from the coefficients of the global operator.

Source: SCP10, arXiv:1001.3807, Section 7, lines 2977–3019.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RI (R : Finset V) := {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R}
private abbrev RB (R : Finset V) := {f : Edge Γ // IsRegionBoundaryEdge R f}
private abbrev RE (R : Finset V) := {f : Edge Γ // f.1.1 ∉ R ∧ f.1.2 ∉ R}
variable {X Y : Type*} {p q : ℕ}

/-- The global product of actual head-tail bond maps, in numbered physical
coordinates. Source: SCP10, Section 7, lines 2977–3019. -/
def graphNumberedBondMatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) : Matrix (V → Fin q) (V → Fin p) ℂ :=
  fun τ σ => ∏ f : Edge Γ,
    F ((eY f.1.2).symm (τ f.1.2) (edgeRightIncident f),
        (eY f.1.1).symm (τ f.1.1) (edgeLeftIncident f))
      ((eX f.1.2).symm (σ f.1.2) (edgeRightIncident f),
        (eX f.1.1).symm (σ f.1.1) (edgeLeftIncident f))

/-- Regroup numbered regional configurations into crossing endpoints and
internal head-tail pairs. Source: SCP10, Section 7, lines 2977–3019. -/
def regionBondConfigEquiv
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V) :
    RegionPhysicalConfig (d := p) R ≃
      (RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X) :=
  (Equiv.piCongrRight fun v : {v // v ∈ R} => (e v.1).symm).trans
    ((regionHalfEdgeLabelEquiv R).trans {
      toFun := fun β => (β.1, fun f => (β.2.2 f, β.2.1 f))
      invFun := fun β => (β.1, (fun f => (β.2 f).2), fun f => (β.2 f).1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl })

/-- The fixed physical endpoint outside a crossing bond. -/
def regionOutsideBoundaryEndpoint
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V)
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) (f : RB (Γ := Γ) R) : X :=
  if ht : f.1.1.1 ∈ R then
    (e f.1.1.2).symm (σ ⟨f.1.1.2, Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (f.2.resolve_right (fun h => h.1 ht)).2⟩⟩)
      (edgeRightIncident f.1)
  else (e f.1.1.1).symm (σ ⟨f.1.1.1, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, ht⟩⟩) (edgeLeftIncident f.1)

/-- Fixing the exterior endpoints of a bond leaves a matrix on its inside
endpoint, with the original head-tail orientation retained. -/
def graphBoundaryBondMatrix (F : Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X)
    (f : RB (Γ := Γ) R) : Matrix Y X ℂ :=
  fun y x => if f.1.1.1 ∈ R then F (γY f, y) (γX f, x)
    else F (y, γY f) (x, γX f)

/-- Bonds wholly outside a region contribute this scalar to its operator block. -/
def graphExteriorBondCoefficient
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) : ℂ :=
  ∏ f : RE (Γ := Γ) R,
    F ((eY f.1.1.2).symm (τ ⟨f.1.1.2, by simp [f.2.2]⟩) (edgeRightIncident f.1),
        (eY f.1.1.1).symm (τ ⟨f.1.1.1, by simp [f.2.1]⟩) (edgeLeftIncident f.1))
      ((eX f.1.1.2).symm (σ ⟨f.1.1.2, by simp [f.2.2]⟩) (edgeRightIncident f.1),
        (eX f.1.1.1).symm (σ ⟨f.1.1.1, by simp [f.2.1]⟩) (edgeLeftIncident f.1))

/-- A graph-edge product splits into exterior, crossing, and internal bonds. -/
theorem prod_edge_eq_exterior_boundary_internal (R : Finset V) (w : Edge Γ → ℂ) :
    (∏ f, w f) = (∏ f : RE (Γ := Γ) R, w f.1) *
      ((∏ f : RB (Γ := Γ) R, w f.1) * ∏ f : RI (Γ := Γ) R, w f.1) := by
  classical
  have h (f : Edge Γ) : w f =
      (if _h : f.1.1 ∉ R ∧ f.1.2 ∉ R then w f else 1) *
        ((if _h : IsRegionBoundaryEdge R f then w f else 1) *
          (if _h : f.1.1 ∈ R ∧ f.1.2 ∈ R then w f else 1)) := by
    by_cases ht : f.1.1 ∈ R <;> by_cases hh : f.1.2 ∈ R <;>
      simp [IsRegionBoundaryEdge, ht, hh]
  calc
    _ = ∏ f : Edge Γ,
        (if _h : f.1.1 ∉ R ∧ f.1.2 ∉ R then w f else 1) *
          ((if _h : IsRegionBoundaryEdge R f then w f else 1) *
            (if _h : f.1.1 ∈ R ∧ f.1.2 ∈ R then w f else 1)) :=
      Finset.prod_congr rfl (fun f _ => h f)
    _ = _ := by
      simp only [Finset.prod_mul_distrib]
      simp only [Fintype.prod_dite, Finset.prod_const_one, mul_one]

/-- Every block of the actual global bond product is the exterior scalar
 times the mixed product of its crossing and internal factors.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem regionOperatorBlock_graphNumberedBondMatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R))
    (y : RegionPhysicalConfig (d := q) R) (x : RegionPhysicalConfig (d := p) R) :
    regionOperatorBlock R (graphNumberedBondMatrix eX eY F) τ σ y x =
      graphExteriorBondCoefficient eX eY F R τ σ *
        mixedPhysicalProductMatrix
          (graphBoundaryBondMatrix F R (regionOutsideBoundaryEndpoint eY R τ)
            (regionOutsideBoundaryEndpoint eX R σ)) (fun _ : RI (Γ := Γ) R => F)
          (regionBondConfigEquiv eY R y) (regionBondConfigEquiv eX R x) := by
  classical
  unfold regionOperatorBlock graphNumberedBondMatrix
  rw [prod_edge_eq_exterior_boundary_internal R]
  unfold graphExteriorBondCoefficient mixedPhysicalProductMatrix
  congr 1
  · apply Finset.prod_congr rfl
    intro f _
    simp only [assembleRegionσ, f.2.1, f.2.2, dite_false]
  · congr 1
    · apply Finset.prod_congr rfl
      intro f _
      by_cases ht : f.1.1.1 ∈ R
      · have hh : f.1.1.2 ∉ R := (f.2.resolve_right (fun h => h.1 ht)).2
        simp only [graphBoundaryBondMatrix, ht, ite_true, regionOutsideBoundaryEndpoint,
          dite_true, regionBondConfigEquiv, Equiv.trans_apply,
          Equiv.piCongrRight_apply, Pi.map_apply,
          Equiv.coe_fn_mk, regionHalfEdgeLabelEquiv_apply_boundary_tail R _ f ht,
          assembleRegionσ, hh, dite_false]
      · have hh : f.1.1.2 ∈ R := (f.2.resolve_left (fun h => ht h.1)).2
        simp only [graphBoundaryBondMatrix, ht, ite_false, regionOutsideBoundaryEndpoint,
          dite_false, regionBondConfigEquiv, Equiv.trans_apply,
          Equiv.piCongrRight_apply, Pi.map_apply,
          Equiv.coe_fn_mk, regionHalfEdgeLabelEquiv_apply_boundary_head R _ f hh,
          assembleRegionσ, hh, dite_true]
    · apply Finset.prod_congr rfl
      intro f _
      simp only [regionBondConfigEquiv, Equiv.trans_apply,
          Equiv.piCongrRight_apply, Pi.map_apply,
        Equiv.coe_fn_mk, regionHalfEdgeLabelEquiv_apply_internal_head,
        regionHalfEdgeLabelEquiv_apply_internal_tail, assembleRegionσ, f.2.1, f.2.2,
        dite_true]

/-- The adjoint reverses each actual bond map. -/
@[simp]
theorem graphNumberedBondMatrix_conjTranspose
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Matrix (Y × Y) (X × X) ℂ) :
    (graphNumberedBondMatrix eX eY F).conjTranspose =
      graphNumberedBondMatrix eY eX F.conjTranspose := by
  ext σ τ
  simp only [graphNumberedBondMatrix, Matrix.conjTranspose_apply, star_prod]

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- The inverse regional coordinate change assigns the crossing registers
and the tail and head registers to their original site incidences. -/
@[simp]
theorem regionBondConfigEquiv_symm_apply
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) (R : Finset V)
    (β : (RB (Γ := Γ) R → X) × (RI (Γ := Γ) R → X × X)) :
    (regionBondConfigEquiv e R).symm β = fun v => e v.1
      ((regionHalfEdgeLabelEquiv R).symm
        (β.1, (fun f => (β.2 f).2), fun f => (β.2 f).1) v) := rfl

variable {I : Type*} [Fintype I] [DecidableEq I]
variable (ν μ : I → Type*) [∀ i, Fintype (ν i)] [∀ i, DecidableEq (ν i)]
variable [∀ i, Fintype (μ i)] [∀ i, DecidableEq (μ i)]

/-- Fixing the tail of the full supported map gives the boundary filter times
an indicator for the fixed exterior base coordinate. -/
theorem fullMultiplicityBondMap_fixed_tail
    (z y : Σ i, ν i × μ i) (a x : Σ i, ν i) :
    fullMultiplicityBondMap ν μ (y, z) (x, a) =
      (if multiplicityEndpointBase ν μ z = a then (1 : ℂ) else 0) *
        multiplicityBoundaryMap ν μ (fun _ => 1) z y x := by
  rw [fullMultiplicityBondMap_apply]
  by_cases ho : multiplicityEndpointBase ν μ z = a <;>
    by_cases hi : multiplicityEndpointBase ν μ y = x <;>
    simp [Prod.mk.injEq, ho, hi, multiplicityBoundaryMap,
      multiplicityBondAmplitude]

/-- Fixing the head of the supported map gives the same boundary filter;
the equal-multiplicity amplitude is invariant under reversing the bond. -/
theorem fullMultiplicityBondMap_fixed_head
    (z y : Σ i, ν i × μ i) (a x : Σ i, ν i) :
    fullMultiplicityBondMap ν μ (z, y) (a, x) =
      (if multiplicityEndpointBase ν μ z = a then (1 : ℂ) else 0) *
        multiplicityBoundaryMap ν μ (fun _ => 1) z y x := by
  rw [fullMultiplicityBondMap_apply, multiplicityBondAmplitude_comm ν μ z y]
  by_cases ho : multiplicityEndpointBase ν μ z = a <;>
    by_cases hi : multiplicityEndpointBase ν μ y = x <;>
    simp [Prod.mk.injEq, ho, hi, multiplicityBoundaryMap,
      multiplicityBondAmplitude]

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- A crossing factor of the actual global multiplicity map is a scalar
indicator times the one-ended boundary filter, for either orientation. -/
theorem graphBoundaryBondMatrix_fullMultiplicityBondMap (R : Finset V)
    (γY : RB (Γ := Γ) R → Σ i, ν i × μ i)
    (γX : RB (Γ := Γ) R → Σ i, ν i) (f : RB (Γ := Γ) R)
    (y : Σ i, ν i × μ i) (x : Σ i, ν i) :
    graphBoundaryBondMatrix (fullMultiplicityBondMap ν μ) R γY γX f y x =
      (if multiplicityEndpointBase ν μ (γY f) = γX f then (1 : ℂ) else 0) *
        multiplicityBoundaryMap ν μ (fun _ => 1) (γY f) y x := by
  unfold graphBoundaryBondMatrix
  by_cases ht : f.1.1.1 ∈ R
  · rw [ite_eq_left ht]
    exact fullMultiplicityBondMap_fixed_head ν μ _ _ _ _
  · rw [ite_eq_right ht]
    exact fullMultiplicityBondMap_fixed_tail ν μ _ _ _ _

/-- The fixed exterior contribution of the actual multiplicity map: full
exterior bonds and the exterior base-coordinate indicators on crossing bonds.
Source: SCP10, Section 7, lines 2977–3019. -/
def graphMultiplicityBlockCoefficient
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, ν i) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, ν i × μ i) ≃ Fin q)
    (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) : ℂ :=
  graphExteriorBondCoefficient eX eY (fullMultiplicityBondMap ν μ) R τ σ *
    ∏ f : RB (Γ := Γ) R,
      if multiplicityEndpointBase ν μ (regionOutsideBoundaryEndpoint eY R τ f) =
          regionOutsideBoundaryEndpoint eX R σ f then 1 else 0

/-- Each block of the actual global supported multiplicity map is a single
scalar times the regional mixed product of boundary filters and internal maps.
The coordinate changes are the genuine incidence regroupings. No regional
range or parent-kernel assumption is used.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem regionOperatorBlock_fullMultiplicityBondMap
    (eX : (v : V) → (IncidentEdge Γ v → Σ i, ν i) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Σ i, ν i × μ i) ≃ Fin q)
    (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R))
    (y : RegionPhysicalConfig (d := q) R) (x : RegionPhysicalConfig (d := p) R) :
    regionOperatorBlock R
        (graphNumberedBondMatrix eX eY (fullMultiplicityBondMap ν μ)) τ σ y x =
      graphMultiplicityBlockCoefficient ν μ eX eY R τ σ *
        mixedPhysicalProductMatrix
          (fun f : RB (Γ := Γ) R => multiplicityBoundaryMap ν μ (fun _ => 1)
            (regionOutsideBoundaryEndpoint eY R τ f))
          (fun _ : RI (Γ := Γ) R => fullMultiplicityBondMap ν μ)
          (regionBondConfigEquiv eY R y) (regionBondConfigEquiv eX R x) := by
  rw [regionOperatorBlock_graphNumberedBondMatrix]
  simp only [mixedPhysicalProductMatrix, graphBoundaryBondMatrix_fullMultiplicityBondMap,
    Finset.prod_mul_distrib, graphMultiplicityBlockCoefficient, mul_assoc]

end TNLean.PEPS
