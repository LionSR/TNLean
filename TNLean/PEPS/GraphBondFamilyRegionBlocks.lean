/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphBondPhysicalCoordinates

/-!
# Regional blocks of edge-dependent graph bond transformations

The product of edge-dependent bond maps, in the numbered physical coordinates
of the graph, has regional blocks that factor into exterior scalars, one-ended
crossing maps, and full internal maps. These statements follow from the
coefficients of the global operator.

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
def graphNumberedBondFamilyMatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) : Matrix (V → Fin q) (V → Fin p) ℂ :=
  fun τ σ => ∏ f : Edge Γ,
    F f ((eY f.1.2).symm (τ f.1.2) (edgeRightIncident f),
        (eY f.1.1).symm (τ f.1.1) (edgeLeftIncident f))
      ((eX f.1.2).symm (σ f.1.2) (edgeRightIncident f),
        (eX f.1.1).symm (σ f.1.1) (edgeLeftIncident f))

/-- Fixing the exterior endpoints of a bond leaves a matrix on its inside
endpoint, with the original head-tail orientation retained. -/
def graphBoundaryBondFamilyMatrix (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (γY : RB (Γ := Γ) R → Y) (γX : RB (Γ := Γ) R → X)
    (f : RB (Γ := Γ) R) : Matrix Y X ℂ :=
  fun y x => if f.1.1.1 ∈ R then F f.1 (γY f, y) (γX f, x)
    else F f.1 (y, γY f) (x, γX f)

/-- Bonds wholly outside a region contribute this scalar to its operator block. -/
def graphExteriorBondFamilyCoefficient
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R)) : ℂ :=
  ∏ f : RE (Γ := Γ) R,
    F f.1 ((eY f.1.1.2).symm (τ ⟨f.1.1.2, by simp [f.2.2]⟩) (edgeRightIncident f.1),
        (eY f.1.1.1).symm (τ ⟨f.1.1.1, by simp [f.2.1]⟩) (edgeLeftIncident f.1))
      ((eX f.1.1.2).symm (σ ⟨f.1.1.2, by simp [f.2.2]⟩) (edgeRightIncident f.1),
        (eX f.1.1.1).symm (σ ⟨f.1.1.1, by simp [f.2.1]⟩) (edgeLeftIncident f.1))

/-- Every block of the actual global bond product is the exterior scalar
 times the mixed product of its crossing and internal factors.
Source: SCP10, Section 7, lines 2977–3019. -/
theorem regionOperatorBlock_graphNumberedBondFamilyMatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) (R : Finset V)
    (τ : RegionPhysicalConfig (d := q) (Finset.univ \ R))
    (σ : RegionPhysicalConfig (d := p) (Finset.univ \ R))
    (y : RegionPhysicalConfig (d := q) R) (x : RegionPhysicalConfig (d := p) R) :
    regionOperatorBlock R (graphNumberedBondFamilyMatrix eX eY F) τ σ y x =
      graphExteriorBondFamilyCoefficient eX eY F R τ σ *
        mixedPhysicalProductMatrix
          (graphBoundaryBondFamilyMatrix F R (regionOutsideBoundaryEndpoint eY R τ)
            (regionOutsideBoundaryEndpoint eX R σ)) (fun f : RI (Γ := Γ) R => F f.1)
          (regionBondConfigEquiv eY R y) (regionBondConfigEquiv eX R x) := by
  classical
  unfold regionOperatorBlock graphNumberedBondFamilyMatrix
  rw [prod_edge_eq_exterior_boundary_internal R]
  unfold graphExteriorBondFamilyCoefficient mixedPhysicalProductMatrix
  congr 1
  · apply Finset.prod_congr rfl
    intro f _
    simp only [assembleRegionσ, f.2.1, f.2.2, dite_false]
  · congr 1
    · apply Finset.prod_congr rfl
      intro f _
      by_cases ht : f.1.1.1 ∈ R
      · have hh : f.1.1.2 ∉ R := (f.2.resolve_right (fun h => h.1 ht)).2
        simp only [graphBoundaryBondFamilyMatrix, ht, ite_true, regionOutsideBoundaryEndpoint,
          dite_true, regionBondConfigEquiv, Equiv.trans_apply,
          Equiv.piCongrRight_apply, Pi.map_apply,
          Equiv.coe_fn_mk, regionHalfEdgeLabelEquiv_apply_boundary_tail R _ f ht,
          assembleRegionσ, hh, dite_false]
      · have hh : f.1.1.2 ∈ R := (f.2.resolve_left (fun h => ht h.1)).2
        simp only [graphBoundaryBondFamilyMatrix, ht, ite_false, regionOutsideBoundaryEndpoint,
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
theorem graphNumberedBondFamilyMatrix_conjTranspose
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) :
    (graphNumberedBondFamilyMatrix eX eY F).conjTranspose =
      graphNumberedBondFamilyMatrix eY eX (fun f => (F f).conjTranspose) := by
  ext σ τ
  simp only [graphNumberedBondFamilyMatrix, Matrix.conjTranspose_apply, star_prod]


/-- The numbered edge-family matrix is the product matrix in the actual
head-tail bond coordinates. -/
theorem graphNumberedBondFamilyMatrix_eq_submatrix
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ) :
    graphNumberedBondFamilyMatrix eX eY F =
      (Matrix.of (fun (τ : Edge Γ → Y × Y) (σ : Edge Γ → X × X) =>
        ∏ f, F f (τ f) (σ f))).submatrix
        (graphBondConfigEquiv eY) (graphBondConfigEquiv eX) := rfl

/-- Numbered products of edge-dependent maps compose independently on each
actual graph bond. -/
theorem graphNumberedBondFamilyMatrix_mul {Z : Type*} {r : ℕ} [Fintype Y]
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (eZ : (v : V) → (IncidentEdge Γ v → Z) ≃ Fin r)
    (F : Edge Γ → Matrix (Z × Z) (Y × Y) ℂ)
    (L : Edge Γ → Matrix (Y × Y) (X × X) ℂ) :
    graphNumberedBondFamilyMatrix eY eZ F * graphNumberedBondFamilyMatrix eX eY L =
      graphNumberedBondFamilyMatrix eX eZ (fun f => F f * L f) := by
  classical
  simp only [graphNumberedBondFamilyMatrix_eq_submatrix]
  rw [Matrix.submatrix_mul_equiv]
  ext τ σ
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.of_apply,
    ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun (f : Edge Γ) (j : Y × Y) =>
    F f (graphBondConfigEquiv eZ τ f) j * L f j (graphBondConfigEquiv eX σ f))).symm

/-- Identity maps on all bonds give the identity in numbered coordinates. -/
@[simp] theorem graphNumberedBondFamilyMatrix_one [DecidableEq X]
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p) :
    graphNumberedBondFamilyMatrix e e (fun _ => (1 : Matrix (X × X) (X × X) ℂ)) = 1 := by
  classical
  rw [graphNumberedBondFamilyMatrix_eq_submatrix]
  ext τ σ
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Matrix.one_apply, Fintype.prod_boole,
    ← funext_iff, Equiv.apply_eq_iff_eq]

/-- Edgewise right inverses assemble into a right inverse on the full
numbered physical space. -/
theorem graphNumberedBondFamilyMatrix_mul_eq_one [Fintype X] [DecidableEq Y]
    (eX : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (eY : (v : V) → (IncidentEdge Γ v → Y) ≃ Fin q)
    (F : Edge Γ → Matrix (Y × Y) (X × X) ℂ)
    (L : Edge Γ → Matrix (X × X) (Y × Y) ℂ)
    (h : ∀ f, F f * L f = 1) :
    graphNumberedBondFamilyMatrix eX eY F * graphNumberedBondFamilyMatrix eY eX L = 1 := by
  rw [graphNumberedBondFamilyMatrix_mul]
  simp only [h, graphNumberedBondFamilyMatrix_one]

end TNLean.PEPS
