/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularInvariantStateSpan
import TNLean.PEPS.ParentHamiltonian.RegionVertexImageSupport
import TNLean.PEPS.ParentHamiltonian.RegularRegionBondRightInvariance
import TNLean.PEPS.ParentHamiltonian.RegularRegionFlatness
import TNLean.PEPS.ParentHamiltonian.VertexInverseRegionSlice

/-!
# Global regular coordinates of arbitrary parent ground vectors

Let each site map be invariant under simultaneous left translation and injective
on the invariant subspace. Choose local maps whose composition with the site
maps is the regular averaging projector. If a collection of parent regions
covers the vertices, a vector satisfying all regional parent conditions is
recovered by applying the chosen maps and then the original site maps.
Ordinary injectivity on the entire virtual space is not needed.

The exposed vector is invariant under independent vertex translations. Its
regional slices inherit shared internal-edge right invariance and vanish at
nonidentity cycle coordinates. These statements concern arbitrary physical
parent ground vectors; no inserted-bond expression for the vector is assumed.

Source: Schuch, Cirac, and Pérez-García, arXiv:1001.3807, Definition 5.1,
Theorems 5.5 and 5.7, and the accessible regular coordinates in Section 6. The
results here concern the regular representation on finite simple graphs.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Restore the physical vector from independent group-labelled half-edges,
by applying the original site tensor at every vertex. -/
noncomputable def globalRegularTensorMap
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) :
    (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) →ₗ[ℂ] ((V → Fin d) → ℂ) :=
  (fullRegionPhysicalEquiv d).symm.toLinearMap ∘ₗ
    regionPhysicalMap Finset.univ (fun v => Matrix.of (fun s α => a v α s))

private theorem regularSiteRetraction_component
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (v : V) (η : IncidentEdge Γ v → G) :
    ((Matrix.of (fun s α => a v α s)) * F v) *ᵥ a v η = a v η := by
  rw [← Matrix.mulVec_mulVec]
  have h : F v *ᵥ a v η = fun α => regularLegProjector (IncidentEdge Γ v) α η := by
    funext α
    exact hF v α η
  rw [h]
  funext s
  exact (ha v).regularSiteMap_projector_coefficients s η

/-- The regular local inverse followed by the site tensor fixes the full
physical image of that tensor, including tensors that are not ordinarily
injective. Source: SCP10, Definition 5.1(ii). -/
theorem regularSiteRetraction_eq_self_of_mem_range
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (v : V) {q : Fin d → ℂ} (hq : q ∈ (localTensorMap (groupBondTensor a) v).range) :
    ((Matrix.of (fun s α => a v α s)) * F v) *ᵥ q = q := by
  classical
  obtain ⟨x, rfl⟩ := hq
  change Matrix.mulVecLin _ (∑ η, x η • (groupBondTensor a).component v η) = _
  rw [map_sum]
  simp only [map_smul]
  apply Finset.sum_congr rfl
  intro η _
  congr 1
  exact regularSiteRetraction_component a ha F hF v _

/-- Product reconstruction on the common site-image space using only regular
G-injectivity. Source: SCP10, the local inverse of Definition 5.1(ii). -/
theorem globalRegularTensorMap_inverse_eq_self_of_mem_vertexImage
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    {Ψ : (V → Fin d) → ℂ} (hΨ : Ψ ∈ vertexImageGroundSpace (groupBondTensor a)) :
    globalRegularTensorMap a (globalDependentPhysicalMap F Ψ) = Ψ := by
  classical
  let P : V → Matrix (Fin d) (Fin d) ℂ :=
    fun v => (Matrix.of (fun s α => a v α s)) * F v
  have hone (v : V) : globalPhysicalMap (oneVertexPhysicalFamily v (P v)) Ψ = Ψ := by
    funext τ
    rw [globalPhysicalMap_oneVertex_apply]
    have h := regularSiteRetraction_eq_self_of_mem_range a ha F hF v
      ((mem_vertexImageGroundSpace_iff _ _).mp hΨ v τ)
    have hτ := congrFun h (τ v)
    simpa only [Matrix.mulVec, dotProduct, vertexPhysicalSlice, LinearMap.coe_mk,
      AddHom.coe_mk, Function.update_eq_self] using hτ
  have h := globalPhysicalMap_fixed_of_oneVertex_fixed P Ψ hone
  change (fullRegionPhysicalEquiv d).symm
    (regionPhysicalMap Finset.univ (fun v => Matrix.of (fun s α => a v α s))
      (regionPhysicalMap Finset.univ F
      (fullRegionPhysicalEquiv d Ψ))) = Ψ
  rw [← LinearMap.comp_apply, regionPhysicalMap_comp]
  exact h

/-- Covering parent regions supply all the support needed for exact regular
inverse reconstruction of an arbitrary physical ground vector.
Source: SCP10, Theorem 5.7 and Definition 5.1(ii). -/
theorem globalRegularTensorMap_inverse_eq_self_of_mem_parent
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    {ι : Type*} (R : ι → Finset V) (hcover : ∀ v, ∃ i, v ∈ R i)
    {Ψ : (V → Fin d) → ℂ} (hΨ : Ψ ∈ regionParentGroundSpace (groupBondTensor a) R) :
    globalRegularTensorMap a (globalDependentPhysicalMap F Ψ) = Ψ :=
  globalRegularTensorMap_inverse_eq_self_of_mem_vertexImage a ha F hF
    (regionParentGroundSpace_le_vertexImageGroundSpace (groupBondTensor a) R hcover hΨ)

private theorem regularLegProjector_leftMul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (g : G) (α η : ι → G) :
    regularLegProjector ι (g • α) η = regularLegProjector ι α η := by
  have h := (regularLegRepresentation (G := G) ι).averageMap_invariant
    (Pi.single η (1 : ℂ)) g⁻¹
  have hα := congrFun h α
  simpa only [regularLegProjector, LinearMap.toMatrix'_apply,
    regularLegRepresentation_apply, inv_inv] using hα

/-- The exposed global vector is fixed by independent left translation at
all vertices. Only site-image support and the projector inverse equations
are required. Source: SCP10, Definition 5.1 and accessible coordinates in §6. -/
theorem globalDependentPhysicalMap_regularInverse_leftMul
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v)))
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    {Ψ : (V → Fin d) → ℂ} (hΨ : Ψ ∈ vertexImageGroundSpace (groupBondTensor a))
    (k : V → G) (α : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ) :
    globalDependentPhysicalMap F Ψ (fun w e => k w.1 * α w e) =
      globalDependentPhysicalMap F Ψ α := by
  classical
  let φ := globalDependentPhysicalMap F Ψ
  have hrec := globalRegularTensorMap_inverse_eq_self_of_mem_vertexImage a ha F hF hΨ
  have hproj : regionPhysicalMap Finset.univ
      (fun v => regularLegProjector (G := G) (IncidentEdge Γ v)) φ = φ := by
    have h := congrArg (globalDependentPhysicalMap F) hrec
    change regionPhysicalMap Finset.univ F
      ((fullRegionPhysicalEquiv d) ((fullRegionPhysicalEquiv d).symm
        (regionPhysicalMap Finset.univ (fun v => Matrix.of (fun s η => a v η s)) φ))) = φ at h
    rw [LinearEquiv.apply_symm_apply, ← LinearMap.comp_apply, regionPhysicalMap_comp] at h
    have hmat : (fun v => F v * (Matrix.of (fun s η => a v η s))) =
        fun v => regularLegProjector (G := G) (IncidentEdge Γ v) := by
      funext v η θ
      exact hF v η θ
    rwa [hmat] at h
  change φ (fun w e => k w.1 * α w e) = φ α
  rw [← hproj]
  simp only [regionPhysicalMap_apply]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  apply Finset.prod_congr rfl
  intro w _
  exact regularLegProjector_leftMul (k w.1) (α w) (β w)

/-- Global inverse slices inherit shared internal-edge right invariance from
the original local parent equation. Source: SCP10, Theorems 5.5 and 5.7. -/
theorem dependentRegionSlice_regularInverse_halfEdgeRightMul
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) R P)
    (Ψ : (V → Fin d) → ℂ) (hΨ : regionLocalTerm R P *ᵥ Ψ = 0)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ (globalDependentPhysicalMap F Ψ)
        (regularRegionHalfEdgeRightMul R r α) =
      dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ
        (globalDependentPhysicalMap F Ψ) α := by
  classical
  rw [dependentRegionSlice_globalDependentPhysicalMap]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro β _
  congr 1
  exact regionPhysicalMap_slice_halfEdgeRightMul_of_parent_annihilates
    a F hF R r hr P hP Ψ hΨ β α

/-- Global inverse slices vanish at any nonidentity regional cycle coordinate.
Source: SCP10, the inverse closure argument in Theorem 5.5. -/
theorem dependentRegionSlice_regularInverse_apply_eq_zero_of_cycle_ne_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (T : SimpleGraph {v : V // v ∈ R}) [DecidableRel T.Adj]
    (hT : T ≤ Γ.induce (R : Set V)) (htree : T.IsTree) (o : {v : V // v ∈ R})
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) R P)
    (Ψ : (V → Fin d) → ℂ) (hΨ : regionLocalTerm R P *ᵥ Ψ = 0)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R))
    (c : RegularRegionCoordinates (Γ := Γ) (G := G) R T o) (hc : c.2.2.2 ≠ 1) :
    dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ (globalDependentPhysicalMap F Ψ)
      ((regularRegionCoordinatesEquiv R T hT htree o).symm c) = 0 := by
  classical
  rw [dependentRegionSlice_globalDependentPhysicalMap]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro β _
  rw [regionPhysicalMap_slice_apply_eq_zero_of_parent_annihilates
    a F hF R T hT htree o P hP Ψ hΨ β c hc, mul_zero]

/-- Exposing the whole physical state gives shared right invariance on an edge
whenever one parent region contains both of its endpoints. -/
theorem globalDependentPhysicalMap_regularInverse_singleEdgeRightMul
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (e : Edge Γ) (he : e.1.1 ∈ R ∧ e.1.2 ∈ R) (g : G)
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) R P)
    (Ψ : (V → Fin d) → ℂ) (hΨ : regionLocalTerm R P *ᵥ Ψ = 0)
    (α : RegularHalfEdgeConfig Γ G) :
    globalDependentPhysicalMap F Ψ
        (fun w => regularHalfEdgeRightMul (Function.update 1 e g) α w.1) =
      globalDependentPhysicalMap F Ψ (fun w => α w.1) := by
  classical
  let r := Function.update (1 : Edge Γ → G) e g
  have hr : ∀ f, IsRegionBoundaryEdge R f → r f = 1 := by
    intro f hf
    have hne : f ≠ e := by
      rintro rfl
      rcases hf with h | h
      · exact h.2 he.2
      · exact h.1 he.1
    simp [r, Function.update_of_ne hne]
  let β : RegionHalfEdgeConfig (Γ := Γ) G R := fun w => α w.1
  let τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R) := fun w => α w.1
  have h := dependentRegionSlice_regularInverse_halfEdgeRightMul
    a F hF R r hr P hP Ψ hΨ τ β
  have hbase : assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ =
      fun w : {v : V // v ∈ Finset.univ} => α w.1 := by
    funext w f
    simp only [assembleDependentRegionConfig, β, τ]
    split_ifs <;> rfl
  have htrans : assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R
      (regularRegionHalfEdgeRightMul R r β) τ =
      fun w : {v : V // v ∈ Finset.univ} => regularHalfEdgeRightMul r α w.1 := by
    funext w f
    by_cases hw : w.1 ∈ R
    · simp [assembleDependentRegionConfig, hw, regularRegionHalfEdgeRightMul,
        regularHalfEdgeRightMul, β]
    · have hne : f.1 ≠ e := by
        intro hfe
        have hf := f.2
        rw [hfe] at hf
        rcases hf with hf | hf
        · exact hw (hf ▸ he.1)
        · exact hw (hf ▸ he.2)
      simp [assembleDependentRegionConfig, hw, τ, regularHalfEdgeRightMul,
        r, Function.update_of_ne hne]
  change globalDependentPhysicalMap F Ψ _ = globalDependentPhysicalMap F Ψ _ at h
  rwa [hbase, htrans] at h

/-- If each edge lies inside one parent region, all shared right translations
preserve the exposed arbitrary physical ground vector. No flat-connection
representation is assumed. Source: SCP10, accessible regular coordinates, §6. -/
theorem globalDependentPhysicalMap_regularInverse_rightMul
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ e : Edge Γ, ∃ i, e.1.1 ∈ R i ∧ e.1.2 ∈ R i)
    (P : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (hP : ∀ i, IsRegionParentInteraction (groupBondTensor a) (R i) (P i))
    (Ψ : (V → Fin d) → ℂ) (hΨ : ∀ i, regionLocalTerm (R i) (P i) *ᵥ Ψ = 0)
    (r : Edge Γ → G) (α : RegularHalfEdgeConfig Γ G) :
    globalDependentPhysicalMap F Ψ (fun w => regularHalfEdgeRightMul r α w.1) =
      globalDependentPhysicalMap F Ψ (fun w => α w.1) := by
  classical
  let φ : RegularHalfEdgeConfig Γ G → ℂ := fun α =>
    globalDependentPhysicalMap F Ψ (fun w => α w.1)
  have hsingle (e : Edge Γ) (g : G) (β : RegularHalfEdgeConfig Γ G) :
      φ (regularHalfEdgeRightMul (Function.update 1 e g) β) = φ β := by
    obtain ⟨i, he⟩ := hcover e
    exact globalDependentPhysicalMap_regularInverse_singleEdgeRightMul
      a F hF (R i) e he g (P i) (hP i) Ψ (hΨ i) β
  let rS (S : Finset (Edge Γ)) : Edge Γ → G := fun e => if e ∈ S then r e else 1
  have hS (S : Finset (Edge Γ)) : φ (regularHalfEdgeRightMul (rS S) α) = φ α := by
    induction S using Finset.induction with
    | empty =>
      change φ (fun v e => α v e * 1) = φ α
      simp only [mul_one]
    | @insert e S he ih =>
      have haction : regularHalfEdgeRightMul (rS (insert e S)) α =
          regularHalfEdgeRightMul (Function.update 1 e (r e))
            (regularHalfEdgeRightMul (rS S) α) := by
        funext v f
        by_cases hf : f.1 = e
        · simp [regularHalfEdgeRightMul, rS, hf, he]
        · simp [regularHalfEdgeRightMul, rS, hf]
      rw [haction, hsingle, ih]
  simpa only [rS, Finset.mem_univ, ite_true] using hS Finset.univ

/-- The exposed vector vanishes whenever the quotient of its half-edge labels
has nontrivial holonomy on a closed walk inside a connected parent region.
Source: SCP10, converse closure constraints in Theorem 5.5. -/
theorem globalDependentPhysicalMap_regularInverse_eq_zero_of_holonomy_ne_one
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (F : (v : V) → Matrix (IncidentEdge Γ v → G) (Fin d) ℂ)
    (hF : ∀ v α η, (∑ s : Fin d, F v α s * a v η s) =
      regularLegProjector (IncidentEdge Γ v) α η)
    (R : Finset V) (hR : (Γ.induce (R : Set V)).Connected)
    (o : {v : V // v ∈ R}) (p : (Γ.induce (R : Set V)).Walk o o)
    (P : Matrix (RegionPhysicalConfig (d := d) R) (RegionPhysicalConfig (d := d) R) ℂ)
    (hP : IsRegionParentInteraction (groupBondTensor a) R P)
    (Ψ : (V → Fin d) → ℂ) (hΨ : regionLocalTerm R P *ᵥ Ψ = 0)
    (α : RegularHalfEdgeConfig Γ G)
    (hhol : regularWalkHolonomy
      (regularRegionInternalOperators R (regularHalfEdgeOperators α)) p ≠ 1) :
    globalDependentPhysicalMap F Ψ (fun w => α w.1) = 0 := by
  classical
  obtain ⟨T, hT, htree⟩ := hR.exists_isTree_le
  let β : RegionHalfEdgeConfig (Γ := Γ) G R := fun w => α w.1
  let c := regularRegionCoordinatesEquiv R T hT htree o β
  have hdecode : (regularRegionCoordinatesEquiv R T hT htree o).symm c = β :=
    (regularRegionCoordinatesEquiv R T hT htree o).symm_apply_apply β
  have hc : c.2.2.2 ≠ 1 := by
    intro hc
    apply hhol
    have hops : regularRegionInternalOperators R (regularHalfEdgeOperators α) =
        fun e => c.2.2.1.1 e.1.2 * (c.2.2.1.1 e.1.1)⁻¹ := by
      funext e
      let f := inducedRegionEdgeEquiv R e
      have ht := regularRegionCoordinatesEquiv_symm_internal_tail R T hT htree o c f
      have hh := regularRegionCoordinatesEquiv_symm_internal_head R T hT htree o c f
      rw [hdecode] at ht hh
      change α e.1.1.1 _ = _ at ht
      change α e.1.2.1 _ = _ at hh
      change α e.1.2.1 _ * (α e.1.1.1 _)⁻¹ = _
      rw [ht, hh, hc]
      simp only [Pi.one_apply]
      split_ifs <;> dsimp [f, inducedRegionEdgeEquiv] <;> group
    rw [hops]
    exact regularWalkHolonomy_gradient_loop _ p
  let τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R) := fun w => α w.1
  have h := dependentRegionSlice_regularInverse_apply_eq_zero_of_cycle_ne_one
    a F hF R T hT htree o P hP Ψ hΨ τ c hc
  rw [hdecode] at h
  have hassemble : assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ =
      fun w : {v : V // v ∈ Finset.univ} => α w.1 := by
    funext w f
    simp only [assembleDependentRegionConfig, β, τ]
    split_ifs <;> rfl
  change globalDependentPhysicalMap F Ψ _ = 0 at h
  rwa [hassemble] at h

/-- Restoring a closed canonical regular-projector vector gives the original
PEPS with the same inserted edge operators. Source: SCP10, accessible inverse
coordinates in Section 6 and the closure definition following Theorem 5.5. -/
theorem globalRegularTensorMap_regularProjectorClosedState
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (ha : ∀ v, IsGInjective (regularLegRepresentation (IncidentEdge Γ v))
      (regularSiteMap (a v))) (u : Edge Γ → G) :
    globalRegularTensorMap a
        (fun α => regularProjectorClosedState u (fullRegionHalfEdgeConfigEquiv α)) =
      stateCoeff (groupBondTensor (regularTwistedSite a u)) := by
  classical
  funext σ
  change regionPhysicalMap Finset.univ (fun v => Matrix.of (fun s α => a v α s))
    (fun α => regularProjectorClosedState u (fullRegionHalfEdgeConfigEquiv α))
      (fun w => σ w.1) = _
  rw [regionPhysicalMap_apply]
  trans ∑ α : RegularHalfEdgeConfig Γ G,
    (∏ v, a v (α v) (σ v)) * regularProjectorClosedState u α
  · apply Fintype.sum_equiv fullRegionHalfEdgeConfigEquiv
    intro α
    congr 1
    exact (Finset.prod_subtype Finset.univ (fun _ => Iff.rfl)
      (fun v => a v (α ⟨v, Finset.mem_univ v⟩) (σ v))).symm
  · exact sum_regularProjectorClosedState_eq_stateCoeff a ha u σ

end TNLean.PEPS
