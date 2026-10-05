/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenSemiRegularSupport
import TNLean.PEPS.PhysicalProductRangeSupport

/-!
# Product bond support of the repeated-representation canonical parent

Every actual open-region contraction of the multiplicity-restored representation
has internal-bond slices in the multiplicity-restoring product range. The
coherent weights retain all target boundary factors. Covering each edge by an
internal bond of a parent region then puts every actual parent ground vector in
the full product range, without any assumption on closed-state spanning.

Source: SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2977–3019.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {f : Edge Γ // f.1.1 ∈ R ∧ f.1.2 ∈ R}
private abbrev RB (R : Finset V) := {f : Edge Γ // IsRegionBoundaryEdge R f}
variable {G I : Type*} [Group G] [Fintype G] [Fintype I] [DecidableEq I]

/-- Dressing by the identity gives the original averaging-site tensor. -/
@[simp] theorem graphDressedAveragingSite_one {X : Type*} [Fintype X] [DecidableEq X]
    (U : G →* Matrix X X ℂ) :
    graphDressedAveragingSite (Γ := Γ) U 1 = graphAveragingSite U := by
  funext v η σ
  exact graphDress_one v (fun ξ => graphAveragingSite U v ξ σ) η

/-- The actual target open contraction has an explicit preimage under the
internal multiplicity-restoring product, with its own arbitrary boundary
factors retained. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphRegionInternalBondSlice_multiplicityRestored_mem_range
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (θ σ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i)) :
    graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (Γ := Γ)
        (graphAveragingSite (multiplicityRestoredRepresentation d D)) R θ) ∈
      LinearMap.range (physicalProductMap (RI (Γ := Γ) R)
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))) := by
  have hslice := graphRegionInternalBondSlice_dressedAveragingSite
    (Γ := Γ) (multiplicityRestoredRepresentation d D) 1
    (fun _ => Commute.one_left _) R θ σ
  simp only [graphDressedAveragingSite_one, one_pow, one_mul] at hslice
  rw [hslice]
  have hr := (coherentWeightedBlocks_support_restore
    (E := RI (Γ := Γ) R) (Q := RV R → G) (A := G) d (fun i g => D i g)
    (fun g => blockFourthRootWeight d ^ 2 * blockMatrixRepresentation d D g)
    (blockFourthRootWeight_sq_mul d D) hd
    (graphOpenAveragingBoundaryCoefficient (multiplicityRestoredRepresentation d D)
      1 R θ σ)
    (fun q f => q ⟨f.1.1.2, f.2.2⟩ * (q ⟨f.1.1.1, f.2.1⟩)⁻¹)).2
  exact ⟨_, hr⟩

/-- Numbered open-region columns and native incidence columns have identical
internal slices under the actual physical enumerations. -/
theorem regionInternalBondSlice_openRegionWeight {X : Type*} [Fintype X] {p : ℕ}
    (a : (v : V) → (IncidentEdge Γ v → X) → (IncidentEdge Γ v → X) → ℂ)
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (θ σ : RB (Γ := Γ) R → X) :
    regionInternalBondSlice e R σ
      (openRegionWeight (groupBondTensor (fun v η s => a v η ((e v).symm s)))
        R (fun f => Fintype.equivFin X (θ f))) =
      graphRegionInternalBondSlice R σ (graphOpenRegionNetwork a R θ) := by
  funext β
  change openRegionWeight _ R _ _ = graphOpenRegionNetwork a R θ _
  rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork]
  simp only [graphOpenRegionNetwork, Equiv.symm_apply_apply]

/-- Every genuine regional target ground vector has internal slices in the
multiplicity-restoring product range. This follows from all actual virtual
boundary columns. Source: SCP10, Theorem 5.7 and Section 7, lines 2977–3019. -/
theorem regionInternalBondSlice_mem_fullMultiplicityRange {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin p)
    (R : Finset V) (σ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i))
    {ψ : RegionPhysicalConfig (d := p) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor (fun v η s =>
      graphAveragingSite (multiplicityRestoredRepresentation d D)
        v η ((e v).symm s))) R) :
    regionInternalBondSlice e R σ ψ ∈ LinearMap.range
      (physicalProductMap (RI (Γ := Γ) R)
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))) := by
  classical
  let A := groupBondTensor (fun v η s =>
    graphAveragingSite (multiplicityRestoredRepresentation d D) v η ((e v).symm s))
  let S := LinearMap.range (physicalProductMap (RI (Γ := Γ) R)
    (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))))
  have hle : regionGroundSpace A R ≤ S.comap (regionInternalBondSlice e R σ) := by
    apply (regionGroundSpace_le_iff A R _).mpr
    intro μ
    let θ : RB (Γ := Γ) R → Σ i, Fin (d i) × Fin (d i) :=
      fun f => (Fintype.equivFin (Σ i, Fin (d i) × Fin (d i))).symm (μ f)
    have hμ : (fun f => Fintype.equivFin (Σ i, Fin (d i) × Fin (d i)) (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply _ _
    have hslice : regionInternalBondSlice e R σ (openRegionWeight A R μ) =
        graphRegionInternalBondSlice R σ (graphOpenRegionNetwork
          (graphAveragingSite (multiplicityRestoredRepresentation d D)) R θ) := by
      rw [← hμ]
      exact regionInternalBondSlice_openRegionWeight
        (graphAveragingSite (multiplicityRestoredRepresentation d D)) e R θ σ
    change regionInternalBondSlice e R σ (openRegionWeight A R μ) ∈ S
    rw [hslice]
    exact graphRegionInternalBondSlice_multiplicityRestored_mem_range d D hd R θ σ
  exact hle hψ

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem regionHalfEdgeLabelEquiv_global_update {X : Type*}
    (R : Finset V) (β : Edge Γ → X × X) (f : RI (Γ := Γ) R) (s : X × X) :
    regionHalfEdgeLabelEquiv R
      (fun v => graphSiteBondEndpointEquiv.symm (Function.update β f.1 s) v.1) =
      ((regionHalfEdgeLabelEquiv R
          (fun v => graphSiteBondEndpointEquiv.symm β v.1)).1,
        (fun g => (Function.update (fun g : RI (Γ := Γ) R => β g.1) f s g).2),
        fun g => (Function.update (fun g : RI (Γ := Γ) R => β g.1) f s g).1) := by
  classical
  have hupdate (g : RI (Γ := Γ) R) :
      Function.update β f.1 s g.1 =
        Function.update (fun g : RI (Γ := Γ) R => β g.1) f s g := by
    by_cases h : g = f
    · subst g
      simp only [Function.update_self]
    · rw [Function.update_of_ne h, Function.update_of_ne (Subtype.coe_ne_coe.mpr h)]
  apply Prod.ext
  · funext g
    have hne : g.1 ≠ f.1 := by
      intro h
      have hg : IsRegionBoundaryEdge R f.1 := h ▸ g.2
      rcases hg with ht | hh
      · exact ht.2 f.2.2
      · exact hh.1 f.2.1
    by_cases ht : g.1.1.1 ∈ R
    · simp only [regionHalfEdgeLabelEquiv_apply_boundary_tail R _ g ht,
        graphSiteBondEndpointEquiv_symm_tail, Function.update_of_ne hne]
    · have hh : g.1.1.2 ∈ R := (g.2.resolve_left (fun h => ht h.1)).2
      simp only [regionHalfEdgeLabelEquiv_apply_boundary_head R _ g hh,
        graphSiteBondEndpointEquiv_symm_head, Function.update_of_ne hne]
  · apply Prod.ext <;> funext g
    · simp only [regionHalfEdgeLabelEquiv_apply_internal_tail,
        graphSiteBondEndpointEquiv_symm_tail, hupdate]
    · simp only [regionHalfEdgeLabelEquiv_apply_internal_head,
        graphSiteBondEndpointEquiv_symm_head, hupdate]

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem graphSiteBondEndpointEquiv_update_outside {X : Type*}
    (R : Finset V) (β : Edge Γ → X × X) (f : RI (Γ := Γ) R) (s : X × X)
    (v : V) (hv : v ∉ R) :
    graphSiteBondEndpointEquiv.symm (Function.update β f.1 s) v =
      graphSiteBondEndpointEquiv.symm β v := by
  classical
  funext g
  have hne : g.1 ≠ f.1 := by
    intro h
    have hg : f.1.1.1 = v ∨ f.1.1.2 = v := h ▸ g.2
    rcases hg with ht | hh
    · exact hv (ht ▸ f.2.1)
    · exact hv (hh ▸ f.2.2)
  simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
    Function.update_of_ne hne]

omit [DecidableRel Γ.Adj] in
/-- An internal one-bond slice of a regional slice is the same one-bond slice
of the global vector, after the actual incidence regrouping. -/
theorem regionInternalBondSlice_regionSliceMap_update {X : Type*} {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (β : Edge Γ → X × X) (f : RI (Γ := Γ) R)
    (ψ : (V → Fin p) → ℂ) (s : X × X) :
    regionInternalBondSlice e R
        (regionHalfEdgeLabelEquiv R
          (fun v => graphSiteBondEndpointEquiv.symm β v.1)).1
        (regionSliceMap R (fun v => e v.1 (graphSiteBondEndpointEquiv.symm β v.1)) ψ)
        (Function.update (fun g : RI (Γ := Γ) R => β g.1) f s) =
      ψ (fun v => e v (graphSiteBondEndpointEquiv.symm (Function.update β f.1 s) v)) := by
  classical
  have hreg := congrArg (regionHalfEdgeLabelEquiv (Γ := Γ) R).symm
    (regionHalfEdgeLabelEquiv_global_update R β f s)
  simp only [Equiv.symm_apply_apply] at hreg
  change ψ (assembleRegionσ R _ _) = _
  congr 1
  funext v
  by_cases hv : v ∈ R
  · simp only [assembleRegionσ, hv, dite_true]
    rw [← hreg]
  · simp only [assembleRegionσ, hv, dite_false]
    rw [graphSiteBondEndpointEquiv_update_outside R β f s v hv]

/-- Edge-covering actual parent constraints force the full product range
whenever every actual regional internal slice lies in the corresponding
internal product range. This statement imposes no rank condition on the map. -/
theorem regionParentGroundSpace_mem_product_range_of_internal_slices
    {X In : Type*} [Finite X] [Fintype In] {p : ℕ}
    (A : Tensor Γ p) (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (F : Matrix (X × X) In ℂ) {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    (hsupport : ∀ i σ (φ : RegionPhysicalConfig (d := p) (R i) → ℂ),
      φ ∈ regionGroundSpace A (R i) →
        regionInternalBondSlice e (R i) σ φ ∈
          LinearMap.range (physicalProductMap (RI (Γ := Γ) (R i)) F))
    {ψ : (V → Fin p) → ℂ} (hψ : ψ ∈ regionParentGroundSpace A R) :
    (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
      LinearMap.range (physicalProductMap (Edge Γ) F) := by
  classical
  apply (mem_range_physicalProductMap_iff F _).mpr
  intro f β
  obtain ⟨i, ht, hh⟩ := hcover f
  let fR : RI (Γ := Γ) (R i) := ⟨f, ht, hh⟩
  have hlocal := (mem_regionParentGroundSpace_iff A R ψ).mp hψ i
    (fun v => e v.1 (graphSiteBondEndpointEquiv.symm β v.1))
  have hs := hsupport i (regionHalfEdgeLabelEquiv (R i)
    (fun v => graphSiteBondEndpointEquiv.symm β v.1)).1 _ hlocal
  have hone := (mem_range_physicalProductMap_iff F _).mp hs fR
    (fun g : RI (Γ := Γ) (R i) => β g.1)
  simpa only [regionInternalBondSlice_regionSliceMap_update, fR] using hone

/-- Every actual canonical parent ground vector for the repeated
representation lies in the full multiplicity-restoring bond product range,
provided the parent regions contain both endpoints of every edge. Neither a
closed-state span nor a parent-kernel equality is assumed.
Source: SCP10, Theorem 5.7 and Section 7, lines 2977–3019. -/
theorem regionParentGroundSpace_mem_product_fullMultiplicityRange {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i) × Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (groupBondTensor (fun v η s =>
      graphAveragingSite (multiplicityRestoredRepresentation d D)
        v η ((e v).symm s))) R) :
    (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
      LinearMap.range (physicalProductMap (Edge Γ)
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i)))) := by
  exact regionParentGroundSpace_mem_product_range_of_internal_slices _ e _ R hcover
    (fun i σ φ hφ => regionInternalBondSlice_mem_fullMultiplicityRange
      d D hd e (R i) σ hφ) hψ

end TNLean.PEPS
