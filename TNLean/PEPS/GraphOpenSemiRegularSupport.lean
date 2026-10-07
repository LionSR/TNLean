/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphOpenAveragingBondState
import TNLean.PEPS.CoherentMultiplicityTransport
import TNLean.PEPS.TorusBlockMultiplicityState
import TNLean.PEPS.ParentHamiltonian.RegionPhysicalGroundSpaceTransport

/-!
# Internal bond support of every semi-regular regional ground vector

Fix the physical endpoints of all crossing bonds of a region. The remaining
physical vector, indexed by internal endpoint pairs, is a coherent product of
the matrices Θ²V(q_head q_tail⁻¹). For positive block dimensions, every such
vector has matching-sector support on every internal bond. This holds for
every genuine regional ground vector and arbitrary virtual boundary data.

The internal multiplicity-restoring map acts on this open contraction term by
term. The crossing-bond factors remain the original ΘV(q_tail⁻¹) or V(q_head)Θ;
they are not silently replaced by regular-representation boundary data.

Source: the arbitrary-boundary regional contractions of SCP10,
arXiv:1001.3807, lines 1765–1920 and 1935–1957, and the semi-regular
bond transformation in Section 7, lines 2977–3019. This is a local-support
step toward transport of canonical parent kernels, not the complete transport.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RI (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}
variable {X G : Type*} [Fintype X] [DecidableEq X] [Group G] [Fintype G]

/-- The retained factors of the physical crossing endpoints, including the
normalization of the site averages. The virtual boundary labels are arbitrary.
Source: SCP10, Section 7, equations preceding the endpoint-pair isometry. -/
def graphOpenAveragingBoundaryCoefficient (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ)
    (R : Finset V) (θ σ : RB (Γ := Γ) R → X) (q : RV R → G) : ℂ :=
  (Fintype.card G : ℂ)⁻¹ ^ R.card *
    ∏ e : RB (Γ := Γ) R, if h : e.1.1.1 ∈ R then
      (W * U ((q ⟨e.1.1.1, h⟩)⁻¹)) (θ e) (σ e)
    else (U (q ⟨e.1.1.2, (e.2.resolve_left (fun h' => h h'.1)).2⟩) * W)
      (σ e) (θ e)

omit [Group G] [Fintype G] [DecidableEq X] in
/-- Fix the retained physical crossing endpoints and regroup all internal
physical endpoints into head-tail pairs. -/
def graphRegionInternalBondSlice (R : Finset V) (σ : RB (Γ := Γ) R → X) :
    (RegionHalfEdgeConfig (Γ := Γ) X R → ℂ) →ₗ[ℂ]
      ((RI (Γ := Γ) R → X × X) → ℂ) where
  toFun ψ β := ψ ((regionHalfEdgeLabelEquiv R).symm
    (σ, (fun e => (β e).2), fun e => (β e).1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Every internal-bond slice of the actual open weighted contraction is a
coherent product of weighted relative representation matrices, with the
full boundary factors retained. Source: SCP10, Section 7, lines 2977–3019. -/
theorem graphRegionInternalBondSlice_dressedAveragingSite
    (U : G →* Matrix X X ℂ) (W : Matrix X X ℂ) (hc : ∀ g, Commute W (U g))
    (R : Finset V) (θ σ : RB (Γ := Γ) R → X) :
    graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (Γ := Γ) (graphDressedAveragingSite (Γ := Γ) U W) R θ) =
      fun β => ∑ q : RV R → G, graphOpenAveragingBoundaryCoefficient U W R θ σ q *
        ∏ e : RI (Γ := Γ) R,
          (W ^ 2 * U (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹))
            (β e).1 (β e).2 := by
  funext β
  calc
    _ = graphOpenAveragingBondState U W R θ
        (σ, (fun e => (β e).2), fun e => (β e).1) :=
      graphOpenBondRegrouping_dressedAveragingSite (Γ := Γ) U W hc R θ _
    _ = _ := by
      unfold graphOpenAveragingBondState graphOpenAveragingBoundaryCoefficient
      apply Finset.sum_congr rfl
      intro q _
      exact (mul_assoc _ _ _).symm.trans (mul_right_comm _ _ _)

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Every open weighted contraction has matching block sectors on its
internal bonds, and multiplicity restoration acts on those internal bonds
without changing the retained boundary factors. Source: SCP10, Section 7,
lines 2977–3019, with arbitrary virtual boundary conditions. -/
theorem graphRegionInternalBondSlice_blockFourthRootWeight
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i) (R : Finset V)
    (θ σ : RB (Γ := Γ) R → Σ i, Fin (d i)) :
    let U := blockMatrixRepresentation d D
    let W := blockFourthRootWeight d
    let ψ := graphRegionInternalBondSlice R σ
      (graphOpenRegionNetwork (Γ := Γ) (graphDressedAveragingSite (Γ := Γ) U W) R θ)
    ψ ∈ LinearMap.range
      (physicalProductMap (RI (Γ := Γ) R) (blockBondInclusion (fun i => Fin (d i)))) ∧
      physicalProductMap (RI (Γ := Γ) R)
        (fullMultiplicityBondMap (fun i => Fin (d i)) (fun i => Fin (d i))) ψ =
        fun β => ∑ q : RV R → G, graphOpenAveragingBoundaryCoefficient U W R θ σ q *
          ∏ e : RI (Γ := Γ) R,
            multiplicityRestoredRepresentation d D
              (q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹) (β e).1 (β e).2 := by
  dsimp only
  rw [graphRegionInternalBondSlice_dressedAveragingSite _ _
    (blockFourthRootWeight_commute d D)]
  exact coherentWeightedBlocks_support_restore
    (E := RI (Γ := Γ) R) (Q := RV R → G) (A := G) d (fun i g => D i g)
    (fun g => blockFourthRootWeight d ^ 2 * blockMatrixRepresentation d D g)
    (blockFourthRootWeight_sq_mul d D) hd
    (graphOpenAveragingBoundaryCoefficient (blockMatrixRepresentation d D)
      (blockFourthRootWeight d) R θ σ)
    (fun q e => q ⟨e.1.1.2, e.2.2⟩ * (q ⟨e.1.1.1, e.2.1⟩)⁻¹)

omit [Group G] [Fintype G] [Fintype I] [DecidableEq I] [DecidableEq X] in
/-- The same internal-bond slice in the numbered physical coordinates of the
actual regional parent construction. -/
def regionInternalBondSlice {p : ℕ}
    (e : (v : V) → (IncidentEdge Γ v → X) ≃ Fin p)
    (R : Finset V) (σ : RB (Γ := Γ) R → X) :
    (RegionPhysicalConfig (d := p) R → ℂ) →ₗ[ℂ]
      ((RI (Γ := Γ) R → X × X) → ℂ) where
  toFun ψ β := ψ (fun v => e v.1 ((regionHalfEdgeLabelEquiv R).symm
    (σ, (fun f => (β f).2), fun f => (β f).1) v))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Genuine regional ground vectors, rather than only one closed state, have
matching-sector support on all internal bonds after fixing the physical
crossing endpoints. Source: SCP10, Section 7, lines 2977–3019, and the
regional parent spaces of Theorem 5.7. -/
theorem regionInternalBondSlice_mem_matchingSectorRange {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (R : Finset V) (σ : RB (Γ := Γ) R → Σ i, Fin (d i))
    {ψ : RegionPhysicalConfig (d := p) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor (fun v η s =>
      graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)
        v η ((e v).symm s))) R) :
    regionInternalBondSlice e R σ ψ ∈ LinearMap.range
      (physicalProductMap (RI (Γ := Γ) R) (blockBondInclusion (fun i => Fin (d i)))) := by
  classical
  let A := groupBondTensor (fun v η s =>
    graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)
      v η ((e v).symm s))
  let S := LinearMap.range
    (physicalProductMap (RI (Γ := Γ) R) (blockBondInclusion (fun i => Fin (d i))))
  have hle : regionGroundSpace A R ≤ S.comap (regionInternalBondSlice e R σ) := by
    apply (regionGroundSpace_le_iff A R _).mpr
    intro μ
    let θ : RB (Γ := Γ) R → Σ i, Fin (d i) :=
      fun f => (Fintype.equivFin (Σ i, Fin (d i))).symm (μ f)
    have hμ : (fun f => Fintype.equivFin (Σ i, Fin (d i)) (θ f)) = μ := by
      funext f
      exact Equiv.apply_symm_apply _ _
    have hslice : regionInternalBondSlice e R σ (openRegionWeight A R μ) =
        graphRegionInternalBondSlice R σ (graphOpenRegionNetwork
          (graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d))
          R θ) := by
      funext β
      change openRegionWeight A R μ
        (fun v => e v.1 ((regionHalfEdgeLabelEquiv R).symm
          (σ, (fun f => (β f).2), fun f => (β f).1) v)) = _
      calc
        _ = graphOpenAveragingBondState (blockMatrixRepresentation d D)
            (blockFourthRootWeight d) R θ
            (σ, (fun f => (β f).2), fun f => (β f).1) := by
          have h := openRegionWeight_groupBondTensor_dressedAveragingSite
            (blockMatrixRepresentation d D) (blockFourthRootWeight d)
            (blockFourthRootWeight_commute d D) e R θ
            (fun v => e v.1 ((regionHalfEdgeLabelEquiv R).symm
              (σ, (fun f => (β f).2), fun f => (β f).1) v))
          simpa only [hμ, Equiv.symm_apply_apply, Equiv.apply_symm_apply] using h
        _ = _ := (graphOpenBondRegrouping_dressedAveragingSite
          (blockMatrixRepresentation d D) (blockFourthRootWeight d)
          (blockFourthRootWeight_commute d D) R θ _).symm
    change regionInternalBondSlice e R σ (openRegionWeight A R μ) ∈ S
    rw [hslice]
    exact (graphRegionInternalBondSlice_blockFourthRootWeight d D hd R θ σ).1
  exact hle hψ

/-- A vector in the product matching-sector range vanishes whenever one bond
has different endpoint sectors. -/
theorem apply_eq_zero_of_mem_product_matchingSectorRange
    {E : Type*} [Fintype E] [DecidableEq E]
    (d : I → ℕ)
    {ψ : (E → ((Σ i, Fin (d i)) × (Σ i, Fin (d i)))) → ℂ}
    (hψ : ψ ∈ LinearMap.range (physicalProductMap E (blockBondInclusion (fun i => Fin (d i)))))
    (β : E → ((Σ i, Fin (d i)) × (Σ i, Fin (d i)))) (f : E)
    (hne : (β f).1.1 ≠ (β f).2.1) : ψ β = 0 := by
  classical
  obtain ⟨χ, rfl⟩ := hψ
  change (∑ α, (∏ e, blockBondInclusion (fun i => Fin (d i)) (β e) (α e)) * χ α) = 0
  apply Finset.sum_eq_zero
  intro α _
  have hf : blockBondInclusion (fun i => Fin (d i)) (β f) (α f) = 0 := by
    change (if β f = (⟨(α f).1, (α f).2.1⟩, ⟨(α f).1, (α f).2.2⟩)
      then (1 : ℂ) else 0) = 0
    apply ite_eq_right
    intro h
    exact hne ((congrArg (fun x => x.1.1) h).trans (congrArg (fun x => x.2.1) h).symm)
  rw [Finset.prod_eq_zero (Finset.mem_univ f) hf, zero_mul]

/-- Every genuine regional ground vector vanishes at an internal bond whose
physical endpoint sectors differ. Source: SCP10, Section 7, lines 2992–3019.
This is derived from the entire open-region range, not from a closed state. -/
theorem regionGroundSpace_apply_eq_zero_of_internal_sector_ne {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    (R : Finset V) {ψ : RegionPhysicalConfig (d := p) R → ℂ}
    (hψ : ψ ∈ regionGroundSpace (groupBondTensor (fun v η s =>
      graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)
        v η ((e v).symm s))) R)
    (σ : RegionPhysicalConfig (d := p) R) (f : RI (Γ := Γ) R)
    (hne : ((e f.1.1.2).symm (σ ⟨f.1.1.2, f.2.2⟩) (edgeRightIncident f.1)).1 ≠
      ((e f.1.1.1).symm (σ ⟨f.1.1.1, f.2.1⟩) (edgeLeftIncident f.1)).1) : ψ σ = 0 := by
  classical
  let α : RegionHalfEdgeConfig (Γ := Γ) (Σ i, Fin (d i)) R :=
    fun v => (e v.1).symm (σ v)
  let b := regionHalfEdgeLabelEquiv R α
  let β : RI (Γ := Γ) R → ((Σ i, Fin (d i)) × (Σ i, Fin (d i))) :=
    fun f => (b.2.2 f, b.2.1 f)
  have hs := regionInternalBondSlice_mem_matchingSectorRange d D hd e R b.1 hψ
  have hn : (β f).1.1 ≠ (β f).2.1 := by
    simpa only [β, b, regionHalfEdgeLabelEquiv_apply_internal_head,
      regionHalfEdgeLabelEquiv_apply_internal_tail, α] using hne
  have hz := apply_eq_zero_of_mem_product_matchingSectorRange d hs β f hn
  have hb : (b.1, (fun f => (β f).2), fun f => (β f).1) = b := rfl
  change ψ (fun v => e v.1 ((regionHalfEdgeLabelEquiv R).symm
    (b.1, (fun f => (β f).2), fun f => (β f).1) v)) = 0 at hz
  simpa only [hb, b, Equiv.symm_apply_apply, α, Equiv.apply_symm_apply] using hz

/-- Edge-covering canonical parent regions force matching block sectors on
every physical bond of every ground vector. No closure-spanning assumption
is used. Source: SCP10, Theorem 5.7 and Section 7, lines 2977–3019. -/
theorem regionParentGroundSpace_apply_eq_zero_of_sector_ne {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (groupBondTensor (fun v η s =>
      graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)
        v η ((e v).symm s))) R)
    (σ : V → Fin p) (f : Edge Γ)
    (hne : ((e f.1.2).symm (σ f.1.2) (edgeRightIncident f)).1 ≠
      ((e f.1.1).symm (σ f.1.1) (edgeLeftIncident f)).1) : ψ σ = 0 := by
  obtain ⟨i, htail, hhead⟩ := hcover f
  have hs := (mem_regionParentGroundSpace_iff _ R ψ).mp hψ i (fun v => σ v.1)
  have hz := regionGroundSpace_apply_eq_zero_of_internal_sector_ne d D hd e (R i) hs
    (fun v => σ v.1) ⟨f, htail, hhead⟩ hne
  have hrec : assembleRegionσ (R i) (fun v => σ v.1) (fun v => σ v.1) = σ := by
    funext v
    by_cases hv : v ∈ R i <;> simp [assembleRegionσ, hv]
  change ψ (assembleRegionσ (R i) (fun v => σ v.1) (fun v => σ v.1)) = 0 at hz
  rwa [hrec] at hz

/-- Edge-covering canonical parent regions supply the full product
matching-sector support required by the Section 7 bond isometry. This is a
statement about every ground vector of the actual regional parent, with no
closed-state or closure-spanning premise. -/
theorem regionParentGroundSpace_mem_product_matchingSectorRange {p : ℕ}
    (d : I → ℕ) (D : ∀ i, G →* Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (hd : ∀ i, 0 < d i)
    (e : (v : V) → (IncidentEdge Γ v → Σ i, Fin (d i)) ≃ Fin p)
    {ι : Type*} (R : ι → Finset V)
    (hcover : ∀ f : Edge Γ, ∃ i, f.1.1 ∈ R i ∧ f.1.2 ∈ R i)
    {ψ : (V → Fin p) → ℂ}
    (hψ : ψ ∈ regionParentGroundSpace (groupBondTensor (fun v η s =>
      graphDressedAveragingSite (blockMatrixRepresentation d D) (blockFourthRootWeight d)
        v η ((e v).symm s))) R) :
    (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
      LinearMap.range (physicalProductMap (Edge Γ) (blockBondInclusion (fun i => Fin (d i)))) := by
  classical
  change (fun β => ψ (fun v => e v (graphSiteBondEndpointEquiv.symm β v))) ∈
    (Matrix.mulVecLin (physicalProductMatrix (Edge Γ)
      (endpointEmbeddingMatrix (matchingEndpointEmbedding (fun i => Fin (d i)))))).range
  rw [physicalProductMatrix_endpointEmbeddingMatrix, mem_range_endpointEmbeddingMatrix_iff]
  intro β hβ
  have hex : ∃ f : Edge Γ, (β f).1.1 ≠ (β f).2.1 := by
    by_contra hn
    push Not at hn
    have hp (f : Edge Γ) : ∃ a, matchingEndpointEmbedding (fun i => Fin (d i)) a = β f := by
      rcases hpair : β f with ⟨⟨i, a⟩, ⟨j, b⟩⟩
      have hij : i = j := by simpa only [hpair] using hn f
      subst j
      exact ⟨⟨i, a, b⟩, rfl⟩
    choose α hα using hp
    exact hβ ⟨α, funext hα⟩
  obtain ⟨f, hf⟩ := hex
  apply regionParentGroundSpace_apply_eq_zero_of_sector_ne d D hd e R hcover hψ _ f
  simpa only [Equiv.symm_apply_apply, graphSiteBondEndpointEquiv_symm_head,
    graphSiteBondEndpointEquiv_symm_tail] using hf

end TNLean.PEPS
