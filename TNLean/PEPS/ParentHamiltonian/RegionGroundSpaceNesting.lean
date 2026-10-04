/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegionParentHamiltonian

/-!
# Nested regional PEPS ground spaces

The open tensor of a larger region satisfies every smaller regional ground-space
condition. The proof separates the labels incident to the smaller region from
the remaining labels, and then contracts the former with a boundary-dependent
coefficient. No nonzero bond dimensions or injectivity assumptions are needed.

Source: CPGSV21, arXiv:2011.12127, the regional parent construction in
Section IV.C.1, lines 2003–2011. The nesting assertion is a consequence of that
construction, rather than a separately stated theorem in the source.

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- J. I. Cirac, D. Pérez-García,
  N. Schuch, F. Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped BigOperators

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

omit [Fintype V] [DecidableRel Γ.Adj] in
/-- An edge touching a smaller region also touches a containing region.
Source: CPGSV21, arXiv:2011.12127, regional contraction, lines 2003–2008. -/
theorem isRegionIncidentEdge_of_subset {R S : Finset V} (hRS : R ⊆ S)
    {e : Edge Γ} (he : IsRegionIncidentEdge R e) : IsRegionIncidentEdge S e :=
  he.imp (fun h => hRS h) (fun h => hRS h)

/-- The incident labels of a larger region that do not touch the smaller region.
Source: CPGSV21, arXiv:2011.12127, regional contraction, lines 2003–2008. -/
abbrev RegionRemainderConfig (A : Tensor Γ d) (R S : Finset V) :=
  (e : {e : Edge Γ // IsRegionIncidentEdge S e ∧ ¬ IsRegionIncidentEdge R e}) →
    Fin (A.bondDim e.1)

/-- Separate the labels incident to a nested subregion from the remaining labels.
Source: CPGSV21, arXiv:2011.12127, regional contraction, lines 2003–2008. -/
def regionIncidentConfigEquivNested (A : Tensor Γ d) {R S : Finset V} (hRS : R ⊆ S) :
    RegionIncidentConfig A S ≃ RegionIncidentConfig A R × RegionRemainderConfig A R S where
  toFun η := (fun e => η ⟨e.1, isRegionIncidentEdge_of_subset hRS e.2⟩,
    fun e => η ⟨e.1, e.2.1⟩)
  invFun p e := if he : IsRegionIncidentEdge R e.1 then p.1 ⟨e.1, he⟩
    else p.2 ⟨e.1, e.2, he⟩
  left_inv η := by
    funext e
    dsimp only
    split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext <;> funext e
    · simp [e.2]
    · simp [e.2.2]

/-- Contracting a boundary coefficient against the open-region tensor is the
same as summing all incident labels with that boundary coefficient.
Source: CPGSV21, arXiv:2011.12127, arbitrary boundary conditions, lines 2003–2008. -/
theorem sum_mul_openRegionWeight (A : Tensor Γ d) (R : Finset V)
    (f : RegionBoundaryConfig A R → ℂ) (σ : RegionPhysicalConfig (d := d) R) :
    (∑ μ, f μ * openRegionWeight A R μ σ) =
      ∑ η : RegionIncidentConfig A R,
        f (regionIncidentBoundaryLabel A R η) * regionIncidentWeight A R η σ := by
  classical
  simp only [openRegionWeight, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro η hη
  simp [mul_ite]

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_of_incident_not_internal (R : Finset V) {e : Edge Γ}
    (he : IsRegionIncidentEdge R e) (hn : ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)) :
    IsRegionBoundaryEdge R e := by
  rcases he with h | h
  · exact Or.inl ⟨h, fun h' => hn ⟨h, h'⟩⟩
  · exact Or.inr ⟨fun h' => hn ⟨h', h⟩, h⟩

private def nestedExteriorLabel (A : Tensor Γ d) {R S : Finset V}
    (μ : RegionBoundaryConfig A R) (ζ : RegionRemainderConfig A R S)
    (e : Edge Γ) (he : IsRegionIncidentEdge S e)
    (hn : ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)) : Fin (A.bondDim e) :=
  if hR : IsRegionIncidentEdge R e then μ ⟨e, boundary_of_incident_not_internal R hR hn⟩
    else ζ ⟨e, he, hR⟩

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem not_internal_of_boundary_larger {R S : Finset V} (hRS : R ⊆ S)
    {e : Edge Γ} (he : IsRegionBoundaryEdge S e) :
    ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R) := by
  rintro ⟨h₁, h₂⟩
  rcases he with h | h
  · exact h.2 (hRS h₂)
  · exact h.1 (hRS h₁)

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem not_internal_of_complement_vertex (R S : Finset V)
    (w : {w : V // w ∈ S \ R}) (e : IncidentEdge Γ w.1) :
    ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rintro ⟨h₁, h₂⟩
  have hw := (Finset.mem_sdiff.mp w.2).2
  rcases e.2 with h | h
  · exact hw (h ▸ h₁)
  · exact hw (h ▸ h₂)

private def nestedRegionBoundaryLabel (A : Tensor Γ d) {R S : Finset V} (hRS : R ⊆ S)
    (μ : RegionBoundaryConfig A R) (ζ : RegionRemainderConfig A R S) :
    RegionBoundaryConfig A S :=
  fun e => nestedExteriorLabel A μ ζ e.1 (isRegionBoundaryEdge_touches S e.2)
    (not_internal_of_boundary_larger hRS e.2)

private noncomputable def nestedRegionComplementWeight (A : Tensor Γ d)
    {R S : Finset V}
    (μ : RegionBoundaryConfig A R) (ζ : RegionRemainderConfig A R S)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) : ℂ :=
  ∏ w : {w : V // w ∈ S \ R}, A.component w.1
    (fun e => nestedExteriorLabel A μ ζ e.1
      (isRegionIncidentEdge_of_regionVertex S
        ⟨w.1, (Finset.mem_sdiff.mp w.2).1⟩ e)
      (not_internal_of_complement_vertex R S w e))
    (τ ⟨w.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp w.2).2⟩⟩)

private def regionVertexEquivNested {R S : Finset V} (hRS : R ⊆ S) :
    {w : V // w ∈ S} ≃ {w : V // w ∈ R} ⊕ {w : V // w ∈ S \ R} where
  toFun w := if hw : w.1 ∈ R then Sum.inl ⟨w.1, hw⟩
    else Sum.inr ⟨w.1, Finset.mem_sdiff.mpr ⟨w.2, hw⟩⟩
  invFun
    | Sum.inl w => ⟨w.1, hRS w.2⟩
    | Sum.inr w => ⟨w.1, (Finset.mem_sdiff.mp w.2).1⟩
  left_inv w := by
    dsimp only
    split_ifs <;> rfl
  right_inv w := by
    cases w with
    | inl w => simp [w.2]
    | inr w => simp [(Finset.mem_sdiff.mp w.2).2]

omit [Fintype V] in
private theorem regionIncidentBoundaryLabel_nested (A : Tensor Γ d)
    {R S : Finset V} (hRS : R ⊆ S)
    (η : RegionIncidentConfig A R) (ζ : RegionRemainderConfig A R S) :
    regionIncidentBoundaryLabel A S ((regionIncidentConfigEquivNested A hRS).symm (η, ζ)) =
      nestedRegionBoundaryLabel A hRS (regionIncidentBoundaryLabel A R η) ζ := by
  funext e
  rfl

private theorem regionIncidentWeight_nested (A : Tensor Γ d)
    {R S : Finset V} (hRS : R ⊆ S)
    (η : RegionIncidentConfig A R) (ζ : RegionRemainderConfig A R S)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    regionIncidentWeight A S ((regionIncidentConfigEquivNested A hRS).symm (η, ζ))
      (fun w => assembleRegionσ R σ τ w.1) =
      regionIncidentWeight A R η σ *
        nestedRegionComplementWeight A (regionIncidentBoundaryLabel A R η) ζ τ := by
  classical
  rw [regionIncidentWeight, ← Equiv.prod_comp (regionVertexEquivNested hRS).symm,
    Fintype.prod_sum_type]
  dsimp only [regionVertexEquivNested]
  congr 1
  · apply Finset.prod_congr rfl
    intro w hw
    congr 1
    · funext e
      simp [regionIncidentConfigEquivNested, isRegionIncidentEdge_of_regionVertex R w e]
    · exact assembleRegionσ_mem R σ τ w
  · apply Finset.prod_congr rfl
    intro w hw
    congr 1
    exact assembleRegionσ_notMem R σ τ
      ⟨w.1, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp w.2).2⟩⟩

private theorem openRegionWeight_nested (A : Tensor Γ d)
    {R S : Finset V} (hRS : R ⊆ S)
    (μS : RegionBoundaryConfig A S)
    (σ : RegionPhysicalConfig (d := d) R)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    openRegionWeight A S μS (fun w => assembleRegionσ R σ τ w.1) =
      ∑ ζ : RegionRemainderConfig A R S, ∑ μ : RegionBoundaryConfig A R,
        (if nestedRegionBoundaryLabel A hRS μ ζ = μS then
          nestedRegionComplementWeight A μ ζ τ else 0) * openRegionWeight A R μ σ := by
  classical
  rw [openRegionWeight, ← Equiv.sum_comp (regionIncidentConfigEquivNested A hRS).symm,
    Fintype.sum_prod_type, Finset.sum_comm]
  simp only [regionIncidentBoundaryLabel_nested, regionIncidentWeight_nested]
  apply Finset.sum_congr rfl
  intro ζ hζ
  rw [sum_mul_openRegionWeight]
  apply Finset.sum_congr rfl
  intro η hη
  split_ifs <;> simp [mul_comm]

/-- Every slice of a larger open-region tensor satisfies the smaller regional
ground-space condition. Source: CPGSV21, arXiv:2011.12127, consequence of the
regional contraction with arbitrary boundary conditions, lines 2003–2008. -/
theorem openRegionWeight_nested_slice_mem_regionGroundSpace (A : Tensor Γ d)
    {R S : Finset V} (hRS : R ⊆ S) (μS : RegionBoundaryConfig A S)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (fun σ => openRegionWeight A S μS (fun w => assembleRegionσ R σ τ w.1)) ∈
      regionGroundSpace A R := by
  classical
  refine ⟨fun μ => ∑ ζ : RegionRemainderConfig A R S,
    if nestedRegionBoundaryLabel A hRS μ ζ = μS then
      nestedRegionComplementWeight A μ ζ τ else 0, ?_⟩
  funext σ
  rw [openRegionMap_apply]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm, openRegionWeight_nested]

/-- Fix the physical labels outside a subregion and read the corresponding
slice of a vector on a larger region. Source: CPGSV21, arXiv:2011.12127,
regional physical configurations, lines 2003–2008. -/
def subregionSliceMap (R S : Finset V)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (RegionPhysicalConfig (d := d) S → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (d := d) R → ℂ) where
  toFun ψ σ := ψ (fun w => assembleRegionσ R σ τ w.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A larger regional ground space satisfies every smaller regional condition
after fixing the complementary physical labels. Source: CPGSV21,
arXiv:2011.12127, consequence of the regional contraction, lines 2003–2008. -/
theorem regionGroundSpace_nested (A : Tensor Γ d) {R S : Finset V} (hRS : R ⊆ S)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    regionGroundSpace A S ≤ (regionGroundSpace A R).comap (subregionSliceMap R S τ) := by
  rw [regionGroundSpace_eq_span]
  apply Submodule.span_le.mpr
  rintro ψ ⟨μ, rfl⟩
  exact openRegionWeight_nested_slice_mem_regionGroundSpace A hRS μ τ

/-- Restrict a complementary physical configuration when the region is enlarged.
Source: CPGSV21, arXiv:2011.12127, complementary physical labels, lines 2003–2008. -/
def regionComplementConfigOfSubset {R S : Finset V} (hRS : R ⊆ S)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    RegionPhysicalConfig (d := d) (Finset.univ \ S) :=
  fun w => τ ⟨w.1, Finset.mem_sdiff.mpr
    ⟨Finset.mem_univ _, fun hw => (Finset.mem_sdiff.mp w.2).2 (hRS hw)⟩⟩

/-- Fixing the complement of a smaller region factors through a larger region.
Source: CPGSV21, arXiv:2011.12127, regional contraction, lines 2003–2011. -/
theorem regionSliceMap_eq_subregionSliceMap_comp {R S : Finset V} (hRS : R ⊆ S)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    regionSliceMap R τ = subregionSliceMap R S τ ∘ₗ
      regionSliceMap S (regionComplementConfigOfSubset hRS τ) := by
  refine LinearMap.ext fun ψ => funext fun σ => ?_
  change ψ (assembleRegionσ R σ τ) = ψ (assembleRegionσ S
    (fun w => assembleRegionσ R σ τ w.1) (regionComplementConfigOfSubset hRS τ))
  congr 1
  funext w
  by_cases hwS : w ∈ S
  · simp [assembleRegionσ, hwS]
  · have hwR : w ∉ R := fun hw => hwS (hRS hw)
    simp [assembleRegionσ, regionComplementConfigOfSubset, hwS, hwR]

/-- Enlarging a collection of regions, or replacing each region by a containing
one, strengthens the common PEPS ground-space conditions. Source: CPGSV21,
arXiv:2011.12127, consequence of the regional parent construction, lines 2003–2011. -/
theorem regionParentGroundSpace_le_of_regions_covered (A : Tensor Γ d)
    {ι κ : Type*} (R : ι → Finset V) (S : κ → Finset V)
    (hRS : ∀ i, ∃ j, R i ⊆ S j) :
    regionParentGroundSpace A S ≤ regionParentGroundSpace A R := by
  intro ψ hψ
  simp only [regionParentGroundSpace, Submodule.mem_iInf, Submodule.mem_comap] at hψ ⊢
  intro i τ
  obtain ⟨j, hij⟩ := hRS i
  rw [regionSliceMap_eq_subregionSliceMap_comp hij τ]
  exact regionGroundSpace_nested A hij τ
    (hψ j (regionComplementConfigOfSubset hij τ))

/-- Increasing each region strengthens the common regional ground space.
Source: CPGSV21, arXiv:2011.12127, regional parent conditions, lines 2003–2011. -/
theorem regionParentGroundSpace_antitone_regions (A : Tensor Γ d)
    {ι : Type*} (R S : ι → Finset V) (hRS : ∀ i, R i ⊆ S i) :
    regionParentGroundSpace A S ≤ regionParentGroundSpace A R :=
  regionParentGroundSpace_le_of_regions_covered A R S (fun i => ⟨i, hRS i⟩)

/-- Parent kernels decrease when their regional constraints are enlarged or
supplemented by containing regions. Source: CPGSV21, arXiv:2011.12127,
regional parent kernels and frustration freeness, lines 2003–2011. -/
theorem ker_regionParentHamiltonian_le_of_regions_covered (A : Tensor Γ d)
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : ι → Finset V) (S : κ → Finset V)
    (h : (i : ι) → Matrix (RegionPhysicalConfig (d := d) (R i))
      (RegionPhysicalConfig (d := d) (R i)) ℂ)
    (k : (j : κ) → Matrix (RegionPhysicalConfig (d := d) (S j))
      (RegionPhysicalConfig (d := d) (S j)) ℂ)
    (hh : ∀ i, IsRegionParentInteraction A (R i) (h i))
    (hk : ∀ j, IsRegionParentInteraction A (S j) (k j))
    (hRS : ∀ i, ∃ j, R i ⊆ S j) :
    (Matrix.mulVecLin (regionParentHamiltonian S k)).ker ≤
      (Matrix.mulVecLin (regionParentHamiltonian R h)).ker := by
  rw [ker_regionParentHamiltonian A S k hk, ker_regionParentHamiltonian A R h hh]
  exact regionParentGroundSpace_le_of_regions_covered A R S hRS

end TNLean.PEPS
