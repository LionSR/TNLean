/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.RegularRegionInvariantSpan
import TNLean.PEPS.ParentHamiltonian.RegularConstraintFixedSpaces
import TNLean.PEPS.ParentHamiltonian.VertexVirtualParentTransport

/-!
# The actual regional range in the ambient half-edge space

A regional range condition applies to every complementary slice. Its exact
left, right and support characterization retains arbitrary exterior labels.
Source: SCP10, arXiv:1001.3807, Theorem 6.12, lines 2131–2153.
-/

open scoped BigOperators Matrix

namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- Extend a regional vertex gauge by the identity outside the region. -/
def regularRegionExtendVertexGauge (R : Finset V) (k : {v : V // v ∈ R} → G) :
    {v : V // v ∈ (Finset.univ : Finset V)} → G :=
  fun v => if h : v.1 ∈ R then k ⟨v.1, h⟩ else 1

/-- Retain an edge multiplier only on the original internal edges. -/
def regularRegionInternalMultiplier (R : Finset V) (r : Edge Γ → G) : Edge Γ → G :=
  fun e => if e.1.1 ∈ R ∧ e.1.2 ∈ R then r e else 1

/-- The global subspace whose every complementary slice is an actual
untwisted regular regional ground vector. -/
noncomputable def regularGlobalRegionRange (R : Finset V) :
    Submodule ℂ (RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :=
  ⨅ τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R),
    (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R)).range.comap
      (dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ)

/-- The ambient regional range is the actual local range condition on each slice. -/
theorem mem_regularGlobalRegionRange_iff (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    x ∈ regularGlobalRegionRange R ↔
      ∀ τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R),
        dependentRegionSlice (Out := fun v => IncidentEdge Γ v → G) R τ x ∈
          (Matrix.mulVecLin (regularProjectorOpenRegionMatrix (Γ := Γ) (G := G) R)).range := by
  simp only [regularGlobalRegionRange, Submodule.mem_iInf, Submodule.mem_comap]

omit [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Regional gauges leave the complementary coordinates unchanged. -/
theorem regularRegionGauge_assemble (R : Finset V) (k : {v : V // v ∈ R} → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    regularRegionGaugePhysicalLabels Finset.univ (regularRegionExtendVertexGauge R k)
        (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R α τ) =
      assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R
        (regularRegionGaugePhysicalLabels R k α) τ := by
  funext v e
  by_cases h : v.1 ∈ R <;>
    simp [assembleDependentRegionConfig, regularRegionGaugePhysicalLabels_apply,
      regularRegionExtendVertexGauge, h]

omit [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Internal shared right translations leave the complementary coordinates unchanged. -/
theorem regularRegionRight_assemble (R : Finset V) (r : Edge Γ → G)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    regularRegionHalfEdgeRightMul Finset.univ (regularRegionInternalMultiplier R r)
        (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R α τ) =
      assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R
        (regularRegionHalfEdgeRightMul R (regularRegionInternalMultiplier R r) α) τ := by
  funext v e
  by_cases h : v.1 ∈ R
  · simp [assembleDependentRegionConfig, regularRegionHalfEdgeRightMul, h]
  · have he : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
      intro he
      rcases e.2 with ht | hh
      · exact h (ht ▸ he.1)
      · exact h (hh ▸ he.2)
    simp [assembleDependentRegionConfig, regularRegionHalfEdgeRightMul,
      regularRegionInternalMultiplier, h, he]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
/-- Boundary-trivial right assignments have the same regional action after
removing their irrelevant exterior values. -/
theorem regularRegionRight_eq_internalMultiplier (R : Finset V) (r : Edge Γ → G)
    (hr : ∀ e, IsRegionBoundaryEdge R e → r e = 1)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R) :
    regularRegionHalfEdgeRightMul R (regularRegionInternalMultiplier R r) α =
      regularRegionHalfEdgeRightMul R r α := by
  funext v e
  by_cases he : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R
  · simp [regularRegionHalfEdgeRightMul, regularRegionInternalMultiplier, he]
  · have hb : IsRegionBoundaryEdge R e.1 := by
      rcases e.2 with ht | hh
      · have htR : e.1.1.1 ∈ R := ht.symm ▸ v.2
        exact Or.inl ⟨htR, fun hhR => he ⟨htR, hhR⟩⟩
      · have hhR : e.1.1.2 ∈ R := hh.symm ▸ v.2
        exact Or.inr ⟨fun htR => he ⟨htR, hhR⟩, hhR⟩
    simp [regularRegionHalfEdgeRightMul, regularRegionInternalMultiplier, he, hr e.1 hb]

omit [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
/-- Restricting an assembled configuration recovers its regional coordinates. -/
theorem restrictRegularRegionHalfEdges_assemble (R : Finset V)
    (α : RegionHalfEdgeConfig (Γ := Γ) G R)
    (τ : RegionHalfEdgeConfig (Γ := Γ) G (Finset.univ \ R)) :
    restrictRegularRegionHalfEdges R
      (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R α τ) = α := by
  funext v
  simp [restrictRegularRegionHalfEdges, assembleDependentRegionConfig, v.2]

/-- Exact ambient version of the actual open-region range characterization. -/
theorem mem_regularGlobalRegionRange_iff_invariant_flat (R : Finset V)
    (x : RegionHalfEdgeConfig (Γ := Γ) G Finset.univ → ℂ) :
    x ∈ regularGlobalRegionRange R ↔
      (∀ k α, x (regularRegionGaugePhysicalLabels Finset.univ
        (regularRegionExtendVertexGauge R k) α) = x α) ∧
      (∀ r α, x (regularRegionHalfEdgeRightMul Finset.univ
        (regularRegionInternalMultiplier R r) α) = x α) ∧
      (∀ α, ¬ IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R α) →
        x α = 0) := by
  classical
  rw [mem_regularGlobalRegionRange_iff]
  constructor
  · intro hx
    have hslice τ := (mem_regularProjectorOpenRegionRange_iff R _).mp (hx τ)
    refine ⟨?_, ?_, ?_⟩
    · intro k α
      obtain ⟨⟨β, τ⟩, rfl⟩ :=
        (dependentRegionConfigEquiv (Out := fun v => IncidentEdge Γ v → G) R).symm.surjective α
      change x (regularRegionGaugePhysicalLabels Finset.univ
        (regularRegionExtendVertexGauge R k)
        (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ)) =
          x (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ)
      rw [regularRegionGauge_assemble]
      exact (hslice τ).1 k β
    · intro r α
      obtain ⟨⟨β, τ⟩, rfl⟩ :=
        (dependentRegionConfigEquiv (Out := fun v => IncidentEdge Γ v → G) R).symm.surjective α
      change x (regularRegionHalfEdgeRightMul Finset.univ (regularRegionInternalMultiplier R r)
        (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ)) =
          x (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ)
      rw [regularRegionRight_assemble]
      apply (hslice τ).2.1
      intro e he
      have hn : ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R) := by
        rcases he with he | he
        · exact fun h => he.2 h.2
        · exact fun h => he.1 h.1
      simp [regularRegionInternalMultiplier, hn]
    · intro α hα
      obtain ⟨⟨β, τ⟩, rfl⟩ :=
        (dependentRegionConfigEquiv (Out := fun v => IncidentEdge Γ v → G) R).symm.surjective α
      change ¬ IsRegularRegionHalfEdgeFlat R (restrictRegularRegionHalfEdges R
        (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R β τ)) at hα
      rw [restrictRegularRegionHalfEdges_assemble] at hα
      exact (hslice τ).2.2 β hα
  · rintro ⟨hl, hr, hs⟩ τ
    apply (mem_regularProjectorOpenRegionRange_iff R _).mpr
    refine ⟨?_, ?_, ?_⟩
    · intro k α
      change x (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R
        (regularRegionGaugePhysicalLabels R k α) τ) = _
      rw [← regularRegionGauge_assemble, hl]
      rfl
    · intro r hboundary α
      change x (assembleDependentRegionConfig (Out := fun v => IncidentEdge Γ v → G) R
        (regularRegionHalfEdgeRightMul R r α) τ) = _
      rw [← regularRegionRight_eq_internalMultiplier R r hboundary α,
        ← regularRegionRight_assemble, hr]
      rfl
    · intro α hα
      apply hs
      rwa [restrictRegularRegionHalfEdges_assemble]

end TNLean.PEPS
