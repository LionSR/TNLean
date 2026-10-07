/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegularTwoSitePhysicalChargeMeasurement
import TNLean.PEPS.GraphOpenRegionContraction
/-!
# The literal diagonal charge on an actual graph edge

The two endpoint region has exactly one internal bond. Its native open
contraction with the weight χ(p k) on that bond is the actual two-site charge
column, with every other incident label supplied by the native boundary.
Source: SCP10, arXiv:1001.3807, definition and detection of chargeons,
lines 2432–2486. No contraction identity or physical measurement is assumed.
-/
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
/-- The actual region of the two endpoints of one bond. Source: SCP10,
charge detection, lines 2464–2486. -/
abbrev regularEdgeRegion (e : Edge Γ) : Finset V := {e.1.1,e.1.2}
private abbrev Internal (e : Edge Γ) :=
  {f : Edge Γ // f.1.1 ∈ regularEdgeRegion e ∧ f.1.2 ∈ regularEdgeRegion e}
/-- The shared bond at its ordered tail. Auxiliary coordinates for SCP10,
charge detection, lines 2464–2486. -/
def regularEdgeTailLeg (e : Edge Γ) : IncidentEdge Γ e.1.1 := ⟨e,Or.inl rfl⟩
/-- The shared bond at its ordered head. Auxiliary coordinates for SCP10,
charge detection, lines 2464–2486. -/
def regularEdgeHeadLeg (e : Edge Γ) : IncidentEdge Γ e.1.2 := ⟨e,Or.inr rfl⟩
omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem internal_eq (e f : Edge Γ)
    (hf : f.1.1 ∈ regularEdgeRegion e ∧ f.1.2 ∈ regularEdgeRegion e) : f = e := by
  apply Subtype.ext
  simp only [regularEdgeRegion, Finset.mem_insert, Finset.mem_singleton] at hf
  rcases hf with ⟨h₀|h₀,h₁|h₁⟩
  · have hlt := f.2.1
    rw [h₀,h₁] at hlt
    exact (lt_irrefl _ hlt).elim
  · exact Prod.ext h₀ h₁
  · have hlt := f.2.1
    rw [h₀,h₁] at hlt
    exact (not_lt.mpr e.2.1.le hlt).elim
  · have hlt := f.2.1
    rw [h₀,h₁] at hlt
    exact (lt_irrefl _ hlt).elim
private abbrev internalUnique (e : Edge Γ) : Unique (Internal e) where
  default := ⟨e,by simp [regularEdgeRegion]⟩
  uniq f := Subtype.ext (internal_eq e f.1 f.2)
omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_of_other (e : Edge Γ) (v : V) (hv : v ∈ regularEdgeRegion e)
    (f : IncidentEdge Γ v) (hne : f.1 ≠ e) : IsRegionBoundaryEdge (regularEdgeRegion e) f.1 := by
  have hn : ¬ (f.1.1.1 ∈ regularEdgeRegion e ∧ f.1.1.2 ∈ regularEdgeRegion e) :=
    fun h => hne (internal_eq e f.1 h)
  rcases f.2 with h | h
  · have hm : f.1.1.1 ∈ regularEdgeRegion e := by rwa [h]
    exact Or.inl ⟨hm,fun hh => hn ⟨hm,hh⟩⟩
  · have hm : f.1.1.2 ∈ regularEdgeRegion e := by rwa [h]
    exact Or.inr ⟨fun ht => hn ⟨ht,hm⟩,hm⟩
private def vertices (e : Edge Γ) : Bool ≃ {v : V // v ∈ regularEdgeRegion e} where
  toFun b := if b then ⟨e.1.2,by simp [regularEdgeRegion]⟩ else ⟨e.1.1,by simp [regularEdgeRegion]⟩
  invFun v := decide (v.1 = e.1.2)
  left_inv b := by cases b <;> simp [ne_of_lt e.2.1]
  right_inv v := by
    apply Subtype.ext
    have hv := v.2
    simp only [regularEdgeRegion, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with hv|hv <;> simp [hv,ne_of_lt e.2.1]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
/-- Multiply exactly one endpoint by the diagonal character weight on the actual
shared group label. Source: SCP10, `eq:anyons:chargeon-def`, lines 2432–2453. -/
def regularEdgeCharacterSite
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (e : Edge Γ) (χ : G → ℂ) (p : G)
    (v : V) (α : IncidentEdge Γ v → G) (s : Fin d) : ℂ :=
  if hv : v = e.1.1 then χ (p * α ⟨e,Or.inl hv.symm⟩) * a v α s else a v α s
/-- Read the remaining native crossing labels at the two actual endpoint sites.
Source: SCP10, the two adjacent vertices in charge detection, lines 2464–2486. -/
def regularEdgeChargeBoundaryLabels (e : Edge Γ)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
    ({f : IncidentEdge Γ e.1.1 // f ≠ regularEdgeTailLeg e} → G) ×
      ({f : IncidentEdge Γ e.1.2 // f ≠ regularEdgeHeadLeg e} → G) :=
  (fun f => θ ⟨f.1.1, boundary_of_other e e.1.1 (by simp [regularEdgeRegion]) f.1
      (fun h => f.2 (Subtype.ext h))⟩,
   fun f => θ ⟨f.1.1, boundary_of_other e e.1.2 (by simp [regularEdgeRegion]) f.1
      (fun h => f.2 (Subtype.ext h))⟩)
/-- The two actual original-spin coordinates are their ordered endpoint pair.
Source: SCP10, two-site charge measurement, lines 2464–2486. -/
def regularEdgePhysicalPairEquiv (e : Edge Γ) :
    RegionPhysicalConfig (d := d) (regularEdgeRegion e) ≃ Fin d × Fin d where
  toFun σ := (σ ⟨e.1.1,by simp [regularEdgeRegion]⟩,σ ⟨e.1.2,by simp [regularEdgeRegion]⟩)
  invFun s v := if v.1 = e.1.1 then s.1 else s.2
  left_inv σ := by
    funext v
    rcases v with ⟨v,hv⟩
    simp only [regularEdgeRegion,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv|hv <;> subst v <;> simp [ne_of_gt e.2.1]
  right_inv s := by simp [ne_of_gt e.2.1]
private def remainingBoundary (e : Edge Γ) (v : V) (hv : v ∈ regularEdgeRegion e)
    (i : IncidentEdge Γ v) (hi : i.1 = e)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
    {f : IncidentEdge Γ v // f ≠ i} → G :=
  fun f => θ ⟨f.1.1,boundary_of_other e v hv f.1
    (fun h => f.2 (Subtype.ext (h.trans hi.symm)))⟩
omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem labels_at_vertex (e : Edge Γ) (v : V) (hv : v ∈ regularEdgeRegion e)
    (i : IncidentEdge Γ v) (hi : i.1 = e)
    (ξ : Internal e → G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
    (fun f : IncidentEdge Γ v => (graphRegionIncidentConfigEquiv (regularEdgeRegion e)).symm (ξ,θ)
      ⟨f.1,isRegionIncidentEdge_of_regionVertex (regularEdgeRegion e) ⟨v,hv⟩ f⟩) =
      (Equiv.funSplitAt i G).symm
        (ξ ⟨e,by simp [regularEdgeRegion]⟩,remainingBoundary e v hv i hi θ) := by
  let η := (graphRegionIncidentConfigEquiv (regularEdgeRegion e)).symm (ξ,θ)
  apply (Equiv.funSplitAt i G).injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · change η ⟨i.1,_⟩ = _
    have htag : (⟨i.1,isRegionIncidentEdge_of_regionVertex (regularEdgeRegion e) ⟨v,hv⟩ i⟩ :
        {f : Edge Γ // IsRegionIncidentEdge (regularEdgeRegion e) f}) =
        ⟨e,Or.inl (by simp [regularEdgeRegion])⟩ :=
      Subtype.ext hi
    rw [htag]
    rw [← graphRegionIncidentConfigEquiv_apply_internal (regularEdgeRegion e) η
      ⟨e,by simp [regularEdgeRegion]⟩]
    exact congrArg (fun z => z.1 ⟨e,by simp [regularEdgeRegion]⟩)
      ((graphRegionIncidentConfigEquiv (regularEdgeRegion e)).apply_symm_apply (ξ,θ))
  · funext f
    change η ⟨f.1.1,_⟩ = θ ⟨f.1.1,_⟩
    rw [← graphRegionIncidentConfigEquiv_apply_boundary (regularEdgeRegion e) η
      ⟨f.1.1,boundary_of_other e v hv f.1
        (fun h => f.2 (Subtype.ext (h.trans hi.symm)))⟩]
    exact congrArg (fun z => z.2 ⟨f.1.1,boundary_of_other e v hv f.1
      (fun h => f.2 (Subtype.ext (h.trans hi.symm)))⟩)
      ((graphRegionIncidentConfigEquiv (regularEdgeRegion e)).apply_symm_apply (ξ,θ))
omit [DecidableEq G] in
/-- The literal native region coefficient is the charged two-site column,
without assuming a contraction comparison. Both endpoint orders are retained.
Source: SCP10, `eq:anyons:measure-chargeon`, lines 2464–2486. -/
theorem openRegionWeight_regularEdgeCharacterSite
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (e : Edge Γ) (χ : G → ℂ) (p : G)
    (θ : {f : Edge Γ // IsRegionBoundaryEdge (regularEdgeRegion e) f} → G)
    (σ : RegionPhysicalConfig (d := d) (regularEdgeRegion e)) :
    openRegionWeight (groupBondTensor (regularEdgeCharacterSite a e χ p))
        (regularEdgeRegion e) (fun f => Fintype.equivFin G (θ f)) σ =
      regularTwoSitePhysicalChargeColumn (regularEdgeTailLeg e) (regularEdgeHeadLeg e)
        (a e.1.1) (a e.1.2) χ p (regularEdgeChargeBoundaryLabels e θ)
        (regularEdgePhysicalPairEquiv e σ) := by
  classical
  let _ := internalUnique e
  rw [openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork,
    graphOpenRegionNetwork_eq_sum_internal,
    ← (Equiv.funUnique (Internal e) G).symm.sum_comp]
  unfold regularTwoSitePhysicalChargeColumn
  apply Finset.sum_congr rfl
  intro k _
  let ξ := (Equiv.funUnique (Internal e) G).symm k
  have ht := labels_at_vertex e e.1.1 (by simp [regularEdgeRegion]) (regularEdgeTailLeg e) rfl ξ θ
  have hh := labels_at_vertex e e.1.2 (by simp [regularEdgeRegion]) (regularEdgeHeadLeg e) rfl ξ θ
  rw [← (vertices e).prod_comp, Fintype.prod_bool]
  change regularEdgeCharacterSite a e χ p e.1.2
      (fun f => (graphRegionIncidentConfigEquiv (regularEdgeRegion e)).symm (ξ,θ)
        ⟨f.1,isRegionIncidentEdge_of_regionVertex (regularEdgeRegion e)
          ⟨e.1.2,by simp [regularEdgeRegion]⟩ f⟩)
      (σ ⟨e.1.2,by simp [regularEdgeRegion]⟩) *
    regularEdgeCharacterSite a e χ p e.1.1
      (fun f => (graphRegionIncidentConfigEquiv (regularEdgeRegion e)).symm (ξ,θ)
        ⟨f.1,isRegionIncidentEdge_of_regionVertex (regularEdgeRegion e)
          ⟨e.1.1,by simp [regularEdgeRegion]⟩ f⟩)
      (σ ⟨e.1.1,by simp [regularEdgeRegion]⟩) = _
  rw [ht,hh]
  change regularEdgeCharacterSite a e χ p e.1.2
      ((Equiv.funSplitAt (regularEdgeHeadLeg e) G).symm
        (k,(regularEdgeChargeBoundaryLabels e θ).2)) (σ ⟨e.1.2,_⟩) *
    regularEdgeCharacterSite a e χ p e.1.1
      ((Equiv.funSplitAt (regularEdgeTailLeg e) G).symm
        (k,(regularEdgeChargeBoundaryLabels e θ).1)) (σ ⟨e.1.1,_⟩) = _
  simp only [regularEdgeCharacterSite, ne_of_gt e.2.1, dite_false, dite_true]
  have hk : ((Equiv.funSplitAt (regularEdgeTailLeg e) G).symm
      (k,(regularEdgeChargeBoundaryLabels e θ).1)) (regularEdgeTailLeg e) = k :=
    congrArg Prod.fst ((Equiv.funSplitAt (regularEdgeTailLeg e) G).apply_symm_apply
      (k,(regularEdgeChargeBoundaryLabels e θ).1))
  change _ * (χ (p * ((Equiv.funSplitAt (regularEdgeTailLeg e) G).symm
    (k,(regularEdgeChargeBoundaryLabels e θ).1)) (regularEdgeTailLeg e)) * _) = _
  rw [hk]
  exact mul_comm _ _
end TNLean.PEPS
