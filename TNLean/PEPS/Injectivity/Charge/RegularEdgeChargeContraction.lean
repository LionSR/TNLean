/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Injectivity.Charge.RegularTwoSitePhysicalChargeMeasurement
import TNLean.PEPS.Tensor.GraphState.GraphOpenRegionContraction
import TNLean.PEPS.Tensor.GraphState.RegularOpenRegion
import TNLean.PEPS.Tensor.GraphState.GraphOpenRegionGluing

/-!
# The literal diagonal charge on an actual graph edge

The two endpoint region has exactly one internal bond. Its native open
contraction with the weight χ(p k) on that bond is the actual two-site charge
column, with every other incident label supplied by the native boundary.
Source: SCP10, arXiv:1001.3807, definition and detection of chargeons,
lines 2432–2486. No contraction identity or physical measurement is assumed.

## Charge measurement on the actual two-endpoint region

The complete physical measurement is transported along the actual endpoint
coordinate equivalence. It detects a diagonal irreducible-character insertion
on the shared bond uniformly in every native boundary label.
Source: SCP10, arXiv:1001.3807, charge detection, lines 2464–2486.

It also contains the following results.

* `TNLean.PEPS.graphOpenRegionNetwork_regularEdgeCharacterSite_boundary`,
  `TNLean.PEPS.graphOpenRegionNetwork_regularEdgeCharacterSite_union`: a diagonal charge on an open
  boundary bond.
-/

section RegularEdgeChargeContraction

section

open ManyBody (Edge)
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
    (f : IncidentEdge Γ v) (hne : f.1 ≠ e) : ManyBody.IsRegionBoundaryEdge
      (regularEdgeRegion e) f.1 :=
  ManyBody.IsRegionIncidentEdge.isRegionBoundaryEdge
    (isRegionIncidentEdge_of_regionVertex _ ⟨v, hv⟩ f)
    (fun h => hne (internal_eq e f.1 h))
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
    (θ : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
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
    (θ : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
    {f : IncidentEdge Γ v // f ≠ i} → G :=
  fun f => θ ⟨f.1.1,boundary_of_other e v hv f.1
    (fun h => f.2 (Subtype.ext (h.trans hi.symm)))⟩
omit [Fintype V] [DecidableRel Γ.Adj] [Group G] [Fintype G] [DecidableEq G] in
private theorem labels_at_vertex (e : Edge Γ) (v : V) (hv : v ∈ regularEdgeRegion e)
    (i : IncidentEdge Γ v) (hi : i.1 = e)
    (ξ : Internal e → G)
    (θ : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge (regularEdgeRegion e) f} → G) :
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
        {f : Edge Γ // ManyBody.IsRegionIncidentEdge (regularEdgeRegion e) f}) =
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
    (θ : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge (regularEdgeRegion e) f} → G)
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
end

end

section

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix ComplexOrder
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}

/-- A complete original-spin measurement for the literal character-weighted
shared bond, fixed before every charge, parameter and boundary configuration.
Source: SCP10, charge detection, lines 2464–2486. -/
theorem exists_regularEdgePhysicalAllChargeMeasurement
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ) (e : Edge Γ)
    (ha : IsGIsometric (regularLegRepresentation (IncidentEdge Γ e.1.1))
      (regularSiteMap (a e.1.1)))
    (hb : IsGIsometric (regularLegRepresentation (IncidentEdge Γ e.1.2))
      (regularSiteMap (a e.1.2))) :
    ∃ Q : Option (regularChargeLabels (G := G)) →
        Matrix (RegionPhysicalConfig (d := d) {e.1.1,e.1.2})
          (RegionPhysicalConfig (d := d) {e.1.1,e.1.2}) ℂ,
      (∀ r, (Q r).IsHermitian ∧ (Q r).PosSemidef) ∧
      (∀ r s, Q r * Q s = if r = s then Q r else 0) ∧
      (∑ r, Q r = 1) ∧
      ∀ (b : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
        (_ : ∀ v ∈ ({e.1.1,e.1.2} : Finset V), b v = a v)
        (χ : regularChargeLabels (G := G)) r p
        (θ : {f : Edge Γ // ManyBody.IsRegionBoundaryEdge {e.1.1,e.1.2} f} → G),
        Q r *ᵥ openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
            {e.1.1,e.1.2} (fun f => Fintype.equivFin G (θ f)) =
          if r = some χ then
            openRegionWeight (groupBondTensor (regularEdgeCharacterSite b e χ.val p))
              {e.1.1,e.1.2} (fun f => Fintype.equivFin G (θ f)) else 0 := by
  classical
  obtain ⟨P,hPh,hPP,hPs,hPa⟩ := exists_regularTwoSitePhysicalAllChargeMeasurement
    (regularEdgeTailLeg e) (regularEdgeHeadLeg e) (a e.1.1) (a e.1.2) ha hb
  let E := regularEdgePhysicalPairEquiv (d := d) e
  refine ⟨fun r => (P r).submatrix E E, ?_, ?_, ?_, ?_⟩
  · intro r
    exact ⟨(hPh r).1.submatrix E, (hPh r).2.submatrix E⟩
  · intro r s
    rw [Matrix.submatrix_mul_equiv, hPP]
    split_ifs <;> rfl
  · ext σ τ
    have hs := congrFun (congrFun hPs (E σ)) (E τ)
    simpa only [Matrix.sum_apply, Matrix.submatrix_apply, Matrix.one_apply,
      E.injective.eq_iff] using hs
  · intro b hba χ r p θ
    have hcol : openRegionWeight
        (groupBondTensor (regularEdgeCharacterSite b e χ.val p)) {e.1.1,e.1.2}
        (fun f => Fintype.equivFin G (θ f)) =
        regularTwoSitePhysicalChargeColumn (regularEdgeTailLeg e) (regularEdgeHeadLeg e)
          (a e.1.1) (a e.1.2) χ.val p (regularEdgeChargeBoundaryLabels e θ) ∘ E := by
      funext σ
      have ht := hba e.1.1 (by simp)
      have hh := hba e.1.2 (by simp)
      simpa only [ht, hh, E, Function.comp_apply] using
        openRegionWeight_regularEdgeCharacterSite b e χ.val p θ σ
    rw [hcol, Matrix.submatrix_mulVec_equiv]
    funext σ
    simp only [Function.comp_def, Equiv.apply_symm_apply]
    have hs := congrFun (hPa χ r p (regularEdgeChargeBoundaryLabels e θ)) (E σ)
    split_ifs with h
    · simpa only [h, ite_true] using hs
    · simpa only [h, ite_false, Pi.zero_apply] using hs
end TNLean.PEPS
end

end

end RegularEdgeChargeContraction

section RegularBoundaryChargeContraction

/-!
## A diagonal charge on an open boundary bond

On the part containing its ordered tail, a prescribed boundary label turns the
charge insertion into its literal scalar character weight. On the other part
no site factor changes. Source: SCP10, arXiv:1001.3807,
`eq:anyons:chargeon-def` and `eq:anyons:chargeon-move-setting`,
lines 2432–2453 and 2489–2507.
-/

open ManyBody (Edge)
noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G] {d : ℕ}
private abbrev RV (R : Finset V) := {v : V // v ∈ R}
private abbrev RB (R : Finset V) := {e : Edge Γ // ManyBody.IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype G] [DecidableEq G] in
private theorem prod_charge_at_tail
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : Edge Γ) (ht : e.1.1 ∈ R) (χ : G → ℂ) (p : G)
    (α : (v : RV R) → IncidentEdge Γ v.1 → G) (σ : RV R → Fin d) :
    (∏ v : RV R, regularEdgeCharacterSite a e χ p v.1 (α v) (σ v)) =
      χ (p * α ⟨e.1.1,ht⟩ (edgeLeftIncident e)) *
        ∏ v : RV R, a v.1 (α v) (σ v) := by
  classical
  let o : RV R := ⟨e.1.1,ht⟩
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ o,
    Fintype.prod_eq_mul_prod_subtype_ne (fun v : RV R => a v.1 (α v) (σ v)) o]
  have hr : (∏ v : {v : RV R // v ≠ o},
      regularEdgeCharacterSite a e χ p v.1.1 (α v.1) (σ v.1)) =
      ∏ v : {v : RV R // v ≠ o}, a v.1.1 (α v.1) (σ v.1) := by
    apply Finset.prod_congr rfl
    intro v _
    have hv : v.1.1 ≠ e.1.1 := fun h => v.2 (Subtype.ext h)
    simp only [regularEdgeCharacterSite, dite_eq_right hv]
  rw [hr]
  simp only [o, regularEdgeCharacterSite, dite_true, edgeLeftIncident, mul_assoc]

omit [DecidableEq G] in
/-- The actual open contraction retains exactly the prescribed diagonal weight
at the tail endpoint of a crossing bond. Source: SCP10, lines 2489–2507. -/
theorem graphOpenRegionNetwork_regularEdgeCharacterSite_boundary
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (R : Finset V) (e : RB (Γ := Γ) R) (χ : G → ℂ) (p : G)
    (θ : RB (Γ := Γ) R → G) (σ : RV R → Fin d) :
    graphOpenRegionNetwork (regularEdgeCharacterSite a e.1 χ p) R θ σ =
      (if e.1.1.1 ∈ R then χ (p * θ e) else 1) * graphOpenRegionNetwork a R θ σ := by
  classical
  rw [graphOpenRegionNetwork_eq_sum_internal, graphOpenRegionNetwork_eq_sum_internal,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases ht : e.1.1.1 ∈ R
  · rw [ite_eq_left ht, prod_charge_at_tail a R e.1 ht]
    congr 3
    change (graphRegionIncidentConfigEquiv R).symm (ξ,θ)
      ⟨e.1,ManyBody.isRegionBoundaryEdge_touches R e.2⟩ = θ e
    exact congrArg (fun z => z.2 e)
      ((graphRegionIncidentConfigEquiv R).apply_symm_apply (ξ,θ))
  · rw [ite_eq_right ht, one_mul]
    apply Finset.prod_congr rfl
    intro v _
    have hv : v.1 ≠ e.1.1.1 := fun h => ht (h ▸ v.2)
    simp only [regularEdgeCharacterSite, dite_eq_right hv]


omit [DecidableEq G] in
/-- The charge-inserted union is the actual joined contraction with precisely one
character weight on its shared bond label. Source: SCP10, lines 2489–2507. -/
theorem graphOpenRegionNetwork_regularEdgeCharacterSite_union
    (a : (v : V) → (IncidentEdge Γ v → G) → Fin d → ℂ)
    (L S : Finset V) (hd : Disjoint L S) (e : RegionJoiningEdge (Γ := Γ) L S)
    (χ : G → ℂ) (p : G) (θ : RB (Γ := Γ) (L ∪ S) → G)
    (σ : RV (L ∪ S) → Fin d) :
    graphOpenRegionNetwork (regularEdgeCharacterSite a e.1 χ p) (L ∪ S) θ σ =
      ∑ μ : RegionJoiningEdge (Γ := Γ) L S → G, χ (p * μ e) *
        (graphOpenRegionNetwork a L (regionGluingBoundary L S L μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_left _ v.2⟩) *
        graphOpenRegionNetwork a S (regionGluingBoundary L S S μ θ)
          (fun v => σ ⟨v.1,Finset.mem_union_right _ v.2⟩)) := by
  classical
  rw [graphOpenRegionNetwork_union _ L S hd]
  apply Finset.sum_congr rfl
  intro μ _
  obtain ⟨heL,heS⟩ := regionJoiningEdge_boundary L S hd e
  rw [graphOpenRegionNetwork_regularEdgeCharacterSite_boundary a L ⟨e.1,heL⟩,
    graphOpenRegionNetwork_regularEdgeCharacterSite_boundary a S ⟨e.1,heS⟩]
  have hL : regionGluingBoundary L S L μ θ ⟨e.1,heL⟩ = μ e := by
    simp only [regionGluingBoundary, regionGluingLabels, dite_eq_left e.2]
  have hS : regionGluingBoundary L S S μ θ ⟨e.1,heS⟩ = μ e := by
    simp only [regionGluingBoundary, regionGluingLabels, dite_eq_left e.2]
  rw [hL,hS]
  rcases Finset.mem_union.mp e.2.1.1 with ht | ht
  · have hn : e.1.1.1 ∉ S := fun h => Finset.disjoint_left.mp hd ht h
    simp only [ite_eq_left ht, ite_eq_right hn, one_mul, mul_assoc]
  · have hn : e.1.1.1 ∉ L := fun h => Finset.disjoint_left.mp hd h ht
    simp only [ite_eq_left ht, ite_eq_right hn, one_mul]
    ring
end TNLean.PEPS

end

end RegularBoundaryChargeContraction
