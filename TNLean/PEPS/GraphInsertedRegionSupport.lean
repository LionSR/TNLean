/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.GraphInsertedBondState
import TNLean.PEPS.GraphOpenRegionContraction
import TNLean.PEPS.ParentHamiltonian.RegionGroundSpace

/-!
# Regional support of contractions with exterior bond insertions

An arbitrary matrix on a crossing or exterior bond changes only the boundary
condition presented to a region. When every internal bond matrix is the
identity, every physical slice therefore belongs to the original regional
ground space. The virtual alphabet and the site coefficients are arbitrary.

Source: SCP10, arXiv:1001.3807, local closure deformation in Theorem 5.5,
lines 1440–1545, and regional contraction, lines 1935–1990.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
variable {X : Type*} [Fintype X] [DecidableEq X]

private abbrev Internal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev Noninternal (R : Finset V) := {e : Edge Γ // ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)}
private abbrev Boundary (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_not_internal (R : Finset V) (e : Boundary (Γ := Γ) R) :
    ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rcases e.2 with h | h
  · exact fun hh => h.2 hh.2
  · exact fun hh => h.1 hh.1

private def insertedBoundary (R : Finset V) (ζ : Noninternal (Γ := Γ) R → X × X)
    (e : Boundary (Γ := Γ) R) : X :=
  if e.1.1.1 ∈ R then (ζ ⟨e.1, boundary_not_internal R e⟩).2
  else (ζ ⟨e.1, boundary_not_internal R e⟩).1

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem outside_not_internal (R : Finset V) (v : {v : V // v ∉ R})
    (e : IncidentEdge Γ v.1) : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rintro ⟨ht, hh⟩
  rcases e.2 with h | h
  · exact v.2 (h ▸ ht)
  · exact v.2 (h ▸ hh)

private def outsideLabels (R : Finset V) (ζ : Noninternal (Γ := Γ) R → X × X)
    (v : {v : V // v ∉ R}) (e : IncidentEdge Γ v.1) : X :=
  if e.1.1.1 = v.1 then (ζ ⟨e.1, outside_not_internal R v e⟩).2
  else (ζ ⟨e.1, outside_not_internal R v e⟩).1

private theorem sum_identity_pairs {I : Type*} [Fintype I] [DecidableEq I]
    (f : (I → X × X) → ℂ) :
    (∑ ξ : I → X × X, (∏ i, (1 : Matrix X X ℂ) (ξ i).1 (ξ i).2) * f ξ) =
      ∑ ξ : I → X, f (fun i => (ξ i, ξ i)) := by
  classical
  let E := Equiv.arrowProdEquivProdArrow I (fun _ => X) (fun _ => X)
  rw [← E.symm.sum_comp, Fintype.sum_prod_type]
  simp [E, Equiv.arrowProdEquivProdArrow, Matrix.one_apply,
    Fintype.prod_boole, ← funext_iff]

omit [Fintype V] [DecidableRel Γ.Adj] [Fintype X] [DecidableEq X] in
private theorem assembled_region_labels (R : Finset V)
    (ξ : Internal (Γ := Γ) R → X) (ζ : Noninternal (Γ := Γ) R → X × X)
    (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1) :
    graphSiteBondEndpointEquiv.symm
      ((Equiv.piEquivPiSubtypeProd
        (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R) (fun _ => X × X)).symm
          ((fun e => (ξ e, ξ e)), ζ)) v.1 e =
    (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
      ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ := by
  classical
  by_cases hi : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R
  · have h := graphRegionIncidentConfigEquiv_apply_internal R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)) ⟨e.1, hi⟩
    rw [Equiv.apply_symm_apply] at h
    simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
      Equiv.piEquivPiSubtypeProd, hi]
    simpa using h
  · have hb : IsRegionBoundaryEdge R e.1 := by
      rcases e.2 with ht | hh
      · exact Or.inl ⟨ht.symm ▸ v.2, fun h => hi ⟨ht.symm ▸ v.2, h⟩⟩
      · exact Or.inr ⟨fun h => hi ⟨h, hh.symm ▸ v.2⟩, hh.symm ▸ v.2⟩
    have h := graphRegionIncidentConfigEquiv_apply_boundary R
      ((graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)) ⟨e.1, hb⟩
    rw [Equiv.apply_symm_apply] at h
    rw [← h]
    simp only [graphSiteBondEndpointEquiv, Equiv.coe_fn_symm_mk,
      Equiv.piEquivPiSubtypeProd, hi, ↓reduceDIte, insertedBoundary]
    by_cases ht : e.1.1.1 = v.1
    · simp [ht, v.2]
    · have hh := e.2.resolve_left ht
      have hn : e.1.1.1 ∉ R := fun hn => hi ⟨hn, hh.symm ▸ v.2⟩
      simp [ht, hn]

/-- Matrices on crossing and exterior bonds preserve every regional physical
slice when all internal matrices are identities. No invertibility or symmetry
of the matrices or sites is required. Source: SCP10, Theorem 5.5 and
lines 1935–1990, the boundary-condition argument for local closures. -/
theorem graphInsertedBondNetwork_slice_mem_regionGroundSpace_of_internal_eq_one {d : ℕ}
    (K : Edge Γ → Matrix X X ℂ)
    (a : (v : V) → (IncidentEdge Γ v → X) → Fin d → ℂ)
    (R : Finset V)
    (hK : ∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → K e = 1)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (fun σ => graphInsertedBondNetwork K a (assembleRegionσ R σ τ)) ∈
      regionGroundSpace (groupBondTensor a) R := by
  classical
  let E := Equiv.piEquivPiSubtypeProd
    (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R) (fun _ => X × X)
  let c : (Noninternal (Γ := Γ) R → X × X) → ℂ := fun ζ =>
    (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
      ∏ v : {v : V // v ∉ R}, a v.1 (outsideLabels R ζ v)
        (τ ⟨v.1, by simp [v.2]⟩)
  have hk (ξ : Internal (Γ := Γ) R → X × X)
      (ζ : Noninternal (Γ := Γ) R → X × X) :
      (∏ e, K e (E.symm (ξ, ζ) e).1 (E.symm (ξ, ζ) e).2) =
        (∏ e : Internal (Γ := Γ) R, (1 : Matrix X X ℂ) (ξ e).1 (ξ e).2) *
        ∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2 := by
    rw [← Fintype.prod_subtype_mul_prod_subtype
      (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R)]
    congr 1
    · apply Finset.prod_congr rfl
      intro e _
      simp [E, hK e.1 e.2.1 e.2.2, e.2]
    · apply Finset.prod_congr rfl
      intro e _
      simp [E, e.2]
  have hv (ξ : Internal (Γ := Γ) R → X)
      (ζ : Noninternal (Γ := Γ) R → X × X)
      (σ : RegionPhysicalConfig (d := d) R) :
      (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
        (∏ v, a v (graphSiteBondEndpointEquiv.symm
          (E.symm ((fun e => (ξ e, ξ e)), ζ)) v) (assembleRegionσ R σ τ v)) =
      c ζ * ∏ v : {v : V // v ∈ R}, a v.1
        (fun e => (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
          ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) := by
    have hr : (∏ v : {v : V // v ∈ R}, a v.1
          (graphSiteBondEndpointEquiv.symm (E.symm ((fun e => (ξ e, ξ e)), ζ)) v.1)
          (assembleRegionσ R σ τ v.1)) =
        ∏ v : {v : V // v ∈ R}, a v.1
          (fun e => (graphRegionIncidentConfigEquiv R).symm (ξ, insertedBoundary R ζ)
            ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩) (σ v) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte]
      congr 1
      funext e
      exact assembled_region_labels R ξ ζ v e
    have ho : (∏ v : {v : V // v ∉ R}, a v.1
          (graphSiteBondEndpointEquiv.symm (E.symm ((fun e => (ξ e, ξ e)), ζ)) v.1)
          (assembleRegionσ R σ τ v.1)) =
        ∏ v : {v : V // v ∉ R}, a v.1 (outsideLabels R ζ v)
          (τ ⟨v.1, by simp [v.2]⟩) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte]
      congr 1
      funext e
      simp only [graphSiteBondEndpointEquiv, E, Equiv.piEquivPiSubtypeProd,
        Equiv.coe_fn_symm_mk, outside_not_internal R v e, ↓reduceDIte, outsideLabels]
    have hp := Fintype.prod_subtype_mul_prod_subtype (fun v : V => v ∈ R)
      (fun v => a v (graphSiteBondEndpointEquiv.symm
        (E.symm ((fun e => (ξ e, ξ e)), ζ)) v) (assembleRegionσ R σ τ v))
    have hi : Subtype.fintype (fun v : V => v ∈ R) = Finset.Subtype.fintype R :=
      Subsingleton.elim _ _
    rw [hi] at hp
    have ht := hp.symm.trans (congrArg₂ (· * ·) hr ho)
    exact (congrArg
      (fun z => (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) * z)
      ht).trans (by dsimp only [c]; ring)
  have heq : (fun σ => graphInsertedBondNetwork K a (assembleRegionσ R σ τ)) =
      ∑ ζ : Noninternal (Γ := Γ) R → X × X,
        c ζ • graphOpenRegionNetwork a R (insertedBoundary R ζ) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold graphInsertedBondNetwork
    rw [← E.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ζ _
    simp_rw [hk, mul_assoc]
    rw [sum_identity_pairs]
    simp_rw [hv]
    rw [← Finset.mul_sum, graphOpenRegionNetwork_eq_sum_internal]
  rw [heq]
  apply Submodule.sum_mem
  intro ζ _
  apply Submodule.smul_mem
  have h := openRegionWeight_mem_regionGroundSpace (groupBondTensor a) R
    (fun e => Fintype.equivFin X (insertedBoundary R ζ e))
  have heq : openRegionWeight (groupBondTensor a) R
      (fun e => Fintype.equivFin X (insertedBoundary R ζ e)) =
      graphOpenRegionNetwork a R (insertedBoundary R ζ) := by
    funext σ
    exact openRegionWeight_groupBondTensor_eq_graphOpenRegionNetwork a R _ σ
  rwa [heq] at h

end TNLean.PEPS
