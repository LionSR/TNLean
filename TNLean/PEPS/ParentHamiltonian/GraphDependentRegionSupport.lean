/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.ParentHamiltonian.GraphDependentCutCoordinates

/-!
# Regional support of independently sized bond insertions

Identity matrices on internal edges leave the original open-region range.
Arbitrary matrices on crossing and exterior edges only change its boundary.
Auxiliary regional contraction for SCP10, Theorem 5.7, lines 1527–1558.
-/

noncomputable section
open scoped BigOperators Matrix
namespace TNLean.PEPS
open DependentBondNetwork

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {Γ : SimpleGraph V} [DecidableRel Γ.Adj] {d : ℕ}

private abbrev Internal (R : Finset V) := {e : Edge Γ // e.1.1 ∈ R ∧ e.1.2 ∈ R}
private abbrev Noninternal (R : Finset V) := {e : Edge Γ // ¬ (e.1.1 ∈ R ∧ e.1.2 ∈ R)}
private abbrev Boundary (R : Finset V) := {e : Edge Γ // IsRegionBoundaryEdge R e}

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem boundary_not_internal (R : Finset V) (e : Boundary (Γ := Γ) R) :
    ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rcases e.2 with h | h
  · exact fun hh => h.2 hh.2
  · exact fun hh => h.1 hh.1

private def regionSplit (A : Tensor Γ d) (R : Finset V) :
    RegionIncidentConfig A R ≃
      ((e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1)) × RegionBoundaryConfig A R where
  toFun η := (fun e ↦ η ⟨e.1, Or.inl e.2.1⟩, regionIncidentBoundaryLabel A R η)
  invFun p e := if hi : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R then p.1 ⟨e.1, hi⟩ else
    p.2 ⟨e.1, by
      rcases e.2 with ht | hh
      · exact Or.inl ⟨ht, fun hh ↦ hi ⟨ht, hh⟩⟩
      · exact Or.inr ⟨fun ht ↦ hi ⟨ht, hh⟩, hh⟩⟩
  left_inv η := by funext e; dsimp only; split_ifs <;> rfl
  right_inv p := by
    apply Prod.ext
    · funext e
      simp [e.2]
    · funext e
      simp [regionIncidentBoundaryLabel, boundary_not_internal R e]

private theorem openRegionWeight_eq_sum_internal (A : Tensor Γ d) (R : Finset V)
    (μ : RegionBoundaryConfig A R) (σ : RegionPhysicalConfig (d := d) R) :
    openRegionWeight A R μ σ =
      ∑ ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1),
        regionIncidentWeight A R ((regionSplit A R).symm (ξ, μ)) σ := by
  classical
  unfold openRegionWeight
  rw [← (regionSplit A R).symm.sum_comp, Fintype.sum_prod_type]
  have hb (ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1))
      (ζ : RegionBoundaryConfig A R) :
      regionIncidentBoundaryLabel A R ((regionSplit A R).symm (ξ, ζ)) = ζ :=
    congrArg Prod.snd ((regionSplit A R).apply_symm_apply (ξ, ζ))
  simp_rw [hb]
  simp

private def insertedBoundary (A : Tensor Γ d) (R : Finset V)
    (ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1))
    (e : Boundary (Γ := Γ) R) : Fin (A.bondDim e.1) :=
  if e.1.1.1 ∈ R then (ζ ⟨e.1, boundary_not_internal R e⟩).2
  else (ζ ⟨e.1, boundary_not_internal R e⟩).1

omit [Fintype V] [DecidableRel Γ.Adj] in
private theorem outside_not_internal (R : Finset V) (v : {v : V // v ∉ R})
    (e : IncidentEdge Γ v.1) : ¬ (e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R) := by
  rintro ⟨ht, hh⟩
  rcases e.2 with h | h
  · exact v.2 (h ▸ ht)
  · exact v.2 (h ▸ hh)

private def outsideLabels (A : Tensor Γ d) (R : Finset V)
    (ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1))
    (v : {v : V // v ∉ R}) (e : IncidentEdge Γ v.1) : Fin (A.bondDim e.1) :=
  if e.1.1.1 = v.1 then (ζ ⟨e.1, outside_not_internal R v e⟩).2
  else (ζ ⟨e.1, outside_not_internal R v e⟩).1

private theorem sum_identity_pairs {I : Type*} [Fintype I] [DecidableEq I]
    (D : I → Type*) [∀ i, Fintype (D i)] [∀ i, DecidableEq (D i)]
    (f : ((i : I) → D i × D i) → ℂ) :
    (∑ ξ : (i : I) → D i × D i,
      (∏ i, (1 : Matrix (D i) (D i) ℂ) (ξ i).1 (ξ i).2) * f ξ) =
      ∑ ξ : (i : I) → D i, f (fun i => (ξ i, ξ i)) := by
  classical
  rw [← (endpointPairEquiv D).sum_comp]
  exact sum_identityWeight_mul D (fun β ↦ f (endpointPairEquiv D β))

omit [Fintype V] in
private theorem assembled_region_labels (A : Tensor Γ d) (R : Finset V)
    (ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1))
    (ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1))
    (v : {v : V // v ∈ R}) (e : IncidentEdge Γ v.1) :
    (endpointPairEquiv (graphBondAlphabet A)).symm
      ((Equiv.piEquivPiSubtypeProd
        (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R)
        (fun e => Fin (A.bondDim e) × Fin (A.bondDim e))).symm
          ((fun e => (ξ e, ξ e)), ζ)) (graphIncidentEndpoint v.1 e).1 =
    (regionSplit A R).symm (ξ, insertedBoundary A R ζ)
      ⟨e.1, isRegionIncidentEdge_of_regionVertex R v e⟩ := by
  classical
  by_cases hi : e.1.1.1 ∈ R ∧ e.1.1.2 ∈ R
  · simp [endpointPairEquiv, graphIncidentEndpoint, Equiv.piEquivPiSubtypeProd,
      regionSplit, hi]
  · simp only [endpointPairEquiv, Equiv.coe_fn_symm_mk, graphIncidentEndpoint,
      Equiv.piEquivPiSubtypeProd, hi, ↓reduceDIte, regionSplit, insertedBoundary]
    by_cases ht : e.1.1.1 = v.1
    · simp [ht, v.2]
    · have hh := e.2.resolve_left ht
      have hn : e.1.1.1 ∉ R := fun hn => hi ⟨hn, hh.symm ▸ v.2⟩
      simp [ht, hn]

/-- Independently sized matrices on crossing and exterior edges only change the
virtual boundary. Internal identity matrices retain the actual regional range.
Source: SCP10, Theorem 5.7, local sufficiency of commuting closures. -/
theorem graphDependentNetwork_slice_mem_regionGroundSpace_of_internal_eq_one
    (A : Tensor Γ d)
    (K : (e : Edge Γ) → Matrix (graphBondAlphabet A e) (graphBondAlphabet A e) ℂ)
    (R : Finset V)
    (hK : ∀ e : Edge Γ, e.1.1 ∈ R → e.1.2 ∈ R → K e = 1)
    (τ : RegionPhysicalConfig (d := d) (Finset.univ \ R)) :
    (fun σ => network graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) K (assembleRegionσ R σ τ)) ∈ regionGroundSpace A R := by
  classical
  let E := Equiv.piEquivPiSubtypeProd
    (fun e : Edge Γ => e.1.1 ∈ R ∧ e.1.2 ∈ R)
    (fun e => Fin (A.bondDim e) × Fin (A.bondDim e))
  let c : ((e : Noninternal (Γ := Γ) R) →
      Fin (A.bondDim e.1) × Fin (A.bondDim e.1)) → ℂ := fun ζ =>
    (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
      ∏ v : {v : V // v ∉ R}, A.component v.1 (outsideLabels A R ζ v)
        (τ ⟨v.1, by simp [v.2]⟩)
  have hk (ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1))
      (ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1)) :
      (∏ e, K e (E.symm (ξ, ζ) e).1 (E.symm (ξ, ζ) e).2) =
        (∏ e : Internal (Γ := Γ) R,
          (1 : Matrix (Fin (A.bondDim e.1)) (Fin (A.bondDim e.1)) ℂ) (ξ e).1 (ξ e).2) *
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
  have hv (ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1))
      (ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1))
      (σ : RegionPhysicalConfig (d := d) R) :
      (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) *
        (∏ v, graphDependentTensor A v (endpointSiteEquiv graphEdgeTail graphEdgeHead
          (graphBondAlphabet A) ((endpointPairEquiv (graphBondAlphabet A)).symm
            (E.symm ((fun e => (ξ e, ξ e)), ζ))) v) (assembleRegionσ R σ τ v)) =
      c ζ * regionIncidentWeight A R ((regionSplit A R).symm (ξ, insertedBoundary A R ζ)) σ := by
    have hr : (∏ v : {v : V // v ∈ R}, graphDependentTensor A v.1
          (endpointSiteEquiv graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            ((endpointPairEquiv (graphBondAlphabet A)).symm
              (E.symm ((fun e => (ξ e, ξ e)), ζ))) v.1) (assembleRegionσ R σ τ v.1)) =
        regionIncidentWeight A R ((regionSplit A R).symm (ξ, insertedBoundary A R ζ)) σ := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte, graphDependentTensor,
        endpointSiteEquiv_apply]
      congr 1
      funext e
      exact assembled_region_labels A R ξ ζ v e
    have ho : (∏ v : {v : V // v ∉ R}, graphDependentTensor A v.1
          (endpointSiteEquiv graphEdgeTail graphEdgeHead (graphBondAlphabet A)
            ((endpointPairEquiv (graphBondAlphabet A)).symm
              (E.symm ((fun e => (ξ e, ξ e)), ζ))) v.1) (assembleRegionσ R σ τ v.1)) =
        ∏ v : {v : V // v ∉ R}, A.component v.1 (outsideLabels A R ζ v)
          (τ ⟨v.1, by simp [v.2]⟩) := by
      apply Finset.prod_congr rfl
      intro v _
      simp only [assembleRegionσ, v.2, ↓reduceDIte, graphDependentTensor,
        endpointSiteEquiv_apply]
      congr 1
      funext e
      simp only [endpointPairEquiv, graphIncidentEndpoint, E, Equiv.piEquivPiSubtypeProd,
        Equiv.coe_fn_symm_mk, outside_not_internal R v e, ↓reduceDIte, outsideLabels]
      by_cases ht : e.1.1.1 = v.1 <;> simp [ht]
    have hp := Fintype.prod_subtype_mul_prod_subtype (fun v : V => v ∈ R)
      (fun v => graphDependentTensor A v (endpointSiteEquiv graphEdgeTail graphEdgeHead
        (graphBondAlphabet A) ((endpointPairEquiv (graphBondAlphabet A)).symm
          (E.symm ((fun e => (ξ e, ξ e)), ζ))) v) (assembleRegionσ R σ τ v))
    have hi : Subtype.fintype (fun v : V => v ∈ R) = Finset.Subtype.fintype R :=
      Subsingleton.elim _ _
    rw [hi] at hp
    have ht := hp.symm.trans (congrArg₂ (· * ·) hr ho)
    exact (congrArg
      (fun z => (∏ e : Noninternal (Γ := Γ) R, K e.1 (ζ e).1 (ζ e).2) * z)
      ht).trans (by dsimp only [c]; ring)
  have heq : (fun σ => network graphEdgeTail graphEdgeHead (graphBondAlphabet A)
      (graphDependentTensor A) K (assembleRegionσ R σ τ)) =
      ∑ ζ : (e : Noninternal (Γ := Γ) R) → Fin (A.bondDim e.1) × Fin (A.bondDim e.1),
        c ζ • openRegionWeight A R (insertedBoundary A R ζ) := by
    funext σ
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    unfold network bondWeight
    rw [← (endpointPairEquiv (graphBondAlphabet A)).symm.sum_comp]
    simp only [endpointPairEquiv, Equiv.coe_fn_symm_mk, Bool.false_eq_true, ↓reduceIte]
    rw [← E.symm.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ζ _
    simp_rw [hk, mul_assoc]
    rw [sum_identity_pairs]
    calc
      _ = ∑ ξ : (e : Internal (Γ := Γ) R) → Fin (A.bondDim e.1),
          c ζ * regionIncidentWeight A R
            ((regionSplit A R).symm (ξ, insertedBoundary A R ζ)) σ :=
        Finset.sum_congr rfl fun ξ _ ↦ hv ξ ζ σ
      _ = _ := by rw [← Finset.mul_sum, openRegionWeight_eq_sum_internal]
  rw [heq]
  apply Submodule.sum_mem
  intro ζ _
  exact Submodule.smul_mem _ _ (openRegionWeight_mem_regionGroundSpace A R _)

end TNLean.PEPS
