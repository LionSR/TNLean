/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.Basic

/-!
# Piecewise calculus for PEPS virtual configurations

This file provides low-level operations for splitting, reindexing, and gluing virtual
configurations. Given a predicate on edges, `mergeVirtualConfig` reads one configuration
where the predicate holds and another configuration elsewhere. The region-specific
`regionMerge` specializes this operation to the edges incident to a region.
The equivalence `vertexConfigSplitAt` separates the labels incident to one vertex from all
remaining edge labels.

The vertex-product lemmas compare products before and after merging configurations. The
final lemma groups a finite sum by its merged configuration and collapses fibers of constant
cardinality.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Split and reindex equivalences -/

/-- Split a virtual configuration into its restrictions to the edges satisfying `select`
and the edges not satisfying `select`. -/
noncomputable def virtualConfigSplit (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] :
    VirtualConfig A ≃
      ((e : {e : Edge G // select e}) → Fin (A.bondDim e.1)) ×
        ((e : {e : Edge G // ¬ select e}) → Fin (A.bondDim e.1)) :=
  Equiv.piEquivPiSubtypeProd select fun e => Fin (A.bondDim e)

omit [Fintype V] in
theorem virtualConfigSplit_fst_apply (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (ζ : VirtualConfig A) (e : {e : Edge G // select e}) :
    (virtualConfigSplit A select ζ).1 e = ζ e.1 := rfl

omit [Fintype V] in
theorem virtualConfigSplit_snd_apply (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (ζ : VirtualConfig A) (e : {e : Edge G // ¬ select e}) :
    (virtualConfigSplit A select ζ).2 e = ζ e.1 := rfl

/-! ### Split at one vertex -/

/-- The predicate on edges singling out those incident to `j`. -/
def IsIncidentEdge (j : V) (f : Edge G) : Prop :=
  f.1.1 = j ∨ f.1.2 = j

instance (j : V) (f : Edge G) : Decidable (IsIncidentEdge (G := G) j f) := by
  unfold IsIncidentEdge
  infer_instance

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge underlying an incidence at `j` satisfies the vertex-incidence predicate. -/
theorem isIncidentEdge_of_incident (j : V) (ie : IncidentEdge G j) :
    IsIncidentEdge (G := G) j ie.1 := ie.2

/-- Split a virtual configuration into its labels on the edges incident to `j`
and its labels on all remaining edges. -/
noncomputable def vertexConfigSplitAt (A : Tensor G d) (j : V) :
    VirtualConfig A ≃
      LocalVirtualConfig A j ×
        ((f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1)) :=
  virtualConfigSplit A fun f => IsIncidentEdge (G := G) j f

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_fst (A : Tensor G d) (j : V) (ζ : VirtualConfig A)
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j ζ).1 ie = ζ ie.1 := rfl

omit [Fintype V] in
@[simp] theorem vertexConfigSplitAt_symm_apply_incident (A : Tensor G d) (j : V)
    (η : LocalVirtualConfig A j)
    (r : (f : {f : Edge G // ¬ IsIncidentEdge (G := G) j f}) → Fin (A.bondDim f.1))
    (ie : IncidentEdge G j) :
    (vertexConfigSplitAt (G := G) A j).symm (η, r) ie.1 = η ie := by
  unfold vertexConfigSplitAt virtualConfigSplit IsIncidentEdge
  rw [Equiv.piEquivPiSubtypeProd_symm_apply, dif_pos ie.2]

/-- Reindex every virtual bond along equality of the bond-dimension families. -/
noncomputable def virtualConfigCongr (A B : Tensor G d) (h : A.bondDim = B.bondDim) :
    VirtualConfig A ≃ VirtualConfig B :=
  Equiv.piCongrRight fun e => finCongr (congrFun h e)

omit [Fintype V] in
theorem virtualConfigCongr_apply (A B : Tensor G d) (h : A.bondDim = B.bondDim)
    (ζ : VirtualConfig A) (e : Edge G) :
    virtualConfigCongr A B h ζ e = Fin.cast (congrFun h e) (ζ e) := rfl

/-! ### Piecewise merge -/

/-- Merge two virtual configurations, reading `left` where `select` holds and `right`
elsewhere. The fibers may depend on the selected edge, as virtual bond dimensions do. -/
noncomputable def mergeVirtualConfig (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (left right : VirtualConfig A) : VirtualConfig A :=
  fun e => if select e then left e else right e

omit [Fintype V] in
@[simp]
theorem mergeVirtualConfig_of_pos (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (left right : VirtualConfig A) {e : Edge G} (he : select e) :
    mergeVirtualConfig A select left right e = left e := by
  simp [mergeVirtualConfig, he]

omit [Fintype V] in
@[simp]
theorem mergeVirtualConfig_of_neg (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (left right : VirtualConfig A) {e : Edge G} (he : ¬ select e) :
    mergeVirtualConfig A select left right e = right e := by
  simp [mergeVirtualConfig, he]

omit [Fintype V] in
theorem mergeVirtualConfig_self (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (ζ : VirtualConfig A) : mergeVirtualConfig A select ζ ζ = ζ := by
  ext e
  by_cases he : select e <;> simp [mergeVirtualConfig, he]

omit [Fintype V] in
theorem virtualConfigSplit_mergeVirtualConfig (A : Tensor G d) (select : Edge G → Prop)
    [DecidablePred select] (left right : VirtualConfig A) :
    virtualConfigSplit A select (mergeVirtualConfig A select left right) =
      (fun e : {e : Edge G // select e} => left e.1,
        fun e : {e : Edge G // ¬ select e} => right e.1) := by
  apply Prod.ext
  · funext e
    exact mergeVirtualConfig_of_pos A select left right e.2
  · funext e
    exact mergeVirtualConfig_of_neg A select left right e.2

omit [Fintype V] in
/-- Reindexing virtual bonds commutes with a piecewise merge. -/
theorem virtualConfigCongr_mergeVirtualConfig (A B : Tensor G d)
    (h : A.bondDim = B.bondDim) (select : Edge G → Prop) [DecidablePred select]
    (left right : VirtualConfig A) :
    virtualConfigCongr A B h (mergeVirtualConfig A select left right) =
      mergeVirtualConfig B select (virtualConfigCongr A B h left)
        (virtualConfigCongr A B h right) := by
  ext e
  by_cases he : select e
  · simp only [virtualConfigCongr_apply, mergeVirtualConfig_of_pos A select left right he,
      mergeVirtualConfig_of_pos B select _ _ he]
  · simp only [virtualConfigCongr_apply, mergeVirtualConfig_of_neg A select left right he,
      mergeVirtualConfig_of_neg B select _ _ he]

/-! ### Region specialization -/

/-- Merge a pair of virtual configurations along a region: region-incident edges read the
first configuration and all remaining edges read the second. -/
noncomputable def regionMerge (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) : VirtualConfig A :=
  mergeVirtualConfig A (IsRegionIncidentEdge (G := G) R) p.1 p.2

omit [Fintype V] in
@[simp]
theorem regionMerge_of_incident (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) {e : Edge G}
    (he : IsRegionIncidentEdge (G := G) R e) : regionMerge A R p e = p.1 e := by
  exact mergeVirtualConfig_of_pos A _ _ _ he

omit [Fintype V] in
@[simp]
theorem regionMerge_of_not_incident (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) {e : Edge G}
    (he : ¬ IsRegionIncidentEdge (G := G) R e) : regionMerge A R p e = p.2 e := by
  exact mergeVirtualConfig_of_neg A _ _ _ he

omit [Fintype V] in
/-- The region vertex product reads the first input of `regionMerge`. -/
theorem regionProd_eq_merge (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (p : VirtualConfig A × VirtualConfig A) :
    (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ R},
        A.component w.1 (fun ie => regionMerge (G := G) A R p ie.1) (σ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  symm
  apply regionMerge_of_incident
  rcases ie.2 with hie | hie
  · exact Or.inl (by rw [hie]; exact w.2)
  · exact Or.inr (by rw [hie]; exact w.2)

omit [Fintype V] in
/-- A vertex product reads the second configuration through a region merge if the two
configurations agree on every edge incident to both the merge region and the product region. -/
theorem regionProd_p2_eq_merge_of_incident_agree (A : Tensor G d) (T B : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) B)
    (p : VirtualConfig A × VirtualConfig A)
    (hp : ∀ e : Edge G, IsRegionIncidentEdge (G := G) T e →
      IsRegionIncidentEdge (G := G) B e → p.1 e = p.2 e) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.2 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  have hB : IsRegionIncidentEdge (G := G) B ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  by_cases hT : IsRegionIncidentEdge (G := G) T ie.1
  · rw [regionMerge_of_incident A T p hT, hp ie.1 hT hB]
  · rw [regionMerge_of_not_incident A T p hT]

/-- The complement vertex product reads the second input of `regionMerge`, provided the two
inputs agree on the boundary of the region. -/
theorem complementProd_eq_merge (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2) :
    (∏ w : {w : V // w ∈ Finset.univ \ R},
        A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      ∏ w : {w : V // w ∈ Finset.univ \ R},
        A.component w.1 (fun ie => regionMerge (G := G) A R p ie.1) (τ w) := by
  apply regionProd_p2_eq_merge_of_incident_agree
  intro e hR hcompl
  have hbdry : IsRegionBoundaryEdge (G := G) R e := by
    rcases hR with hR1 | hR2 <;> rcases hcompl with hc1 | hc2
    · exact absurd hR1 (Finset.mem_sdiff.mp hc1).2
    · exact Or.inl ⟨hR1, (Finset.mem_sdiff.mp hc2).2⟩
    · exact Or.inr ⟨(Finset.mem_sdiff.mp hc1).2, hR2⟩
    · exact absurd hR2 (Finset.mem_sdiff.mp hc2).2
  exact congrFun hp ⟨e, hbdry⟩

/-! ### Constant-cardinality fiber sums -/

/-- Collapse a sum whose summand factors through a map to virtual configurations, when all
fibers of that map on the indexing finset have the same cardinality. -/
theorem sum_comp_of_config_fiber_card {A : Tensor G d} {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (merge : ι → VirtualConfig A) (n : ℕ)
    (hcard : ∀ η : VirtualConfig A, (s.filter fun x => merge x = η).card = n)
    (g : VirtualConfig A → M) :
    (∑ x ∈ s, g (merge x)) = n • ∑ η : VirtualConfig A, g η := by
  classical
  rw [← Finset.sum_fiberwise s merge (fun x => g (merge x)), Finset.smul_sum]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  rw [Finset.sum_congr rfl (g := fun _ => g η)
      (fun x hx => by rw [Finset.mem_filter] at hx; rw [hx.2]),
    Finset.sum_const, hcard η]

end PEPS
end TNLean
