/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Tensor.Region.RegionConfigSplit

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

The region/complement decomposition of the closed state coefficient closes the file:
the closed state coefficient splits at a region `R` into the region vertex product
against the complement vertex product (`prod_assembleRegionσ_split`), and the sum over
pairs of global configurations agreeing on the boundary of `R` overcounts the closed
state coefficient by the bond-dimension product over the edges not crossing the
boundary (`regionInteriorBondProd`, `stateCoeff_eq_regionComplement`,
`sum_regionBlockedWeight_mul_complement`). Source: arXiv:1804.04964, Section 3,
Lemma `inj_isomorph`, lines 254--582 of `Papers/1804.04964/paper_normal.tex`.
-/

open ManyBody (Edge)

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

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
  change (if h : IsIncidentEdge (G := G) j ie.1 then η ⟨ie.1, h⟩ else r ⟨ie.1, h⟩) = η ie
  split
  · rfl
  · exact (‹¬ IsIncidentEdge (G := G) j ie.1› (isIncidentEdge_of_incident (G := G) j ie)).elim

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
  mergeVirtualConfig A (ManyBody.IsRegionIncidentEdge (G := G) R) p.1 p.2

omit [Fintype V] in
@[simp]
theorem regionMerge_of_incident (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) {e : Edge G}
    (he : ManyBody.IsRegionIncidentEdge (G := G) R e) : regionMerge A R p e = p.1 e := by
  exact mergeVirtualConfig_of_pos A _ _ _ he

omit [Fintype V] in
@[simp]
theorem regionMerge_of_not_incident (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) {e : Edge G}
    (he : ¬ ManyBody.IsRegionIncidentEdge (G := G) R e) : regionMerge A R p e = p.2 e := by
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
    (hp : ∀ e : Edge G, ManyBody.IsRegionIncidentEdge (G := G) T e →
      ManyBody.IsRegionIncidentEdge (G := G) B e → p.1 e = p.2 e) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.2 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  classical
  refine Finset.prod_congr rfl (fun w _ => ?_)
  congr 1
  funext ie
  have hB : ManyBody.IsRegionIncidentEdge (G := G) B ie.1 := by
    rcases ie.2 with hie | hie
    · exact Or.inl (by rw [hie]; exact w.2)
    · exact Or.inr (by rw [hie]; exact w.2)
  by_cases hT : ManyBody.IsRegionIncidentEdge (G := G) T ie.1
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
  have hbdry : ManyBody.IsRegionBoundaryEdge (G := G) R e := by
    rcases hR with hR1 | hR2 <;> rcases hcompl with hc1 | hc2
    · exact absurd hR1 (Finset.mem_sdiff.mp hc1).2
    · exact Or.inl ⟨hR1, (Finset.mem_sdiff.mp hc2).2⟩
    · exact Or.inr ⟨(Finset.mem_sdiff.mp hc1).2, hR2⟩
    · exact absurd hR2 (Finset.mem_sdiff.mp hc2).2
  exact congrFun hp ⟨e, hbdry⟩

/-! ### Boundary-label and product-subset transfer

These lemmas transfer boundary labels and vertex products through a region merge
`regionMerge A T p`.  When a region `H` is contained in the merge region `T`, its
boundary label and vertex product read `p.1` through the merge.  When a region
is disjoint from `T`, they read `p.2`, provided the pair agrees on the `T`-boundary.
-/

omit [Fintype V] in
/-- A boundary edge of a region `H` with `H ⊆ T`, read off the merge `regionMerge A T p`,
equals the value of `p.1`: such an edge touches `H ⊆ T`, hence is `T`-incident, where the
merge reads `p.1`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the host-side boundary-edge reading);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionBoundaryLabel_regionMerge_of_subset_left {T H : Finset V} (hHT : H ⊆ T)
    (p : VirtualConfig A × VirtualConfig A) :
    regionBoundaryLabel (G := G) A H (regionMerge (G := G) A T p) =
      regionBoundaryLabel (G := G) A H p.1 := by
  funext f
  simp only [regionBoundaryLabel_apply]
  have hinc : ManyBody.IsRegionIncidentEdge (G := G) T f.1 := by
    rcases ManyBody.isRegionBoundaryEdge_touches (G := G) H f.2 with h1 | h2
    · exact Or.inl (hHT h1)
    · exact Or.inr (hHT h2)
  rw [regionMerge_of_incident (G := G) A _ p hinc]

/-- A boundary edge of the host `univ \ K` with `K ⊆ univ \ T`, read off the merge
`regionMerge A T p`, equals the value of `p.2`, provided the pair agrees on the `T`-boundary.
Such an edge has its `K`-endpoint in `univ \ T` (so not in `T`); if `T`-incident, its other
endpoint is in `T`, making it a `T`-boundary edge where the agreement pins the value, and
otherwise the merge reads `p.2` directly.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 355--486 of
`Papers/1804.04964/paper_normal.tex` (the complement-side boundary-edge reading);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionBoundaryLabel_regionMerge_compl_of_subset {T K : Finset V}
    (hKT : K ⊆ Finset.univ \ T) (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2) :
    regionBoundaryLabel (G := G) A (Finset.univ \ K) (regionMerge (G := G) A T p) =
      regionBoundaryLabel (G := G) A (Finset.univ \ K) p.2 := by
  classical
  funext f
  simp only [regionBoundaryLabel_apply]
  by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) T f.1
  · -- `f` is a boundary edge of `univ \ K` and `T`-incident: it is a `T`-boundary edge.
    have hbdry : ManyBody.IsRegionBoundaryEdge (G := G) T f.1 := by
      rcases f.2 with ⟨h1host, h2nothost⟩ | ⟨h1nothost, h2host⟩
      · have h2K : f.1.1.2 ∈ K := by
          by_contra hk; exact h2nothost (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)
        have h2notT : f.1.1.2 ∉ T := by
          have := hKT h2K; rw [Finset.mem_sdiff] at this; exact this.2
        rcases hinc with hc1 | hc2
        · exact Or.inl ⟨hc1, h2notT⟩
        · exact absurd hc2 h2notT
      · have h1K : f.1.1.1 ∈ K := by
          by_contra hk; exact h1nothost (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hk⟩)
        have h1notT : f.1.1.1 ∉ T := by
          have := hKT h1K; rw [Finset.mem_sdiff] at this; exact this.2
        rcases hinc with hc1 | hc2
        · exact absurd hc1 h1notT
        · exact Or.inr ⟨h1notT, hc2⟩
    rw [regionMerge_of_incident (G := G) A _ p hinc]
    have := congrFun hp ⟨f.1, hbdry⟩
    simpa [regionBoundaryLabel] using this
  · rw [regionMerge_of_not_incident (G := G) A _ p hinc]

omit [Fintype V] in
/-- A vertex product over `B ⊆ T` reads `p.1` through the merge `regionMerge A T p`: edges
incident to `B ⊆ T` are `T`-incident, where the merge reads `p.1`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionProd_p1_eq_merge_of_subset {T B : Finset V} (hBT : B ⊆ T)
    (σ : RegionPhysicalConfig (V := V) (d := d) B) (p : VirtualConfig A × VirtualConfig A) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  apply regionProd_subtype_congr
  intro ie hie
  have hinc : ManyBody.IsRegionIncidentEdge (G := G) T ie :=
    hie.elim (fun h => Or.inl (hBT h)) (fun h => Or.inr (hBT h))
  rw [regionMerge_of_incident (G := G) A _ p hinc]

/-- A vertex product over `B ⊆ univ \ T` reads `p.2` through the merge `regionMerge A T p`, given
the pair agrees on the `T`-boundary: an edge incident to `B` either misses `T` (where the merge
reads `p.2`) or, being `T`-incident with an endpoint in `B ⊆ univ \ T`, is a `T`-boundary edge
where the agreement pins it.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 3. -/
theorem regionProd_p2_eq_merge_of_compl {T B : Finset V} (hBT : B ⊆ Finset.univ \ T)
    (σ : RegionPhysicalConfig (V := V) (d := d) B) (p : VirtualConfig A × VirtualConfig A)
    (hp : regionBoundaryLabel (G := G) A T p.1 = regionBoundaryLabel (G := G) A T p.2) :
    (∏ w : {w : V // w ∈ B}, A.component w.1 (fun ie => p.2 ie.1) (σ w)) =
      ∏ w : {w : V // w ∈ B},
        A.component w.1 (fun ie => regionMerge (G := G) A T p ie.1) (σ w) := by
  classical
  apply regionProd_subtype_congr
  intro ie hie
  have hcompl : ManyBody.IsRegionIncidentEdge (G := G) (Finset.univ \ T) ie :=
    hie.elim (fun h => Or.inl (hBT h)) (fun h => Or.inr (hBT h))
  by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) T ie
  · have hbdry : ManyBody.IsRegionBoundaryEdge (G := G) T ie :=
      ManyBody.isRegionBoundaryEdge_of_disjoint_incident (G := G) (Finset.univ \ T) T
        Finset.sdiff_disjoint hcompl hinc
    rw [regionMerge_of_incident (G := G) A _ p hinc]
    have := congrFun hp ⟨ie, hbdry⟩
    simpa [regionBoundaryLabel] using this.symm
  · rw [regionMerge_of_not_incident (G := G) A _ p hinc]

/-! ### Blocked-weight config-sum expansion -/

open scoped Classical in
/-- The blocked-region weight grouped over the configurations realizing a boundary label: a
boundary-indicator config sum collapses the blocked-region weight to a sum over the global
configurations, grouping by the boundary label. -/
theorem blockedWeight_as_configSum (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (f : RegionBoundaryConfig (G := G) A R → ℂ) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
        f μ * regionBlockedWeight (G := G) A R μ σ) =
      ∑ ζ : VirtualConfig A,
        f (regionBoundaryLabel (G := G) A R ζ) *
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w) := by
  classical
  rw [← Finset.sum_fiberwise (Finset.univ : Finset (VirtualConfig A))
    (fun ζ => regionBoundaryLabel (G := G) A R ζ)
    (fun ζ => f (regionBoundaryLabel (G := G) A R ζ) *
      ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w))]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [regionBlockedWeight, Finset.mul_sum]
  refine Finset.sum_congr ?_ (fun ζ hζ => ?_)
  · ext ζ; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  · rw [Finset.mem_filter] at hζ; rw [hζ.2]

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

section RegionComplement

open scoped Matrix

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### Region/complement decomposition of the closed state coefficient

The closed state coefficient splits at an arbitrary region `R`, as a contraction
of the blocked-region weight on `R` against the blocked-region weight on the set
complement `univ \ R`, summed over the boundary configuration. Because the
blocked-region weight of `R` is a sum over *all* global virtual configurations
restricting to a given boundary configuration -- including free values on the
edges internal to the complement, which the region vertex product ignores -- the
contraction overcounts the closed state coefficient by the product of the bond
dimensions over the edges *not* crossing the boundary of `R`. This is the
region analogue of `stateCoeff_eq_vertexComplement`, where the single-vertex
star contraction has no such overcounting because its complement product reads
every edge. -/

/-- The global vertex product of the assembled physical configuration splits as
the region vertex product (reading `σ`) times the complement vertex product
(reading `τ`), at any fixed global virtual configuration. -/
theorem prod_assembleRegionσ_split (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (ζ : VirtualConfig A) :
    (∏ v : V, A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v)) =
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => ζ ie.1) (τ w) := by
  classical
  -- Read both region/complement subtype products through the assembled configuration.
  rw [show (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w.1) from
      Finset.prod_congr rfl (fun w _ => by rw [assembleRegionσ_mem]),
    show (∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => ζ ie.1) (τ w)) =
        ∏ w : {w : V // w ∈ Finset.univ \ R}, A.component w.1 (fun ie => ζ ie.1)
          (assembleRegionσ (V := V) (d := d) R σ τ w.1) from
      Finset.prod_congr rfl (fun w _ => by rw [assembleRegionσ_notMem])]
  -- Convert the two subtype products into the corresponding Finset products.
  rw [← Finset.prod_subtype R (fun x => Iff.rfl)
      (fun v => A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v)),
    ← Finset.prod_subtype (Finset.univ \ R) (fun x => Iff.rfl)
      (fun v => A.component v (fun ie => ζ ie.1)
        (assembleRegionσ (V := V) (d := d) R σ τ v))]
  -- Split the global product into `R` and its complement.
  rw [← Finset.compl_eq_univ_sdiff, Finset.prod_mul_prod_compl R
    (fun v => A.component v (fun ie => ζ ie.1)
      (assembleRegionσ (V := V) (d := d) R σ τ v))]

/-- The complement boundary label of a global virtual configuration equals
`regionComplementBoundaryConfig μ` exactly when its region boundary label equals
`μ`. Both record that the configuration agrees with `μ` on every boundary edge of
`R`, read through the boundary-edge identification of `R` with its complement. -/
theorem regionBoundaryLabel_compl_eq_iff (A : Tensor G d) (R : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R) (ξ : VirtualConfig A) :
    regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
        regionComplementBoundaryConfig (G := G) A R μ ↔
      regionBoundaryLabel (G := G) A R ξ = μ := by
  constructor
  · intro h
    funext f
    have hh := congrFun h (regionBoundaryEdgeToCompl (G := G) R f)
    rw [regionComplementBoundaryConfig_apply_toCompl] at hh
    simpa [regionBoundaryLabel, regionBoundaryEdgeToCompl, regionBoundaryEdgeComplEquiv,
      Equiv.subtypeEquivRight] using hh
  · intro h
    funext f
    simp only [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
    have hh := congrFun h ((regionBoundaryEdgeComplEquiv (G := G) R).symm f)
    rw [regionBoundaryLabel_apply] at hh
    exact hh

/-! ### Multiplicity collapse to the closed state coefficient

The boundary-agreement double sum overcounts the closed state coefficient by the
bond-dimension product over the edges not crossing the boundary of `R`. To see
this, merge the two configurations of an agreeing pair into one global
configuration that reads the region side from the first and the complement side
from the second: the region vertex product depends only on the merged
configuration through the region-incident edges, the complement vertex product
only through the complement-incident edges, and over each merged configuration
the agreeing pairs form a product of the free interior bonds. -/

/-- The bond-dimension product over the edges not crossing the boundary of `R`:
the overcounting multiplicity of the boundary-agreement double sum relative to the
closed state coefficient. -/
noncomputable def regionInteriorBondProd (A : Tensor G d) (R : Finset V) : ℕ :=
  ∏ e ∈ Finset.univ.filter (fun e : Edge G => ¬ ManyBody.IsRegionBoundaryEdge (G := G) R e),
    A.bondDim e

/-! ### The cardinality collapse to the closed state coefficient

Over each merged configuration `η` the agreeing pairs of an `η`-fiber are
parameterized by the free virtual indices on the edges not crossing the boundary
of `R`: an agreeing pair is determined on the boundary-crossing edges and on the
region-incident edges by `η`, leaving free the complement values on the
region-interior edges and the region values on the edges away from `R`. The
common count of these free indices is the bond-dimension product
`regionInteriorBondProd`, so the boundary-agreement double sum is that product
times the closed state coefficient. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge not incident to `R` does not cross the boundary of `R`: a
boundary-crossing edge touches `R`. -/
theorem not_boundary_of_not_incident (R : Finset V) {e : Edge G}
    (h : ¬ ManyBody.IsRegionIncidentEdge (G := G) R e) : ¬ ManyBody.IsRegionBoundaryEdge
      (G := G) R e :=
  fun hb => h (ManyBody.isRegionBoundaryEdge_touches (G := G) R hb)

omit [Fintype V] [DecidableRel G.Adj] in
/-- An edge crossing the boundary of `R` is incident to `R`. -/
theorem incident_of_boundary (R : Finset V) {e : Edge G}
    (h : ManyBody.IsRegionBoundaryEdge (G := G) R e) : ManyBody.IsRegionIncidentEdge (G := G) R e :=
  ManyBody.isRegionBoundaryEdge_touches (G := G) R h

/-- The free virtual indices of an agreeing pair: on a region-incident interior
edge the complement value, on an edge away from `R` the region value. These are
the indices left free once the merged configuration and the boundary agreement
are fixed. -/
def regionFiberLegs (A : Tensor G d) (R : Finset V)
    (p : VirtualConfig A × VirtualConfig A) :
    (e : {e : Edge G // ¬ ManyBody.IsRegionBoundaryEdge (G := G) R e}) → Fin (A.bondDim e.1) :=
  fun e => if ManyBody.IsRegionIncidentEdge (G := G) R e.1 then p.2 e.1 else p.1 e.1

/-- Reconstruct an agreeing pair in the `η`-fiber from its free virtual indices:
the region-incident edges read `η`, the edges away from `R` read the free indices
in the first configuration, and the region-interior edges read them in the
second. -/
noncomputable def regionFiberPair (A : Tensor G d) (R : Finset V) (η : VirtualConfig A)
    (h : (e : {e : Edge G // ¬ ManyBody.IsRegionBoundaryEdge (G := G) R e}) → Fin (A.bondDim e.1)) :
    VirtualConfig A × VirtualConfig A :=
  (fun e => if hinc : ManyBody.IsRegionIncidentEdge (G := G) R e then η e
              else h ⟨e, not_boundary_of_not_incident (G := G) R hinc⟩,
   fun e => if hb : ManyBody.IsRegionBoundaryEdge (G := G) R e then η e
              else if _hinc : ManyBody.IsRegionIncidentEdge (G := G) R e then h ⟨e, hb⟩
              else η e)

open scoped Classical in
/-- The `η`-fiber of the boundary-agreeing pairs under `regionMerge` has
cardinality `regionInteriorBondProd A R`: the free virtual indices on the
non-boundary edges biject with the fiber. -/
theorem regionFiber_card (A : Tensor G d) (R : Finset V) (η : VirtualConfig A) :
    (Finset.univ.filter (fun p : VirtualConfig A × VirtualConfig A =>
        (regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2)
          ∧ regionMerge (G := G) A R p = η)).card =
      regionInteriorBondProd (G := G) A R := by
  classical
  rw [show regionInteriorBondProd (G := G) A R =
      (Finset.univ : Finset ((e : {e : Edge G // ¬ ManyBody.IsRegionBoundaryEdge (G := G) R e})
        → Fin (A.bondDim e.1))).card from ?_]
  · refine Finset.card_nbij'
      (regionFiberLegs (G := G) A R) (regionFiberPair (G := G) A R η) ?_ ?_ ?_ ?_
    · -- The free indices land in the full configuration set.
      intro p _; exact Finset.mem_univ _
    · -- The reconstruction lands in the `η`-fiber of agreeing pairs.
      intro h _
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨?_, ?_⟩
      · -- The reconstructed pair agrees on every boundary edge.
        funext f
        simp only [regionBoundaryLabel_apply, regionFiberPair]
        rw [dite_eq_left (incident_of_boundary (G := G) R f.2), dite_eq_left f.2]
      · -- The reconstructed pair merges back to `η`.
        funext e
        by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) R e
        · rw [regionMerge_of_incident (G := G) A R _ hinc]
          simp [regionFiberPair, hinc]
        · rw [regionMerge_of_not_incident (G := G) A R _ hinc]
          simp [regionFiberPair, hinc, not_boundary_of_not_incident (G := G) R hinc]
    · -- Reconstructing from the free indices of a fiber pair recovers the pair.
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨hagree, hmerge⟩ := hp
      have hagree' : ∀ f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f},
          p.1 f.1 = p.2 f.1 := fun f => congrFun hagree f
      have hmerge' : ∀ e : Edge G, regionMerge (G := G) A R p e = η e :=
        fun e => congrFun hmerge e
      refine Prod.ext ?_ ?_
      · -- First configuration.
        funext e
        simp only [regionFiberPair, regionFiberLegs]
        by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) R e
        · rw [dite_eq_left hinc]
          have := hmerge' e
          rw [regionMerge_of_incident (G := G) A R p hinc] at this
          exact this.symm
        · rw [dite_eq_right hinc, ite_eq_right hinc]
      · -- Second configuration.
        funext e
        simp only [regionFiberPair, regionFiberLegs]
        by_cases hb : ManyBody.IsRegionBoundaryEdge (G := G) R e
        · rw [dite_eq_left hb]
          -- On a boundary edge the agreement and the merge identity force `p.2 e = η e`.
          have hinc := incident_of_boundary (G := G) R hb
          have h1 := hmerge' e
          rw [regionMerge_of_incident (G := G) A R p hinc] at h1
          have h2 := hagree' ⟨e, hb⟩
          rw [← h1, h2]
        · rw [dite_eq_right hb]
          by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) R e
          · rw [dite_eq_left hinc, ite_eq_left hinc]
          · rw [dite_eq_right hinc]
            have := hmerge' e
            rw [regionMerge_of_not_incident (G := G) A R p hinc] at this
            exact this.symm
    · -- Reading the free indices of a reconstruction recovers them.
      intro h _
      funext e
      simp only [regionFiberLegs, regionFiberPair]
      by_cases hinc : ManyBody.IsRegionIncidentEdge (G := G) R e.1
      · rw [ite_eq_left hinc, dite_eq_right e.2, dite_eq_left hinc]
      · rw [ite_eq_right hinc, dite_eq_right hinc]
  · -- The free-index configuration set has the bond-dimension product as its size.
    rw [Finset.card_univ, Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [regionInteriorBondProd,
      ← Finset.prod_subtype (Finset.univ.filter
          (fun e : Edge G => ¬ ManyBody.IsRegionBoundaryEdge (G := G) R e))
        (fun e => by simp [Finset.mem_filter]) (fun e => A.bondDim e)]

open scoped Classical in
/-- The merged summand at a global virtual configuration `η`: the region vertex
product against the complement vertex product, both read from `η`. -/
noncomputable def regionMergedSummand (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
    (η : VirtualConfig A) : ℂ :=
  (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => η ie.1) (σ w)) *
    ∏ w : {w : V // w ∈ Finset.univ \ R}, A.component w.1 (fun ie => η ie.1) (τ w)

open scoped Classical in
/-- The sum of the merged summands over all global virtual configurations is the
closed state coefficient of the assembled physical configuration, by the
region/complement split of the global vertex product. -/
theorem sum_regionMergedSummand (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ η : VirtualConfig A, regionMergedSummand (G := G) A R σ τ η) =
      stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  unfold stateCoeff regionMergedSummand
  refine Finset.sum_congr rfl (fun η _ => ?_)
  exact (prod_assembleRegionσ_split (G := G) A R σ τ η).symm

open scoped Classical in
/-- **Cardinality collapse of the boundary-agreement double sum.** The
boundary-agreement double sum of the region vertex product against the complement
vertex product collapses to the bond-dimension product over the edges not
crossing the boundary of `R`, times the closed state coefficient of the assembled
physical configuration. This is the multiplicity collapse promised by the
double-global-sum form `regionInsertedCoeff_identity_eq_doubleSum`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem stateCoeff_eq_regionComplement (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  -- Read each agreeing summand through the merged configuration.
  rw [show (∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
      (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
        ∏ w : {w : V // w ∈ Finset.univ \ R},
          A.component w.1 (fun ie => p.2 ie.1) (τ w)) =
      ∑ p ∈ Finset.univ.filter
        (fun p : VirtualConfig A × VirtualConfig A =>
          regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
        regionMergedSummand (G := G) A R σ τ (regionMerge (G := G) A R p) from ?_]
  · -- Group the agreeing pairs by their merged configuration.
    rw [← sum_regionMergedSummand (G := G) A R σ τ]
    apply sum_comp_of_config_fiber_card
    intro η
    simpa only [Finset.filter_filter, Finset.mem_univ, true_and] using
      regionFiber_card (G := G) A R η
  · -- Each agreeing summand is the merged summand at the merged configuration.
    refine Finset.sum_congr rfl (fun p hp => ?_)
    rw [Finset.mem_filter] at hp
    rw [regionMergedSummand, regionProd_eq_merge (G := G) A R σ p,
      complementProd_eq_merge (G := G) A R τ p hp.2]

/-! ### The blocked-region-weight contraction of the closed state coefficient

Contracting the blocked-region weight on `R` against the blocked-region weight on
`univ \ R`, summed over the boundary configuration, reads the interior bond
multiple of the closed state coefficient. It does not single out a boundary edge,
so it applies to a region with no boundary edge as well. -/

open scoped Classical in
/-- The boundary-configuration contraction of the region weight against the
complement weight reads the interior bond multiple of the closed state
coefficient. This is the edge-free identity-insertion reading: it follows from the
double-global-configuration form of the closed-state split
(`stateCoeff_eq_regionComplement`) after expanding both weights. -/
theorem sum_regionBlockedWeight_mul_complement (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    (∑ μ : RegionBoundaryConfig (G := G) A R,
        regionBlockedWeight (G := G) A R μ σ *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R μ) τ) =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  classical
  rw [← stateCoeff_eq_regionComplement (G := G) A R σ τ]
  -- Expand both blocked-region weights as filtered sums over global configurations.
  simp only [regionBlockedWeight]
  -- Distribute the products of filtered sums and reorganize into the
  -- boundary-agreement pair sum, mirroring `regionInsertedCoeff_identity_eq_doubleSum`.
  rw [show (∑ μ : RegionBoundaryConfig (G := G) A R,
        (∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A =>
              regionBoundaryLabel (G := G) A (Finset.univ \ R) ξ =
                regionComplementBoundaryConfig (G := G) A R μ),
            ∏ w : {w : V // w ∈ Finset.univ \ R},
              A.component w.1 (fun ie => ξ ie.1) (τ w)) =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        ∑ ζ ∈ Finset.univ.filter
            (fun ζ : VirtualConfig A => regionBoundaryLabel (G := G) A R ζ = μ),
          ∑ ξ ∈ Finset.univ.filter
            (fun ξ : VirtualConfig A => regionBoundaryLabel (G := G) A R ξ = μ),
            (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) *
              ∏ w : {w : V // w ∈ Finset.univ \ R},
                A.component w.1 (fun ie => ξ ie.1) (τ w) from ?_]
  · -- Reindex the triple sum (μ, ζ, ξ) onto the boundary-agreement pair sum.
    simp only [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    rw [Finset.sum_eq_single (regionBoundaryLabel (G := G) A R ζ)]
    · rw [ite_eq_left rfl]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases heq : regionBoundaryLabel (G := G) A R ζ = regionBoundaryLabel (G := G) A R ξ
      · rw [ite_eq_left heq.symm, ite_eq_left heq]
      · rw [ite_eq_right (fun h => heq h.symm), ite_eq_right heq]
    · intro μ _ hμ
      rw [ite_eq_right (fun h => hμ h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- The complement filter matches the region filter after the boundary-edge
    -- identification, and the product of sums is the doubled sum.
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    refine Finset.sum_congr ?_ (fun ξ _ => rfl)
    ext ξ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ

/-- The interior bond product is positive when every bond dimension is positive. -/
theorem regionInteriorBondProd_pos (A : Tensor G d) (R : Finset V)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e) :
    0 < regionInteriorBondProd (G := G) A R := by
  rw [regionInteriorBondProd]
  exact Finset.prod_pos (fun e _ => hposA e)

end RegionComplement

end PEPS
end TNLean
