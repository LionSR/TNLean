import TNLean.PEPS.RegionBlock.Basic

/-!
# Splitting the region vertex product across an inserted site

For a region `R` and a vertex `v ∉ R`, the inserted region `insert v R` carries
one extra physical site. This file isolates the single algebraic step that the
block-granularity one-site quotient of the normal PEPS Fundamental Theorem rests
on (arXiv:1804.04964, Section 3, proof of Theorem 3, the comparison of the
one-site-different regions `R` and `S`, lines 1407--1443 and 1544 of
`Papers/1804.04964/paper_normal.tex`): the product of the tensors over the
vertices of `insert v R` factors as the tensor at the inserted site `v` times the
product of the tensors over the vertices of `R`.

The blocked-region weight of `insert v R` is a constrained sum of this vertex
product over global virtual configurations. The split below is therefore the
vertex-product half of the one-site quotient: it isolates `A.component v` from the
remaining region product, the residual being exactly the vertex product of the
smaller region `R`. The full quotient still needs the boundary-configuration
bookkeeping relating the crossing edges of `insert v R` to those of `R` together
with the bonds incident to `v`; that bookkeeping is recorded as the remaining
obstruction of the per-vertex relation in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1407--1544 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The equivalence between the vertices of `R` and the non-`v` vertices of
`insert v R`, for `v ∉ R`. -/
noncomputable def insertVertexComplEquiv (R : Finset V) {v : V} (hv : v ∉ R) :
    {w : V // w ∈ R} ≃
      {w : {x : V // x ∈ insert v R} //
        w ∈ ({⟨v, Finset.mem_insert_self v R⟩} : Finset {x : V // x ∈ insert v R})ᶜ} where
  toFun w := ⟨⟨w.1, Finset.mem_insert_of_mem w.2⟩, by
    simp only [Finset.mem_compl, Finset.mem_singleton]
    intro hc
    have : w.1 = v := congrArg Subtype.val hc
    exact hv (this ▸ w.2)⟩
  invFun w := ⟨w.1.1, by
    have hne : w.1.1 ≠ v := by
      intro hc
      have : w.1 = ⟨v, Finset.mem_insert_self v R⟩ := Subtype.ext hc
      exact (Finset.mem_compl.mp w.2) (Finset.mem_singleton.mpr this)
    rcases Finset.mem_insert.mp w.1.2 with h | h
    · exact absurd h hne
    · exact h⟩
  left_inv w := rfl
  right_inv w := by ext; rfl

/-- The physical configuration on a region `R`, obtained by restricting a physical
configuration on the inserted region `insert v R`. -/
noncomputable def restrictInsertPhysical (R : Finset V) {v : V}
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => σ ⟨w.1, Finset.mem_insert_of_mem w.2⟩

omit [Fintype V] in
/-- **The region vertex product splits across the inserted site.**

For a vertex `v ∉ R`, the product of the tensors `A.component w` over the
vertices of `insert v R`, at a fixed global virtual configuration `ζ` and a
physical configuration `σ` on `insert v R`, equals the tensor at the inserted site
`v` (read at `ζ`'s local configuration at `v` and the physical leg `σ` assigns to
`v`) times the product over the vertices of `R` of the same tensors, with the
physical legs restricted to `R`.

This is the vertex-product half of the block-granularity one-site quotient: the
inserted site `v` is isolated from the residual region product, which is exactly
the vertex product of `R`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem prod_region_insert_split (A : Tensor G d) (R : Finset V) {v : V} (hv : v ∉ R)
    (ζ : VirtualConfig A)
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    (∏ w : {w : V // w ∈ insert v R}, A.component w.1 (fun ie => ζ ie.1) (σ w)) =
      A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_insert_self v R⟩) *
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (restrictInsertPhysical (V := V) (d := d) R σ w) := by
  classical
  -- Factor the inserted site `v` out of the product over `insert v R`.
  rw [Fintype.prod_eq_mul_prod_compl
      (⟨v, Finset.mem_insert_self v R⟩ : {w : V // w ∈ insert v R})
      (fun w : {w : V // w ∈ insert v R} => A.component w.1 (fun ie => ζ ie.1) (σ w))]
  congr 1
  -- Read the residual product over the complement finset as a product over its coe-sort,
  -- then reindex it through the vertices of `R`.
  rw [← Finset.prod_coe_sort
      (({⟨v, Finset.mem_insert_self v R⟩} : Finset {x : V // x ∈ insert v R})ᶜ)
      (fun w : {x : V // x ∈ insert v R} => A.component w.1 (fun ie => ζ ie.1) (σ w))]
  rw [← Equiv.prod_comp (insertVertexComplEquiv (V := V) R hv)
      (fun w => A.component w.1.1 (fun ie => ζ ie.1) (σ w.1))]
  rfl

/-- **The blocked-region weight of an inserted region splits at the inserted
site.**

For a vertex `v ∉ R`, the blocked-region weight of `insert v R` is the constrained
sum, over global virtual configurations restricting to `μ` on the crossing edges
of `insert v R`, of the tensor at the inserted site `v` times the vertex product
over `R`. This lifts `prod_region_insert_split` to the constrained
blocked-weight sum.

The remaining content of the one-site quotient is the boundary-configuration
bookkeeping that reads the `μ`-constraint and the local configuration at `v`
through `R`'s own crossing edges, identifying the residual vertex product as a
blocked-region weight of `R`; that bookkeeping is recorded as the remaining
obstruction in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_insert_eq_sum_split (A : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    regionBlockedWeight (G := G) A (insert v R) μ σ =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A (insert v R) ζ = μ),
        A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_insert_self v R⟩) *
          ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
            (restrictInsertPhysical (V := V) (d := d) R σ w) := by
  classical
  rw [regionBlockedWeight]
  refine Finset.sum_congr rfl (fun ζ _ => ?_)
  exact prod_region_insert_split (G := G) A R hv ζ σ

/-! ### The boundary-configuration bridge across an inserted site

The crossing edges of `R` and of `insert v R` differ only at the edges incident
to the inserted site `v`.  An `R`-boundary edge not incident to `v` is also an
`insert v R`-boundary edge, and one incident to `v` becomes internal to
`insert v R` while remaining an edge incident to `v`.  The boundary label of `R`
is therefore read off the boundary label of `insert v R` away from `v` and the
local virtual configuration at `v` on the edges incident to `v`. -/

omit [Fintype V] [DecidableRel G.Adj] in
/-- An `R`-boundary edge not incident to the inserted site `v` is an
`insert v R`-boundary edge. -/
theorem isRegionBoundaryEdge_insert_of_not_incident (R : Finset V) {v : V} (hv : v ∉ R)
    {g : Edge G} (hg : IsRegionBoundaryEdge (G := G) R g)
    (hgv : g.1.1 ≠ v ∧ g.1.2 ≠ v) :
    IsRegionBoundaryEdge (G := G) (insert v R) g := by
  obtain ⟨hgv1, hgv2⟩ := hgv
  rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine Or.inl ⟨Finset.mem_insert_of_mem h1, ?_⟩
    rw [Finset.mem_insert]
    rintro (rfl | hc)
    · exact hgv2 rfl
    · exact h2 hc
  · refine Or.inr ⟨?_, Finset.mem_insert_of_mem h2⟩
    rw [Finset.mem_insert]
    rintro (rfl | hc)
    · exact hgv1 rfl
    · exact h1 hc

/-- The crossing-edge label of `R` read off the crossing-edge label of
`insert v R` and the local virtual configuration at the inserted site `v`.

An `R`-boundary edge incident to `v` becomes internal to `insert v R`; its label
is read from the local configuration `η` at `v`.  An `R`-boundary edge not
incident to `v` is also an `insert v R`-boundary edge; its label is read from `μ`.

The label values agree as elements of `Fin (A.bondDim g.1)` because every edge of
`G` carries a single bond dimension regardless of which region it bounds. -/
noncomputable def boundaryLabelOfInsert (A : Tensor G d) (R : Finset V) {v : V} (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (η : LocalVirtualConfig A v) :
    RegionBoundaryConfig (G := G) A R :=
  fun g =>
    if hgv : g.1.1.1 = v ∨ g.1.1.2 = v then
      η ⟨g.1, hgv⟩
    else
      μ ⟨g.1, isRegionBoundaryEdge_insert_of_not_incident (G := G) R hv g.2
        ⟨fun h => hgv (Or.inl h), fun h => hgv (Or.inr h)⟩⟩

omit [Fintype V] in
/-- **The boundary-label fiber identity across an inserted site.**

For a global virtual configuration `ζ` restricting to `μ` on the crossing edges of
`insert v R` and to `η` at the inserted site `v`, the crossing-edge label of `R`
read from `ζ` is exactly the bridge label `boundaryLabelOfInsert μ η`.

This is the boundary-configuration half of the block-granularity one-site
quotient: it folds the `insert v R` boundary label and the local configuration at
`v` into the boundary label of `R`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBoundaryLabel_eq_boundaryLabelOfInsert (A : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R) (ζ : VirtualConfig A)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (η : LocalVirtualConfig A v)
    (hμ : regionBoundaryLabel (G := G) A (insert v R) ζ = μ)
    (hη : (fun ie : IncidentEdge G v => ζ ie.1) = η) :
    regionBoundaryLabel (G := G) A R ζ =
      boundaryLabelOfInsert (G := G) A R hv μ η := by
  funext g
  rw [regionBoundaryLabel_apply, boundaryLabelOfInsert]
  by_cases hgv : g.1.1.1 = v ∨ g.1.1.2 = v
  · rw [dif_pos hgv]
    exact congrFun hη ⟨g.1, hgv⟩
  · rw [dif_neg hgv]
    have := congrFun hμ ⟨g.1, isRegionBoundaryEdge_insert_of_not_incident (G := G) R hv g.2
      ⟨fun h => hgv (Or.inl h), fun h => hgv (Or.inr h)⟩⟩
    rw [regionBoundaryLabel_apply] at this
    exact this

end PEPS
end TNLean
