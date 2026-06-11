import TNLean.PEPS.RegionBlock.InsertSplit

/-!
# Grouping the inserted-site blocked weight by the local configuration at `v`

The blocked-region weight of `insert v R` splits, at a fixed local configuration
`η` of the inserted site `v`, into the inserted-site tensor `A.component v η`
times the residual sum over the vertices of `R` constrained to `η` at `v` and to
`μ` on the crossing edges of `insert v R`
(arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`).

This file lifts the vertex-product split `prod_region_insert_split` and the
constrained-sum split `regionBlockedWeight_insert_eq_sum_split` to the
local-configuration grouping at `v`: grouping the constrained global sum by the
local virtual configuration `η` at the inserted site, the inserted-site tensor
factor `A.component v η (σ_v)` is constant on each `η`-fiber, so the blocked
weight of `insert v R` is the sum over `η` of `A.component v η (σ_v)` against the
residual region-vertex product. This is the inserted-site grouping that the
residual-multiplicity factorization rests on: it isolates `A.component v` from
the residual exactly as the route note's per-vertex relation requires.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1544--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- The residual region-vertex sum at a fixed local configuration `η` of the
inserted site `v`: the sum, over global virtual configurations restricting to `μ`
on the crossing edges of `insert v R` and to `η` at `v`, of the vertex product
over the smaller region `R`.

This is the residual of the inserted-site quotient: it carries the bond data of
`R` together with the `v`-incident consistency constraint between `μ` and `η`. -/
noncomputable def insertResidual (A : Tensor G d) (R : Finset V) {v : V}
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R))
    (η : LocalVirtualConfig A v) : ℂ :=
  ∑ ζ ∈ Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (insert v R) ζ = μ ∧
          (fun ie : IncidentEdge G v => ζ ie.1) = η),
    ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
      (restrictInsertPhysical (V := V) (d := d) R σ w)

open scoped Classical in
/-- **The inserted-site blocked weight groups by the local configuration at `v`.**

The blocked weight of `insert v R` is the sum, over local virtual configurations
`η` of the inserted site `v`, of the inserted-site tensor `A.component v η` read
at `σ`'s physical leg at `v` times the residual region-vertex sum `insertResidual`
at `η`.

The inserted-site tensor factor is constant on each `η`-fiber of the constrained
global sum, so factoring it out of `regionBlockedWeight_insert_eq_sum_split` and
grouping by `η` gives the inserted-site grouping.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1544--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionBlockedWeight_insert_eq_sum_localConfig (A : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R)) :
    regionBlockedWeight (G := G) A (insert v R) μ σ =
      ∑ η : LocalVirtualConfig A v,
        A.component v η (σ ⟨v, Finset.mem_insert_self v R⟩) *
          insertResidual (G := G) A R μ σ η := by
  classical
  rw [regionBlockedWeight_insert_eq_sum_split (G := G) A R hv μ σ]
  -- Group the constrained global sum by the local configuration `η` at `v`.
  rw [← Finset.sum_fiberwise (Finset.univ.filter
      (fun ζ : VirtualConfig A =>
        regionBoundaryLabel (G := G) A (insert v R) ζ = μ))
    (fun ζ => (fun ie : IncidentEdge G v => ζ ie.1))
    (fun ζ =>
      A.component v (fun ie => ζ ie.1) (σ ⟨v, Finset.mem_insert_self v R⟩) *
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (restrictInsertPhysical (V := V) (d := d) R σ w))]
  refine Finset.sum_congr rfl (fun η _ => ?_)
  -- On the `η`-fiber the inserted-site tensor factor is constant `A.component v η (σ_v)`.
  rw [insertResidual, Finset.mul_sum, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr (fun ζ _ => by tauto)) (fun ζ hζ => ?_)
  rw [Finset.mem_filter] at hζ
  obtain ⟨_, _, hηζ⟩ := hζ
  rw [hηζ]

/-! ### The `v`-incident consistency delta

An edge incident to the inserted site `v` that crosses the boundary of `insert v R`
runs from `v` to a vertex outside `insert v R`; it is constrained both by `μ` (as a
crossing edge of `insert v R`) and by `η` (as a `v`-incident edge), so the residual
sum is empty --- hence zero --- whenever `μ` and `η` disagree on such an edge. This
is the consistency delta the inserted-site quotient carries: only the local
configurations `η` at `v` that match `μ` on the outer `v`-incident edges contribute. -/

/-- A `v`-incident edge `g` that crosses the boundary of `insert v R` is constrained
by both `μ` (its crossing-edge label) and `η` (its `v`-incident label) in the
residual filter, so if `μ` and `η` disagree on `g` the residual sum is zero. -/
theorem insertResidual_eq_zero_of_inconsistent (A : Tensor G d) (R : Finset V)
    {v : V} (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R))
    (η : LocalVirtualConfig A v)
    (g : {g : Edge G // IsRegionBoundaryEdge (G := G) (insert v R) g})
    (hgv : g.1.1.1 = v ∨ g.1.1.2 = v)
    (hne : μ g ≠ η ⟨g.1, hgv⟩) :
    insertResidual (G := G) A R μ σ η = 0 := by
  classical
  rw [insertResidual]
  refine Finset.sum_eq_zero (fun ζ hζ => ?_)
  exfalso
  rw [Finset.mem_filter] at hζ
  obtain ⟨_, hμ, hη⟩ := hζ
  apply hne
  -- `μ g = ζ g.1` from the crossing-edge label, `η ⟨g.1, hgv⟩ = ζ g.1` from the `v`-incident label.
  have h1 : μ g = ζ g.1 := by rw [← hμ, regionBoundaryLabel_apply]
  have h2 : η ⟨g.1, hgv⟩ = ζ g.1 := by rw [← hη]
  rw [h1, h2]

/-! ### The residual is a refinement of the smaller-region blocked weight

Every global virtual configuration in the residual filter restricts to the bridge
label `boundaryLabelOfInsert μ η` on the crossing edges of `R`
(`regionBoundaryLabel_eq_boundaryLabelOfInsert`), so the residual sum is the
sub-sum of the blocked weight of `R` at the bridge label over the configurations
that additionally restrict to `μ` on the crossing edges of `insert v R` and to `η`
at `v`.  This refinement is the bond-data identity the route note records: the
residual carries the bond data of `R` constrained by the inserted site, and the
free `insert v R`-boundary and `v`-incident edges away from `R` supply the
overcounting multiplicity that is identical for `A` and the reindexed comparison
tensor. -/

/-- The residual sum is the blocked weight of `R` at the bridge label
`boundaryLabelOfInsert μ η`, restricted to the configurations restricting to `μ`
on the crossing edges of `insert v R` and to `η` at `v`.

Concretely, the residual filter refines the blocked-weight filter at the bridge
label: every residual configuration carries `R`-boundary label
`boundaryLabelOfInsert μ η` by `regionBoundaryLabel_eq_boundaryLabelOfInsert`, and
the residual product is exactly the blocked-weight summand. -/
theorem insertResidual_eq_filter_regionBlockedWeight (A : Tensor G d) (R : Finset V)
    {v : V} (hv : v ∉ R)
    (μ : RegionBoundaryConfig (G := G) A (insert v R))
    (σ : RegionPhysicalConfig (V := V) (d := d) (insert v R))
    (η : LocalVirtualConfig A v) :
    insertResidual (G := G) A R μ σ η =
      ∑ ζ ∈ Finset.univ.filter
          (fun ζ : VirtualConfig A =>
            regionBoundaryLabel (G := G) A R ζ = boundaryLabelOfInsert (G := G) A R hv μ η ∧
              regionBoundaryLabel (G := G) A (insert v R) ζ = μ ∧
              (fun ie : IncidentEdge G v => ζ ie.1) = η),
        ∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => ζ ie.1)
          (restrictInsertPhysical (V := V) (d := d) R σ w) := by
  classical
  rw [insertResidual]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext ζ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hμ, hη⟩
    exact ⟨regionBoundaryLabel_eq_boundaryLabelOfInsert (G := G) A R hv ζ μ η hμ hη, hμ, hη⟩
  · rintro ⟨_, hμ, hη⟩
    exact ⟨hμ, hη⟩

end PEPS
end TNLean
