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
