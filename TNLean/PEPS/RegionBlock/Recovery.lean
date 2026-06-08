import TNLean.PEPS.RegionBlock.Algebra
import TNLean.PEPS.NormalFundamentalTheorem

/-!
# Region realization and the region insertion transfer

This file builds the region analogue of the physical-to-virtual recovery
`physical_to_virtual_insertion`, supplying the data of a `RegionInsertionTransfer`
on a boundary edge of an arbitrary finite region `R`.

The edge-level recovery of `TNLean.PEPS.InsertionAlgebra` realizes a matrix
insertion on the chosen bond as a physical operator at one endpoint vertex,
transfers it to the second tensor across `SameState`, and reads the matrix back
off. The region analogue realizes the matrix insertion at the single in-region
endpoint vertex of the boundary edge `f`, which is the one endpoint of `f` lying
in `R`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `inj_isomorph`, lines 254--582 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

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
    simpa [regionBoundaryLabel, regionComplementBoundaryConfig, regionBoundaryEdgeToCompl,
      regionBoundaryEdgeComplEquiv, Equiv.subtypeEquivRight] using hh
  · intro h
    funext f
    simp only [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
    have hh := congrFun h ((regionBoundaryEdgeComplEquiv (G := G) R).symm f)
    rw [regionBoundaryLabel_apply] at hh
    exact hh

/-! ### The boundary-agreement form of the identity region insertion

Summing the product of the blocked-region weight on `R` against the blocked-region
weight on `univ \ R` over the boundary configuration collapses the two boundary
filters into a single constraint: the two global virtual configurations agree on
every edge crossing the boundary of `R`. This is the double-global-sum form of
`regionInsertedCoeff_identity`, the starting point for the multiplicity collapse
to the closed state coefficient. -/

open scoped Classical in
/-- The identity-inserted region coefficient, in its double-global-configuration
form: a sum over pairs of global virtual configurations agreeing on the boundary
of `R`, of the region vertex product against the complement vertex product. -/
theorem regionInsertedCoeff_identity_eq_doubleSum (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f
        (1 : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) σ τ =
      ∑ p ∈ Finset.univ.filter
          (fun p : VirtualConfig A × VirtualConfig A =>
            regionBoundaryLabel (G := G) A R p.1 = regionBoundaryLabel (G := G) A R p.2),
        (∏ w : {w : V // w ∈ R}, A.component w.1 (fun ie => p.1 ie.1) (σ w)) *
          ∏ w : {w : V // w ∈ Finset.univ \ R},
            A.component w.1 (fun ie => p.2 ie.1) (τ w) := by
  classical
  rw [regionInsertedCoeff_identity]
  -- Expand each blocked-region weight as a filtered sum over global configurations.
  simp only [regionBlockedWeight]
  -- Distribute the products of filtered sums and identify the combined filter.
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
    · rw [if_pos rfl]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases heq : regionBoundaryLabel (G := G) A R ζ = regionBoundaryLabel (G := G) A R ξ
      · rw [if_pos heq.symm, if_pos heq]
      · rw [if_neg (fun h => heq h.symm), if_neg heq]
    · intro μ _ hμ
      rw [if_neg (fun h => hμ h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- The complement filter matches the region filter after the boundary-edge bridge,
    -- and the product of sums is the doubled sum.
    refine Finset.sum_congr rfl (fun μ _ => ?_)
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun ζ _ => ?_)
    refine Finset.sum_nbij' id id ?_ ?_ (fun _ _ => rfl) (fun _ _ => rfl) (fun ξ hξ => rfl)
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ).mp hξ
    · intro ξ hξ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hξ ⊢
      exact (regionBoundaryLabel_compl_eq_iff (G := G) A R μ ξ).mpr hξ

end PEPS
end TNLean
