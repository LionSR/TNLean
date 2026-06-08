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

end PEPS
end TNLean
