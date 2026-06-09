import TNLean.PEPS.RegionBlock.Recovery6

/-!
# Block-level image coincidence for the normal PEPS Fundamental Theorem

This file proves the **block-level image coincidence** lemma: under `SameState`,
the range of the blocked-region tensor map of a region `R` is the same for two
tensors `A` and `B`, provided the *complement* block `univ \ R` of each tensor is
blocked-tensor injective and the bond dimensions are positive and equal.

This is the block-granularity analogue of the vertex-level image coincidence
`range_localTensorMap_eq_of_sameState` of `TNLean.PEPS.RegionBlock.Recovery3`. The
vertex frame is too weak for the general normal theorem because a single vertex
need not be injective; the *block* `R` is the object that is injective in the
normal setting, so the image coincidence must hold at block granularity.

## The Schmidt-span argument

Both ranges equal the column space of the global state across the `R` / complement
cut, which is `SameState`-invariant. Concretely, both ranges equal the span of the
**partial states**

> `regionPartialState A R τ := fun σ => stateCoeff A (assembleRegionσ R σ τ)`

as the complement physical configuration `τ` ranges. The proof mirrors the
vertex-level proof of `TNLean.PEPS.RegionBlock.Recovery3` at block granularity:

* The range of the blocked-region tensor map is the span of the blocked-region
  weights (`Fintype.range_linearCombination`).
* Each partial state is, up to the nonzero interior bond multiplicity, a
  blocked-region-weight combination of `A` over `R` (the identity-insertion
  reading of the closed state coefficient), so the partial states lie in the span
  of the blocked-region weights.
* Conversely, blocked-tensor injectivity of the complement
  (`RegionBlockedTensorInjective A (univ \ R)`) makes the complement weight family
  linearly independent, so by `span_cols_eq_top_of_linearIndependent` its columns
  span; this realizes every blocked-region weight as a partial-state combination.
* The partial states depend only on `stateCoeff`, so they are `SameState`-invariant.

Combining these gives
`range (regionBlockedTensorMap A R) = span τ {regionPartialState A R τ}
  = span τ {regionPartialState B R τ} = range (regionBlockedTensorMap B R)`,
the block analogue of `range_localTensorMap_eq_of_sameState`.

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

/-! ### The partial states across the region cut

The partial state at a complement physical configuration `τ` is the closed state
coefficient of the assembled global configuration, read as a function of the
region physical configuration `σ`. It is the column of the global state vector
across the `R` / complement cut at the fixed complement configuration `τ`. -/

/-- The partial state across the region cut at a complement physical
configuration `τ`: the closed state coefficient of `assembleRegionσ R σ τ`, viewed
as a function of the region physical configuration `σ`. This is a column of the
global state vector across the `R` / complement cut. -/
noncomputable def regionPartialState (A : Tensor G d) (R : Finset V)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    RegionPhysicalConfig (V := V) (d := d) R → ℂ :=
  fun σ => stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ)

/-- The partial state depends on the tensor only through its closed state
coefficient, so it is invariant under `SameState`. -/
theorem regionPartialState_sameState {A B : Tensor G d} (hAB : SameState A B)
    (R : Finset V) (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionPartialState (G := G) A R τ = regionPartialState (G := G) B R τ := by
  funext σ
  rw [regionPartialState, regionPartialState, hAB]

/-! ### The blocked-region-weight contraction of the closed state coefficient

Contracting the blocked-region weight on `R` against the blocked-region weight on
`univ \ R`, summed over the boundary configuration, reads the interior bond
multiple of the closed state coefficient. This is the edge-free form of the
identity-insertion reading `regionInsertedCoeff_one_eq_stateCoeff`: it does not
single out a boundary edge, so it applies to a region with no boundary edge as
well. -/

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
    · rw [if_pos rfl]
      refine Finset.sum_congr rfl (fun ξ _ => ?_)
      by_cases heq : regionBoundaryLabel (G := G) A R ζ = regionBoundaryLabel (G := G) A R ξ
      · rw [if_pos heq.symm, if_pos heq]
      · rw [if_neg (fun h => heq h.symm), if_neg heq]
    · intro μ _ hμ
      rw [if_neg (fun h => hμ h.symm)]
    · intro h; exact absurd (Finset.mem_univ _) h
  · -- The complement filter matches the region filter after the boundary-edge
    -- identification, and the product of sums is the doubled sum.
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
