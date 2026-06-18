import TNLean.PEPS.RegionBlock.Recovery4

/-!
# Region physical-to-virtual recovery: the out-of-region endpoint of a boundary edge

This file develops the out-of-region endpoint of a boundary edge `f` of a region
`R`, the second endpoint feeding the region resonate step behind the normal PEPS
Fundamental Theorem (remaining obligation 4 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`).

A boundary edge `f` of `R` is also a boundary edge of the set complement
`univ \ R` (`regionBoundaryEdgeToCompl`), and its in-region endpoint with respect
to the complement is the out-of-region endpoint of `f` with respect to `R`. The
complement-side reading of the region-inserted coefficient
(`regionInsertedCoeff_eq_complementTwoBlock`, `TNLean.PEPS.RegionBlock.Recovery4`)
contracts the complement block first, so realizing the inserted coefficient
through the out-of-region endpoint is the complement-region instance of the
v-side realization `regionInsertedCoeff_eq_smul_op_regionStateVec`.

This file records the endpoint identity and the basic structural facts that the
complement-side realization needs, isolating the dependent-type reindexing
`univ \ (univ \ R) = R` into dedicated transport lemmas rather than threading it
through the realization argument.

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

/-! ### The out-of-region endpoint of a boundary edge

The out-of-region endpoint of a boundary edge `f` of `R` is the unique endpoint of
`f` lying outside `R`. It coincides with the in-region endpoint of `f` viewed as a
boundary edge of the set complement `univ \ R`. -/

/-- The out-of-region endpoint of a boundary edge `f` of `R`: the unique endpoint
of `f` not lying in `R`. -/
def regionBoundaryEdgeOutVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) : V :=
  if f.1.1.1 ∈ R then f.1.1.2 else f.1.1.1

omit [Fintype V] [DecidableRel G.Adj] in
/-- The out-of-region endpoint of a boundary edge does not lie in `R`. -/
theorem regionBoundaryEdgeOutVertex_not_mem (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeOutVertex (G := G) R f ∉ R := by
  unfold regionBoundaryEdgeOutVertex
  rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1]; exact h2
  · rw [if_neg h1]; exact h1

omit [DecidableRel G.Adj] in
/-- The out-of-region endpoint of a boundary edge lies in the set complement
`univ \ R`. -/
theorem regionBoundaryEdgeOutVertex_mem_compl (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeOutVertex (G := G) R f ∈ Finset.univ \ R := by
  rw [Finset.mem_sdiff]
  exact ⟨Finset.mem_univ _, regionBoundaryEdgeOutVertex_not_mem (G := G) R f⟩

omit [DecidableRel G.Adj] in
/-- The out-of-region endpoint of `f` is the in-region endpoint of `f` viewed as a
boundary edge of the set complement `univ \ R`.

The complement membership predicate `w ∈ univ \ R` is `w ∉ R`, so the conditional
defining the in-region endpoint of the complement boundary edge selects the
endpoint of `f` outside `R`, which is the out-of-region endpoint of `f`. -/
theorem regionBoundaryEdgeInVertex_compl_eq_outVertex (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) :
    regionBoundaryEdgeInVertex (G := G) (Finset.univ \ R)
        (regionBoundaryEdgeToCompl (G := G) R f) =
      regionBoundaryEdgeOutVertex (G := G) R f := by
  rw [regionBoundaryEdgeInVertex, regionBoundaryEdgeOutVertex,
    regionBoundaryEdgeToCompl]
  rcases f.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [if_pos h1, if_neg (by rw [Finset.mem_sdiff]; push Not; exact fun _ => h1)]
  · rw [if_neg h1, if_pos (by rw [Finset.mem_sdiff]; exact ⟨Finset.mem_univ _, h1⟩)]

/-! ### The blocked-region tensor map and its left inverse

The blocked-region weight family of a region `R` assembles into a linear map from
boundary-configuration coefficients to region physical functions
(`regionBlockedTensorMap`). Blocked-tensor injectivity of `R`
(`RegionBlockedTensorInjective`) is exactly injectivity of this map, so it has a
chosen left inverse (`regionBlockedLeftInverse`). This is the region analogue of
the blocked-middle contraction inverse `edgeMiddleLeftInverse`: where the edge
proof inverts the middle block to read off the recovered matrix, the region proof
inverts the blocked endpoint block of `R` (or its complement) for the same
purpose. The interior of the region/complement split is empty, so there is no
middle tensor to invert; the two endpoint blocks are exactly the region block and
the complement block, and inverting either is this left inverse. -/

/-- The blocked-region tensor map: the linear combination of the blocked-region
weight family of `R`, sending a boundary-configuration coefficient to the region
physical function it produces.

This is the region analogue of `edgeMiddleTensorMap`. Its injectivity is exactly
the blocked-tensor injectivity of `R`. -/
noncomputable def regionBlockedTensorMap (A : Tensor G d) (R : Finset V) :
    (RegionBoundaryConfig (G := G) A R → ℂ) →ₗ[ℂ]
      (RegionPhysicalConfig (V := V) (d := d) R → ℂ) :=
  Fintype.linearCombination ℂ (regionBlockedTensorFamily (G := G) A R)

/-- The blocked-region tensor map is injective when the region is blocked-tensor
injective. This is the region analogue of
`edgeMiddleTensorMap_injective_of_injective`. -/
theorem regionBlockedTensorMap_injective_of_injective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    Function.Injective (regionBlockedTensorMap (G := G) A R) :=
  hR.fintypeLinearCombination_injective

/-- Kernel form of `regionBlockedTensorMap_injective_of_injective`. -/
theorem regionBlockedTensorMap_ker_eq_bot_of_injective (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    LinearMap.ker (regionBlockedTensorMap (G := G) A R) = ⊥ :=
  LinearMap.ker_eq_bot.mpr <| regionBlockedTensorMap_injective_of_injective (G := G) A R hR

/-- A chosen left inverse of the blocked-region tensor map under blocked-tensor
injectivity. This is the region analogue of `edgeMiddleLeftInverse`, built the
same way from `LinearMap.exists_leftInverse_of_injective`. It is the
contraction-inverse of the blocked region block used in the region resonate step.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def regionBlockedLeftInverse (A : Tensor G d) (R : Finset V)
    (hR : RegionBlockedTensorInjective (G := G) A R) :
    (RegionPhysicalConfig (V := V) (d := d) R → ℂ) →ₗ[ℂ]
      (RegionBoundaryConfig (G := G) A R → ℂ) :=
  ((regionBlockedTensorMap (G := G) A R).exists_leftInverse_of_injective
    (regionBlockedTensorMap_ker_eq_bot_of_injective (G := G) A R hR)).choose

@[simp] theorem regionBlockedLeftInverse_comp_regionBlockedTensorMap (A : Tensor G d)
    (R : Finset V) (hR : RegionBlockedTensorInjective (G := G) A R) :
    (regionBlockedLeftInverse (G := G) A R hR).comp
        (regionBlockedTensorMap (G := G) A R) =
      LinearMap.id :=
  ((regionBlockedTensorMap (G := G) A R).exists_leftInverse_of_injective
    (regionBlockedTensorMap_ker_eq_bot_of_injective (G := G) A R hR)).choose_spec

@[simp] theorem regionBlockedLeftInverse_apply_regionBlockedTensorMap (A : Tensor G d)
    (R : Finset V) (hR : RegionBlockedTensorInjective (G := G) A R)
    (c : RegionBoundaryConfig (G := G) A R → ℂ) :
    regionBlockedLeftInverse (G := G) A R hR
        (regionBlockedTensorMap (G := G) A R c) = c := by
  change ((regionBlockedLeftInverse (G := G) A R hR).comp
    (regionBlockedTensorMap (G := G) A R)) c = c
  rw [regionBlockedLeftInverse_comp_regionBlockedTensorMap]
  rfl

/-- The blocked-region tensor map, expanded as the boundary-configuration sum of
the blocked-region weights. -/
theorem regionBlockedTensorMap_apply (A : Tensor G d) (R : Finset V)
    (c : RegionBoundaryConfig (G := G) A R → ℂ)
    (τ : RegionPhysicalConfig (V := V) (d := d) R) :
    regionBlockedTensorMap (G := G) A R c τ =
      ∑ μ : RegionBoundaryConfig (G := G) A R,
        c μ • regionBlockedWeight (G := G) A R μ τ := by
  rw [regionBlockedTensorMap, Fintype.linearCombination_apply, Finset.sum_apply]
  rfl

/-- The blocked-region tensor map sends the standard basis configuration `μ` to the
blocked-region weight of `μ`. -/
@[simp] theorem regionBlockedTensorMap_single (A : Tensor G d) (R : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R) :
    regionBlockedTensorMap (G := G) A R (Pi.single μ (1 : ℂ)) =
      regionBlockedWeight (G := G) A R μ := by
  classical
  rw [regionBlockedTensorMap, Fintype.linearCombination_apply_single, one_smul]
  rfl

/-- Reading the blocked-region weight of `μ` through the chosen left inverse
recovers the standard basis configuration `μ`. This is the read-off the region
resonate step uses: the blocked endpoint block is inverted on the physical
function it produces. -/
@[simp] theorem regionBlockedLeftInverse_regionBlockedWeight (A : Tensor G d)
    (R : Finset V) (hR : RegionBlockedTensorInjective (G := G) A R)
    (μ : RegionBoundaryConfig (G := G) A R) :
    regionBlockedLeftInverse (G := G) A R hR
        (regionBlockedWeight (G := G) A R μ) = Pi.single μ (1 : ℂ) := by
  rw [← regionBlockedTensorMap_single A R μ,
    regionBlockedLeftInverse_apply_regionBlockedTensorMap]

end PEPS
end TNLean
