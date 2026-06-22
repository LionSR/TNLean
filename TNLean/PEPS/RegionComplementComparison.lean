import TNLean.PEPS.RegionBlock.Insertion
import TNLean.PEPS.FundamentalTheorem
import TNLean.PEPS.NormalEdgeGauge

/-!
# Region-versus-complement comparison for the normal PEPS Fundamental Theorem

This file performs the final `R`/`S` comparison step of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, proof of Theorem 3, lines
1519--1571 of `Papers/1804.04964/paper_normal.tex`).

After the per-edge gauges are absorbed into the second tensor, the source compares
two one-site-different injective regions `R` and `S`, both with injective
complements, against the modified tensor `B'` (written with a tilde over `B` in
the source). At line 1544 the source applies its `lem:inj_equal_tensors_2` to
conclude `A_R ∝ B'_R` and `A_S ∝ B'_S`.

This is the region analogue of the one-vertex-versus-complement comparison
`one_vertex_complement_comparison` used in the injective case. The single vertex is
replaced by an arbitrary injective region `R`, and the vertex complement by the set
complement `univ \ R`. The two blocks are wrapped as `regionTwoBlock A R` and
`regionComplementTwoBlock A R`, both two-block injective for a vertex-injective PEPS
with positive bonds (`regionBlockedTensorInjective_of_isVertexInjective`). The
generalized two-injective comparison `two_injective_tensor_insertion_comparison`
then gives scalar proportionality `A_R ∝ B'_R`.

## The conditional structure

The region-inserted-coefficient equality between `A` and `B'` --- the source's
statement at line 1519 that "inserting a matrix `Z` on any bond of the first PEPS
gives the same state as inserting the same matrix on the corresponding bond of the
second PEPS" --- is taken as a hypothesis. It is the region form of the
post-absorption insertion equality, supplied by the per-edge gauge family that is
the open kernel piece of the normal route (remaining obligation 5 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`). The wrapping and the
two-injective comparison on top of it are unconditional.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1519--1571 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The region against its set complement

A region `R` and its set complement `univ \ R` form a two-block pair over the edges
crossing the boundary of `R`. The region-inserted-coefficient equality between `A`
and the modified tensor `B'` (transported to `A`'s bonds) gives, via
`sameTwoBlockInsertions_of_regionInsertedCoeff_eq` and the generalized two-injective
comparison, scalar proportionality of the region block of `A` with the region block
of `B'`. -/

/-- **Region-versus-complement scalar proportionality.**

For a region `R` whose two block tensors over `A` and over the reindexed `B'` are
all two-block injective, if `A` and `B'` have matched bond dimensions and equal
region-inserted coefficients on every boundary edge of `R`, then the region blocks
are scalar proportional: there is a nonzero `c` with `A_R = c · B'_R`.

This is the region analogue of `one_vertex_complement_comparison`. The matched
region-inserted coefficients are turned into equal one-bond two-block insertions by
`sameTwoBlockInsertions_of_regionInsertedCoeff_eq`, and the scalar follows from
`two_injective_tensor_insertion_comparison`.

The region-inserted-coefficient equality is the conditional kernel input; see the
module docstring.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`: `A_R ∝ B'_R`. -/
theorem regionComplement_comparison (A Btilde : Tensor G d)
    (R : Finset V) (hbd : A.bondDim = Btilde.bondDim)
    [Nonempty {f : Edge G // IsRegionBoundaryEdge (G := G) R f}]
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) R)
    (hCB :
      RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) (Finset.univ \ R))
    (hregion : ∀ (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f N σ τ =
        regionInsertedCoeff (G := G) Btilde R f
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N) σ τ) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
        (regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R) c := by
  classical
  rcases two_injective_tensor_insertion_comparison
      (External₂ := PUnit.{1})
      (Physical₂ := RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R))
      (regionTwoBlock (G := G) A R)
      (regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R)
      (regionComplementTwoBlock (G := G) A R)
      (regionComplementTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R)
      (isTwoBlockInjective_regionTwoBlock (G := G) A R hRA)
      (isTwoBlockInjective_regionComplementTwoBlock (G := G) A R hCA)
      (isTwoBlockInjective_regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R hRB)
      (isTwoBlockInjective_regionComplementTwoBlock (G := G)
        (reindexTensor (G := G) Btilde hbd) R hCB)
      (sameTwoBlockInsertions_of_regionInsertedCoeff_eq A Btilde R hbd hregion)
      with ⟨c, hc_ne, hregionProp, _hcomplProp⟩
  exact ⟨c, hc_ne, hregionProp⟩

/-- **Region-versus-complement comparison for vertex-injective tensors.**

For vertex-injective `A` and `Btilde` with positive bond dimensions and matched
bond dimensions, every region `R` with at least one boundary edge admits the
region-block scalar proportionality `A_R ∝ B'_R`, provided the region-inserted
coefficients of `A` and `B'` agree on every boundary edge of `R`.

The four two-block injectivity hypotheses are discharged uniformly from vertex
injectivity by `regionBlockedTensorInjective_of_isVertexInjective`, so the region
need not be one of the special source regions. The region-inserted-coefficient
equality is the conditional kernel input.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionComplement_comparison_of_vertexInjective (A Btilde : Tensor G d)
    (R : Finset V) (hbd : A.bondDim = Btilde.bondDim)
    [Nonempty {f : Edge G // IsRegionBoundaryEdge (G := G) R f}]
    (hA : IsVertexInjective A) (hBtilde : IsVertexInjective Btilde)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hregion : ∀ (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
      (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f N σ τ =
        regionInsertedCoeff (G := G) Btilde R f
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N) σ τ) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
        (regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R) c := by
  have hposBt : ∀ e : Edge G, 0 < (reindexTensor (G := G) Btilde hbd).bondDim e := by
    intro e; rw [reindexTensor_bondDim]; exact hpos e
  have hBtreindex : IsVertexInjective (reindexTensor (G := G) Btilde hbd) :=
    isVertexInjective_reindexTensor Btilde hbd hBtilde
  exact regionComplement_comparison A Btilde R hbd
    (regionBlockedTensorInjective_of_isVertexInjective (G := G) A R hA hpos)
    (regionBlockedTensorInjective_of_isVertexInjective (G := G) A (Finset.univ \ R) hA hpos)
    (regionBlockedTensorInjective_of_isVertexInjective (G := G)
      (reindexTensor (G := G) Btilde hbd) R hBtreindex hposBt)
    (regionBlockedTensorInjective_of_isVertexInjective (G := G)
      (reindexTensor (G := G) Btilde hbd) (Finset.univ \ R) hBtreindex hposBt)
    hregion

end PEPS
end TNLean
