/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.AbsorbedEquality
import TNLean.PEPS.FundamentalTheorem.Normal.RegionInsertion.Insertion
import TNLean.PEPS.FundamentalTheorem.Injective.FundamentalTheorem

/-!
# Region proportionalities from the edge-level absorbed equality

This file performs the orientation-reconciliation step of the normal PEPS Fundamental Theorem's
final comparison (arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`).

Throughout, `B'` abbreviates the gauged tensor `applyGauge B X`, which the source writes
with a tilde over `B`; the `Source:` citations below use this notation.

The region comparison `regionComplement_comparison` consumes, as its load-bearing hypothesis
`hregion`, the *absorbed plain* region-inserted coefficient equality

> `regionInsertedCoeff A R f M = regionInsertedCoeff (applyGauge B X) R f (reindex M)`

against a single gauge family `X`.  The per-edge gauge engine instead delivers a *conjugation*-form
identity against a per-edge gauge `Z_e`, whose region-level absorbed form
(`regionInsertedCoeff_eq_applyGauge_of_conjIdentity`) holds against the orientation-adapted
absorbing gauge `absorbedBoundaryGauge` at the boundary edge, not against a single uniform `X`.

The reconciliation here is the *region-independence* of the absorbed equality: an absorbed equality
holding at the *edge level* on every boundary edge of `R` --- the bare-edge statement
`edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`, which mentions
no region --- multiplies back up to the region absorbed equality at `R`
(`regionInsertedCoeff_eq_applyGauge_of_edge`), supplying `hregion` for *every* comparison region
whose boundary edges all carry the edge-level absorbed equality.  Feeding it to
`regionComplement_comparison` produces the region-block scalar proportionality `A_R ∝ B'_R` that
the inserted-site scalar extraction consumes.

The single uniform `X` realizing the edge-level absorbed equality at every edge --- the
transpose/orientation transport of the per-edge engine gauges into one orientation-uniform family
--- is the remaining open piece recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`; this file assembles the proportionalities
on top of it.

It also contains the following results.

* `TNLean.PEPS.regionComplement_comparison`,
  `TNLean.PEPS.regionComplement_comparison_of_vertexInjective`: region-versus-complement comparison
  for the normal PEPS Fundamental Theorem.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open ManyBody (Edge)
open scoped BigOperators Matrix

namespace TNLean

section RegionComplementComparison

/-!
## Region-versus-complement comparison for the normal PEPS Fundamental Theorem

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

### The conditional structure

The region-inserted-coefficient equality between `A` and `B'` --- the source's
statement at line 1519 that "inserting a matrix `Z` on any bond of the first PEPS
gives the same state as inserting the same matrix on the corresponding bond of the
second PEPS" --- is taken as a hypothesis. It is the region form of the
post-absorption insertion equality, supplied by the per-edge gauge family that is
the open kernel piece of the normal route (remaining obligation 5 of
`docs/paper-gaps/peps_normal_ft_section3_route.tex`). The wrapping and the
two-injective comparison on top of it are unconditional.

### References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 1519--1571 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

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
    [Nonempty {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}]
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) R)
    (hCB :
      RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) (Finset.univ \ R))
    (hregion : ∀ (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
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
    [Nonempty {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}]
    (hA : IsVertexInjective A) (hBtilde : IsVertexInjective Btilde)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hregion : ∀ (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
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

end RegionComplementComparison

section ProportionalityFromAbsorbed

namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-- **The edge-level absorbed equality from a region conjugation identity.**

If the per-edge gauge `Z` realizes the engine's conjugation-form region-inserted coefficient
identity at a region `R` with single boundary edge `f` --- `A` inserting `M` matches `B` inserting
`Z · (reindex M) · Z⁻¹` --- then the *edge-level* absorbed equality holds at `f.1` against
`applyGauge B X`, provided `X f.1` is the orientation-adapted absorbing gauge
`absorbedBoundaryGauge B R f Z` and every bond dimension of `A` is positive.  The edge-level
identity over the bare edge `f.1` mentions no region.

The conversion is `regionInsertedCoeff_eq_applyGauge_of_conjIdentity` (turning the conjugation
identity into the region absorbed equality at `R`) followed by
`edgeInsertedCoeff_eq_applyGauge_of_region` (cancelling the shared positive interior multiplicity
to the bare-edge identity).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem edgeAbsorbed_of_conjIdentity (A B : Tensor G d) (R : Finset V)
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (hbd : A.bondDim = B.bondDim)
    (Z : GL (Fin (B.bondDim f.1)) ℂ)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (hXf : X f.1 = absorbedBoundaryGauge (G := G) B R f Z)
    (hposA : ∀ e : Edge G, 0 < A.bondDim e)
    (hid : ∀ (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
      (σ : RegionPhysicalConfig (V := V) (d := d) R)
      (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)),
      regionInsertedCoeff (G := G) A R f M σ τ =
        regionInsertedCoeff (G := G) B R f
          ((Z : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) *
              Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M *
            (↑Z⁻¹ : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)) σ τ)
    (σ : V → Fin d) (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    edgeInsertedCoeff (G := G) A f.1 σ N =
      edgeInsertedCoeff (G := G) (applyGauge B X) f.1 σ
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N) :=
  edgeInsertedCoeff_eq_applyGauge_of_region A B R f hbd X hposA
    (fun M σ' τ' =>
      regionInsertedCoeff_eq_applyGauge_of_conjIdentity A B R f hbd Z X hXf hid M σ' τ')
    σ N

/-- **The region absorbed equality from the edge-level absorbed equality on every boundary edge.**

If the edge-level absorbed equality holds against `applyGauge B X` at *every* boundary edge of `R`
--- inserting `N` on `A`'s edge `e` matches inserting the reindexed `N` on `applyGauge B X`'s edge
`e` for every global physical configuration --- then the *region* absorbed equality holds at `R`:
inserting `M` on `A` over `R` at a boundary edge `f` matches inserting the reindexed `M` on
`applyGauge B X` over `R` at `f`.

This is the `hregion` hypothesis of `regionComplement_comparison`, here packaged from the
region-independent edge-level identity `regionInsertedCoeff_eq_applyGauge_of_edge`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem regionAbsorbed_of_edgeAbsorbed (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (R : Finset V)
    (hedge : ∀ (e : Edge G) (σ : V → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N))
    (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    regionInsertedCoeff (G := G) A R f M σ τ =
      regionInsertedCoeff (G := G) (applyGauge B X) R f
        (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) M) σ τ :=
  regionInsertedCoeff_eq_applyGauge_of_edge A B hbd X f.1 (hedge f.1) R f rfl M σ τ

/-- **Region-block scalar proportionality from the edge-level absorbed equality.**

For a region `R` whose two block tensors over `A` and over the gauge-absorbed second tensor
`applyGauge B X` are all two-block injective, if the edge-level absorbed equality against
`applyGauge B X` holds at every edge of the graph, then the region blocks of `A` and of the
reindexed `applyGauge B X` are scalar proportional: there is a nonzero `c` with `A_R = c · B'_R`.

This is `regionComplement_comparison` fed the region absorbed equality of
`regionAbsorbed_of_edgeAbsorbed`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`: `A_R ∝ B'_R`. -/
theorem twoBlockProportional_of_edgeAbsorbed (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (R : Finset V)
    [Nonempty {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}]
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) R)
    (hCB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) (Finset.univ \ R))
    (hedge : ∀ (e : Edge G) (σ : V → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
      edgeInsertedCoeff (G := G) A e σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) e σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd e)) N)) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
        (regionTwoBlock (G := G) (reindexTensor (G := G) (applyGauge B X) hbd) R) c :=
  regionComplement_comparison A (applyGauge B X) R hbd hRA hCA hRB hCB
    (fun f N σ τ => regionAbsorbed_of_edgeAbsorbed A B hbd X R hedge f N σ τ)

/-- **Region-block scalar proportionality from the absorbed equality on the boundary edges.**

The same conclusion as `twoBlockProportional_of_edgeAbsorbed`, with the edge-level absorbed
equality required only at the *boundary edges* of the comparison region `R` rather than at every
edge of the graph.  The comparison `regionComplement_comparison` consumes the region absorbed
equality only at boundary edges of `R`, so the bare-edge identities there suffice.

This restriction is what the open square lattice provides: the blocking frames reach only the
edges with interior margins, so the absorbed equality is available on the boundary edges of a
comparison region placed in the interior window, not on every lattice edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`: `A_R ∝ B'_R`. -/
theorem twoBlockProportional_of_boundaryEdgeAbsorbed (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (R : Finset V)
    [Nonempty {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}]
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) R)
    (hCB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) (Finset.univ \ R))
    (hedge : ∀ (f : {f : Edge G // ManyBody.IsRegionBoundaryEdge (G := G) R f}) (σ : V → Fin d)
        (N : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ),
      edgeInsertedCoeff (G := G) A f.1 σ N =
        edgeInsertedCoeff (G := G) (applyGauge B X) f.1 σ
          (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbd f.1)) N)) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
        (regionTwoBlock (G := G) (reindexTensor (G := G) (applyGauge B X) hbd) R) c :=
  regionComplement_comparison A (applyGauge B X) R hbd hRA hCA hRB hCB
    (fun f M σ τ =>
      regionInsertedCoeff_eq_applyGauge_of_edge A B hbd X f.1 (hedge f) R f rfl M σ τ)

end PEPS

end ProportionalityFromAbsorbed

end TNLean
