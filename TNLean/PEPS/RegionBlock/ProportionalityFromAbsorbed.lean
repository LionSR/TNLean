import TNLean.PEPS.RegionBlock.AbsorbedEquality
import TNLean.PEPS.RegionComplementComparison

/-!
# Region proportionalities from the edge-level absorbed equality

This file performs the orientation-reconciliation step of the normal PEPS Fundamental Theorem's
final comparison (arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`).

The region comparison `regionComplement_comparison` consumes, as its load-bearing hypothesis
`hregion`, the *absorbed plain* region-inserted coefficient equality

> `regionInsertedCoeff A R f M = regionInsertedCoeff (applyGauge B X) R f (reindex M)`

against a single gauge family `X`.  The per-edge gauge engine instead delivers a *conjugation*-form
identity against a per-edge gauge `Z_e`, whose region-level absorbed form
(`regionInsertedCoeff_eq_applyGauge_of_conjIdentity`) holds against the orientation-adapted
absorbing gauge `absorbedBoundaryGauge` at the boundary edge, not against a single uniform `X`.

The reconciliation here is the *region-independence* of the absorbed equality: an absorbed equality
holding at the *edge level* on every boundary edge of `R` --- the bare-edge statement
`edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`, which mentions no
region --- multiplies back up to the region absorbed equality at `R`
(`regionInsertedCoeff_eq_applyGauge_of_edge`), supplying `hregion` for *every* comparison region
whose boundary edges all carry the edge-level absorbed equality.  Feeding it to
`regionComplement_comparison` produces the region-block scalar proportionality `A_R ∝ B̃_R` that the
inserted-site scalar extraction consumes.

The single uniform `X` realizing the edge-level absorbed equality at every edge --- the
transpose/orientation transport of the per-edge engine gauges into one orientation-uniform family
--- is the remaining open piece recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`; this file assembles the proportionalities
on top of it.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

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
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
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
reindexed `applyGauge B X` are scalar proportional: there is a nonzero `c` with `A_R = c · B̃_R`.

This is `regionComplement_comparison` fed the region absorbed equality of
`regionAbsorbed_of_edgeAbsorbed`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`: `A_R ∝ B̃_R`. -/
theorem twoBlockProportional_of_edgeAbsorbed (A B : Tensor G d)
    (hbd : A.bondDim = B.bondDim)
    (X : (e : Edge G) → GL (Fin (B.bondDim e)) ℂ)
    (R : Finset V)
    [Nonempty {f : Edge G // IsRegionBoundaryEdge (G := G) R f}]
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

end PEPS
end TNLean
