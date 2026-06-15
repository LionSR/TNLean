import TNLean.PEPS.RegionBlock.AbsorbedEquality
import TNLean.PEPS.RegionComplementComparison

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
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
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
reindexed `applyGauge B X` are scalar proportional: there is a nonzero `c` with `A_R = c · B'_R`.

This is `regionComplement_comparison` fed the region absorbed equality of
`regionAbsorbed_of_edgeAbsorbed`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1544 of
`Papers/1804.04964/paper_normal.tex`: `A_R ∝ B'_R`. -/
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
    [Nonempty {f : Edge G // IsRegionBoundaryEdge (G := G) R f}]
    (hRA : RegionBlockedTensorInjective (G := G) A R)
    (hCA : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (hRB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) R)
    (hCB : RegionBlockedTensorInjective (G := G)
      (reindexTensor (G := G) (applyGauge B X) hbd) (Finset.univ \ R))
    (hedge : ∀ (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f}) (σ : V → Fin d)
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

/-! ### Uniqueness of the proportionality scalar

The scalar `c` in a region-block proportionality `A_R = c · B'_R` is determined by `A` and `B'`
once `B'`'s blocked family is linearly independent: a linearly independent family has no zero
member, so some blocked weight of `B'` is nonzero, and the proportionality reads `c` off that
nonzero entry.  This names the proportionality scalar canonically --- the translation-invariant
common quotient the torus scalar condition consumes is the ratio of two such named scalars. -/

/-- **Uniqueness of the region-block proportionality scalar.**

If the reindexed comparison tensor `B' = reindexTensor Btilde hbd` has a linearly independent
blocked family over `R`, every bond dimension is positive, and both `c` and `c'` are
proportionality scalars of `A_R` against `B'_R`, then `c = c'`: positivity makes the boundary-label
index nonempty, linear independence forbids a zero member there, so some blocked weight of `B'` is
nonzero and both scalars equal `A`'s weight divided by it.

Source: arXiv:1804.04964, Section 3, Lemma `inj_equal_tensors_2`: the proportionality constant is
unique. -/
theorem twoBlockScalarProportional_unique (A Btilde : Tensor G d) (R : Finset V)
    (hbd : A.bondDim = Btilde.bondDim)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (hBinj : RegionBlockedTensorInjective (G := G) (reindexTensor (G := G) Btilde hbd) R)
    {c c' : ℂ}
    (hc : TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
      (regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R) c)
    (hc' : TwoBlockScalarProportional (regionTwoBlock (G := G) A R)
      (regionTwoBlock (G := G) (reindexTensor (G := G) Btilde hbd) R) c') :
    c = c' := by
  classical
  set C := reindexTensor (G := G) Btilde hbd with hCdef
  -- The boundary-label index is nonempty: each incident bond is positive, so the value space is
  -- nonempty and the (possibly empty) boundary-edge index admits a configuration.
  have hCpos : ∀ e : Edge G, 0 < C.bondDim e := fun e => by
    rw [hCdef, reindexTensor_bondDim]; exact hpos e
  have hNe : Nonempty (RegionBoundaryConfig (G := G) C R) :=
    ⟨fun f => ⟨0, hCpos f.1⟩⟩
  -- A linearly independent family has no zero member: pick a boundary label `b` and a physical
  -- configuration `ρ` where `B'`'s blocked weight is nonzero.
  have hne : (regionBlockedTensorFamily (G := G) C R)
      (Classical.arbitrary (RegionBoundaryConfig (G := G) C R)) ≠ 0 :=
    hBinj.ne_zero _
  obtain ⟨ρ, hρ⟩ : ∃ ρ, regionBlockedWeight (G := G) C R
      (Classical.arbitrary (RegionBoundaryConfig (G := G) C R)) ρ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  set b := Classical.arbitrary (RegionBoundaryConfig (G := G) C R) with hbdef
  -- Both proportionalities read at `(b, ρ)` give `A_R = c · B'_R` and `A_R = c' · B'_R`.
  have h1 := hc PUnit.unit b ρ
  have h2 := hc' PUnit.unit b ρ
  simp only [regionTwoBlock_apply] at h1 h2
  have : c * regionBlockedWeight (G := G) C R b ρ =
      c' * regionBlockedWeight (G := G) C R b ρ := by rw [← h1, ← h2]
  exact mul_right_cancel₀ hρ this

end PEPS
end TNLean
