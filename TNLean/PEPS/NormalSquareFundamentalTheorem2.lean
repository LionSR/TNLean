import TNLean.PEPS.NormalSquareInteriorAbsorbedFamily
import TNLean.PEPS.NormalSquareComparisonRegion
import TNLean.PEPS.NormalSquareInjectivity
import TNLean.PEPS.RegionBlock.ScalarExtraction
import TNLean.PEPS.RegionBlock.ProportionalityFromAbsorbed
import TNLean.PEPS.RegionBlock.ReindexInjectivity
import TNLean.PEPS.RegionBlock.GaugeInjectivity2

/-!
# The unconditional normal PEPS Fundamental Theorem on the open square lattice

This file assembles the unconditional interior form of the normal PEPS Fundamental Theorem on
the finite **open** `width × height` square lattice (arXiv:1804.04964, Section 3, Theorem 3,
lines 1449--1571 of `Papers/1804.04964/paper_normal.tex`): from the source hypotheses alone ---
the rectangular-injectivity hypotheses for both tensors, matched bond dimensions, positive
bonds, and the same state --- it produces a per-edge gauge family `X` with

* the bare-edge absorbed equality at every edge with interior margins, and
* at every vertex in the interior comparison window, a nonzero scalar `λ_v` with the per-vertex
  relation `A_v = λ_v · (gauge action of B at v)`.

The union closure of injective regions is derived from the positive bonds
(`regionInjectivityUnionClosure_of_overlap`), not assumed, and no single-vertex injectivity is
used anywhere.  This is the open-lattice port of the torus assembly
(`fundamentalTheorem_normalTorusPEPS_unconditional`), in the scope the open blocking geometry
honestly supports.

**Scope restriction (interior window, per-vertex scalars):** the conclusion is restricted in
two ways relative to the source's Theorem 3, both documented in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining mathematical
obligations".

1. *Interior window.*  The open lattice's translated blocking frames require interior margins,
   so the absorbed equality reaches only the interior edges and the comparison pair only the
   offsets of `IsNormalSquareComparisonWindow` (`4 ≤ x ≤ width - 9`, `4 ≤ y ≤ height - 9`).
   Vertices near the lattice boundary are not reached: the boundary edges of any comparison
   region adjacent to them lie outside the interior margins.  On the torus every edge is a
   translate of a reference edge, so no such window appears there.

2. *Per-vertex scalars.*  The scalars `λ_v` of distinct vertices are not asserted equal, and no
   product condition `λ^{n·m} = 1` is asserted.  The source's single `λ` comes from translation
   invariance of the tensors, which transports one comparison pair (and its scalars) to every
   site; the open coordinate lattice carries no translations and the present development has no
   translation-invariance predicate on it, so the per-edge gauges and per-vertex scalars are
   chosen independently.  A single `λ` is in fact false without a translation-invariance
   hypothesis: rescaling `A`'s components at two interior vertices by `μ` and `μ⁻¹` preserves
   the state and the rectangular injectivity but separates the two scalars.

The structural findings behind this scope (recorded here as the port's scouting note): the open
lattice encodes no translation structure --- `IsTorusTranslationInvariant` and the whole torus
witness-transport layer act through the graph automorphisms `translate a b`, which have no
open-lattice analogue, partial translations not being graph automorphisms; the open witness
machinery (`exists_regionEdgeGauge_normalSquare*TranslatedEdge`) delivers per-edge gauges at
interior edges only, each chosen independently, with the orientation-uniform reduction of
`NormalSquareTI` having no derivation without a translation-invariance predicate; and the
per-vertex relation is well formed at boundary vertices (the local virtual configuration ranges
over the existing incident edges only) but not derivable there, the comparison regions' boundary
edges falling outside the interior margins.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1571 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

/- Sealing `gaugeVertex` (file-locally irreducible) keeps the statements below within the
default elaboration budget.  Elaborating `reindexTensor (applyGauge B X) hbond` checks
`(applyGauge B X).bondDim ≡ B.bondDim`; before reducing the projection, the unifier first
attempts the structure congruence `applyGauge B X ≡ B`, whose component comparison unfolds the
`gaugeVertex` sums over `Finset.univ` of the concrete `Fin width × Fin height` lattice — a
reduction that runs deep into the `List.finRange`/`Multiset.product` evaluation before sticking
on the variable `width` and `height`, far past the heartbeat budget (the torus lattice `ZMod`
coordinates stick immediately, which is why the torus assembly needs no seal).  With
`gaugeVertex` irreducible the doomed congruence fails at once and the projection reduces
normally.  All proofs below treat `gaugeVertex` as opaque, so nothing else changes. -/
seal gaugeVertex

variable {width height d : ℕ}

/-- **The comparison-region proportionality at a window vertex.**

The first half of the comparison pair at a window vertex `v`: the absorbed equality on the
boundary edges of the `3 × 3`-minus-corner region at `v` yields the two-block scalar
proportionality of `A` and the reindexed gauge-absorbed tensor over that region.  Isolated in
its own declaration so that the comparison instantiation elaborates within the heartbeat
budget.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem comparisonRegionProportional_of_interiorAbsorbed
    (A B : Tensor (squareLatticeGraph width height) d)
    (hAr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hBr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hedge : ∀ e : Edge (squareLatticeGraph width height),
      NormalSquareInteriorEdgeDatum e →
      ∀ (σ : SquareLatticeVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
          edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (v : SquareLatticeVertex width height)
    (hwin : IsNormalSquareComparisonWindow width height v.1.1 v.2.1) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional.{0, 0, 0, 0}
        (regionTwoBlock (G := squareLatticeGraph width height) A
          (normalSquareComparisonRegion v.1.1 v.2.1))
        (regionTwoBlock (G := squareLatticeGraph width height)
          (reindexTensor (G := squareLatticeGraph width height) (applyGauge B X) hbond)
          (normalSquareComparisonRegion v.1.1 v.2.1)) c := by
  classical
  obtain ⟨ha4, haw, hb4, hbh⟩ := hwin
  have hRA : RegionBlockedTensorInjective (G := squareLatticeGraph width height) A
      (normalSquareComparisonRegion v.1.1 v.2.1) := by
    have hi := hAr.comparisonRegion_injective hUA (a := v.1.1) (b := v.2.1)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCRA : RegionBlockedTensorInjective (G := squareLatticeGraph width height) A
      (Finset.univ \ normalSquareComparisonRegion v.1.1 v.2.1) := by
    have hi := hAr.compl_comparisonRegion_injective hUA (a := v.1.1) (b := v.2.1)
      (by omega) (by omega) (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (normalSquareComparisonRegion v.1.1 v.2.1) := by
    have hi := hBr.comparisonRegion_injective hUB (a := v.1.1) (b := v.2.1)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ normalSquareComparisonRegion v.1.1 v.2.1) := by
    have hi := hBr.compl_comparisonRegion_injective hUB (a := v.1.1) (b := v.2.1)
      (by omega) (by omega) (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  haveI hNeR : Nonempty {f : Edge (squareLatticeGraph width height) //
      IsRegionBoundaryEdge (G := squareLatticeGraph width height)
        (normalSquareComparisonRegion v.1.1 v.2.1) f} :=
    ⟨⟨squareLatticeUpEdge v.1.1 v.2.1 (by omega) (by omega),
      isRegionBoundaryEdge_normalSquareComparisonRegion (by omega) (by omega)⟩⟩
  exact twoBlockProportional_of_boundaryEdgeAbsorbed A B hbond X
    (normalSquareComparisonRegion v.1.1 v.2.1) hRA hCRA
    (regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ hRB))
    (regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ hCRB))
    (fun f σ N => hedge f.1
      (normalSquareInteriorEdgeDatum_of_boundary_comparisonRegion
        ⟨ha4, haw, hb4, hbh⟩ f.2) σ N)

/-- **The completed-square proportionality at a window vertex.**

The second half of the comparison pair: the absorbed equality on the boundary edges of the
completed `3 × 3` square at `v` yields the two-block scalar proportionality over the one-site
completion `insert v` of the comparison region.  Isolated in its own declaration so that the
comparison instantiation elaborates within the heartbeat budget.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem comparisonSquareProportional_of_interiorAbsorbed
    (A B : Tensor (squareLatticeGraph width height) d)
    (hAr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hBr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hedge : ∀ e : Edge (squareLatticeGraph width height),
      NormalSquareInteriorEdgeDatum e →
      ∀ (σ : SquareLatticeVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
          edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (v : SquareLatticeVertex width height)
    (hwin : IsNormalSquareComparisonWindow width height v.1.1 v.2.1) :
    ∃ c : ℂ, c ≠ 0 ∧
      TwoBlockScalarProportional.{0, 0, 0, 0}
        (regionTwoBlock (G := squareLatticeGraph width height) A
          (insert v (normalSquareComparisonRegion v.1.1 v.2.1)))
        (regionTwoBlock (G := squareLatticeGraph width height)
          (reindexTensor (G := squareLatticeGraph width height) (applyGauge B X) hbond)
          (insert v (normalSquareComparisonRegion v.1.1 v.2.1))) c := by
  classical
  obtain ⟨ha4, haw, hb4, hbh⟩ := hwin
  rw [insert_normalSquareComparisonRegion v]
  have hSA : RegionBlockedTensorInjective (G := squareLatticeGraph width height) A
      (normalSquareComparisonSquare v.1.1 v.2.1) := by
    have hi := hAr.comparisonSquare_injective hUA (a := v.1.1) (b := v.2.1)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCSA : RegionBlockedTensorInjective (G := squareLatticeGraph width height) A
      (Finset.univ \ normalSquareComparisonSquare v.1.1 v.2.1) := by
    have hi := hAr.compl_comparisonSquare_injective hUA (a := v.1.1) (b := v.2.1)
      (by omega) (by omega) (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hSB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (normalSquareComparisonSquare v.1.1 v.2.1) := by
    have hi := hBr.comparisonSquare_injective hUB (a := v.1.1) (b := v.2.1)
      (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hCSB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
      (Finset.univ \ normalSquareComparisonSquare v.1.1 v.2.1) := by
    have hi := hBr.compl_comparisonSquare_injective hUB (a := v.1.1) (b := v.2.1)
      (by omega) (by omega) (by omega) (by omega)
    rwa [regionInjectivityDataOf_isInjective] at hi
  haveI hNeS : Nonempty {f : Edge (squareLatticeGraph width height) //
      IsRegionBoundaryEdge (G := squareLatticeGraph width height)
        (normalSquareComparisonSquare v.1.1 v.2.1) f} :=
    ⟨⟨squareLatticeUpEdge v.1.1 (v.2.1 - 1) (by omega) (by omega),
      isRegionBoundaryEdge_normalSquareComparisonSquare (by omega) (by omega) (by omega)⟩⟩
  exact twoBlockProportional_of_boundaryEdgeAbsorbed A B hbond X
    (normalSquareComparisonSquare v.1.1 v.2.1) hSA hCSA
    (regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ hSB))
    (regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ hCSB))
    (fun f σ N => hedge f.1
      (normalSquareInteriorEdgeDatum_of_boundary_comparisonSquare
        ⟨ha4, haw, hb4, hbh⟩ f.2) σ N)

/-- **The window scalar from the interior absorbed equality.**

At a vertex `v` of the interior comparison window, the comparison pair (the `3 × 3` square at
`v` minus its corner, and the completed square) together with the absorbed equality on interior
edges produces a nonzero scalar `λ_v` with the per-vertex relation
`A_v = λ_v · (gauge action of B at v)`.  The two comparison proportionalities are taken from
their own declarations so each comparison instantiation elaborates within the heartbeat budget.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1519--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_windowScalar_of_interiorAbsorbed
    (A B : Tensor (squareLatticeGraph width height) d)
    (hAr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hBr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ)
    (hedge : ∀ e : Edge (squareLatticeGraph width height),
      NormalSquareInteriorEdgeDatum e →
      ∀ (σ : SquareLatticeVertex width height → Fin d)
        (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
        edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
          edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
            (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N))
    (v : SquareLatticeVertex width height)
    (hwin : IsNormalSquareComparisonWindow width height v.1.1 v.2.1) :
    ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (η : (ie : IncidentEdge (squareLatticeGraph width height) v) →
          Fin (A.bondDim ie.1))
        (σ : Fin d),
        A.component v η σ =
          lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ := by
  classical
  obtain ⟨cR, hcR0, hcRprop⟩ := comparisonRegionProportional_of_interiorAbsorbed A B hAr hBr
    hUA hUB hbond X hedge v hwin
  obtain ⟨cS, hcS0, hcSprop⟩ := comparisonSquareProportional_of_interiorAbsorbed A B hAr hBr
    hUA hUB hbond X hedge v hwin
  obtain ⟨ha4, haw, hb4, hbh⟩ := hwin
  have hRC : RegionBlockedTensorInjective (G := squareLatticeGraph width height)
      (reindexTensor (G := squareLatticeGraph width height) (applyGauge B X) hbond)
      (normalSquareComparisonRegion v.1.1 v.2.1) := by
    have hRB : RegionBlockedTensorInjective (G := squareLatticeGraph width height) B
        (normalSquareComparisonRegion v.1.1 v.2.1) := by
      have hi := hBr.comparisonRegion_injective hUB (a := v.1.1) (b := v.2.1)
        (by omega) (by omega)
      rwa [regionInjectivityDataOf_isInjective] at hi
    exact regionBlockedTensorInjective_reindexTensor (applyGauge B X) hbond _
      (regionBlockedTensorInjective_applyGauge B X _ hRB)
  exact ⟨cS / cR, div_ne_zero hcS0 hcR0,
    component_eq_gaugeVertex_of_twoBlockProportional A B
      (normalSquareComparisonRegion v.1.1 v.2.1)
      (notMem_normalSquareComparisonRegion v) hbond X cR cS hcR0 hposA
      hRC hcRprop hcSprop⟩

/-- **Unconditional normal PEPS Fundamental Theorem on the open square lattice (interior
window).**

For two tensors on the open `width × height` square lattice with the rectangular-injectivity
hypotheses, matched bond dimensions, positive bonds, and the same state, there is a per-edge
gauge family `X` over the second tensor's bonds such that

* the bare-edge absorbed equality holds at every edge with interior margins: inserting `N` on
  `A`'s edge matches inserting the reindexed `N` on `applyGauge B X`'s edge, for every global
  physical configuration; and
* every vertex `v` in the interior comparison window carries a nonzero scalar `λ_v` with
  `A_v = λ_v · (gauge action of B at v)` on every local virtual configuration and physical
  index.

The union closure of injective regions is derived from the positive bonds; the comparison pair
at `v` is the `3 × 3` square at `v` minus its corner and the completed square, whose
proportionality scalars `c_R`, `c_S` give `λ_v = c_S / c_R` by the inserted-site scalar
extraction.

**Scope restriction (interior window, per-vertex scalars):** the absorbed equality is asserted
on interior edges only, the per-vertex relation on window vertices only, and the scalars of
distinct vertices are not asserted equal (no `λ^{n·m} = 1`); see the module docstring and
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining mathematical
obligations".  The source's Theorem 3 obtains the single `λ` from translation invariance, which
the open coordinate lattice does not encode.

Source: arXiv:1804.04964, Section 3, Theorem 3, lines 1449--1571 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem fundamentalTheorem_normalSquarePEPS_unconditional
    (A B : Tensor (squareLatticeGraph width height) d)
    (hAr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hBr : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    ∃ X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      (∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N)) ∧
      ∀ v : SquareLatticeVertex width height,
        IsNormalSquareComparisonWindow width height v.1.1 v.2.1 →
        ∃ lam : ℂ, lam ≠ 0 ∧
          ∀ (η : (ie : IncidentEdge (squareLatticeGraph width height) v) →
              Fin (A.bondDim ie.1))
            (σ : Fin d),
            A.component v η σ =
              lam * gaugeVertex B X v (fun ie => Fin.cast (congr_fun hbond ie.1) (η ie)) σ := by
  classical
  -- The union closure of injective regions, from positive bonds.
  have hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) A) :=
    regionInjectivityUnionClosure_of_overlap A hposA
  have hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := squareLatticeGraph width height) B) :=
    regionInjectivityUnionClosure_of_overlap B hposB
  -- The interior absorbed gauge family.
  obtain ⟨X, hedge⟩ := exists_normalSquareInteriorAbsorbedGaugeFamily A B hAr hUA hBr hUB
    hbond hAB hd hposA hposB
  exact ⟨X, hedge, fun v hwin => exists_windowScalar_of_interiorAbsorbed A B hAr hBr hUA hUB
    hbond hposA X hedge v hwin⟩

end PEPS
end TNLean
