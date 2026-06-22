import TNLean.PEPS.NormalSquareEdgeCoeff

/-!
# The interior absorbed gauge family on the open square lattice

This file assembles the per-edge absorbing gauges of the interior edges of the finite open
square lattice into a single per-edge gauge family `X` carrying the bare-edge absorbed equality

> `edgeInsertedCoeff A e σ N = edgeInsertedCoeff (applyGauge B X) e σ (reindex N)`

at every edge with interior margins (`NormalSquareInteriorEdgeDatum`).  This is the open-lattice
counterpart of the torus family `exists_torusCovariantAbsorbedGaugeFamily`, restricted to the
edges the open blocking geometry reaches: the bare-edge identity at an edge depends only on the
family's value there, so the absorbing gauges of distinct interior edges combine edge by edge
with no compatibility conditions.

Unlike the torus, the open lattice carries no translations, so the family is *chosen* at each
interior edge rather than transported from one reference witness per orientation class; no
covariance between the gauges at distinct edges is asserted.  Edges without interior margins
(those near the lattice boundary) receive the identity gauge and carry no absorbed equality;
that boundary geometry is the residual open part recorded in
`docs/paper-gaps/peps_normal_ft_section3_route.tex`, Section "Remaining mathematical
obligations".

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544
  of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ}

/-- **The absorbing gauge at an edge with interior margins.**

An edge of the open square lattice carrying the cover-free interior datum --- horizontal or
vertical with the corresponding interior margins --- admits an invertible matrix `Ze` such that
every per-edge gauge family `X` with `X e = Ze` satisfies the bare-edge absorbed equality at `e`
against `applyGauge B X`.

The horizontal and vertical cases are
`exists_absorbingGauge_normalSquareHorizontalTranslatedEdge` and its vertical counterpart,
reached by rewriting the edge as the distinguished edge of the translated interior frame at
offset `(x-1, y-2)` (horizontal) or `(x-2, y-1)` (vertical).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_absorbingGauge_of_normalSquareInteriorEdgeDatum
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g)
    (e : Edge (squareLatticeGraph width height))
    (he : NormalSquareInteriorEdgeDatum e) :
    ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
      ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
        X e = Ze →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  rcases he with ⟨hEdge, hMargins⟩ | ⟨hEdge, hMargins⟩
  · -- Horizontal interior edge: the translated frame at `(x-1, y-2)`.
    obtain ⟨hx3, hx7, hy4, hy6⟩ := hMargins
    have heq : e = normalSquareHorizontalTranslatedEdge
        (e.1.1.1.1 - 1) (e.1.1.2.1 - 2) (by omega) (by omega) := by
      rw [normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge
        (by omega) (by omega) (by omega) (by omega)]
      exact horizontalSquareLatticeEdge_eq_rightEdge e hEdge
    rw [heq]
    exact exists_absorbingGauge_normalSquareHorizontalTranslatedEdge A B hA hUA hB hUB
      (by omega) (by omega) (by omega) (by omega) hbond hAB hd hposA hposB
  · -- Vertical interior edge: the translated frame at `(x-2, y-1)`.
    obtain ⟨hx4, hx6, hy3, hy7⟩ := hMargins
    have heq : e = normalSquareVerticalTranslatedEdge
        (e.1.1.1.1 - 2) (e.1.1.2.1 - 1) (by omega) (by omega) := by
      rw [normalSquareVerticalTranslatedEdge_sub_eq_upEdge
        (by omega) (by omega) (by omega) (by omega)]
      exact verticalSquareLatticeEdge_eq_upEdge e hEdge
    rw [heq]
    exact exists_absorbingGauge_normalSquareVerticalTranslatedEdge A B hA hUA hB hUB
      (by omega) (by omega) (by omega) (by omega) hbond hAB hd hposA hposB

/-- **The interior absorbed gauge family on the open square lattice.**

For two tensors on the open square lattice with the rectangular-injectivity hypotheses, union
closure, matched bond dimensions, the same state, and positive bonds, there is a per-edge gauge
family `X` over the second tensor's bonds satisfying the bare-edge absorbed equality against
`applyGauge B X` at every edge with interior margins: inserting `N` on `A`'s edge `e` matches
inserting the reindexed `N` on `applyGauge B X`'s edge `e`, for every global physical
configuration and every matrix.

The family is built edge by edge: each interior edge receives its own absorbing gauge
(`exists_absorbingGauge_of_normalSquareInteriorEdgeDatum`), and edges without interior margins
receive the identity.  Because the bare-edge identity at an edge constrains only the family's
value there, no compatibility between the choices is needed.  No covariance between the gauges
of distinct edges is asserted; the translation-invariant reduction to one horizontal and one
vertical matrix has no carrier on the open lattice, which carries no translations.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1544 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem exists_normalSquareInteriorAbsorbedGaugeFamily
    (A B : Tensor (squareLatticeGraph width height) d)
    (hA : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hUA : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) A))
    (hB : NormalSquareLatticeRectangleInjectivityHypotheses
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
            (regionInjectivityDataOf (G := squareLatticeGraph width height) B))
    (hbond : A.bondDim = B.bondDim) (hAB : SameState A B) (hd : 0 < d)
    (hposA : ∀ g : Edge (squareLatticeGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (squareLatticeGraph width height), 0 < B.bondDim g) :
    ∃ X : (e : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim e)) ℂ,
      ∀ e : Edge (squareLatticeGraph width height),
        NormalSquareInteriorEdgeDatum e →
        ∀ (σ : SquareLatticeVertex width height → Fin d)
          (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
          edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
            edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
              (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
  classical
  -- The per-edge selection: at interior edges the absorbing gauge, elsewhere the identity.
  have hsel : ∀ e : Edge (squareLatticeGraph width height),
      ∃ Ze : GL (Fin (B.bondDim e)) ℂ,
        NormalSquareInteriorEdgeDatum e →
        ∀ X : (g : Edge (squareLatticeGraph width height)) → GL (Fin (B.bondDim g)) ℂ,
          X e = Ze →
          ∀ (σ : SquareLatticeVertex width height → Fin d)
            (N : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ),
            edgeInsertedCoeff (G := squareLatticeGraph width height) A e σ N =
              edgeInsertedCoeff (G := squareLatticeGraph width height) (applyGauge B X) e σ
                (Matrix.reindexAlgEquiv ℂ ℂ (finCongr (congr_fun hbond e)) N) := by
    intro e
    by_cases he : NormalSquareInteriorEdgeDatum e
    · obtain ⟨Ze, hZe⟩ := exists_absorbingGauge_of_normalSquareInteriorEdgeDatum A B
        hA hUA hB hUB hbond hAB hd hposA hposB e he
      exact ⟨Ze, fun _ => hZe⟩
    · exact ⟨1, fun hcon => absurd hcon he⟩
  choose X hX using hsel
  exact ⟨X, fun e he σ N => hX e he X rfl σ N⟩

end PEPS
end TNLean
