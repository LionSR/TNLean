import TNLean.PEPS.RegionTransportData
import TNLean.PEPS.TorusTranslationInvariant

/-!
# Translation of one-edge blocking data on the torus

A translation-invariant tensor on the discrete torus satisfies
`A.transport (translate a b) = A`, so transporting a one-edge blocking datum along the
translation automorphism produces a one-edge blocking datum **for the same tensor** at the
translated edge.  This carries one reference blocking datum at the reference edge of an
orientation class to a datum at every edge of that class
(`translateBlockingData`), and the red-to-blue crossing carries across
(`isCrossingEdge_translateBlockingData`).

This is the torus realization of the source's translation step
(arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498): once the edge blocking is fixed at
one edge, translation invariance reproduces it at every translate, so the per-edge gauges are
the same across each orientation class.  The bridge from `transportBlockingDataAlong` to the
torus is `translateEdge a b e = Edge.map (translate a b) e` and the fixed-point equation
`A.transport (translate a b) = A`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines
  1407--1572 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- For a translation-invariant tensor, the region-injectivity predicate of the translated
tensor equals that of the tensor itself, so a blocking datum over the translated tensor is a
blocking datum over the tensor. -/
theorem regionInjectivityDataOf_translate_eq {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height) :
    regionInjectivityDataOf (G := torusGraph width height) (A.transport (translate a b)) =
      regionInjectivityDataOf (G := torusGraph width height) A := by
  rw [hA a b]

/-- **Translation of a one-edge blocking datum on the torus.**

For a translation-invariant tensor `A`, a one-edge blocking datum at the edge `e` gives a
one-edge blocking datum at the translated edge `translateEdge a b e`, for the *same* tensor.
The three blocks are the translates of the original blocks (read off
`transportBlockingDataAlong` of the translation automorphism); injectivity uses the fixed-point
equation `A.transport (translate a b) = A`.

The fields are stated explicitly (rather than by transporting the structure across the
fixed-point equation) so the red, blue, and complement projections are definitional, which the
single-crossing hypothesis and the gauge interface consume.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def translateBlockingData {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) (translateEdge a b e) :=
  let D' := transportBlockingDataAlong A (translate a b) D
  { red := D'.red
    blue := D'.blue
    complement := D'.complement
    left_mem_red := by rw [translateEdge_eq_map]; exact D'.left_mem_red
    right_mem_blue := by rw [translateEdge_eq_map]; exact D'.right_mem_blue
    red_injective := regionInjectivityDataOf_translate_eq hA a b ▸ D'.red_injective
    blue_injective := regionInjectivityDataOf_translate_eq hA a b ▸ D'.blue_injective
    complement_injective :=
      regionInjectivityDataOf_translate_eq hA a b ▸ D'.complement_injective
    red_disjoint_blue := D'.red_disjoint_blue
    red_disjoint_complement := D'.red_disjoint_complement
    blue_disjoint_complement := D'.blue_disjoint_complement
    cover_univ := D'.cover_univ }

@[simp] theorem translateBlockingData_red {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e) :
    (translateBlockingData hA a b D).red =
      (transportBlockingDataAlong A (translate a b) D).red := rfl

@[simp] theorem translateBlockingData_blue {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e) :
    (translateBlockingData hA a b D).blue =
      (transportBlockingDataAlong A (translate a b) D).blue := rfl

@[simp] theorem translateBlockingData_complement {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e) :
    (translateBlockingData hA a b D).complement =
      (transportBlockingDataAlong A (translate a b) D).complement := rfl

/-- **The single red-to-blue crossing of the translated datum is the translated edge.**

If the red-to-blue crossings of the reference datum `D` are exactly the reference edge `e`,
then the red-to-blue crossings of the translated datum are exactly the translated edge
`translateEdge a b e`.  The translated datum's blocks are the translation images of `D`'s
blocks, so crossing transports along the translation; the crossing condition is independent of
the tensor, so it holds for `A` itself.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_translateBlockingData {A : Tensor (torusGraph width height) d}
    (hA : IsTorusTranslationInvariant A) (a : ZMod width) (b : ZMod height)
    {e : Edge (torusGraph width height)}
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) e)
    (hsingle : ∀ g : Edge (torusGraph width height),
      IsCrossingEdge (G := torusGraph width height) A D.red D.blue g ↔ g = e)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A (translateBlockingData hA a b D).red
        (translateBlockingData hA a b D).blue g ↔
      g = translateEdge a b e := by
  rw [translateBlockingData_red, translateBlockingData_blue, translateEdge_eq_map]
  -- `IsCrossingEdge` ignores the tensor, so the crossing for `A` equals the crossing for
  -- `A.transport (translate a b)`; the latter transports by the datum-along lemma.
  exact isCrossingEdge_transportBlockingDataAlong A (translate a b) D hsingle g

end PEPS
end TNLean
