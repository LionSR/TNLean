import TNLean.PEPS.TorusWindowBondTransport
import TNLean.PEPS.TorusTranslationInvariant
import TNLean.PEPS.RegionTransport

/-!
# The uniform interior-bond product of the staircase windows under translation invariance

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`) is the
strengthening of the *torus* Theorem 3, whose tensors are translation invariant
(`IsTorusTranslationInvariant`).  This file records the consequence of that translation invariance
that the per-consecutive-window bond transport
`horizontalStaircaseConsecutiveWindow_bondTransport_extend_eq`
(`TNLean/PEPS/TorusWindowBondTransport.lean`) needs to glue into a single common-state family: every
staircase window `W_j` has the *same* interior-bond product `regionInteriorBondProd`.

## The mechanism

Each staircase window is an `L × K` cyclic rectangle `torusArcRectangle`, and any two such
rectangles of the same dimensions are translates of one another.  The interior-bond product is the
product of the bond dimensions over the edges interior to the region (the non-boundary edges); a
translation carries the interior edges of one rectangle bijectively onto those of its translate
(`regionInteriorBondProd_map`, the edge action reindexing the product), and a translation-invariant
tensor has equal bond dimensions on an edge and its translate
(`bondDim_translateEdge_of_translationInvariant`).  So the interior-bond product is invariant under
translation (`regionInteriorBondProd_translate_of_translationInvariant`), hence independent of the
rectangle's start vertex (`regionInteriorBondProd_torusArcRectangle_eq`), hence equal for every
window of the staircase (`regionInteriorBondProd_staircaseWindow_eq`).

This is the translation-invariance input that turns the neighbour-dependent rescaling of the
per-step bond transport into a uniform one: the per-step transport scales window `W_j` by
`regionInteriorBondProd W_{j+1}` and `W_{j+1}` by `regionInteriorBondProd W_j`, and under
translation invariance both equal one common constant, so the rescalings agree across the whole
chain and the per-step transports glue into a single common-state family.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary at lines 2297--2318 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the filled-in derivation
  in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1.
-/

open scoped BigOperators

namespace TNLean
namespace PEPS

/-! ### The interior-bond product under a graph isomorphism

The interior-bond product of an image region `Region.map φ R`, reindexed by the edge action of
`φ`, is the product of the *transported* bond dimensions over the interior edges of `R`. -/

section General

variable {V : Type*} [Fintype V] [LinearOrder V] {W : Type*} [Fintype W] [LinearOrder W]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {G' : SimpleGraph W} [DecidableRel G'.Adj]
variable {d : ℕ}

omit [Fintype V] [Fintype W] [DecidableRel G.Adj] [DecidableRel G'.Adj] in
/-- An edge `e'` of the image graph crosses the boundary of the image region `Region.map φ R` iff
its preimage `Edge.map φ.symm e'` crosses the boundary of `R`.  This is `isRegionBoundaryEdge_map`
read at the preimage edge, the round trip `Edge.map φ (Edge.map φ.symm e') = e'` collapsing the
image action. -/
theorem isRegionBoundaryEdge_map' (φ : G ≃g G') (R : Finset V) (e' : Edge G') :
    IsRegionBoundaryEdge (G := G') (Region.map φ R) e' ↔
      IsRegionBoundaryEdge (G := G) R (Edge.map φ.symm e') := by
  have h := isRegionBoundaryEdge_map φ R (Edge.map φ.symm e')
  rwa [Edge.map_map_symm] at h

/-- **The interior-bond product of an image region.**  The interior-bond product of
`Region.map φ R` is the product over the interior (non-boundary) edges of `R` of the bond dimension
of the *transported* tensor at the image edge.  The interior edges of the image region are exactly
the images of the interior edges of `R` under the edge action (`isRegionBoundaryEdge_map'`),
reindexing the product by the edge bijection `Edge.equiv φ`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1407--1500 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem regionInteriorBondProd_map (A' : Tensor G' d) (φ : G ≃g G') (R : Finset V) :
    regionInteriorBondProd (G := G') A' (Region.map φ R) =
      ∏ e ∈ Finset.univ.filter (fun e : Edge G => ¬ IsRegionBoundaryEdge (G := G) R e),
        A'.bondDim (Edge.map φ e) := by
  classical
  rw [regionInteriorBondProd]
  refine Finset.prod_nbij' (fun e' => Edge.map φ.symm e') (fun e => Edge.map φ e) ?_ ?_ ?_ ?_ ?_
  · intro e' he'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he' ⊢
    rwa [isRegionBoundaryEdge_map'] at he'
  · intro e he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
    rw [isRegionBoundaryEdge_map', Edge.map_symm_map]; exact he
  · intro e' _; simp [Edge.map_map_symm]
  · intro e _; simp [Edge.map_symm_map]
  · intro e' he'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he'
    rw [Edge.map_map_symm]

end General

/-! ### The uniform interior-bond product on the torus

A translation-invariant torus tensor has the same interior-bond product on a region and its
translate, hence on any two cyclic rectangles of the same dimensions, hence on every window of the
staircase. -/

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ}

/-- The image of a cyclic rectangle under a translation is the cyclic rectangle with the translated
start vertex: translating shifts the start by `(a, b)`. -/
theorem Region_map_translate_torusArcRectangle (a : ZMod width) (b : ZMod height)
    (s : TorusVertex width height) (xLen yLen : ℕ) :
    Region.map (translate a b) (torusArcRectangle s xLen yLen) =
      torusArcRectangle (s.1 + a, s.2 + b) xLen yLen := by
  ext v
  rw [mem_Region_map, mem_torusArcRectangle, mem_torusArcRectangle,
    show ((translate a b).symm v) = (v.1 - a, v.2 - b) from rfl]
  refine and_congr ?_ ?_
  · rw [show v.1 - (s.1 + a) = (v.1 - a) - s.1 by ring]
  · rw [show v.2 - (s.2 + b) = (v.2 - b) - s.2 by ring]

/-- **Translation invariance of the interior-bond product.**  A translation-invariant tensor has the
same interior-bond product on a region and on its translate: the interior-bond product of the image
is the product of the transported bond dimensions (`regionInteriorBondProd_map`), and translation
invariance equates the bond dimension at an edge and at its translate
(`bondDim_translateEdge_of_translationInvariant`).

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem regionInteriorBondProd_translate_of_translationInvariant
    {A : Tensor (torusGraph width height) d} (hA : IsTorusTranslationInvariant A)
    (a : ZMod width) (b : ZMod height) (R : Finset (TorusVertex width height)) :
    regionInteriorBondProd (G := torusGraph width height) A (Region.map (translate a b) R) =
      regionInteriorBondProd (G := torusGraph width height) A R := by
  rw [regionInteriorBondProd_map, regionInteriorBondProd]
  refine Finset.prod_congr rfl (fun e _ => ?_)
  rw [← translateEdge_eq_map, bondDim_translateEdge_of_translationInvariant hA]

/-- **The interior-bond product of a cyclic rectangle is start-independent under translation
invariance.**  Any two cyclic rectangles of the same dimensions are translates of one another, so a
translation-invariant tensor has the same interior-bond product on both.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, line 1498 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem regionInteriorBondProd_torusArcRectangle_eq
    {A : Tensor (torusGraph width height) d} (hA : IsTorusTranslationInvariant A)
    (s s' : TorusVertex width height) (xLen yLen : ℕ) :
    regionInteriorBondProd (G := torusGraph width height) A (torusArcRectangle s xLen yLen) =
      regionInteriorBondProd (G := torusGraph width height) A (torusArcRectangle s' xLen yLen) := by
  have h := regionInteriorBondProd_translate_of_translationInvariant hA (s.1 - s'.1) (s.2 - s'.2)
    (torusArcRectangle s' xLen yLen)
  rw [Region_map_translate_torusArcRectangle] at h
  rw [show (s'.1 + (s.1 - s'.1), s'.2 + (s.2 - s'.2)) = s by
    refine Prod.ext ?_ ?_ <;> simp [add_sub_cancel]] at h
  exact h

/-- **The uniform interior-bond product of the staircase windows.**  Under translation invariance,
every window `W_j` of the staircase family has the same interior-bond product, since each window is
an `L × K` cyclic rectangle and the interior-bond product of such a rectangle is start-independent.
This is the input that makes the neighbour-dependent rescaling of the per-step bond transport
uniform across the whole chain.

Source: arXiv:1804.04964, the corollary at lines 2297--2318 and the proof sketch at lines
2320--2445 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem regionInteriorBondProd_staircaseWindow_eq
    {A : Tensor (torusGraph width height) d} (hA : IsTorusTranslationInvariant A)
    (s : TorusVertex width height) (L K j j' : ℕ) :
    regionInteriorBondProd (G := torusGraph width height) A (staircaseWindow s L K j) =
      regionInteriorBondProd (G := torusGraph width height) A (staircaseWindow s L K j') := by
  rw [staircaseWindow, staircaseWindow]
  exact regionInteriorBondProd_torusArcRectangle_eq hA _ _ L K

end Torus

end PEPS
end TNLean
