import TNLean.PEPS.SingletonEdgeBlockingData
import TNLean.PEPS.TorusTranslationInvariant

/-!
# The concrete torus reference blocking datum

For a vertex-injective torus tensor with positive bond dimensions, the singleton-endpoint blocking
datum (`singletonEdgeBlockingData`) supplies a reference one-edge blocking datum at the reference
horizontal edge `torusRightEdge 0` and the reference vertical edge `torusUpEdge 0` of the two
orientation classes.  This is the concrete reference datum the translation-invariant gauge family
consumes: translation carries it to every edge of its class (`translateBlockingData`), and the
single red-to-blue crossing is the reference edge itself.

The wraparound geometry of the torus never enters.  The open-lattice every-edge construction needs
wraparound-avoiding rectangles with size bounds because it works at rectangle granularity, where
only sufficiently large regions are injective.  Under vertex injectivity every finite region is
injective, so singleton endpoint blocks suffice and the construction is unconditional on the torus
dimensions beyond the nontriviality `1 < width`, `1 < height` that make the graph loopless.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, Section 3, proof of Theorem 3, lines 981--1009 and
  1407--1500 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### Reference horizontal blocking datum -/

/-- **Reference horizontal blocking datum on the torus.**

For a vertex-injective torus tensor with positive bond dimensions, the reference horizontal edge
`torusRightEdge 0` carries the singleton-endpoint blocking datum: its red block is the left
endpoint, its blue block the right endpoint, and its complement the rest of the torus.  All three
are injective, they partition the torus, and the single red-to-blue crossing is the reference edge.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 981--1009 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def torusHorizontalReferenceBlockingDatum
    (A : Tensor (torusGraph width height) d)
    (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge (torusGraph width height), 0 < A.bondDim f) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) (torusRightEdge 0) :=
  singletonEdgeBlockingData A (torusRightEdge 0) hA hpos

/-- The red-to-blue crossings of the reference horizontal blocking datum are exactly the reference
horizontal edge `torusRightEdge 0`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusHorizontalReferenceBlockingDatum
    (A : Tensor (torusGraph width height) d)
    (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge (torusGraph width height), 0 < A.bondDim f)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusHorizontalReferenceBlockingDatum A hA hpos).red
        (torusHorizontalReferenceBlockingDatum A hA hpos).blue g ↔
      g = torusRightEdge 0 :=
  isCrossingEdge_singletonEdgeBlockingData A (torusRightEdge 0) hA hpos g

/-! ### Reference vertical blocking datum -/

/-- **Reference vertical blocking datum on the torus.**

The vertical counterpart of `torusHorizontalReferenceBlockingDatum` at the reference vertical edge
`torusUpEdge 0`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 981--1009 of
`Papers/1804.04964/paper_normal.tex`. -/
noncomputable def torusVerticalReferenceBlockingDatum
    (A : Tensor (torusGraph width height) d)
    (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge (torusGraph width height), 0 < A.bondDim f) :
    NormalEdgeBlockingData (regionInjectivityDataOf (G := torusGraph width height) A)
      (torusGraph width height) (torusUpEdge 0) :=
  singletonEdgeBlockingData A (torusUpEdge 0) hA hpos

/-- The red-to-blue crossings of the reference vertical blocking datum are exactly the reference
vertical edge `torusUpEdge 0`.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1500 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem isCrossingEdge_torusVerticalReferenceBlockingDatum
    (A : Tensor (torusGraph width height) d)
    (hA : IsVertexInjective A)
    (hpos : ∀ f : Edge (torusGraph width height), 0 < A.bondDim f)
    (g : Edge (torusGraph width height)) :
    IsCrossingEdge (G := torusGraph width height) A
        (torusVerticalReferenceBlockingDatum A hA hpos).red
        (torusVerticalReferenceBlockingDatum A hA hpos).blue g ↔
      g = torusUpEdge 0 :=
  isCrossingEdge_singletonEdgeBlockingData A (torusUpEdge 0) hA hpos g

end PEPS
end TNLean
