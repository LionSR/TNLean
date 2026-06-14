import TNLean.PEPS.TorusWindowMult

/-!
# The window-region witness from the single-vertex realization on the left end window

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`) feeds
the window-region witness `windowEdgeCoeffIdentityWitness` a single-bond conjugation coefficient
identity on the reference edge `e`.  The reduction
`exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer` (`TNLean/PEPS/TorusWindowMult.lean`)
produces the witness from three separate inputs: the two cross-tensor coefficient transfers
`htransferAB`/`htransferBA` and the forward-transfer multiplicativity `hmul`.  This file collapses
all three of those inputs to a single block of data --- the region physical-to-virtual realization
on the left end window, in each direction --- and records the two facts that fix the precise
boundary of the construction.

## The injectivity engine is available from window and host injectivity

The window-level edge-insertion injectivity `windowRegionInsertedCoeff_injective` is the concrete
instance of the unconditional region injectivity `regionInsertedCoeff_injective`
(`TNLean/PEPS/RegionBlock/Algebra.lean`) at the left end window: two matrices on the reference edge
`e` giving the same region-inserted coefficient at every window/host physical configuration are
equal.  It is discharged from exactly the window's region injectivity
(`horizontalStaircaseLeftWindow_injective`) and the single-window host injectivity
(`regionBlockedTensorInjective_windowComplement`), both available at the corollary's minimal size,
with no single-vertex spanning.  This is the affirmative half of the boundary: window and host
injectivity *do* power the read-off side --- the inserted matrix is determined by its window
coefficient.

## The multiplicativity is the single-vertex realization residual

What window and host injectivity do *not* supply is the multiplicativity `hmul`.  The forward
transfer of a product `M * M'` on the reference edge is a single matrix product on the bond; reading
it as the product of the two transferred matrices is the homomorphism the source takes from the
physical realization of the inserted operator.  That realization is the region physical-to-virtual
pullback `RegionTransferRealizes` at `e`'s in-region endpoint, which couples the inserted matrix to
the recovered matrix through the single-vertex spanning at that endpoint --- absent for a normal
(region-injective, not vertex-injective) tensor.  The bond product does not decompose at the window
level: there is no internal sum over an intermediate bond configuration to split `M * M'` into a
composition of two separate insertions, so the injectivity engine, although it reduces `hmul` to a
coefficient identity, cannot produce that identity on its own.

`exists_windowEdgeCoeffIdentityWitness_of_realizes` therefore takes the two-directional realization
in place of the three transfer inputs: `regionInsertionTransfer_of_realizes`
(`TNLean/PEPS/RegionBlock/Recovery3.lean`) builds the transfer datum from it, supplying the
coefficient transfers, the unital field, *and* the multiplicativity in one step
(`regionTransferMatrix_mul_of_realizes`), and the datum feeds the landed witness packaging
`exists_windowEdgeCoeffIdentityWitness_of_transfer`.  This is the precise statement of what the
staircase must supply: the single-vertex realization on the window, in each direction, with the
matched bond dimensions and the same state, is the irreducible core the corollary still needs.  The
host injectivity is the single-window complement at the minimal size, in contrast to the rectangle
red block's host, which fails there.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964](https://arxiv.org/abs/1804.04964), Section 3, Lemma
  `inj_isomorph`, lines 254--586 of `Papers/1804.04964/paper_normal.tex`, and the corollary at lines
  2297--2318; the filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1,
  and the single-vertex endpoint-spanning residual in
  `docs/paper-gaps/peps_normal_ft_section3_route.tex`.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The window-level edge-insertion injectivity from window and host injectivity

Two matrices on the reference edge `e` giving the same region-inserted coefficient at every
window/host physical configuration are equal.  This is the left-end-window instance of the
unconditional region injectivity `regionInsertedCoeff_injective`, discharged from the window's
region injectivity and the single-window host injectivity, both available at the minimal size. -/

/-- **The window-level edge-insertion injectivity.**

If two matrices `M`, `M'` on the reference edge `e` of the left end window give the same
region-inserted coefficient at every window/host physical configuration, they are equal.  The
window's region injectivity is `horizontalStaircaseLeftWindow_injective`; its host injectivity is
the single-window complement `regionBlockedTensorInjective_windowComplement`, both at the
corollary's minimal size.  No single-vertex spanning enters: this is the concrete instance of the
unconditional region injectivity `regionInsertedCoeff_injective`
(`TNLean/PEPS/RegionBlock/Algebra.lean`), the read-off side that window and host injectivity power.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 377--457 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem windowRegionInsertedCoeff_injective
    {B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (M M' : Matrix (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (hMM' : ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
        (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
          (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
        regionInsertedCoeff (G := torusGraph width height) B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge B (by omega)
              (by omega) ha0 haw hbh⟩ M σ τ =
          regionInsertedCoeff (G := torusGraph width height) B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge B (by omega)
              (by omega) ha0 haw hbh⟩ M' σ τ) :
    M = M' := by
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  exact regionInsertedCoeff_injective (G := torusGraph width height) B
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    hRB (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _) hposB
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge B (by omega) (by omega)
      ha0 haw hbh⟩ M M' hMM'

/-! ### The window witness from the two-directional single-vertex realization

The region physical-to-virtual realization on the left end window, in each direction, builds the
`RegionInsertionTransfer` datum through `regionInsertionTransfer_of_realizes` --- supplying the two
coefficient transfers, the unital field, and the forward multiplicativity together --- and the
datum feeds the landed witness packaging `exists_windowEdgeCoeffIdentityWitness_of_transfer`.  This
collapses the three separate inputs of `exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer`
(`htransferAB`, `htransferBA`, `hmul`) to one block of data, isolating the irreducible core: the
single-vertex realization at `e`'s in-region endpoint. -/

/-- **The window-region witness from the single-vertex realization.**

With the arc-window injectivity hypotheses and union closure for both tensors, the size hypotheses,
matched bond dimensions, the same state, positive bonds, the single-vertex linear independence
`hvA`/`hvB` at the reference edge's in-region endpoint, and the region physical-to-virtual
realization on the left end window in each direction (`hrealAB`/`hrealBA`), the reference edge
carries an `EdgeCoeffIdentityWitness` whose per-edge and reference gauges are both the gauge read
off the transfer.

`regionInsertionTransfer_of_realizes` builds the `RegionInsertionTransfer` datum from the two
realizations --- the coefficient transfers, the unital field, and the forward multiplicativity in
one step --- and `exists_windowEdgeCoeffIdentityWitness_of_transfer` packages it into the witness.
The host injectivity is the single-window complement at the minimal size; the region injectivity is
the window injectivity from the arc-window hypotheses.  This collapses the three separate transfer
inputs to a single realization datum and is the precise statement of what the staircase must supply
for the multiplicativity: the single-vertex realization at `e`'s in-region endpoint, absent for a
normal tensor and recorded in `docs/paper-gaps/peps_normal_ft_section3_route.tex`.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem exists_windowEdgeCoeffIdentityWitness_of_realizes
    {A B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hA : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUA : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) A))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (hAB : SameState A B)
    (hposA : ∀ g : Edge (torusGraph width height), 0 < A.bondDim g)
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hDim : A.bondDim = B.bondDim)
    (hvA : LinearIndependent ℂ (A.component (regionBoundaryEdgeInVertex
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩)))
    (hvB : LinearIndependent ℂ (B.component (regionBoundaryEdgeInVertex
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩)))
    (hrealAB : RegionTransferRealizes (G := torusGraph width height) A B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩ hvA hvB hposB)
    (hrealBA : RegionTransferRealizes (G := torusGraph width height) B A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩ hvB hvA hposA) :
    ∃ (Z Zref : GL (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
      (hE : A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
        B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)),
      Nonempty (EdgeCoeffIdentityWitness A B
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)
        Z Zref hE) := by
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  exact exists_windowEdgeCoeffIdentityWitness_of_transfer hA hB hUA hUB hL hK ha0 haw hbh hxw hyh
    hposA hposB
    (regionInsertionTransfer_of_realizes A B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩ hvA hvB hAB hRB
      (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
      hposA hposB hDim hrealAB hrealBA)

end PEPS
end TNLean
