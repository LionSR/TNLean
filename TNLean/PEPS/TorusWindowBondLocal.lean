import TNLean.PEPS.TorusWindowMult
import TNLean.PEPS.RegionBlock.ThreeBlockTransfer

/-!
# The window witness from two-directional bond locality on the left end window

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`) feeds
the window-region witness `windowEdgeCoeffIdentityWitness` a single-bond conjugation coefficient
identity on the reference edge `e`.  The reduction
`exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer` (`TNLean/PEPS/TorusWindowMult.lean`)
produces the witness from the two cross-tensor coefficient transfers and the forward-transfer
multiplicativity.  This file restates that reduction with its two coefficient-transfer inputs
replaced by the single block-frame predicate they reduce to --- *bond locality of the transfer
kernel* on the left end window --- so the unconditional window witness assembles from exactly the
two genuinely-new staircase residuals: two-directional bond locality and forward multiplicativity.

## The packaging

The block-frame coefficient transfer of `TNLean/PEPS/RegionBlock/BlockCoeffTransfer.lean` is
unconditional on the window's region and host injectivity, both available at the corollary's minimal
size (the host by `regionBlockedTensorInjective_windowComplement`).  By
`bondLocal_iff_coeffTransfer`, the cross-tensor coefficient transfer
`∀ M, ∃ N, regionInsertedCoeff A W ⟨e⟩ M = regionInsertedCoeff B W ⟨e⟩ N` on the left window is
*equivalent* to bond locality of the transfer kernel `IsBondLocalTransferKernel A B W ⟨e⟩`: the
kernel read off the two blocked left inverses of `B` couples the two boundary configurations only
through their legs on `e`.  Feeding the two directions of bond locality through
`coeffTransfer_of_bondLocal` builds the two coefficient transfers `htransferAB`/`htransferBA`, and
the forward multiplicativity `hmul` over the chosen forward transfer completes the input the witness
reduction consumes.

This isolates the residual of the window route to exactly the two block-frame inputs.  Everything
else --- the four window/host injectivities, the additivity, homogeneity, identity preservation, the
two-sided inverse, the Skolem--Noether read-off, and the witness packaging --- is the unconditional
region-level algebra discharged here from the torus arc-window injectivity hypotheses.

## The port verdict

The one-dimensional operator-transport mechanism `MPSChainTensor.exists_insertionHom`
(`TNLean/PEPS/CycleMPSChainOverlapInsertion.lean`) builds a multiplicative bond homomorphism from
*window spanning*: a length-`L` chain window has a left bond and a right bond, both of dimension
`D`, so the window product is a `D × D` matrix and window injectivity is the statement that these
products span the full matrix algebra at the single bond.  In two dimensions a single end window
touches the reference edge `e` with one endpoint, so the `e`-leg is a single
`Fin (bondDim e)` index --- a vector, not a square matrix --- and window injectivity
`RegionBlockedTensorInjective` is linear independence across the window's whole multi-bond
perimeter, not a single-bond matrix-algebra span.  No per-window square-matrix family exists, so the
matrix-intertwining route does not transfer per window; the forward multiplicativity must come from
the cross-tensor physical-realization homomorphism, whose region read-off currently needs the
single-vertex spanning `span_stateOpenCoeff_eq_top` at `e`'s in-region endpoint (absent for a normal
tensor).  This is the residual `hbondAB`/`hbondBA`/`hmul` packaged here, recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1--5.2.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-! ### The cross-tensor coefficient transfers on the left window from bond locality

Bond locality of the transfer kernel on the left end window, in each direction, is turned into the
cross-tensor coefficient transfer by `coeffTransfer_of_bondLocal`.  The window's region injectivity
is `horizontalStaircaseLeftWindow_injective`, and its host injectivity is the single-window
complement `regionBlockedTensorInjective_windowComplement`, both at the corollary's minimal size. -/

/-- The forward window coefficient transfer from bond locality: for each inserted matrix `M` on the
reference edge `e` of the left window for `A`, a matrix `N` for `B` with matching region-inserted
coefficient.  This is `coeffTransfer_of_bondLocal` on the left window, with the window's region
injectivity and host injectivity discharged from the torus arc-window hypotheses.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem windowCoeffTransferAB_of_bondLocal {A B : Tensor (torusGraph width height) d}
    {L K a b : ℕ}
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
    (hbondAB : IsBondLocalTransferKernel (G := torusGraph width height) A B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (by
        have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩) :
    ∀ M : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ N : Matrix (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (B.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ M σ τ =
            regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ N σ τ := by
  have hRA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hA.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  exact coeffTransfer_of_bondLocal A B
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    hRA hRB (hA.regionBlockedTensorInjective_windowComplement hUA hL hK hxw hyh _)
    (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
    hAB hposA hposB
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
      ha0 haw hbh⟩ hbondAB

/-- The backward window coefficient transfer from bond locality: for each inserted matrix `N` on the
reference edge `e` of the left window for `B`, a matrix `M` for `A` with matching region-inserted
coefficient.  This is `coeffTransfer_of_bondLocal` on the left window with the two tensors swapped.

Source: arXiv:1804.04964, Section 3, Lemma `inj_isomorph`, lines 254--586 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem windowCoeffTransferBA_of_bondLocal {A B : Tensor (torusGraph width height) d}
    {L K a b : ℕ}
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
    (hbondBA : IsBondLocalTransferKernel (G := torusGraph width height) B A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (by
        have hi := hA.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (hA.regionBlockedTensorInjective_windowComplement hUA hL hK hxw hyh _)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩) :
    ∀ N : Matrix (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (B.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      ∃ M : Matrix (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
          (Fin (A.bondDim
            (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
        ∀ (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
          (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
            (Finset.univ \
              horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
          regionInsertedCoeff (G := torusGraph width height) B
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ N σ τ =
            regionInsertedCoeff (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
              ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
                (by omega) ha0 haw hbh⟩ M σ τ := by
  have hRA : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hA.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  have hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) := by
    have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
    rwa [regionInjectivityDataOf_isInjective] at hi
  exact coeffTransfer_of_bondLocal B A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    hRB hRA (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
    (hA.regionBlockedTensorInjective_windowComplement hUA hL hK hxw hyh _)
    hAB.symm hposB hposA
    ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
      ha0 haw hbh⟩ hbondBA

/-! ### The unconditional window witness from two-directional bond locality

Feeding the two coefficient transfers built from bond locality, together with the forward
multiplicativity over the chosen forward transfer, to the witness reduction
`exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer`.  The witness assembles from exactly the
two genuinely-new staircase residuals --- two-directional bond locality `hbondAB`/`hbondBA` and
forward multiplicativity `hmul` --- with every region/host injectivity discharged from the torus
arc-window hypotheses. -/

/-- **The window-region witness from two-directional bond locality on the left end window.**

With the arc-window injectivity hypotheses and union closure for both tensors, the size hypotheses,
matched bond dimensions, the same state, positive bonds, bond locality of the left-window transfer
kernel in both directions, and the forward-transfer multiplicativity, the reference edge carries an
`EdgeCoeffIdentityWitness` whose per-edge and reference gauges are both the gauge `Z` read off the
transfer.  The two coefficient transfers the witness reduction consumes are
`windowCoeffTransferAB_of_bondLocal` and `windowCoeffTransferBA_of_bondLocal`; bond locality is the
block-frame predicate the cross-tensor coefficient transfer reduces to
(`bondLocal_iff_coeffTransfer`, unconditional on the window/host injectivity available at the
minimal size).

This is the §5.2 packaging with the two coefficient-transfer inputs of
`exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer` replaced by the single block-frame
predicate `IsBondLocalTransferKernel` they reduce to.  The residual is exactly
`hbondAB`/`hbondBA`/`hmul`: the forward multiplicativity is the cross-tensor physical-realization
homomorphism the one-dimensional matrix-intertwining port cannot supply per window (the `e`-leg is a
vector, not a square matrix), and bond locality is the single-vertex-spanning content
`span_stateOpenCoeff_eq_top` at `e`'s in-region endpoint, absent for a normal tensor.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1--5.2. -/
theorem exists_windowEdgeCoeffIdentityWitness_of_bondLocal
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
    (hbondAB : IsBondLocalTransferKernel (G := torusGraph width height) A B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (by
        have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩)
    (hbondBA : IsBondLocalTransferKernel (G := torusGraph width height) B A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
      (by
        have hi := hA.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
        rwa [regionInjectivityDataOf_isInjective] at hi)
      (hA.regionBlockedTensorInjective_windowComplement hUA hL hK hxw hyh _)
      ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega) (by omega)
        ha0 haw hbh⟩)
    (hmul : ∀ M M' : Matrix (Fin (A.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ,
      coeffTransferMap (G := torusGraph width height) A B
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
            (by omega) ha0 haw hbh⟩
          (windowCoeffTransferAB_of_bondLocal hA hB hUA hUB hL hK ha0 haw hbh hxw hyh hAB
            hposA hposB hbondAB) (M * M') =
        coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
              (by omega) ha0 haw hbh⟩
            (windowCoeffTransferAB_of_bondLocal hA hB hUA hUB hL hK ha0 haw hbh hxw hyh hAB
              hposA hposB hbondAB) M *
          coeffTransferMap (G := torusGraph width height) A B
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
            ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
              (by omega) ha0 haw hbh⟩
            (windowCoeffTransferAB_of_bondLocal hA hB hUA hUB hL hK ha0 haw hbh hxw hyh hAB
              hposA hposB hbondAB) M') :
    ∃ (Z Zref : GL (Fin (B.bondDim
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
      (hE : A.bondDim
          (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
        B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)),
      Nonempty (EdgeCoeffIdentityWitness A B
        (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)
        Z Zref hE) :=
  exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer hA hB hUA hUB hL hK ha0 haw hbh hxw hyh
    hAB hposA hposB hDim
    (windowCoeffTransferAB_of_bondLocal hA hB hUA hUB hL hK ha0 haw hbh hxw hyh hAB
      hposA hposB hbondAB)
    (windowCoeffTransferBA_of_bondLocal hA hB hUA hUB hL hK ha0 haw hbh hxw hyh hAB
      hposA hposB hbondBA)
    hmul

end PEPS
end TNLean
