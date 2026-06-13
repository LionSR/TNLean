import TNLean.PEPS.TorusWindowPeel2
import TNLean.PEPS.TorusWindowComplement
import TNLean.PEPS.TorusConjCovarianceFamily

/-!
# The window-region coefficient-identity witness

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) feeds the torus covariant-family machinery an
`EdgeCoeffIdentityWitness` at one reference edge per orientation.  The rectangle route of
Theorem 3 takes the witness region to be the reference rectangle's red block, whose host is
injective only at the three-block sizes.  At the corollary's minimal size $(2L+1)\times(2K+1)$ the
host of the rectangle red block is not a union of injective windows, but the host of a *single end
window* is: this is the landed `regionBlockedTensorInjective_windowComplement`, whose complement
decomposition needs exactly $2L+1\le\mathrm{width}$, $2K+1\le\mathrm{height}$.

This file packages a window-region witness.  Every field except the conjugation coefficient
identity is supplied at the minimal size by landed window geometry: the reference edge is a
boundary edge of the left end window, the window is region injective, and its host is injective by
`regionBlockedTensorInjective_windowComplement`.  The conjugation coefficient identity is the
genuinely-new single-bond peeling of the staircase end-pair equality (the residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1), supplied here as a hypothesis: given the
identity, the witness assembles unconditionally, which is the §5.2 packaging the note describes.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445, and Section 3 proof of Theorem 3 at lines 1449--1572 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the filled-in
  derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 4--5.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {width height d : ℕ} [NeZero width] [NeZero height]
  [Fact (1 < width)] [Fact (1 < height)]

/-- **The window-region coefficient-identity witness.**

For two torus tensors `A`, `B` with the left end window of the staircase around the reference edge
`e` injective for `B` (`hRB`) and its host injective for `B` (`hCB`, available at the minimal size
by `regionBlockedTensorInjective_windowComplement`), positive bonds for `B`, and the single-bond
conjugation coefficient identity on `e` realized by a gauge `Z` (`hid`, the §5.1 peeling supplied
as a hypothesis), the data assemble into an `EdgeCoeffIdentityWitness` whose region is the left end
window.  The reference gauge is taken to be `Z` as well, so both witness identities are `hid`.

This is the §5.2 packaging: the witness fields other than the conjugation identity are landed window
geometry, host injectivity available at the minimal size; the identity itself is the genuinely-new
peeling of `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.  The window region's host
injectivity is what makes a single window a valid witness region at the corollary's minimal size,
in place of the rectangle red block whose host fails there.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.2. -/
noncomputable def windowEdgeCoeffIdentityWitness
    {A B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (Z : GL (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (hE : A.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
      B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))
    (hRB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hCB : RegionBlockedTensorInjective (G := torusGraph width height) B
      (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hid : ∀ (M : Matrix (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
      regionInsertedCoeff (G := torusGraph width height) A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh⟩
          M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh⟩
          ((Z : Matrix _ _ ℂ) * Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix _ _ ℂ)) σ τ) :
    EdgeCoeffIdentityWitness A B
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) Z Z hE where
  region := horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K
  isBoundary := isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh
  hRB := hRB
  hCB := hCB
  hposB := hposB
  hidZ := hid
  hidZref := hid

/-- **The window-region witness from the window injectivity hypotheses.**

The assembled form of `windowEdgeCoeffIdentityWitness`: with `B` satisfying the one-orientation
window injectivity hypotheses and union closure, the left end window's region injectivity (`hRB`)
and host injectivity (`hCB`) are discharged from the hypotheses at the minimal size, so the only
remaining input is the single-bond conjugation coefficient identity `hid` (the §5.1 peeling).  The
host injectivity is the landed `regionBlockedTensorInjective_windowComplement`, available exactly at
$2L+1\le\mathrm{width}$, $2K+1\le\mathrm{height}$.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1449--1572 of
`Papers/1804.04964/paper_normal.tex`; the corollary at lines 2297--2318;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.2. -/
noncomputable def windowEdgeCoeffIdentityWitness_of_hypotheses
    {A B : Tensor (torusGraph width height) d} {L K a b : ℕ}
    (hB : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (Z : GL (Fin (B.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
    (hE : A.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) =
      B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K))
    (hposB : ∀ g : Edge (torusGraph width height), 0 < B.bondDim g)
    (hid : ∀ (M : Matrix (Fin (A.bondDim (horizontalStaircaseReferenceEdge
        ((a : ZMod width), (b : ZMod height)) L K)))
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K))) ℂ)
      (σ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
      (τ : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
        (Finset.univ \ horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)),
      regionInsertedCoeff (G := torusGraph width height) A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
            (by omega) ha0 haw hbh⟩ M σ τ =
        regionInsertedCoeff (G := torusGraph width height) B
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          ⟨_, isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A (by omega)
            (by omega) ha0 haw hbh⟩
          ((Z : Matrix _ _ ℂ) * Matrix.reindexAlgEquiv ℂ ℂ (finCongr hE) M *
            (↑Z⁻¹ : Matrix _ _ ℂ)) σ τ) :
    EdgeCoeffIdentityWitness A B
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) Z Z hE :=
  windowEdgeCoeffIdentityWitness (by omega) (by omega) ha0 haw hbh Z hE
    (by
      have hi := hB.horizontalStaircaseLeftWindow_injective ((a : ZMod width), (b : ZMod height))
      rwa [regionInjectivityDataOf_isInjective] at hi)
    (hB.regionBlockedTensorInjective_windowComplement hUB hL hK hxw hyh _)
    hposB hid

end PEPS
end TNLean
