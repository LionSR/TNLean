import TNLean.PEPS.RegionBlock.CoarseThreeSite7

/-!
# The single-crossing specialization of the whole-bundle inserted coefficient

The whole-bundle red inserted coefficient `TNLean.PEPS.redBundleInsertedCoeff` of
`TNLean.PEPS.RegionBlock.CoarseThreeSite6` couples two red boundary configurations
through the *whole* red-to-blue crossing bundle. The source's blocking is chosen so
that the red region crosses to the blue region across a **single** edge `e` (the
distinguished edge): the red sites surround the left endpoint, the blue sites surround
the right endpoint, and `e` is the only edge whose endpoints split between the two.
\footnote{arXiv:1804.04964, Section 3, the three injective regions around an edge,
`Papers/1804.04964/paper_normal.tex:1449--1500`; the coordinate instance discharges
the singleton hypothesis through `NormalBlocking.lean`.}

This file records that single-crossing specialization. When the red-to-blue crossing
set is the singleton `{e}`, the whole red-to-blue crossing bundle
`TNLean.PEPS.CrossingConfig red blue` is a single virtual leg on `e`, the bundle
agreement `TNLean.PEPS.SameAwayFromRBBundle` is the single-edge agreement
`TNLean.PEPS.SameAwayFromBond` on `e`, and the whole-bundle red inserted coefficient
is the ordinary single-edge region-inserted coefficient
`TNLean.PEPS.regionInsertedCoeff` of the carried bond matrix.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, proof of
  Theorem 3, lines 254--583 (the injective three-site comparison) and 1449--1500
  (the single-crossing blocking) of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The single red-to-blue crossing edge

When the red-to-blue crossing set is the singleton `{e}`, the distinguished edge `e`
is the sole red-to-blue crossing. It is therefore a boundary edge of the red region
(`IsCrossingEdge.boundary_left`), and the crossing-configuration type
`CrossingConfig red blue` carries one virtual leg, on `e`. -/

/-- The single red-to-blue crossing edge, as a member of the crossing-edge subtype,
under the hypothesis that the crossings are the singleton `{e}`. -/
def singleCrossing (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e) :
    {g : Edge G // IsCrossingEdge (G := G) A red blue g} :=
  ⟨e, (hsingle e).mpr rfl⟩

/-- The single red-to-blue crossing edge is a boundary edge of the red region. -/
theorem isRegionBoundaryEdge_singleCrossing (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e) :
    IsRegionBoundaryEdge (G := G) red e :=
  ((hsingle e).mpr rfl).boundary_left

/-- The single boundary edge `f := ⟨e, _⟩` of the red region carrying the sole
red-to-blue crossing. -/
def singleBoundaryEdge (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e) :
    {f : Edge G // IsRegionBoundaryEdge (G := G) red f} :=
  ⟨e, isRegionBoundaryEdge_singleCrossing (G := G) A red blue e hsingle⟩

/-- Under the singleton hypothesis, the crossing-edge subtype has the single boundary
edge as its only inhabitant. -/
theorem crossingEdge_unique (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (g : {g : Edge G // IsCrossingEdge (G := G) A red blue g}) :
    g = singleCrossing (G := G) A red blue e hsingle :=
  Subtype.ext ((hsingle g.1).mp g.2)

/-! ### The single-leg crossing bundle equivalence

When the crossings are the singleton `{e}`, evaluating a crossing configuration at the
single crossing edge is a bijection onto the single virtual leg `Fin (A.bondDim e)`. -/

/-- The single-leg crossing bundle equivalence: a crossing configuration on the
singleton bundle `{e}` is its value on the single crossing edge `e`. -/
noncomputable def singletonCrossingEquiv (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e) :
    CrossingConfig (G := G) A red blue ≃ Fin (A.bondDim e) where
  toFun p := p (singleCrossing (G := G) A red blue e hsingle)
  invFun y := fun g => (crossingEdge_unique A red blue e hsingle g) ▸ y
  left_inv p := by
    funext g
    obtain rfl := crossingEdge_unique A red blue e hsingle g
    rfl
  right_inv y := rfl

/-- The single-leg crossing bundle equivalence reads a crossing configuration at the
single crossing edge. -/
@[simp] theorem singletonCrossingEquiv_apply (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (p : CrossingConfig (G := G) A red blue) :
    singletonCrossingEquiv (G := G) A red blue e hsingle p =
      p (singleCrossing (G := G) A red blue e hsingle) := rfl

/-! ### The single-crossing bond matrix

A bond matrix on the single crossing edge `e` is carried to a matrix on the
single-leg crossing bundle through the single-leg crossing equivalence. -/

/-- The bond matrix on the single crossing edge `e`, carried to the single-leg crossing
bundle through `singletonCrossingEquiv`. -/
noncomputable def singletonBundleMatrix (A : Tensor G d) (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ) :
    Matrix (CrossingConfig (G := G) A red blue) (CrossingConfig (G := G) A red blue) ℂ :=
  fun p q => M (singletonCrossingEquiv (G := G) A red blue e hsingle p)
    (singletonCrossingEquiv (G := G) A red blue e hsingle q)

/-- The single-leg crossing equivalence of the red-to-blue crossing label of a red
boundary configuration is the configuration's value on the single crossing edge. -/
theorem singletonCrossingEquiv_redBoundaryRBCrossing (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (μ : RegionBoundaryConfig (G := G) A red) :
    singletonCrossingEquiv (G := G) A red blue e hsingle
        (redBoundaryRBCrossing (G := G) A red blue μ) =
      μ (singleBoundaryEdge (G := G) A red blue e hsingle) := by
  rw [singletonCrossingEquiv_apply, redBoundaryRBCrossing_apply]
  rfl

/-! ### The bundle agreement is the single-edge agreement

The whole-bundle agreement `SameAwayFromRBBundle` -- the two red boundary
configurations carry the same value on every red boundary edge not crossing to the
blue region -- is, when the only red-to-blue crossing is the single edge `e`, the
single-edge agreement `SameAwayFromBond` on the single boundary edge `e`. -/

/-- Under the singleton hypothesis, the whole-bundle agreement is the single-edge
agreement on the single boundary edge `e`. -/
theorem sameAwayFromRBBundle_iff_sameAwayFromBond (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (μ ν : RegionBoundaryConfig (G := G) A red) :
    SameAwayFromRBBundle (G := G) A red blue μ ν ↔
      SameAwayFromBond (singleBoundaryEdge (G := G) A red blue e hsingle) μ ν := by
  constructor
  · intro h f hf
    refine h f ?_
    intro hcross
    exact hf (Subtype.ext ((hsingle f.1).mp hcross))
  · intro h f hf
    refine h f ?_
    intro hf'
    refine hf ?_
    rw [hf']; exact (hsingle e).mpr rfl

/-! ### The single-crossing specialization

When the red-to-blue crossing set is the singleton `{e}`, the whole-bundle red
inserted coefficient of the carried bond matrix is the ordinary single-edge
region-inserted coefficient of that bond matrix on the single boundary edge `e`. -/

open scoped Classical in
/-- **The single-crossing specialization.** When the red region crosses to the blue
region across the single edge `e`, the whole-bundle red inserted coefficient of the
carried bond matrix `singletonBundleMatrix M` equals the single-edge region-inserted
coefficient `regionInsertedCoeff` of `M` on the single boundary edge `e`.

Source: arXiv:1804.04964, Section 3, the single-crossing blocking, lines 254--583 and
1449--1500 of `Papers/1804.04964/paper_normal.tex`. -/
theorem redBundleInsertedCoeff_singleton (red blue : Finset V) (e : Edge G)
    (hsingle : ∀ g : Edge G, IsCrossingEdge (G := G) A red blue g ↔ g = e)
    (M : Matrix (Fin (A.bondDim e)) (Fin (A.bondDim e)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) red)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ red)) :
    redBundleInsertedCoeff (G := G) A red blue
        (singletonBundleMatrix (G := G) A red blue e hsingle M) σ τ =
      regionInsertedCoeff (G := G) A red
        (singleBoundaryEdge (G := G) A red blue e hsingle) M σ τ := by
  classical
  rw [redBundleInsertedCoeff_eq, regionInsertedCoeff_eq]
  refine Finset.sum_congr rfl (fun μ _ => Finset.sum_congr rfl (fun ν _ => ?_))
  by_cases h : SameAwayFromRBBundle (G := G) A red blue μ ν
  · rw [if_pos h,
      if_pos ((sameAwayFromRBBundle_iff_sameAwayFromBond red blue e hsingle μ ν).mp h),
      singletonBundleMatrix, singletonCrossingEquiv_redBoundaryRBCrossing,
      singletonCrossingEquiv_redBoundaryRBCrossing]
  · rw [if_neg h,
      if_neg (fun h' => h
        ((sameAwayFromRBBundle_iff_sameAwayFromBond red blue e hsingle μ ν).mpr h'))]

end PEPS
end TNLean
