import TNLean.PEPS.TorusWindowChain6
import TNLean.PEPS.TorusWindowPeel4

/-!
# The per-consecutive-window bond-insert transport through the injective overlap

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`)
transports a virtual operation on a bond around the corner of the reference edge along the
staircase of `L + K` overlapping windows.  The single load-bearing step of that transport is the
*per-consecutive-window* one: a virtual operation realized as a bond insertion on the window `W_j`
is carried to the window `W_{j+1}` through their injective overlap `U_j = W_j ∪ W_{j+1}`, the
sliding-arm rectangle of `staircaseUnion_eq_horizontalRectangle`.  This file builds that step.

## The mechanism (no `univ \ S` inversion)

The transport rests on two landed facts.  The window-independence of the bond insertion
`bondInserted_windowIndependent` (`TNLean/PEPS/TorusWindowPeel4.lean`) says that two regions
sharing the bond `g` as a boundary edge, with the inserted matrices' orientations agreeing, have
*cross-proportional* assembled deformed states: the interior-bond product of one window times the
state of the other matches the swapped product.  Scaling each window's bond insert by the *other*
window's interior-bond product turns that cross-proportionality into an honest equality of deformed
states.  The consecutive-window comparison `horizontalStaircaseConsecutiveWindow_extend_eq`
(`TNLean/PEPS/TorusWindowChain6.lean`) then inverts the *union* complement --- the injective
`(L + 1) × K` rectangle, not the non-injective `univ \ S` --- to strip the equal states to an
open-boundary equality of the corner-extended inserts on `U_j`.

The interior-bond scalars are nonzero at positive bond dimensions, so the scaled inserts carry the
same information as the bare bond inserts; the cross-proportional form is the faithful one because
the two window translates need not have equal interior-bond products (the bond dimensions need not
be translation invariant).  This is the genuine per-step transport the source's overlapping-window
sketch compresses into ``a virtual operation on a given bond is a physical operation on any window
containing an endpoint'', now realized through the *injective overlap* rather than the obstructed
torus complement of the end pair.

## What this is the foundation of, and where the chain composition walls

The per-step transport composes along the staircase into the single-tensor window-independence the
end-pair peeling `regionInsertedCoeff_endWindows_eq_of_staircase` consumes: each step carries the
operation one window further, the injective overlap mediating, never inverting `univ \ S`.  That
single-tensor transport is the affirmative content this file underwrites.

The forward-transfer *multiplicativity* `hmul` --- the homomorphism `M · M' ↦ (transfer of M)
(transfer of M')` the witness `exists_windowEdgeCoeffIdentityWitness_of_coeffTransfer` consumes ---
is a *different* statement.  It needs the product of two operations on the bond `e` to split at the
intermediate bond index, which in one dimension comes from the length-`L` window product spanning
the full bond algebra (the `LinearMap.ext_on_range` step of `MPSChainTensor.exists_insertionHom`).
A two-dimensional `L × K` window touches `e` with one endpoint, so its `e`-restricted family is a
family of vectors on `Fin (bondDim e)`, never a square-matrix span; the transport this file builds
carries a *single* operation and provides no such splitting.  The verdict that the multiplicativity
is the coarse three-site super-bond multiplicativity, whose third injective block is the obstructed
`univ \ S` at the minimal size, is recorded in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the
section on the multiplicativity verdict.  The per-step transport is the foundation; the homomorphism
is not a consequence of it.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1 and the
  multiplicativity verdict.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ} {L K : ℕ} {B : Tensor (torusGraph width height) d}

/-! ### The scaled bond insert on a staircase window

Scaling the bond insert of a matrix `M` on a window by a constant produces another insert on the
same window whose assembled deformed state is that constant times the bond-insertion coefficient.
The constant is taken to be the *other* window's interior-bond product, so that the window-
independence cross-proportionality becomes an equality of states. -/

/-- The bond insert of `M` on the staircase window `W_j` scaled by a constant `c`: an insert on
`W_j` whose assembled deformed state is `c` times the assembled state of the bond insert.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
noncomputable def scaledBondInsert (B : Tensor (torusGraph width height) d) (R : Finset _)
    (f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge (G := torusGraph width height)
      R f})
    (c : ℂ) (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) :
    RegionInsert (G := torusGraph width height) (d := d) B R :=
  fun ν σ => c * bondInsertedRegionInsert (G := torusGraph width height) B R f M ν σ

/-- The assembled deformed state of the scaled bond insert is the constant times the assembled
deformed state of the bond insert. -/
theorem deformedRegionStateAssembled_scaledBondInsert (R : Finset _)
    (f : {f : Edge (torusGraph width height) // IsRegionBoundaryEdge (G := torusGraph width height)
      R f})
    (c : ℂ) (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ)
    (cfg : TorusVertex width height → Fin d) :
    deformedRegionStateAssembled (G := torusGraph width height) B R
        (scaledBondInsert (d := d) B R f c M) cfg =
      c * deformedRegionStateAssembled (G := torusGraph width height) B R
        (bondInsertedRegionInsert (G := torusGraph width height) B R f M) cfg := by
  rw [show scaledBondInsert (d := d) B R f c M =
      (fun ν σ => c * bondInsertedRegionInsert (G := torusGraph width height) B R f M ν σ) from rfl,
    deformedRegionStateAssembled_const_smul]

/-! ### The per-consecutive-window bond-insert transport (sliding arm)

For a sliding-arm index `j < L`, the two consecutive windows `W_j` and `W_{j+1}` share the bond
`g` as a boundary edge.  The window-independence of the bond insertion, cross-multiplied by the two
interior-bond products and rescaled, gives equal deformed states for the two scaled bond inserts;
the consecutive-window comparison on the injective overlap `U_j` strips the equality to the open-
boundary equality of the corner-extended scaled bond inserts. -/

/-- **The per-consecutive-window bond-insert transport (sliding arm).**

For a sliding-arm index `j < L`, with the staircase windows `W_j` and `W_{j+1}` sharing the bond
`g` as a boundary edge and inserted matrices `M₁`, `M₂` on `g` whose orientations through the two
windows agree (`horient`), the corner-extended scaled bond inserts on the injective overlap
`U_j = W_j ∪ W_{j+1}` are equal.  The left insert is the bond insert of `M₁` on `W_j` scaled by the
interior-bond product of `W_{j+1}`; the right insert is the bond insert of `M₂` on `W_{j+1}` scaled
by the interior-bond product of `W_j`.

The window-independence `bondInserted_windowIndependent` makes the two scaled inserts'
assembled deformed states agree (both equal the cross-product of the two interior-bond products
times the region-independent edge-inserted coefficient of the shared oriented matrix); the
consecutive-window comparison `horizontalStaircaseConsecutiveWindow_extend_eq` inverts the union
complement, the injective `(L + 1) × K` rectangle, never the non-injective `univ \ S`.

This is the genuine per-step transport mediated by the injective overlap.  Its composition along
the staircase underwrites the single-tensor window-independence the end-pair peeling consumes; it
does not on its own yield the forward-transfer multiplicativity, which needs a bond-algebra
spanning the two-dimensional single window lacks (see the module docstring and
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, the multiplicativity verdict).

Source: arXiv:1804.04964, the one-dimensional inversions at lines 2133--2179 and the proof sketch
at lines 2320--2445 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem horizontalStaircaseConsecutiveWindow_bondTransport_extend_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : j < L) (g : Edge (torusGraph width height))
    (hf : IsRegionBoundaryEdge (G := torusGraph width height) (staircaseWindow s L K j) g)
    (hg : IsRegionBoundaryEdge (G := torusGraph width height) (staircaseWindow s L K (j + 1)) g)
    (M₁ M₂ : Matrix (Fin (B.bondDim g)) (Fin (B.bondDim g)) ℂ)
    (horient : regionEdgeOrient (G := torusGraph width height) B (staircaseWindow s L K j) ⟨g, hf⟩
        M₁ =
      regionEdgeOrient (G := torusGraph width height) B (staircaseWindow s L K (j + 1)) ⟨g, hg⟩
        M₂) :
    extendInsert (G := torusGraph width height) (staircaseWindow_subset_staircaseUnion s L K j)
        (scaledBondInsert (d := d) B (staircaseWindow s L K j) ⟨g, hf⟩
          (regionInteriorBondProd (G := torusGraph width height) B
            (staircaseWindow s L K (j + 1))) M₁) =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_succ_subset_staircaseUnion s L K j)
        (scaledBondInsert (d := d) B (staircaseWindow s L K (j + 1)) ⟨g, hg⟩
          (regionInteriorBondProd (G := torusGraph width height) B
            (staircaseWindow s L K j)) M₂) := by
  refine horizontalStaircaseConsecutiveWindow_extend_eq h hUB hpos hL hK hxw hyh s hj _ _ ?_
  funext cfg
  -- The two scaled bond inserts have equal assembled deformed states, by window-independence.
  rw [deformedRegionStateAssembled_scaledBondInsert, deformedRegionStateAssembled_scaledBondInsert]
  exact bondInserted_windowIndependent (G := torusGraph width height) (staircaseWindow s L K j)
    (staircaseWindow s L K (j + 1)) g hf hg M₁ M₂ horient cfg

/-! ### The per-consecutive-window bond-insert transport (descending arm)

The descending-arm transport transposes the sliding one: the consecutive union `U_j` is the
`L × (K + 1)` cyclic rectangle, injective by
`regionBlockedTensorInjective_verticalUnionComplement`, and the consecutive-window comparison is
`verticalConsecutiveWindow_extend_eq`.  Together with the sliding arm this gives the per-step
transport on the whole staircase. -/

/-- **The per-consecutive-window bond-insert transport (descending arm).**

For a descending-arm index `L ≤ j` with `j + 1 < L + K`, with the staircase windows `W_j` and
`W_{j+1}` sharing the bond `g` as a boundary edge and inserted matrices `M₁`, `M₂` on `g` whose
orientations through the two windows agree, the corner-extended scaled bond inserts on the
injective overlap `U_j = W_j ∪ W_{j+1}` are equal.  This is the transpose of
`horizontalStaircaseConsecutiveWindow_bondTransport_extend_eq`, inverting the `L × (K + 1)` union
rectangle.

Source: arXiv:1804.04964, the one-dimensional inversions at lines 2133--2179 and the proof sketch
at lines 2320--2445 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
theorem verticalStaircaseConsecutiveWindow_bondTransport_extend_eq
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (s : TorusVertex width height) {j : ℕ} (hj : L ≤ j) (hjK : j + 1 < L + K)
    (g : Edge (torusGraph width height))
    (hf : IsRegionBoundaryEdge (G := torusGraph width height) (staircaseWindow s L K j) g)
    (hg : IsRegionBoundaryEdge (G := torusGraph width height) (staircaseWindow s L K (j + 1)) g)
    (M₁ M₂ : Matrix (Fin (B.bondDim g)) (Fin (B.bondDim g)) ℂ)
    (horient : regionEdgeOrient (G := torusGraph width height) B (staircaseWindow s L K j) ⟨g, hf⟩
        M₁ =
      regionEdgeOrient (G := torusGraph width height) B (staircaseWindow s L K (j + 1)) ⟨g, hg⟩
        M₂) :
    extendInsert (G := torusGraph width height) (staircaseWindow_subset_staircaseUnion s L K j)
        (scaledBondInsert (d := d) B (staircaseWindow s L K j) ⟨g, hf⟩
          (regionInteriorBondProd (G := torusGraph width height) B
            (staircaseWindow s L K (j + 1))) M₁) =
      extendInsert (G := torusGraph width height)
        (staircaseWindow_succ_subset_staircaseUnion s L K j)
        (scaledBondInsert (d := d) B (staircaseWindow s L K (j + 1)) ⟨g, hg⟩
          (regionInteriorBondProd (G := torusGraph width height) B
            (staircaseWindow s L K j)) M₂) := by
  refine verticalConsecutiveWindow_extend_eq h hUB hpos hL hK hxw hyh s hj hjK _ _ ?_
  funext cfg
  rw [deformedRegionStateAssembled_scaledBondInsert, deformedRegionStateAssembled_scaledBondInsert]
  exact bondInserted_windowIndependent (G := torusGraph width height) (staircaseWindow s L K j)
    (staircaseWindow s L K (j + 1)) g hf hg M₁ M₂ horient cfg

end Torus

end PEPS
end TNLean
