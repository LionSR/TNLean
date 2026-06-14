import TNLean.PEPS.TorusWindowPeel

/-!
# The bond insertion as a window deformed state

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) extracts the bond operator on the distinguished edge `e`
from the open-boundary end-pair equality `staircasePair_insert_eq_open`.  That equality is stated
for the *deformed-window* vocabulary — inserts on a region and their closed-torus deformed
states — while the per-edge gauge of Step 5 is read off the *region-inserted coefficient*
`regionInsertedCoeff`, which inserts a matrix on one crossing bond and contracts the region against
its complement.  This file compares the two descriptions: the deformed state of a window carrying
the *bond-inserted* insert equals the region-inserted coefficient.

## The bond-inserted insert

For a region `R`, a boundary edge `f` of `R`, and a matrix `M` on `f`, the bond-inserted insert
`bondInsertedRegionInsert A R f M` is the insert on `R` whose boundary configuration `ν` reads the
combination of the genuine `R` block over all boundary configurations `μ` agreeing with `ν` away
from `f`, with `M` coupling their `f`-legs.  Contracting this insert against the complement is the
double-boundary-sum of `regionInsertedCoeff`: the inner `μ`-sum builds the bond-inserted insert,
the outer `ν`-sum is the complement contraction of the deformed state.  This is the content of
`deformedRegionState_bondInsertedRegionInsert`.

This comparison lets the staircase end-pair equality, stated as an `extendInsert` equality of window
inserts, determine a relation between region-inserted coefficients on a single window: taking the
window inserts to be the bond-inserted inserts, the end-pair equality compares the genuine block of
one window against the genuine block of the other across the single bond `e`, which is the peeling
of the end-pair equality onto `e`.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 4--5.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The bond-inserted insert on a region

Inserting a matrix `M` on a boundary edge `f` of `R` is, at the level of inserts, the insert whose
boundary configuration `ν` (read by the complement) carries the `M`-coupled combination of the
genuine `R` block over the boundary configurations `μ` that agree with `ν` away from `f`.  Its
deformed state recovers `regionInsertedCoeff`. -/

open scoped Classical in
/-- The bond-inserted insert on `R`: for a boundary configuration `ν` and physical configuration
`σ` on `R`, the combination of the genuine `R` block `regionBlockedWeight A R μ σ` over the
boundary configurations `μ` agreeing with `ν` away from `f`, weighted by `M (μ f) (ν f)`.

Pairing this insert against the complement is the region-inserted coefficient: the boundary
configuration `ν` of the insert is the one read by the complement contraction, and the inner
`μ`-sum is the region side coupled to it by `M` across `f`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex` (one
block against its complement, with a matrix inserted on the shared bond);
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
noncomputable def bondInsertedRegionInsert (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) :
    RegionInsert (G := G) (d := d) A R :=
  fun ν σ =>
    ∑ μ : RegionBoundaryConfig (G := G) A R,
      (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
        regionBlockedWeight (G := G) A R μ σ

open scoped Classical in
/-- **The bond insertion is the bond-inserted insert's deformed state.**

The deformed state of `R` with the bond-inserted insert `bondInsertedRegionInsert A R f M` equals
the region-inserted coefficient `regionInsertedCoeff A R f M`.  Both contract `R` against its
complement with `M` inserted on `f`; the deformed state's single boundary sum over `ν` (read by the
complement) carries the inner `μ`-sum of the bond-inserted insert, reproducing the double sum of
`regionInsertedCoeff`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem deformedRegionState_bondInsertedRegionInsert (A : Tensor G d) (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    deformedRegionState (G := G) A R (bondInsertedRegionInsert (G := G) A R f M) σ τ =
      regionInsertedCoeff (G := G) A R f M σ τ := by
  classical
  rw [deformedRegionState, regionInsertedCoeff_eq]
  -- The deformed state's `ν`-sum carries the bond-inserted insert's inner `μ`-sum.  Push the
  -- complement weight into the `μ`-sum and swap the order of summation to match the `μ`-outer /
  -- `ν`-inner double sum of `regionInsertedCoeff`.
  rw [show (∑ ν : RegionBoundaryConfig (G := G) A R,
        bondInsertedRegionInsert (G := G) A R f M ν σ *
          regionBlockedWeight (G := G) A (Finset.univ \ R)
            (regionComplementBoundaryConfig (G := G) A R ν) τ) =
      ∑ ν : RegionBoundaryConfig (G := G) A R,
        ∑ μ : RegionBoundaryConfig (G := G) A R,
          (if SameAwayFromBond f μ ν then M (μ f) (ν f) else 0) *
            regionBlockedWeight (G := G) A R μ σ *
            regionBlockedWeight (G := G) A (Finset.univ \ R)
              (regionComplementBoundaryConfig (G := G) A R ν) τ from ?_,
    Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [bondInsertedRegionInsert, Finset.sum_mul]

/-! ### The bond insertion as the extended deformed state on a superset

For a region `R ⊆ S`, the bond insertion on `R` (read off a global configuration through its `R`-
and `univ \ R`-restrictions) equals the corner-extended deformed state on `S`: the deformed-state
extension identity `deformedRegionState_extend` reads the bond-inserted deformed state on `R` as
the deformed state on `S` of the corner-extended bond-inserted insert.  This is the form used in the
staircase end-pair equality, where `R = W` is a single end window and `S = W_0 ⊔ W_{L+K-1}` is the
end pair: the genuine block of the *opposite* window the bond `e` joins to is carried by the corner
extension `extendInsert (W ⊆ S)`. -/

/-- **The bond insertion is the corner-extended deformed state on a superset.**

For `R ⊆ S`, the region-inserted coefficient `regionInsertedCoeff A R f M` read off a global
configuration `cfg` (restricted to `R` and to `univ \ R`) equals the assembled deformed state on `S`
of the corner-extended bond-inserted insert `extendInsert (R ⊆ S) (bondInsertedRegionInsert A R f
M)`.  The theorem `deformedRegionState_bondInsertedRegionInsert` writes the coefficient as the
bond-inserted deformed state on `R`, and `deformedRegionState_extend` reads that as the
deformed state on `S` of the corner extension.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 and the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 4. -/
theorem regionInsertedCoeff_eq_extendInsert_bondInserted {R S : Finset V} (hRS : R ⊆ S)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (A.bondDim f.1)) (Fin (A.bondDim f.1)) ℂ) (cfg : V → Fin d) :
    regionInsertedCoeff (G := G) A R f M
        (restrictRegionσ (V := V) (d := d) R cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg) =
      deformedRegionStateAssembled (G := G) A S
        (extendInsert (G := G) hRS (bondInsertedRegionInsert (G := G) A R f M)) cfg := by
  rw [← deformedRegionState_extend hRS hpos (bondInsertedRegionInsert (G := G) A R f M),
    deformedRegionStateAssembled, deformedRegionState_bondInsertedRegionInsert]

end PEPS
end TNLean
