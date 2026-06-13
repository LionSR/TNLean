import TNLean.PEPS.RegionBlock.BlockRangeCoincidence
import TNLean.PEPS.TorusWindowComplement

/-!
# Deformed-window states and the consecutive-window comparison

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) compares the closed-torus states produced
by deforming a single window of the overlapping-window chain.  This file builds
the vocabulary for those deformed states and the load-bearing comparison engine
that strips a closed-state equality to an open-boundary equality on a region,
following the filled-in derivation
(`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1).

## The deformed-window state

For a finite region `R`, `regionBlockedWeight A R` is the contraction of the
network over `R` with the boundary-crossing edges left open.  A *deformed* state
replaces that block by an arbitrary tensor `C` carrying the same boundary
structure, an assignment of a complex amplitude to each boundary configuration on
`R` and physical configuration on `R`.  The deformed state is the closed-torus
contraction with that replacement: the boundary configuration of `C` is paired
against the contraction of the complement `univ \ R`, summed over the boundary.
This reuses the block/complement pairing of
`sum_regionBlockedWeight_mul_complement`; taking `C` to be the genuine block
`regionBlockedWeight A R` recovers the interior-bond multiple of the closed state
coefficient (`deformedRegionState_block`).

## The complement-inversion engine

The key reusable lemma `deformedRegionState_insert_eq_of_complementInjective`
says: if two inserts `C₁` and `C₂` carrying the boundary structure of the same
region `R` produce equal deformed states, and the complement `univ \ R` is
blocked-tensor injective, then `C₁ = C₂`.  For a fixed region physical
configuration the deformed state is the blocked-region tensor map of the
complement applied to the insert, reindexed across the boundary identification;
the complement map is injective, so equal deformed states force equal inserts.
This is the two-dimensional analogue of the one-dimensional inversions producing
the source's displays around Lemma 5 (the one-dimensional inversions are at
`Papers/1804.04964/paper_normal.tex:2133--2179`).

## The consecutive-window comparison

On the torus the engine specializes to two consecutive windows of the chain.
Their union `U` is a single cyclic `(L + 1) × K` (horizontal slide) or
`L × (K + 1)` (vertical slide) rectangle, whose complement is injective at the
minimal sizes `2L + 1 ≤ width`, `2K + 1 ≤ height` by the landed
`regionBlockedTensorInjective_horizontalUnionComplement` /
`...verticalUnionComplement`.  Reading each window's deformed state as a deformed
state of the union, the engine strips an equality of the two closed-torus
deformed states to an open-boundary equality of the two inserts on `U` --- the
note's display restricted to the union.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and
  proof sketch at lines 2296--2445 of `Papers/1804.04964/paper_normal.tex`; the
  one-dimensional inversions at lines 2133--2179](https://arxiv.org/abs/1804.04964);
  the filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
  Step 1.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}

/-! ### The deformed-window insert and its state

An insert on `R` carries the boundary structure of the block `regionBlockedWeight
A R`: an amplitude for each boundary configuration on `R` and physical
configuration on `R`.  The genuine block of the network is the canonical such
insert. -/

/-- An insert on the region `R`: an amplitude for each boundary configuration on
`R` and physical configuration on `R`, the boundary structure of the block
`regionBlockedWeight A R`.  This is the data of a tensor replacing the network
block on `R` in the closed-torus contraction.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (a deformed tensor `C_j` carries the boundary
structure of the window `W_j`); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
abbrev RegionInsert (A : Tensor G d) (R : Finset V) : Type _ :=
  RegionBoundaryConfig (G := G) A R → RegionPhysicalConfig (V := V) (d := d) R → ℂ

/-- The deformed-window state of `R` with insert `C`: the closed-torus
contraction with the network block on `R` replaced by `C`.  The boundary
configuration of `C` is paired against the contraction of the complement
`univ \ R`, summed over the boundary, exactly as in
`sum_regionBlockedWeight_mul_complement` with the genuine block replaced by `C`.
The result is a function of the region physical configuration `σ` and the
complement physical configuration `τ`.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (the deformed states agree as closed-torus
states); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Step 1. -/
noncomputable def deformedRegionState (A : Tensor G d) (R : Finset V)
    (C : RegionInsert (G := G) (d := d) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) : ℂ :=
  ∑ μ : RegionBoundaryConfig (G := G) A R,
    C μ σ * regionBlockedWeight (G := G) A (Finset.univ \ R)
      (regionComplementBoundaryConfig (G := G) A R μ) τ

/-- The genuine block of the network is an insert, and its deformed state is the
interior-bond multiple of the closed state coefficient: taking `C` to be
`regionBlockedWeight A R` in `deformedRegionState` recovers
`sum_regionBlockedWeight_mul_complement`.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem deformedRegionState_block (A : Tensor G d) (R : Finset V)
    (σ : RegionPhysicalConfig (V := V) (d := d) R)
    (τ : RegionPhysicalConfig (V := V) (d := d) (Finset.univ \ R)) :
    deformedRegionState (G := G) A R (regionBlockedWeight (G := G) A R) σ τ =
      regionInteriorBondProd (G := G) A R •
        stateCoeff A (assembleRegionσ (V := V) (d := d) R σ τ) := by
  rw [deformedRegionState, ← sum_regionBlockedWeight_mul_complement (G := G) A R σ τ]

/-! ### The deformed state as the complement tensor map

For a fixed region physical configuration `σ`, the deformed state, viewed as a
function of the complement physical configuration `τ`, is the blocked-region
tensor map of the complement `univ \ R` applied to the insert read across the
boundary identification.  The complement boundary configurations are in bijection
with those on `R` through `regionComplementBoundaryConfigEquiv`, so the
`R`-indexed sum of the insert against the complement weight reindexes to the
complement-indexed sum the complement tensor map evaluates. -/

/-- The deformed state at a fixed region physical configuration `σ` is the
blocked-region tensor map of the complement applied to the insert read across the
boundary identification.  Reindexing the boundary sum by the bijection
`regionComplementBoundaryConfigEquiv` turns the `R`-indexed insert pairing into
the complement-indexed pairing the complement tensor map computes.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem deformedRegionState_eq_complementMap (A : Tensor G d) (R : Finset V)
    (C : RegionInsert (G := G) (d := d) A R)
    (σ : RegionPhysicalConfig (V := V) (d := d) R) :
    deformedRegionState (G := G) A R C σ =
      regionBlockedTensorMap (G := G) A (Finset.univ \ R)
        (fun ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
          C ((regionComplementBoundaryConfigEquiv (G := G) A R).symm ν) σ) := by
  funext τ
  rw [regionBlockedTensorMap_apply, deformedRegionState]
  rw [← Equiv.sum_comp (regionComplementBoundaryConfigEquiv (G := G) A R)
    (fun ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
      C ((regionComplementBoundaryConfigEquiv (G := G) A R).symm ν) σ •
        regionBlockedWeight (G := G) A (Finset.univ \ R) ν τ)]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [Equiv.symm_apply_apply, regionComplementBoundaryConfigEquiv_apply, smul_eq_mul]

/-! ### The complement-inversion engine

The load-bearing comparison lemma.  Two inserts on the same region producing equal
deformed states are equal when the complement is blocked-tensor injective: the
complement tensor map is then injective, so equal deformed states (at each fixed
region physical configuration) force equal reindexed inserts, hence equal
inserts. -/

/-- **The complement-inversion engine.**

If two inserts `C₁` and `C₂` on the same region `R` produce equal deformed states
and the complement `univ \ R` is blocked-tensor injective, then `C₁ = C₂`.

For each fixed region physical configuration the deformed state is the
blocked-region tensor map of the complement applied to the reindexed insert
(`deformedRegionState_eq_complementMap`).  Blocked-tensor injectivity of the
complement makes that map injective, so the reindexed inserts agree; the
reindexing is a bijection of boundary configurations, so the inserts themselves
agree.  This strips a closed-torus state equality to an open-boundary equality on
`R`, the two-dimensional analogue of the one-dimensional inversions producing the
source's displays around Lemma 5.

Source: arXiv:1804.04964, the one-dimensional inversions at lines 2133--2179 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 1. -/
theorem deformedRegionState_insert_eq_of_complementInjective (A : Tensor G d)
    (R : Finset V)
    (hC : RegionBlockedTensorInjective (G := G) A (Finset.univ \ R))
    (C₁ C₂ : RegionInsert (G := G) (d := d) A R)
    (hstate : deformedRegionState (G := G) A R C₁ = deformedRegionState (G := G) A R C₂) :
    C₁ = C₂ := by
  have hmap := regionBlockedTensorMap_injective_of_injective (G := G) A (Finset.univ \ R) hC
  funext μ σ
  -- The reindexed inserts agree at each region physical configuration `σ`.
  have hσ : (fun ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
        C₁ ((regionComplementBoundaryConfigEquiv (G := G) A R).symm ν) σ) =
      (fun ν : RegionBoundaryConfig (G := G) A (Finset.univ \ R) =>
        C₂ ((regionComplementBoundaryConfigEquiv (G := G) A R).symm ν) σ) := by
    apply hmap
    rw [← deformedRegionState_eq_complementMap, ← deformedRegionState_eq_complementMap,
      hstate]
  -- Reading `hσ` at `regionComplementBoundaryConfigEquiv μ` recovers `μ`.
  have hread := congrFun hσ (regionComplementBoundaryConfigEquiv (G := G) A R μ)
  simpa only [Equiv.symm_apply_apply] using hread

end PEPS
end TNLean
