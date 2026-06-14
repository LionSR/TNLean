import TNLean.PEPS.TorusWindowPeel2
import TNLean.PEPS.RegionBlock.GaugeBridge
import TNLean.PEPS.RegionBlock.AbsorbedEquality

/-!
# The window-independence of the bond insertion

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of `Papers/1804.04964/paper_normal.tex`)
extracts the bond operator on the distinguished edge `e` from the open-boundary end-pair equality
`staircasePair_insert_eq_open`, peeled onto `e` by `regionInsertedCoeff_endWindows_eq_of_staircase`.
That peeling consumes a family of inserts on the staircase windows all sharing one deformed state,
with the two end windows carrying the bond-inserted inserts of `M` and `M'`.  The sketch describes
this family as the realization of one virtual operation on the bond `e` as a physical operation on
any window containing an endpoint of `e`; this file supplies the load-bearing fact behind that
correspondence: the deformed state of a bond-inserted insert is **window-independent** up to the
window's interior-bond multiplicity.

## The window-independence

The region-to-edge identity `regionInsertedCoeff_eq_smul_edgeInsertedCoeff`
(`TNLean/PEPS/RegionBlock/GaugeBridge.lean`) writes the region-inserted coefficient on a boundary
edge `f` of a region `R` as the interior-bond product over `R` times the *region-independent*
edge-inserted coefficient `edgeInsertedCoeff B f.1`, with the inserted matrix oriented by
`regionEdgeOrient` (the identity when `f`'s left endpoint lies in `R`, the transpose otherwise).
The edge-inserted coefficient mentions only the edge `f.1`, not the region, so two regions sharing
`f` as a boundary edge produce the same edge-inserted coefficient.  The bond-inserted insert's
assembled deformed state is exactly the region-inserted coefficient
(`deformedRegionState_bondInsertedRegionInsert`), read off the global configuration through the
restriction round-trip `assembleRegionσ_restrict`.  Cross-multiplying by the two interior-bond
products cancels the region-dependent scalars and equates the two assembled deformed states.

This is the realization of the sketch's ``a virtual operation on a given bond is a physical
operation on any window containing an endpoint'' for the two end windows of the staircase, which
carry the bond-inserted inserts the peeling consumes.  The two end windows sit on opposite sides of
`e`, so their orientations differ by a transpose; the general statement carries the orientation
explicitly, and the same-side corollary specializes it.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {B : Tensor G d}

/-! ### The assembled bond-inserted state through the edge-inserted coefficient

The assembled deformed state of a bond-inserted insert on a region `R`, read off a global
configuration `cfg`, is the interior-bond product over `R` times the region-independent
edge-inserted coefficient of the oriented matrix.  This is the bridge
`deformedRegionState_bondInsertedRegionInsert` chained through the region-to-edge identity
`regionInsertedCoeff_eq_smul_edgeInsertedCoeff` after the restriction round-trip. -/

/-- **The assembled bond-inserted state is the interior-bond multiple of the edge-inserted
coefficient.**

For a region `R` with a boundary edge `f`, an inserted matrix `M`, and a global configuration
`cfg`, the assembled deformed state of the bond-inserted insert `bondInsertedRegionInsert B R f M`
equals the interior-bond product over `R` times the region-independent edge-inserted coefficient
`edgeInsertedCoeff B f.1 cfg` of the oriented matrix `regionEdgeOrient B R f M`.

The assembled deformed state is the region-inserted coefficient
(`deformedRegionState_bondInsertedRegionInsert`, read off `cfg` through `restrictRegionσ`), which
the region-to-edge identity `regionInsertedCoeff_eq_smul_edgeInsertedCoeff` writes as the
interior-bond multiple of the edge-inserted coefficient; the restriction round-trip
`assembleRegionσ_restrict` reassembles `cfg` from its two restrictions.

Source: arXiv:1804.04964, Section 3, lines 1205--1210 of `Papers/1804.04964/paper_normal.tex`;
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff (R : Finset V)
    (f : {f : Edge G // IsRegionBoundaryEdge (G := G) R f})
    (M : Matrix (Fin (B.bondDim f.1)) (Fin (B.bondDim f.1)) ℂ) (cfg : V → Fin d) :
    deformedRegionStateAssembled (G := G) B R
        (bondInsertedRegionInsert (G := G) B R f M) cfg =
      regionInteriorBondProd (G := G) B R •
        edgeInsertedCoeff (G := G) B f.1 cfg (regionEdgeOrient (G := G) B R f M) := by
  rw [deformedRegionStateAssembled, deformedRegionState_bondInsertedRegionInsert,
    regionInsertedCoeff_eq_smul_edgeInsertedCoeff]
  -- Reassemble `cfg` from its region and complement restrictions in the edge-inserted coefficient.
  congr 1
  rw [show (assembleRegionσ (V := V) (d := d) R
        (restrictRegionσ (V := V) (d := d) R cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg)) = cfg from ?_]
  exact assembleRegionσ_restrict R cfg

/-! ### The window-independence of the bond insertion

Two regions sharing the edge `f.1` as a boundary edge produce the same edge-inserted coefficient,
so their assembled bond-inserted states are equal once cross-multiplied by the two interior-bond
products and the two orientations agree.  The two end windows of the staircase carry `e`'s two
endpoints on opposite sides, so their orientations differ by a transpose; the general statement
carries the two oriented matrices explicitly. -/

/-- **The window-independence of the bond insertion (general orientation).**

For two regions `R₁`, `R₂` sharing the edge `e` as a boundary edge, two inserted matrices `M₁`, `M₂`
whose orientations through the two regions agree (`horient`), and a global configuration `cfg`, the
two assembled bond-inserted states are equal once cross-multiplied by the two interior-bond
products:
\[
  \mathrm{ribp}(R_2)\cdot\text{(assembled state on }R_1) =
  \mathrm{ribp}(R_1)\cdot\text{(assembled state on }R_2).
\]
Both sides are the corresponding interior-bond product times the same region-independent
edge-inserted coefficient (`deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff`),
since the edge-inserted coefficient mentions only the shared edge and the two orientations agree;
cross-multiplying by the interior-bond products matches the two scalars.

This is the realization of the sketch's correspondence between one virtual operation on the bond and
the physical operation on either window containing an endpoint of it, for windows where the bond is
a boundary edge.

Source: arXiv:1804.04964, the proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex` (a virtual operation on a bond is a physical operation on any
window containing an endpoint); `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem bondInserted_windowIndependent (R₁ R₂ : Finset V) (e : Edge G)
    (hf : IsRegionBoundaryEdge (G := G) R₁ e) (hg : IsRegionBoundaryEdge (G := G) R₂ e)
    (M₁ M₂ : Matrix (Fin (B.bondDim e)) (Fin (B.bondDim e)) ℂ)
    (horient : (regionEdgeOrient (G := G) B R₁ ⟨e, hf⟩ M₁) =
      regionEdgeOrient (G := G) B R₂ ⟨e, hg⟩ M₂)
    (cfg : V → Fin d) :
    (regionInteriorBondProd (G := G) B R₂ : ℂ) •
        deformedRegionStateAssembled (G := G) B R₁
          (bondInsertedRegionInsert (G := G) B R₁ ⟨e, hf⟩ M₁) cfg =
      (regionInteriorBondProd (G := G) B R₁ : ℂ) •
        deformedRegionStateAssembled (G := G) B R₂
          (bondInsertedRegionInsert (G := G) B R₂ ⟨e, hg⟩ M₂) cfg := by
  rw [deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff R₁ ⟨e, hf⟩ M₁ cfg,
    deformedRegionStateAssembled_bondInserted_eq_smul_edgeInsertedCoeff R₂ ⟨e, hg⟩ M₂ cfg]
  -- Both sides carry the same region-independent edge-inserted coefficient; the agreeing
  -- orientation matches them, then the two products of natural scalars commute.
  rw [horient]
  simp only [smul_eq_mul]
  ring

end PEPS
end TNLean
