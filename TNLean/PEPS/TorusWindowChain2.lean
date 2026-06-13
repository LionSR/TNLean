import TNLean.PEPS.TorusWindowChain
import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral

/-!
# Extending a deformed-window state to a larger region

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2297--2318 of
`Papers/1804.04964/paper_normal.tex`) chains the consecutive-window comparisons of
`TNLean/PEPS/TorusDeformedWindow.lean` across the staircase patch around a lattice
edge.  The chaining needs to read a single window's deformed state as the deformed
state of a larger region carrying the genuine network block on the added vertices:
the *corner-extended* insert.  This file builds that extension and the load-bearing
identity, following the filled-in derivation
(`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, Steps 2--3).

## The extension identity

For nested regions `R ⊆ S`, the deformed state on `R` with insert `C` equals the
deformed state on `S` with the *extended* insert `extendInsert R S C`, where the
extended insert pairs `C` with the genuine network block of the added vertices
`S \ R`.  The extension reuses the three-block factorization
`ThreeBlockGeometry.regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical`
of `TNLean/PEPS/RegionBlock/UnionInjectivityGeneral.lean`: with the geometry
`red = R`, `blue = S \ R`, `complement = univ \ S`, the host `univ \ red = univ \ R`
is the complement block of the deformed state on `R`, and the factorization splits its
weight into the blue-coupling combination of the `univ \ S` complement weights.  The
blue-coupling coefficient `threeBlockBlueCoeff`, contracted against `C`, is exactly the
extended insert.  The factorization carries an interior-bond multiplicity factor on the
`univ \ S` block, a nonzero scalar at positive bond dimensions, which cancels.

The deformed state is read as a function of the *full* physical configuration through
`assembleRegionσ`, so the identity is a region-independent equality of functions on
`V → Fin d`; this lets the consecutive-window equalities chain across the patch by
transitivity, the content of Step 2.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, the corollary and proof
  sketch at lines 2296--2445 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
  Steps 2--3.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### The nested-region three-block geometry

For `R ⊆ S` the three blocks `red = R`, `blue = S \ R`, `complement = univ \ S`
partition the vertex set, with host `univ \ red = univ \ R`.  This is the geometry
whose three-block factorization splits the deformed-state complement weight on
`univ \ R` into the `univ \ S` complement weights, the blue coupling carrying the
added vertices `S \ R`. -/

/-- The nested-region three-block geometry for `R ⊆ S`: `red = R`, `blue = S \ R`,
`complement = univ \ S`.  The host `univ \ red` is `univ \ R`, the complement block
of the deformed state on `R`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`,
Step 2. -/
def nestedThreeBlockGeometry {R S : Finset V} (hRS : R ⊆ S) : ThreeBlockGeometry V where
  red := R
  blue := S \ R
  complement := Finset.univ \ S
  red_disjoint_blue := by
    rw [Finset.disjoint_left]; intro v hvR hvSR
    exact (Finset.mem_sdiff.mp hvSR).2 hvR
  red_disjoint_complement := by
    rw [Finset.disjoint_left]; intro v hvR hvS
    exact (Finset.mem_sdiff.mp hvS).2 (hRS hvR)
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]; intro v hvSR hvS
    exact (Finset.mem_sdiff.mp hvS).2 (Finset.mem_sdiff.mp hvSR).1
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    by_cases hvR : v ∈ R
    · exact Or.inl (Or.inl hvR)
    · by_cases hvS : v ∈ S
      · exact Or.inl (Or.inr ⟨hvS, hvR⟩)
      · exact Or.inr hvS

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_red {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).red = R := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_blue {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).blue = S \ R := rfl

omit [DecidableRel G.Adj] in
@[simp] theorem nestedThreeBlockGeometry_complement {R S : Finset V} (hRS : R ⊆ S) :
    (nestedThreeBlockGeometry (V := V) hRS).complement = Finset.univ \ S := rfl

omit [DecidableRel G.Adj] in
/-- The host `univ \ red` of the nested geometry is `univ \ R`. -/
theorem nestedThreeBlockGeometry_sdiff_red {R S : Finset V} (hRS : R ⊆ S) :
    Finset.univ \ (nestedThreeBlockGeometry (V := V) hRS).red = Finset.univ \ R := rfl

/-! ### Restricting a global physical configuration to a region

The deformed state is read as a function of the full physical configuration through
the restriction `restrictRegionσ`, the inverse of `assembleRegionσ`.  Restricting to
the host `univ \ R` factors through the nested geometry's fused leg: the host
restriction is the `complPhysical` of the blue restriction (to `S \ R`) and the
complement restriction (to `univ \ S`). -/

/-- The restriction of a global physical configuration `cfg` to the region `R`. -/
def restrictRegionσ (R : Finset V) (cfg : V → Fin d) :
    RegionPhysicalConfig (V := V) (d := d) R :=
  fun w => cfg w.1

omit [Fintype V] [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem restrictRegionσ_apply (R : Finset V) (cfg : V → Fin d)
    (w : {w : V // w ∈ R}) : restrictRegionσ (V := V) (d := d) R cfg w = cfg w.1 := rfl

omit [DecidableRel G.Adj] in
/-- Assembling the region and complement restrictions recovers the global
configuration. -/
theorem assembleRegionσ_restrict (R : Finset V) (cfg : V → Fin d) :
    assembleRegionσ (V := V) (d := d) R (restrictRegionσ (V := V) (d := d) R cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg) = cfg := by
  funext w
  by_cases h : w ∈ R
  · rw [assembleRegionσ_mem (V := V) (d := d) R _ _ ⟨w, h⟩, restrictRegionσ_apply]
  · have hw : w ∈ Finset.univ \ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩
    rw [assembleRegionσ_notMem (V := V) (d := d) R _ _ ⟨w, hw⟩, restrictRegionσ_apply]

omit [DecidableRel G.Adj] in
/-- The host `univ \ R` restriction is the nested geometry's fused leg of the blue
restriction (to `S \ R`) and the complement restriction (to `univ \ S`). -/
theorem nestedComplPhysical_restrict {R S : Finset V} (hRS : R ⊆ S) (cfg : V → Fin d) :
    (nestedThreeBlockGeometry (V := V) hRS).complPhysical (d := d)
        (restrictRegionσ (V := V) (d := d) (S \ R) cfg)
        (restrictRegionσ (V := V) (d := d) (Finset.univ \ S) cfg) =
      restrictRegionσ (V := V) (d := d) (Finset.univ \ R) cfg := by
  funext w
  rw [ThreeBlockGeometry.complPhysical]
  by_cases hb : w.1 ∈ (nestedThreeBlockGeometry (V := V) hRS).blue
  · rw [dif_pos hb, restrictRegionσ_apply, restrictRegionσ_apply]
  · rw [dif_neg hb, restrictRegionσ_apply, restrictRegionσ_apply]

end PEPS
end TNLean
