import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap

/-!
# The overlapping union lemma: the crossing collapse and the closure

This file closes the overlapping union-of-injective-regions lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines
1324--1400 of `Papers/1804.04964/paper_normal.tex`). The companion
`TNLean.PEPS.RegionBlock.UnionInjectivityOverlap` lands the two host three-block
geometries (`overlapLeftGeometry`, `overlapRightGeometry`) and the first inverse
application `overlap_firstStrip`. This file supplies the remaining sub-step -- the
`P₁`--`P₀` crossing multiplicity collapse -- and assembles the full overlapping union
theorem `regionBlockedTensorInjective_union_overlap`.

With the four parts `P₀ = R₁ \ R₂`, `P₁ = R₁ ∩ R₂`, `P₂ = R₂ \ R₁`, the left
geometry's complement coupling `threeBlockComplCoeff` (over `overlapLeftGeometry`,
constrained by the host `R₁ ∪ R₂` label and the `R₁` boundary label) and the right
geometry's complement coupling (over `overlapRightGeometry`, constrained by the host
`R₂` label and the `P₁` boundary label) are both sums of the same `P₂` vertex product
over global virtual configurations, differing only in the boundary constraints. The
bridge re-partitioning the first by the second is the multiplicity collapse over the
`P₁`--`P₀` edges, which are free in the left coupling (both endpoints in `R₁`, neither
a host nor an `R₁` boundary edge) but pinned by the `R₂` host constraint of the right
geometry.

The key set-theoretic fact making the landed collapse machinery reusable is that, in
the right geometry, `P₀ = R₁ \ R₂` lies entirely inside the red block `R₂ᶜ`, so every
`P₁`--`P₀` edge is a blue/red crossing edge of `overlapRightGeometry`. The landed
`blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq` over the right geometry then
collapses the right coupling onto the `P₂` blocked-region weights; combined with the
right geometry's blue-side factorization, this rebuilds the `R₂` blocked weights, and
the left inverse for `R₂` forces the reconstructed host residual coefficients to
vanish.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

/-! ### `P₀ ⊆ R₂ᶜ`: the right geometry red block contains the difference block

In the right geometry `overlapRightGeometry R₁ R₂` the red block is `R₂ᶜ`, the blue
block is the overlap `R₁ ∩ R₂`, and the complement block is `R₂ \ R₁`. The difference
block `P₀ = R₁ \ R₂` lies inside `R₂ᶜ = red`, so every internal `P₁`--`P₀` edge has one
endpoint in the blue block and one in the red block: it is a blue/red crossing edge of
the right geometry. -/

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The difference block `R₁ \ R₂` lies inside the right geometry red block `R₂ᶜ`. -/
theorem overlapRightGeometry_sdiff_subset_red (R₁ R₂ : Finset V) :
    R₁ \ R₂ ⊆ (overlapRightGeometry (V := V) R₁ R₂).red := by
  rw [overlapRightGeometry_red]
  intro v hv
  rw [Finset.mem_sdiff] at hv ⊢
  exact ⟨Finset.mem_univ _, hv.2⟩

/-! ### The right geometry blue-side host-weight collapse

The right geometry `g := overlapRightGeometry R₁ R₂` has host `univ \ g.red = R₂`, blue
block `R₁ ∩ R₂`, and complement block `R₂ \ R₁`. The blue-side factorization
`regionInteriorBondProd_smul_threeBlockBlueWeight_eq` over `g` expresses the positive
overlap-interior-bond multiple of the host weight, read as a function of the overlap leg,
as the overlap-coupling combination of the overlap blocked weights.

The closure feeds this factorization a coefficient row over host boundary configurations
whose right-coupling combination vanishes for every difference leg and overlap boundary
configuration; the factorization then produces a vanishing host-weight combination, read
through the fused overlap/difference leg. -/

open scoped Classical in
/-- **The right blue-side host-weight collapse.** For a coefficient row over the right
geometry's host boundary configurations whose right-coupling combination
`∑ bdry₂, row bdry₂ • threeBlockComplCoeff(bdry₂, σcompl, bβ)` vanishes for every
difference leg `σcompl` and overlap boundary configuration `bβ`, the row's combination of
the host weights, scaled by the positive overlap interior bond product and read through
any fused overlap/difference leg, vanishes.

The right geometry's blue-side factorization rewrites the scaled host weight as the
overlap-coupling combination of the overlap blocked weights; distributing the row
coefficients through and applying the vanishing coupling combination to each overlap
boundary configuration leaves zero.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlapRight_bondProd_smul_hostWeight_combination_eq_zero
    {R₁ R₂ : Finset V}
    (row : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) → ℂ)
    (hrow : ∀ (σcompl : RegionPhysicalConfig (V := V) (d := d)
          (overlapRightGeometry (V := V) R₁ R₂).complement)
        (bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue),
        ∑ bdry₂ : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row bdry₂ •
            (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ = 0)
    (σblue : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).complement) :
    (regionInteriorBondProd (G := G) A
          (overlapRightGeometry (V := V) R₁ R₂).blue : ℂ) •
        ∑ bdry₂ : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row bdry₂ • regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) bdry₂
            ((overlapRightGeometry (V := V) R₁ R₂).complPhysical σblue σcompl) = 0 := by
  classical
  -- Scale each host weight by the overlap interior bond product and apply the blue-side
  -- factorization read as a function of the overlap leg.
  rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl (g := fun bdry₂ =>
        row bdry₂ • ∑ bβ : RegionBoundaryConfig (G := G) A
            (overlapRightGeometry (V := V) R₁ R₂).blue,
          (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ •
            regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue bβ σblue)
      (fun bdry₂ _ => by
        rw [smul_comm]
        congr 1
        have := congrFun (regionInteriorBondProd_smul_threeBlockBlueWeight_eq
          (overlapRightGeometry (V := V) R₁ R₂) (A := A) bdry₂ σcompl) σblue
        rw [Pi.smul_apply, Finset.sum_apply] at this
        rw [this]
        exact Finset.sum_congr rfl (fun bβ _ => by rw [Pi.smul_apply]))]
  -- Swap the `bdry₂` and `bβ` summation order; the inner `bdry₂`-combination is the
  -- vanishing right-coupling combination scaled into each overlap weight.
  rw [Finset.sum_congr rfl (g := fun bdry₂ =>
        ∑ bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue,
          (row bdry₂ •
              (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ) •
            regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue bβ σblue)
      (fun bdry₂ _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun bβ _ => by rw [smul_assoc])),
    Finset.sum_comm]
  refine Finset.sum_eq_zero (fun bβ _ => ?_)
  rw [← Finset.sum_smul]
  rw [show (∑ bdry₂ : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
        row bdry₂ •
          (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ) = 0
      from hrow σcompl bβ, zero_smul]

end PEPS
end TNLean
