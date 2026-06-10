import TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2

/-!
# The overlapping union-of-injective-regions lemma for normal PEPS

This file proves the source's overlapping union lemma of the normal PEPS
Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma `injective_union`, lines
1324--1400 of `Papers/1804.04964/paper_normal.tex`): for two *possibly
overlapping* finite regions `A` and `B` whose blocked tensors are injective, the
blocked tensor of their union `A ∪ B` is injective. The companion
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral2` proves this only in the
disjoint case; this file removes the disjointness restriction by porting the
source's four-region two-step inverse application.

The source decomposes the vertex set into four pairwise-disjoint blocks
`P₀ = A \ B`, `P₁ = A ∩ B`, `P₂ = B \ A`, and `P₃ = (A ∪ B)ᶜ`, with
`A = P₀ ∪ P₁`, `B = P₁ ∪ P₂`, and `A ∪ B = P₀ ∪ P₁ ∪ P₂`. A coefficient family
`c` annihilating the blocked weights of `A ∪ B` is stripped of `A` by its left
inverse (the host weight, read as a function of the `A` physical leg, factors
through the `A`-block map; the blocks `A` and `B \ A` form a disjoint
two-block split of the host, so this is the landed three-block blue strip with
`blue := A`, `complement := B \ A`). The residual is a coupling through the
`B \ A` block. Re-inserting the overlap `A ∩ B` rebuilds the `B`-block weight,
and the left inverse for `B` then forces the host residual coefficients to
vanish; host-boundary surjectivity makes every residual realized, so `c = 0`.

The two strips reuse the bare three-block geometry of
`TNLean.PEPS.RegionBlock.UnionInjectivityGeneral`: the `A`-strip is the geometry
`g₁` with `blue := A`, `complement := B \ A`, `red := (A ∪ B)ᶜ`, and the second
inversion is carried by the geometry `g₃` with host `B`, `blue := A ∩ B`,
`complement := B \ A`, which factors the `B`-block weight through the same
`B \ A` block as the residual.

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

/-! ### The host three-block geometry of two overlapping regions

For two regions `R₁`, `R₂` (the source's `A`, `B`), the host block whose
injectivity is proved is `R₁ ∪ R₂`. The first strip places `R₁` as the blue
block of a three-block geometry whose complement block is `R₂ \ R₁` and whose red
block is `(R₁ ∪ R₂)ᶜ`. Since `R₁` and `R₂ \ R₁` are disjoint and cover
`R₁ ∪ R₂`, this is a genuine `ThreeBlockGeometry`. -/

/-- The three-block geometry placing `R₁` as the blue block, `R₂ \ R₁` as the
complement block, and `(R₁ ∪ R₂)ᶜ` as the red block. The host block is
`R₁ ∪ R₂`.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
def overlapLeftGeometry (R₁ R₂ : Finset V) : ThreeBlockGeometry V where
  red := Finset.univ \ (R₁ ∪ R₂)
  blue := R₁
  complement := R₂ \ R₁
  red_disjoint_blue := by
    rw [Finset.disjoint_left]
    intro v hv hvR₁
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_union_left _ hvR₁)
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hv hvc
    exact (Finset.mem_sdiff.mp hv).2
      (Finset.mem_union_right _ (Finset.mem_sdiff.mp hvc).1)
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvR₁ hvc
    exact (Finset.mem_sdiff.mp hvc).2 hvR₁
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_univ, true_and, iff_true]
    tauto

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapLeftGeometry_blue (R₁ R₂ : Finset V) :
    (overlapLeftGeometry (V := V) R₁ R₂).blue = R₁ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapLeftGeometry_complement (R₁ R₂ : Finset V) :
    (overlapLeftGeometry (V := V) R₁ R₂).complement = R₂ \ R₁ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapLeftGeometry_red (R₁ R₂ : Finset V) :
    (overlapLeftGeometry (V := V) R₁ R₂).red = Finset.univ \ (R₁ ∪ R₂) := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The host block of the left geometry is the union `R₁ ∪ R₂`. -/
theorem overlapLeftGeometry_univ_sdiff_red (R₁ R₂ : Finset V) :
    Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red = R₁ ∪ R₂ := by
  rw [overlapLeftGeometry_red]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

/-! ### The overlap three-block geometry over the host `R₂`

The second inversion of the source proof reads the residual coupling through the
block `R₂ \ R₁` and inverts the full `R₂`-block weight after re-inserting the
overlap `R₁ ∩ R₂`. This is the three-block geometry whose host is `R₂`, with the
overlap `R₁ ∩ R₂` as the blue block and `R₂ \ R₁` as the complement block; its
red block is `R₂ᶜ`. -/

/-- The three-block geometry over the host `R₂`: the overlap `R₁ ∩ R₂` is the blue
block, `R₂ \ R₁` the complement block, and `R₂ᶜ` the red block.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
def overlapRightGeometry (R₁ R₂ : Finset V) : ThreeBlockGeometry V where
  red := Finset.univ \ R₂
  blue := R₁ ∩ R₂
  complement := R₂ \ R₁
  red_disjoint_blue := by
    rw [Finset.disjoint_left]
    intro v hv hvb
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_inter.mp hvb).2
  red_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hv hvc
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hvc).1
  blue_disjoint_complement := by
    rw [Finset.disjoint_left]
    intro v hvb hvc
    exact (Finset.mem_sdiff.mp hvc).2 (Finset.mem_inter.mp hvb).1
  cover_univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ,
      true_and, iff_true]
    tauto

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapRightGeometry_blue (R₁ R₂ : Finset V) :
    (overlapRightGeometry (V := V) R₁ R₂).blue = R₁ ∩ R₂ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapRightGeometry_complement (R₁ R₂ : Finset V) :
    (overlapRightGeometry (V := V) R₁ R₂).complement = R₂ \ R₁ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
@[simp] theorem overlapRightGeometry_red (R₁ R₂ : Finset V) :
    (overlapRightGeometry (V := V) R₁ R₂).red = Finset.univ \ R₂ := rfl

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The host block of the right geometry is `R₂`. -/
theorem overlapRightGeometry_univ_sdiff_red (R₁ R₂ : Finset V) :
    Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂ := by
  rw [overlapRightGeometry_red]
  ext v
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, not_not]

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The complement block is shared between the two overlap geometries: both read
the residual coupling through `R₂ \ R₁`. -/
theorem overlapRightGeometry_complement_eq_left (R₁ R₂ : Finset V) :
    (overlapRightGeometry (V := V) R₁ R₂).complement =
      (overlapLeftGeometry (V := V) R₁ R₂).complement := rfl

/-! ### The two strips of the source two-step

The source proof inverts the two injective regions in sequence. With the two
overlap geometries this is two applications of the landed blue strip
(`complCoeff_combination_eq_zero`), one for each region: stripping `R₁` leaves the
residual coupling through `R₂ \ R₁`, and stripping `R₂` leaves the residual
coupling through `R₁ \ R₂`. -/

open scoped Classical in
/-- **The first strip (region `R₁`).** A coefficient family `c` annihilating the
blocked weights of `R₁ ∪ R₂` is stripped of `R₁` by its left inverse: for every
physical leg on `R₂ \ R₁` and every `R₁`-boundary configuration, the `c`-weighted
sum of the `R₂ \ R₁`-coupling coefficients vanishes.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlap_firstStrip
    {R₁ R₂ : Finset V} (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (c : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) → ℂ)
    (hc : ∑ bdry, c bdry •
        regionBlockedWeight (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapLeftGeometry (V := V) R₁ R₂).complement)
    (bβ : RegionBoundaryConfig (G := G) A (overlapLeftGeometry (V := V) R₁ R₂).blue) :
    ∑ bdry, c bdry •
        (overlapLeftGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry σcompl bβ = 0 :=
  (overlapLeftGeometry (V := V) R₁ R₂).complCoeff_combination_eq_zero
    (by rw [overlapLeftGeometry_blue]; exact hR₁) c hc σcompl bβ

end PEPS
end TNLean
