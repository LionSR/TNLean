import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap2

/-!
# The overlapping union lemma: the P₀-outer bridge and the closure

This file supplies the final sub-step of the source's overlapping union-of-injective-regions
lemma of the normal PEPS Fundamental Theorem (arXiv:1804.04964, Section 3, Lemma
`injective_union`, lines 1324--1400 of `Papers/1804.04964/paper_normal.tex`) and assembles
the full overlapping union theorem `regionBlockedTensorInjective_union_overlap`.

The companions `TNLean.PEPS.RegionBlock.UnionInjectivityOverlap` and
`TNLean.PEPS.RegionBlock.UnionInjectivityOverlap2` land the two host three-block geometries
(`overlapLeftGeometry`, `overlapRightGeometry`), the first inverse application
`overlap_firstStrip`, and the rebuild step
`overlapRight_bondProd_smul_hostWeight_combination_eq_zero`.

With the four parts `P₀ = R₁ \ R₂`, `P₁ = R₁ ∩ R₂`, `P₂ = R₂ \ R₁`, both the left geometry's
complement coupling and the right geometry's complement coupling are sums of the same `P₂`
vertex product over global virtual configurations. The landed crossing collapse
(`blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq`) reads each coupling, scaled by its
own positive blue/red crossing bond product, as the same family of `P₂` blocked-region
weights `regionBlockedWeight A P₂`, with an existence-indicator coefficient. The bridge matches
the two indicator coefficients: the right geometry's coupling combination, scaled and read
through the `P₂` weights, is exactly the left geometry's first-strip combination read through
the same weights, so it vanishes by `overlap_firstStrip`.

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

/-! ### The shared complement block `P₂`

Both overlap geometries have complement block `R₂ \ R₁ = P₂`, so both complement couplings
read the same `P₂` blocked-region weights `regionBlockedWeight A (R₂ \ R₁)`. -/

omit [LinearOrder V] [DecidableRel G.Adj] in
/-- The two overlap geometries share the complement block `R₂ \ R₁`. -/
theorem overlap_complement_eq (R₁ R₂ : Finset V) :
    (overlapLeftGeometry (V := V) R₁ R₂).complement =
      (overlapRightGeometry (V := V) R₁ R₂).complement := rfl

/-! ### Reducing a coupling combination to the `P₂` blocked-region weights

The landed crossing collapse `blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq` reads, for
either overlap geometry `g`, the positive crossing-bond multiple of the complement coupling
`threeBlockComplCoeff g hostlab σ bluelab` as a sum over complement boundary configurations
`bc'` of an existence indicator times the complement weight `regionBlockedWeight A g.complement
bc' σ`. Distributing a coefficient family over the geometry's host boundary configurations
through this collapse expresses the scaled coupling combination as an
existence-indicator-weighted combination of the complement weights. -/

open scoped Classical in
/-- For a `ThreeBlockGeometry` `g` and a coefficient family `coef` over the host boundary
configurations, the crossing-bond multiple of the `coef`-combination of the complement
couplings (at a fixed blue boundary configuration `bβ`) is the combination of the complement
blocked-region weights with the existence-indicator coefficient
`∑ hostlab, coef hostlab • 1[∃ q realizing host = hostlab, blue = bβ, complement = bc']`. -/
theorem ThreeBlockGeometry.crossingBond_smul_complCoeff_combination_eq
    (g : ThreeBlockGeometry V)
    (coef : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red) → ℂ)
    (bβ : RegionBoundaryConfig (G := G) A g.blue)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) g.complement) :
    (g.blueRedCrossingBondProd A : ℂ) •
        ∑ hostlab : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
          coef hostlab • g.threeBlockComplCoeff hostlab σcompl bβ =
      ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
        (∑ hostlab : RegionBoundaryConfig (G := G) A (Finset.univ \ g.red),
            coef hostlab •
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                    regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                      regionBoundaryLabel (G := G) A g.complement q = bc'
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A g.complement bc' σcompl := by
  classical
  rw [Finset.smul_sum]
  rw [Finset.sum_congr rfl (g := fun hostlab =>
        coef hostlab • ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                  regionBoundaryLabel (G := G) A g.complement q = bc'
            then (1 : ℂ) else 0) • regionBlockedWeight (G := G) A g.complement bc' σcompl)
      (fun hostlab _ => by
        rw [smul_comm, g.blueRedCrossingBondProd_smul_threeBlockComplCoeff_eq hostlab bβ σcompl])]
  -- Push the `coef hostlab` scalar into each `bc'` summand.
  rw [Finset.sum_congr rfl (g := fun hostlab =>
        ∑ bc' : RegionBoundaryConfig (G := G) A g.complement,
          (coef hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (Finset.univ \ g.red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A g.blue q = bβ ∧
                    regionBoundaryLabel (G := G) A g.complement q = bc'
              then (1 : ℂ) else 0)) •
            regionBlockedWeight (G := G) A g.complement bc' σcompl)
      (fun hostlab _ => by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl (fun bc' _ => by rw [smul_assoc]))]
  -- Swap the `hostlab` and `bc'` summation order and gather the coefficient.
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun bc' _ => ?_)
  rw [Finset.sum_smul]

end PEPS
end TNLean
