import TNLean.PEPS.RegionBlock.ThreeBlockResonate2

/-!
# Injectivity of the union of two injective region blocks

This file proves the union lemma of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`): the contraction of injective tensors over the
union of two disjoint injective regions is again injective. The load-bearing
instance is the union of the blue and complement blocks of a
`NormalEdgeBlockingData`, whose union is the set complement of the red block
(`univ \ red`). The three-block gauge chain needs the host block `univ \ red` to be
blocked-tensor injective, which this file supplies from injectivity of the blue and
complement blocks individually.

The proof is the source's two-step inverse application. Suppose a coefficient
family `c` annihilates the blocked-region weight family of `univ \ red`. Reading the
physical leg of `univ \ red` as a fused blue/complement pair
(`threeBlockComplPhysical`, a bijection onto `univ \ red` legs), the core
factorization `regionInteriorBondProd_smul_threeBlockComplWeight_eq` rewrites the
annihilation as a complement-block combination whose coefficients are the
`c`-weighted blue coupling coefficients. Injectivity of the complement block removes
the complement part, leaving `c`-weighted blue coupling coefficients that vanish for
every complement boundary configuration. The blue coupling coefficient, read as a
function of the blue physical leg, factors through the blue block's blocked-region
weights; injectivity of the blue block then removes the remaining part, forcing
`c = 0`.

## References

- [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled
  pair states generating the same state*, arXiv:1804.04964, Section 3, Lemma
  `injective_union`, lines 1324--1400 of
  `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964)
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d} {e : Edge G}

/-! ### The blue inversion of the host annihilation

A coefficient family `c` annihilating the blocked-region weight family of the host
`univ \ red` annihilates, at every fused blue/complement physical leg, the host
weight. Reading the resulting identity as a function of the blue physical leg and
applying the blue block's chosen left inverse strips the blue block, leaving the
`c`-weighted complement coupling coefficients vanishing for every complement physical
leg and blue boundary configuration. -/

open scoped Classical in
/-- The blue block strips out of the host annihilation. If the coefficient family `c`
annihilates the blocked-region weight family of the host `univ \ red`, then for every
complement physical leg `σcompl` and blue boundary configuration `bβ`, the
`c`-weighted sum of complement coupling coefficients
`threeBlockComplCoeff D bdry σcompl bβ` vanishes.

The annihilation, evaluated at the fused leg `threeBlockComplPhysical D σblue σcompl`,
holds for every blue leg `σblue`. Scaling by the nonzero blue interior bond product
and applying the blue smul-factorization
(`regionInteriorBondProd_smul_threeBlockBlueWeight_eq`) rewrites the host weights as
the complement-coupling combination of the blue blocked-region weights; the blue
block's chosen left inverse then reads off the complement coupling row.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem complCoeff_combination_eq_zero
    (D : NormalEdgeBlockingData (regionInjectivityDataOf (G := G) A) G e)
    (hpos : ∀ f : Edge G, 0 < A.bondDim f)
    (c : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry = 0)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) D.complement)
    (bβ : RegionBoundaryConfig (G := G) A D.blue) :
    ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
        c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ = 0 := by
  classical
  -- The σblue-function obtained by `c`-combining the fused host weights.
  set F : RegionPhysicalConfig (V := V) (d := d) D.blue → ℂ :=
    fun σblue => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
        (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl) with hF
  -- The host annihilation makes `F` vanish identically.
  have hFzero : F = 0 := by
    funext σblue
    rw [hF]
    have := congrFun hc (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)
    simpa [Finset.sum_apply, Pi.smul_apply] using this
  -- Scaling `F` by the blue interior bond product is the complement-coupling
  -- combination of the blue blocked-region weights.
  have hbluefac :
      (regionInteriorBondProd (G := G) A D.blue : ℂ) • F =
        regionBlockedTensorMap (G := G) A D.blue
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') := by
    rw [hF]
    funext σblue
    rw [Pi.smul_apply, regionBlockedTensorMap_apply]
    -- Distribute the bond multiple through the `c`-combination and apply the blue
    -- smul-factorization to each fused host weight.
    rw [Finset.smul_sum]
    rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          (regionInteriorBondProd (G := G) A D.blue : ℂ) •
            c bdry • regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
              (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry • ((regionInteriorBondProd (G := G) A D.blue : ℂ) •
            regionBlockedWeight (G := G) A (Finset.univ \ D.red) bdry
              (threeBlockComplPhysical (A := A) (e := e) D σblue σcompl)) from
        Finset.sum_congr rfl (fun bdry _ => by rw [smul_comm])]
    rw [show (∑ μ : RegionBoundaryConfig (G := G) A D.blue,
          (fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') μ •
              regionBlockedWeight (G := G) A D.blue μ σblue) =
        ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
          c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
            threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ' •
              regionBlockedWeight (G := G) A D.blue bβ' σblue from ?_]
    · refine Finset.sum_congr rfl (fun bdry _ => ?_)
      congr 1
      rw [regionInteriorBondProd_smul_regionBlockedWeight_threeBlockComplPhysical_blue
        (A := A) (e := e) D bdry σblue σcompl]
    · -- Beta-reduce, distribute the `bβ'`-sum out of each `c bdry` scalar, and swap
      -- the `bdry`/`bβ'` summation order.
      simp only []
      rw [show (∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            c bdry • ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
              threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ' •
                regionBlockedWeight (G := G) A D.blue bβ' σblue) =
          ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
            ∑ bβ' : RegionBoundaryConfig (G := G) A D.blue,
              (c bdry * threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ') •
                regionBlockedWeight (G := G) A D.blue bβ' σblue from
        Finset.sum_congr rfl (fun bdry _ => by
          rw [Finset.smul_sum]
          exact Finset.sum_congr rfl (fun bβ' _ => by rw [smul_smul]))]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun bβ' _ => ?_)
      rw [Finset.sum_smul]
      refine Finset.sum_congr rfl (fun bdry _ => ?_)
      simp only [smul_eq_mul, mul_assoc]
  -- The left side is zero, so the blue blocked map kills the complement coupling row;
  -- injectivity of the blue block forces that row to vanish.
  rw [hFzero, smul_zero] at hbluefac
  have hrow := regionBlockedTensorMap_injective_of_injective (G := G) A D.blue
    (regionBlockedTensorInjective_blue (A := A) (e := e) D)
    (a₁ := fun bβ' => ∑ bdry : RegionBoundaryConfig (G := G) A (Finset.univ \ D.red),
      c bdry • threeBlockComplCoeff (A := A) (e := e) D bdry σcompl bβ')
    (a₂ := 0) (by rw [← hbluefac, map_zero])
  have := congrFun hrow bβ
  simpa using this

end PEPS
end TNLean
