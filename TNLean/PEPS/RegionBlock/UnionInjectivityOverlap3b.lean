/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3

/-!
# The overlapping union lemma: the first-strip reduction and the bridge coefficient identity

This file continues `TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3` (split for the
file-length convention): the left first-strip combination reduced to the `P₂` blocked-region
weights, and the bridge host-coefficient identity in the right geometry's native types.

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

/-! ### The left first-strip combination, reduced to the `P₂` weights

The first strip's vanishing left coupling combination, scaled by the positive left crossing
bond and read through the crossing collapse, expresses the left-indicator combination of the
`R₂ \ R₁` blocked-region weights as zero, for every left blue `R₁` boundary configuration. -/

open scoped Classical in
/-- The left first-strip combination read through the crossing collapse vanishes: for a
coefficient family `c` over the union host configurations whose host blocked-weight combination
vanishes, and every left blue `R₁` boundary configuration `β₁`, the left-indicator combination
of the `R₂ \ R₁` blocked-region weights is zero. -/
theorem overlapLeft_firstStrip_weightCombination_eq_zero {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
        (fun b => c (regionBoundaryConfigCongr (A := A)
            (overlapLeftGeometry_univ_sdiff_red R₁ R₂) b)) bdry •
          regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (β₁ : RegionBoundaryConfig (G := G) A R₁)
    (σcompl : RegionPhysicalConfig (V := V) (d := d) (R₂ \ R₁)) :
    ∑ bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁),
        (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            c bdry *
              (if ∃ q : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A (R₂ \ R₁) bc' σcompl = 0 := by
  classical
  have hHL : Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red = R₁ ∪ R₂ :=
    overlapLeftGeometry_univ_sdiff_red R₁ R₂
  set c'' : RegionBoundaryConfig (G := G) A
      (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) → ℂ :=
    fun b => c (regionBoundaryConfigCongr (A := A) hHL b) with hc''
  -- The first strip: the `c''`-combination of the left complement couplings vanishes.
  have hstrip := overlap_firstStrip (G := G) (A := A) (R₁ := R₁) (R₂ := R₂) hR₁ c'' hc σcompl β₁
  -- The crossing collapse expresses the scaled coupling combination through the `R₂\R₁` weights.
  have hcollapse := (overlapLeftGeometry (V := V) R₁ R₂).crossingBond_smul_complCoeff_combination_eq
    (A := A) c'' β₁ σcompl
  -- The first strip kills the left-hand side, so the indicator combination is zero.
  rw [hstrip, smul_zero] at hcollapse
  simp only [overlapLeftGeometry_blue, overlapLeftGeometry_complement] at hcollapse
  -- Per `bc'`, the literal-union coefficient equals the geometry-host coefficient. Reindex the
  -- host sum along the transport and rewrite each indicator; this is the only host conversion.
  have hcoeff : ∀ bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁),
      (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
          c bdry *
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q = bdry ∧
                  regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
              then (1 : ℂ) else 0)) =
        ∑ hostlab : RegionBoundaryConfig (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
          c'' hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A
                  (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
              then (1 : ℂ) else 0) := by
    intro bc'
    refine (Fintype.sum_equiv (regionBoundaryConfigCongr (A := A) hHL) _ _ (fun hostlab => ?_)).symm
    rw [hc'', smul_eq_mul,
      existsLabel_indicator_congr (A := A) hHL hostlab
        (fun q => regionBoundaryLabel (G := G) A R₁ q = β₁ ∧
          regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc')]
  -- Substitute the coefficient identity termwise and conclude by `hcollapse`.
  rw [Finset.sum_congr rfl (fun bc' _ => by rw [hcoeff bc'])]
  exact hcollapse.symm

private theorem overlapBridge_host_sum_eq {R₁ R₂ : Finset V}
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (bβ : RegionBoundaryConfig (G := G) A (R₁ ∩ R₂))
    (bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁))
    (hHR : Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂) :
    (∑ hostlab : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
      overlapBridgeRow (G := G) (A := A) c
          (regionBoundaryConfigCongr (A := A)
            hHR hostlab) *
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A
                (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
              regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
              regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
          then (1 : ℂ) else 0)) =
      ∑ b₂ : RegionBoundaryConfig (G := G) A R₂,
        overlapBridgeRow (G := G) (A := A) c b₂ *
          (if ∃ q : VirtualConfig A,
              regionBoundaryLabel (G := G) A R₂ q = b₂ ∧
                regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
                regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
            then (1 : ℂ) else 0) := by
  classical
  refine Fintype.sum_equiv (regionBoundaryConfigCongr (A := A) hHR) _ _
    (fun hostlab => ?_)
  exact congrArg (overlapBridgeRow (G := G) (A := A) c
      (regionBoundaryConfigCongr (A := A) hHR hostlab) * ·)
    (existsLabel_indicator_congr (A := A) hHR hostlab
      (fun q => regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
        regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'))

private theorem overlapBridge_host_coeff_eq {R₁ R₂ : Finset V}
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (bβ : RegionBoundaryConfig (G := G) A (R₁ ∩ R₂))
    (bc' : RegionBoundaryConfig (G := G) A (R₂ \ R₁))
    (hHR : Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂) :
    (∑ hostlab : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
      overlapBridgeRow (G := G) (A := A) c
          (regionBoundaryConfigCongr (A := A)
            hHR hostlab) *
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A
                (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
              regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
              regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
          then (1 : ℂ) else 0)) =
      ∑ β₁ : RegionBoundaryConfig (G := G) A R₁,
        (if ∃ q₁ : VirtualConfig A,
            regionBoundaryLabel (G := G) A R₁ q₁ = β₁ ∧
              regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q₁ = bβ
          then (1 : ℂ) else 0) *
          ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            c bdry *
              (if ∃ q₂ : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₂ = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q₂ = β₁ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q₂ = bc'
                then (1 : ℂ) else 0) :=
  (overlapBridge_host_sum_eq (G := G) (A := A) c bβ bc' hHR).trans
    (overlapBridge_coeff_eq (G := G) (A := A) c bβ bc')

/-- The bridge host-coefficient identity in the native types of the right overlap geometry. -/
theorem overlapBridge_geometry_host_coeff_eq {R₁ R₂ : Finset V}
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (bβ : RegionBoundaryConfig (G := G) A
      (overlapRightGeometry (V := V) R₁ R₂).blue)
    (bc' : RegionBoundaryConfig (G := G) A
      (overlapRightGeometry (V := V) R₁ R₂).complement)
    (hHR : Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂) :
    (∑ hostlab : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
      overlapBridgeRow (G := G) (A := A) c
          (regionBoundaryConfigCongr (A := A) hHR hostlab) *
        (if ∃ q : VirtualConfig A,
            regionBoundaryLabel (G := G) A
                (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
              regionBoundaryLabel (G := G) A
                (overlapRightGeometry (V := V) R₁ R₂).blue q = bβ ∧
              regionBoundaryLabel (G := G) A
                (overlapRightGeometry (V := V) R₁ R₂).complement q = bc'
          then (1 : ℂ) else 0)) =
      ∑ β₁ : RegionBoundaryConfig (G := G) A R₁,
        (if ∃ q₁ : VirtualConfig A,
            regionBoundaryLabel (G := G) A R₁ q₁ = β₁ ∧
              regionBoundaryLabel (G := G) A
                (overlapRightGeometry (V := V) R₁ R₂).blue q₁ = bβ
          then (1 : ℂ) else 0) *
          ∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            c bdry *
              (if ∃ q₂ : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₂ = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q₂ = β₁ ∧
                    regionBoundaryLabel (G := G) A
                      (overlapRightGeometry (V := V) R₁ R₂).complement q₂ = bc'
                then (1 : ℂ) else 0) := by
  convert overlapBridge_host_coeff_eq (G := G) (A := A) c bβ bc' hHR using 1
  all_goals rfl

end PEPS
end TNLean
