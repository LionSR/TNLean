import TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3

/-!
# The overlapping union lemma: the first-strip reduction and the bridge capstone

This file continues `TNLean.PEPS.RegionBlock.UnionInjectivityOverlap3` (split for the
file-length convention): the left first-strip combination reduced to the `P₂` blocked-region
weights, and the bridge capstone `overlap_bridge_rightCoupling_eq_zero` — the right
geometry's coupling combination vanishes from the first inverse application.

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

/-! ### The bridge: the right coupling combination vanishes

The right coupling combination, scaled by the positive right crossing bond and read through
the crossing collapse, is the bridge-row indicator combination of the `R₂ \ R₁` weights. The
bridge coefficient identity rewrites it as the overlap-glue-weighted combination of the left
first-strip combinations, each vanishing by `overlapLeft_firstStrip_weightCombination_eq_zero`.
Dividing by the positive right crossing bond gives the rebuild hypothesis. -/

open scoped Classical in
/-- **The bridge.** From the first strip's vanishing left coupling combination, the bridge row
`overlapBridgeRow c` (carried to the right host via the transport) makes the right coupling
combination vanish for every difference physical leg and overlap boundary configuration. This
is the exact hypothesis the rebuild step
`overlapRight_bondProd_smul_hostWeight_combination_eq_zero` consumes.

Source: arXiv:1804.04964, Section 3, Lemma `injective_union`, lines 1324--1400 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem overlap_bridge_rightCoupling_eq_zero {R₁ R₂ : Finset V}
    (hR₁ : RegionBlockedTensorInjective (G := G) A R₁)
    (c : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂) → ℂ)
    (hc : ∑ bdry : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red),
        (fun b => c (regionBoundaryConfigCongr (A := A)
            (overlapLeftGeometry_univ_sdiff_red R₁ R₂) b)) bdry •
          regionBlockedWeight (G := G) A
            (Finset.univ \ (overlapLeftGeometry (V := V) R₁ R₂).red) bdry = 0)
    (hpos : ∀ e : Edge G, 0 < A.bondDim e)
    (σcompl : RegionPhysicalConfig (V := V) (d := d)
        (overlapRightGeometry (V := V) R₁ R₂).complement)
    (bβ : RegionBoundaryConfig (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue) :
    ∑ bdry₂ : RegionBoundaryConfig (G := G) A
        (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
      (fun b => overlapBridgeRow (G := G) (A := A) c
          (regionBoundaryConfigCongr (A := A)
            (overlapRightGeometry_univ_sdiff_red R₁ R₂) b)) bdry₂ •
        (overlapRightGeometry (V := V) R₁ R₂).threeBlockComplCoeff bdry₂ σcompl bβ = 0 := by
  classical
  have hHR : Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red = R₂ :=
    overlapRightGeometry_univ_sdiff_red R₁ R₂
  set row : RegionBoundaryConfig (G := G) A
      (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) → ℂ :=
    fun b => overlapBridgeRow (G := G) (A := A) c
      (regionBoundaryConfigCongr (A := A) hHR b) with hrow
  -- The right crossing bond is positive.
  have hcrosspos : 0 < (overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd A :=
    (overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd_pos A hpos
  have hcrossne : ((overlapRightGeometry (V := V) R₁ R₂).blueRedCrossingBondProd A : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcrosspos.ne'
  -- It suffices to show the scaled combination vanishes.
  rw [← smul_right_injective ℂ hcrossne |>.eq_iff (a := _) (b := (0 : _)), smul_zero]
  -- The crossing collapse expresses the scaled combination through the `R₂\R₁` weights.
  have hcollapse := (overlapRightGeometry (V := V) R₁ R₂).crossingBond_smul_complCoeff_combination_eq
    (A := A) row bβ σcompl
  rw [hcollapse]
  -- Per `bc'`, transport the host coefficient sum to `R₂` and apply the bridge identity.
  have hcoeff : ∀ bc' : RegionBoundaryConfig (G := G) A
        (overlapRightGeometry (V := V) R₁ R₂).complement,
      (∑ hostlab : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A
                  (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue q = bβ ∧
                    regionBoundaryLabel (G := G) A
                      (overlapRightGeometry (V := V) R₁ R₂).complement q = bc'
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
                  then (1 : ℂ) else 0) := by
    intro bc'
    rw [show (∑ hostlab : RegionBoundaryConfig (G := G) A
          (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red),
          row hostlab •
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A
                  (Finset.univ \ (overlapRightGeometry (V := V) R₁ R₂).red) q = hostlab ∧
                  regionBoundaryLabel (G := G) A (overlapRightGeometry (V := V) R₁ R₂).blue q = bβ ∧
                    regionBoundaryLabel (G := G) A
                      (overlapRightGeometry (V := V) R₁ R₂).complement q = bc'
              then (1 : ℂ) else 0)) =
        ∑ b₂ : RegionBoundaryConfig (G := G) A R₂,
          overlapBridgeRow (G := G) (A := A) c b₂ *
            (if ∃ q : VirtualConfig A,
                regionBoundaryLabel (G := G) A R₂ q = b₂ ∧
                  regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
                    regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'
              then (1 : ℂ) else 0) from ?_]
    · exact overlapBridge_coeff_eq (G := G) (A := A) c bβ bc'
    · -- Transport the host sum to `R₂` and rewrite each indicator.
      refine Fintype.sum_equiv (regionBoundaryConfigCongr (A := A) hHR) _ _ (fun hostlab => ?_)
      rw [hrow, smul_eq_mul]
      exact congrArg (overlapBridgeRow (G := G) (A := A) c
          (regionBoundaryConfigCongr (A := A) hHR hostlab) * ·)
        (existsLabel_indicator_congr (A := A) hHR hostlab
          (fun q => regionBoundaryLabel (G := G) A (R₁ ∩ R₂) q = bβ ∧
            regionBoundaryLabel (G := G) A (R₂ \ R₁) q = bc'))
  -- Substitute, swap the `bc'`/`β₁` order, and recognize the vanishing strip per `β₁`.
  rw [Finset.sum_congr rfl (fun bc' _ => by rw [hcoeff bc', Finset.sum_smul])]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero (fun β₁ _ => ?_)
  -- Pull the `β₁`-indicator out and recognize the left first-strip combination, which vanishes.
  rw [Finset.sum_congr rfl (fun bc' _ => by rw [mul_smul]), ← Finset.smul_sum]
  have hstripzero := overlapLeft_firstStrip_weightCombination_eq_zero (G := G) (A := A)
      hR₁ c hc β₁ σcompl
  rw [(by exact hstripzero : (∑ x : RegionBoundaryConfig (G := G) A
        (overlapRightGeometry (V := V) R₁ R₂).complement,
        (∑ bdry : RegionBoundaryConfig (G := G) A (R₁ ∪ R₂),
            c bdry *
              (if ∃ q₂ : VirtualConfig A,
                  regionBoundaryLabel (G := G) A (R₁ ∪ R₂) q₂ = bdry ∧
                    regionBoundaryLabel (G := G) A R₁ q₂ = β₁ ∧
                      regionBoundaryLabel (G := G) A (R₂ \ R₁) q₂ = x
                then (1 : ℂ) else 0)) •
          regionBlockedWeight (G := G) A (overlapRightGeometry (V := V) R₁ R₂).complement
            x σcompl) = 0), smul_zero]

end PEPS
end TNLean
