/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusWindowPeeling.BondInsertedRegion
import TNLean.PEPS.TorusWindowBondUniform
import TNLean.PEPS.TwoInjectiveComparison.Basic

/-!
# The single-bond peeling of the staircase end-pair equality

The two-dimensional strengthening of the normal PEPS Fundamental Theorem
(arXiv:1804.04964, the corollary at lines 2296--2318 of
`Papers/1804.04964/paper_normal.tex`) extracts the bond operator on the distinguished edge `e` from
the open-boundary end-pair equality `staircasePair_insert_eq_open`.  This file performs the peeling
of that equality onto the single bond `e`.  It first factors the normalized three-block coupling
into the genuine opposite-window blocked tensor, with incompatible external labels giving zero.
It then rewrites both end-pair extensions as contractions over `e` and applies the two-injective-
family comparison to obtain the unique virtual operation.  The final section specializes the same
extension equality to bond-inserted end-window inserts and obtains equality of the corresponding
region-inserted coefficients.

## The peeling and end operation

The exact boundary-coordinate factorizations separate the reference-edge coordinate from each
window's external legs and split the end-pair boundary into its left and right parts.  In these
coordinates the normalized blue coupling is the genuine tensor of the opposite window on the
compatible external-label fibre and is zero elsewhere.  Thus equal end-pair extensions give the
single-bond contraction identity used by `existsUnique_virtualOperation_of_endPair`; injectivity of
only the two genuine end-window blocked tensors yields the unique matrix on `e`.

For the bond-inserted specialization, the theorem
`regionInsertedCoeff_eq_extendInsert_bondInserted` of
`TNLean/PEPS/TorusWindowPeeling/BondInsertedRegion.lean` writes the region-inserted coefficient as
the assembled deformed state of the corner-extended insert.  Chaining these identities through
`staircasePair_insert_eq_open` gives equality of the two region-inserted coefficients.  The
remaining operator-map composition and cross-tensor gauge assembly are recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected entangled pair states
  generating the same state*, arXiv:1804.04964, the corollary and proof sketch at lines
  2296--2445 of `Papers/1804.04964/paper_normal.tex`](https://arxiv.org/abs/1804.04964); the
  filled-in derivation in `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.
-/

open scoped BigOperators Matrix

namespace TNLean
namespace PEPS

section CompatibleBoundaryLabels

variable {V : Type*} [Fintype V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ}
variable {A : Tensor G d}

private theorem sum_mul_dite_eq_sum_fiber
    {I K X : Type*} [Fintype I] [Fintype K] [Finite X] [DecidableEq X]
    (E : I ≃ K × X) (x : X) (f : I → ℂ) (w : K → ℂ) :
    (∑ i : I, f i * (if _h : (E i).2 = x then w (E i).1 else 0)) =
      ∑ k : K, f (E.symm (k, x)) * w k := by
  classical
  let _ : Fintype X := Fintype.ofFinite X
  rw [← Equiv.sum_comp E.symm, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  rw [Finset.sum_eq_single x]
  · simp
  · intro x' _ hx'
    simp only [E.apply_symm_apply]
    rw [dite_eq_right hx']
    exact mul_zero _
  · intro hx
    exact absurd (Finset.mem_univ x) hx

private theorem linearIndependent_shared_of_joint
    {External K Physical : Type*} [Finite K] [Nonempty External]
    (T : External → K → Physical → ℂ)
    (hT : LinearIndependent ℂ
      (fun p : External × K ↦ (T p.1 p.2 : Physical → ℂ))) :
    LinearIndependent ℂ
      (fun k : K ↦ fun p : External × Physical ↦ T p.1 k p.2) := by
  classical
  let _ : Fintype K := Fintype.ofFinite K
  rw [Fintype.linearIndependent_iff]
  intro c hc k₀
  let eta₀ : External := Classical.arbitrary External
  have hjoint := linearIndependent_iff'.1 hT
  let support : Finset (External × K) :=
    {eta₀} ×ˢ (Finset.univ : Finset K)
  have hzero : (∑ p ∈ support, (fun p : External × K ↦ c p.2) p •
      (T p.1 p.2 : Physical → ℂ)) = 0 := by
    funext sigma
    rw [Finset.sum_apply]
    have hcsigma := congrFun hc (eta₀, sigma)
    rw [Finset.sum_apply] at hcsigma
    simp only [Pi.smul_apply, smul_eq_mul] at hcsigma ⊢
    rw [show support = {eta₀} ×ˢ (Finset.univ : Finset K) from rfl,
      Finset.sum_product]
    simp only [Finset.sum_singleton, Pi.zero_apply]
    exact hcsigma
  have hmem : (eta₀, k₀) ∈ support := by
    simp [support]
  simpa using hjoint support (fun p ↦ c p.2) hzero (eta₀, k₀) hmem

private noncomputable def compatibleBoundaryVirtualConfig (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) : VirtualConfig A :=
  fun eg =>
    if hR : IsRegionBoundaryEdge (G := G) R eg then μ ⟨eg, hR⟩
    else if hS : IsRegionBoundaryEdge (G := G) S eg then ν ⟨eg, hS⟩
    else ⟨0, hpos eg⟩

omit [Fintype V] in
private theorem compatibleBoundaryVirtualConfig_apply_left (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg) :
    compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos eg = μ ⟨eg, hR⟩ := by
  rw [compatibleBoundaryVirtualConfig, dite_eq_left hR]

omit [Fintype V] in
private theorem compatibleBoundaryVirtualConfig_apply_right (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (hcompat : ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩)
    (eg : Edge G) (hS : IsRegionBoundaryEdge (G := G) S eg) :
    compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos eg = ν ⟨eg, hS⟩ := by
  rw [compatibleBoundaryVirtualConfig]
  by_cases hR : IsRegionBoundaryEdge (G := G) R eg
  · rw [dite_eq_left hR]
    exact hcompat eg hR hS
  · rw [dite_eq_right hR, dite_eq_left hS]

private theorem compatibleBoundaryVirtualConfig_host_label (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg) :
    regionBoundaryLabel (G := G) A (Finset.univ \ R)
        (compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos) =
      regionComplementBoundaryConfig (G := G) A R μ := by
  funext f
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
  exact compatibleBoundaryVirtualConfig_apply_left R S μ ν hpos f.1
    ((isRegionBoundaryEdge_compl_iff (G := G) R f.1).mp f.2)

private theorem compatibleBoundaryVirtualConfig_complement_label (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (hpos : ∀ eg : Edge G, 0 < A.bondDim eg)
    (hcompat : ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩) :
    regionBoundaryLabel (G := G) A (Finset.univ \ S)
        (compatibleBoundaryVirtualConfig (G := G) R S μ ν hpos) =
      regionComplementBoundaryConfig (G := G) A S ν := by
  funext f
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig]
  exact compatibleBoundaryVirtualConfig_apply_right R S μ ν hpos hcompat f.1
    ((isRegionBoundaryEdge_compl_iff (G := G) S f.1).mp f.2)

private theorem boundary_compatible_of_virtualConfig_labels (R S : Finset V)
    (μ : RegionBoundaryConfig (G := G) A R)
    (ν : RegionBoundaryConfig (G := G) A S)
    (q : VirtualConfig A)
    (hhost : regionBoundaryLabel (G := G) A (Finset.univ \ R) q =
      regionComplementBoundaryConfig (G := G) A R μ)
    (hcompl : regionBoundaryLabel (G := G) A (Finset.univ \ S) q =
      regionComplementBoundaryConfig (G := G) A S ν) :
    ∀ (eg : Edge G) (hR : IsRegionBoundaryEdge (G := G) R eg)
      (hS : IsRegionBoundaryEdge (G := G) S eg), μ ⟨eg, hR⟩ = ν ⟨eg, hS⟩ := by
  intro eg hR hS
  have hqR := congrFun hhost (regionBoundaryEdgeToCompl (G := G) R ⟨eg, hR⟩)
  have hqS := congrFun hcompl (regionBoundaryEdgeToCompl (G := G) S ⟨eg, hS⟩)
  rw [regionBoundaryLabel_apply, regionComplementBoundaryConfig_apply_toCompl] at hqR hqS
  exact hqR.symm.trans hqS

end CompatibleBoundaryLabels

section Torus

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (1 < width)] [Fact (1 < height)]
variable {d : ℕ} {L K : ℕ} {B : Tensor (torusGraph width height) d}

private def horizontalStaircaseEndPairPhysicalConfig
    {L K : ℕ} (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair s L K) :=
  fun w ↦
    if hleft : w.1 ∈ horizontalStaircaseLeftWindow s L K then
      sigmaLeft ⟨w.1, hleft⟩
    else
      sigmaRight ⟨w.1, by
        have hw : w.1 ∈ horizontalStaircaseLeftWindow s L K ∪
            horizontalStaircaseRightWindow s L K := by
          simpa only [horizontalStaircaseEndPair] using w.2
        exact (Finset.mem_union.mp hw).resolve_left hleft⟩

omit [Fact (1 < width)] [Fact (1 < height)] in
private theorem restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_left
    {L K : ℕ} (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (horizontalStaircaseLeftWindow_subset_endPair s)
        (horizontalStaircaseEndPairPhysicalConfig s sigmaLeft sigmaRight) =
      sigmaLeft := by
  funext w
  rw [restrictSubRegionσ, horizontalStaircaseEndPairPhysicalConfig,
    dite_eq_left w.2]

omit [Fact (1 < width)] [Fact (1 < height)] in
private theorem restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_right
    {L K : ℕ} (hxw : 2 * L ≤ width) (s : TorusVertex width height)
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow s L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow s L K)) :
    restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (horizontalStaircaseRightWindow_subset_endPair s)
        (horizontalStaircaseEndPairPhysicalConfig s sigmaLeft sigmaRight) =
      sigmaRight := by
  funext w
  have hnotLeft : w.1 ∉ horizontalStaircaseLeftWindow s L K := fun hleft ↦
    (Finset.disjoint_left.mp (horizontalStaircaseEndPair_disjoint hxw s)) hleft w.2
  rw [restrictSubRegionσ, horizontalStaircaseEndPairPhysicalConfig,
    dite_eq_right hnotLeft]

private theorem horizontalStaircaseLeft_endPair_boundary_compatible
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) :
    ∀ (eg : Edge (torusGraph width height))
      (hW : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg)
      (hS : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) eg),
      μ ⟨eg, hW⟩ = ν ⟨eg, hS⟩ := by
  intro eg hW hS
  let f : HorizontalStaircaseLeftExternalBoundaryEdge (width := width) (height := height)
      (L := L) (K := K) ((a : ZMod width), (b : ZMod height)) := ⟨⟨eg, hS⟩, hW⟩
  have h := congrFun hcompat f
  simpa [f] using h

private theorem horizontalStaircaseRight_endPair_boundary_compatible
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) :
    ∀ (eg : Edge (torusGraph width height))
      (hW : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg)
      (hS : IsRegionBoundaryEdge (G := torusGraph width height)
        (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) eg),
      μ ⟨eg, hW⟩ = ν ⟨eg, hS⟩ := by
  intro eg hW hS
  let f : HorizontalStaircaseRightExternalBoundaryEdge (width := width) (height := height)
      (L := L) (K := K) ((a : ZMod width), (b : ZMod height)) := ⟨⟨eg, hS⟩, hW⟩
  have h := congrFun hcompat f
  simpa [f] using h

private theorem compatibleBoundaryVirtualConfig_rightWindow_label
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) :
    regionBoundaryLabel (G := torusGraph width height) A
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
        (compatibleBoundaryVirtualConfig (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) μ ν hpos) =
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) := by
  let E := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · simp only [E, horizontalStaircaseRightWindowBoundaryConfigEquiv_fst,
      horizontalStaircaseLeftWindowBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_left _ _ μ ν hpos _
      (isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A
        hL hK ha0 haw hbh)
  · funext f
    simp only [E, horizontalStaircaseRightWindowBoundaryConfigEquiv_snd,
      horizontalStaircaseEndPairBoundaryConfigEquiv_snd, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_right _ _ μ ν hpos
      (horizontalStaircaseLeft_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
      f.1.1 f.1.2

private theorem compatibleBoundaryVirtualConfig_leftWindow_label
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2) :
    regionBoundaryLabel (G := torusGraph width height) A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
        (compatibleBoundaryVirtualConfig (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) μ ν hpos) =
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1) := by
  let E := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  apply E.injective
  rw [E.apply_symm_apply]
  apply Prod.ext
  · simp only [E, horizontalStaircaseLeftWindowBoundaryConfigEquiv_fst,
      horizontalStaircaseRightWindowBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_left _ _ μ ν hpos _
      (isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge A
        hL hK ha0 haw hbh)
  · funext f
    simp only [E, horizontalStaircaseLeftWindowBoundaryConfigEquiv_snd,
      horizontalStaircaseEndPairBoundaryConfigEquiv_fst, regionBoundaryLabel_apply]
    exact compatibleBoundaryVirtualConfig_apply_right _ _ μ ν hpos
      (horizontalStaircaseRight_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
      f.1.1 f.1.2

/-! ### The common external-boundary normalization of the two end windows

For either end window, the red/exterior crossing edges in the nested three-block geometry are
precisely the window boundary edges other than the reference edge `e`.  Translation invariance
makes the full boundary-bond products of the two congruent windows equal, and removing the same
horizontal edge `e` from both products leaves one common crossing-bond normalization. -/

/-- In the nested geometry whose red block is the left end window, the red/exterior crossing
edges are exactly the left-window boundary edges other than the reference edge.

Source: arXiv:1804.04964, the two highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_isExternalCrossingEdge_iff
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (eg : Edge (torusGraph width height)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.swapBlueComplement.IsBlueRedCrossingEdge A eg ↔
      IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
        eg ≠ horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K := by
  dsimp only
  change (IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
    IsRegionBoundaryEdge (G := torusGraph width height)
      (Finset.univ \ horizontalStaircaseEndPair
        ((a : ZMod width), (b : ZMod height)) L K) eg) ↔ _
  rw [isRegionBoundaryEdge_compl_iff]
  constructor
  · rintro ⟨hleft, hpair⟩
    exact ⟨hleft,
      ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hpair⟩
  · rintro ⟨hleft, hne⟩
    exact ⟨hleft,
      isRegionBoundaryEdge_endPair_of_leftWindow A hL hK ha0 haw hbh hleft hne⟩

/-- In the nested geometry whose red block is the right end window, the red/exterior crossing
edges are exactly the right-window boundary edges other than the reference edge.

Source: arXiv:1804.04964, the two highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_isExternalCrossingEdge_iff
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (eg : Edge (torusGraph width height)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.swapBlueComplement.IsBlueRedCrossingEdge A eg ↔
      IsRegionBoundaryEdge (G := torusGraph width height)
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
        eg ≠ horizontalStaircaseReferenceEdge
          ((a : ZMod width), (b : ZMod height)) L K := by
  dsimp only
  change (IsRegionBoundaryEdge (G := torusGraph width height)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) eg ∧
    IsRegionBoundaryEdge (G := torusGraph width height)
      (Finset.univ \ horizontalStaircaseEndPair
        ((a : ZMod width), (b : ZMod height)) L K) eg) ↔ _
  rw [isRegionBoundaryEdge_compl_iff]
  constructor
  · rintro ⟨hright, hpair⟩
    exact ⟨hright,
      ne_referenceEdge_of_isRegionBoundaryEdge_endPair hL hK ha0 haw hbh hpair⟩
  · rintro ⟨hright, hne⟩
    exact ⟨hright,
      isRegionBoundaryEdge_endPair_of_rightWindow A hL hK ha0 haw hbh hright hne⟩

/-- **The two end-window blue-coupling normalizations agree.**

For each end window the crossing product is the bond-dimension product over its external legs,
namely its full boundary with the common reference edge removed.  The two end windows are
translates of the same `L × K` rectangle, so translation invariance makes their interior-bond
products equal.  Splitting the product over every torus edge into boundary and non-boundary parts
then makes their full boundary products equal; removing the same positive reference-edge factor
gives the displayed equality.

Source: arXiv:1804.04964, the translation-invariant corollary at lines 2296--2318 and its two
highlighted open-boundary end regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseEndWindows_externalCrossingBondProd_eq
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    let gleft := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    let gright := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    gleft.swapBlueComplement.blueRedCrossingBondProd A =
      gright.swapBlueComplement.blueRedCrossingBondProd A := by
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let e := horizontalStaircaseReferenceEdge s L K
  let gleft := nestedThreeBlockGeometry (V := TorusVertex width height)
    (horizontalStaircaseLeftWindow_subset_endPair (L := L) (K := K) s)
  let gright := nestedThreeBlockGeometry (V := TorusVertex width height)
    (horizontalStaircaseRightWindow_subset_endPair (L := L) (K := K) s)
  let boundaryProd := fun W : Finset (TorusVertex width height) ↦
    ∏ eg ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) W eg), A.bondDim eg
  have hinterior : regionInteriorBondProd (G := torusGraph width height) A Wleft =
      regionInteriorBondProd (G := torusGraph width height) A Wright := by
    exact regionInteriorBondProd_torusArcRectangle_eq hTI _ _ L K
  have hinteriorPos : 0 < regionInteriorBondProd (G := torusGraph width height) A Wleft :=
    regionInteriorBondProd_pos (G := torusGraph width height) A Wleft hpos
  have hboundary : boundaryProd Wleft = boundaryProd Wright := by
    apply Nat.eq_of_mul_eq_mul_right hinteriorPos
    calc
      boundaryProd Wleft * regionInteriorBondProd (G := torusGraph width height) A Wleft =
          ∏ eg : Edge (torusGraph width height), A.bondDim eg := by
        exact Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun eg : Edge (torusGraph width height) ↦
            IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg) A.bondDim
      _ = boundaryProd Wright *
          regionInteriorBondProd (G := torusGraph width height) A Wright := by
        exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
          (fun eg : Edge (torusGraph width height) ↦
            IsRegionBoundaryEdge (G := torusGraph width height) Wright eg) A.bondDim).symm
      _ = boundaryProd Wright *
          regionInteriorBondProd (G := torusGraph width height) A Wleft := by rw [hinterior]
  have hleftFilter :
      Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          gleft.swapBlueComplement.IsBlueRedCrossingEdge A eg) =
        (Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg)).erase e := by
    ext eg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [and_comm]
    exact horizontalStaircaseLeftWindow_isExternalCrossingEdge_iff
      A hL hK ha0 haw hbh eg
  have hrightFilter :
      Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          gright.swapBlueComplement.IsBlueRedCrossingEdge A eg) =
        (Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
          IsRegionBoundaryEdge (G := torusGraph width height) Wright eg)).erase e := by
    ext eg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    rw [and_comm]
    exact horizontalStaircaseRightWindow_isExternalCrossingEdge_iff
      A hL hK ha0 haw hbh eg
  have heLeft : e ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) Wleft eg) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge
      A hL hK ha0 haw hbh
  have heRight : e ∈ Finset.univ.filter (fun eg : Edge (torusGraph width height) ↦
      IsRegionBoundaryEdge (G := torusGraph width height) Wright eg) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge
      A hL hK ha0 haw hbh
  apply Nat.eq_of_mul_eq_mul_right (hpos e)
  calc
    gleft.swapBlueComplement.blueRedCrossingBondProd A * A.bondDim e =
        boundaryProd Wleft := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd, hleftFilter]
      exact Finset.prod_erase_mul _ _ heLeft
    _ = boundaryProd Wright := hboundary
    _ = gright.swapBlueComplement.blueRedCrossingBondProd A * A.bondDim e := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd, hrightFilter]
      exact (Finset.prod_erase_mul _ _ heRight).symm

/-- **The left-end blue coupling is the genuine right-window block.**

Suppose the left-window boundary configuration and the end-pair boundary configuration agree on
the left external legs.  In the nested geometry with red block the left window and blue block the
right window, the red/exterior crossing-bond multiple of `threeBlockBlueCoeff` is exactly the
right window's blocked-region weight.  Its boundary data are the reference-edge coordinate of
the left-window configuration and the right external data of the end-pair configuration.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)
    (σright : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm σright)
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) =
      regionBlockedWeight (G := torusGraph width height) A
        (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
          ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2))
        σright := by
  dsimp only
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let hblue : g.blue = Wright := horizontalStaircaseEndPair_sdiff_leftWindow (by omega) _
  let q₀ : VirtualConfig A := compatibleBoundaryVirtualConfig (G := torusGraph width height)
    Wleft S μ ν hpos
  have hqhost : regionBoundaryLabel (G := torusGraph width height) A
      (Finset.univ \ g.red) q₀ =
        regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ := by
    simpa [g, hWS, Wleft, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_host_label Wleft S μ ν hpos
  have hqcompl : regionBoundaryLabel (G := torusGraph width height) A g.complement q₀ =
      regionComplementBoundaryConfig (G := torusGraph width height) A S ν := by
    simpa [g, hWS, Wleft, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_complement_label Wleft S μ ν hpos
        (horizontalStaircaseLeft_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
  have hfactor := g.crossingBondProd_smul_threeBlockBlueCoeff_eq_regionBlockedWeight
    (A := A)
    (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S ν)
    ((regionPhysicalConfigCongr (d := d) hblue).symm σright) q₀ hqhost hqcompl
  change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
      g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ)
        ((regionPhysicalConfigCongr (d := d) hblue).symm σright)
        (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) =
    regionBlockedWeight (G := torusGraph width height) A Wright
      ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)) σright
  rw [hfactor]
  rw [regionBlockedWeight_congr (A := A) hblue]
  have hlabel : regionBoundaryConfigCongr (A := A) hblue
      (regionBoundaryLabel (G := torusGraph width height) A g.blue q₀) =
      regionBoundaryLabel (G := torusGraph width height) A Wright q₀ := by
    funext f
    rfl
  rw [hlabel, Equiv.apply_symm_apply]
  rw [compatibleBoundaryVirtualConfig_rightWindow_label A hL hK ha0 haw hbh hpos μ ν hcompat]

/-- If the left-window and end-pair boundary configurations disagree on a left external leg,
then the corresponding blue coupling is zero: no global virtual configuration can carry both
prescribed boundary labels.

Source: arXiv:1804.04964, the two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hne :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 ≠
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)
    (σblue : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      ((horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) \
        horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
        σblue
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) = 0 := by
  dsimp only
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  change g.threeBlockBlueCoeff
      (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft μ) σblue
      (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) = 0
  apply g.threeBlockBlueCoeff_eq_zero_of_no_compatible_boundary
  rintro ⟨q, hqhost, hqcompl⟩
  apply hne
  funext f
  have hcompat := boundary_compatible_of_virtualConfig_labels Wleft S μ ν q
    (by simpa [g, hWS, Wleft, S, nestedThreeBlockGeometry] using hqhost)
    (by simpa [g, hWS, Wleft, S, nestedThreeBlockGeometry] using hqcompl)
    f.1.1 f.2 f.1.2
  simpa using hcompat

/-- **Normalized left-end blue coupling.**

After the normalization appearing in `extendInsert`, the blue coupling for the left end window
vanishes unless its external boundary data agree with the left part of the end-pair boundary.
In the surviving case it is the genuine right-window blocked weight at the same reference-edge
coordinate and the right external data, multiplied by the inverse product of the exterior
interior-bond factor and the left external crossing-bond factor.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_normalized_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (mu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let S := horizontalStaircaseEndPair
      ((a : ZMod width), (b : ZMod height)) L K
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseLeftWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
          (regionComplementBoundaryConfig (G := torusGraph width height) A S nu) =
      if _hcompat :
          (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1
        then
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
            regionBlockedWeight (G := torusGraph width height) A
              (horizontalStaircaseRightWindow
                ((a : ZMod width), (b : ZMod height)) L K)
              ((horizontalStaircaseRightWindowBoundaryConfigEquiv
                A hL hK ha0 haw hbh).symm
                ((horizontalStaircaseLeftWindowBoundaryConfigEquiv
                  A hL hK ha0 haw hbh mu).1,
                  (horizontalStaircaseEndPairBoundaryConfigEquiv
                    A hL hK ha0 haw hbh nu).2)) sigmaRight
        else 0 := by
  dsimp only
  let S := horizontalStaircaseEndPair
    ((a : ZMod width), (b : ZMod height)) L K
  let hWS := horizontalStaircaseLeftWindow_subset_endPair
    ((a : ZMod width), (b : ZMod height)) (L := L) (K := K)
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let coeff := g.threeBlockBlueCoeff
    (regionComplementBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
    ((regionPhysicalConfigCongr (d := d)
      (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
        ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)
  let weight := regionBlockedWeight (G := torusGraph width height) A
    (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)
    ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
      ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).1,
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2)) sigmaRight
  change (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
      coeff = if hcompat : _ then
        ((regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ) *
          (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ * weight else 0
  by_cases hcompat :
      (horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1
  · rw [dite_eq_left hcompat]
    have hfactor := horizontalStaircaseLeftWindow_threeBlockBlueCoeff_factorization
      A hL hK ha0 haw hbh hpos mu nu hcompat sigmaRight
    dsimp only at hfactor
    change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
      coeff = weight at hfactor
    have houter :
        (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (regionInteriorBondProd_pos (G := torusGraph width height) A
          (Finset.univ \ S) hpos).ne'
    have hcrossPos : 0 < g.swapBlueComplement.blueRedCrossingBondProd A := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd]
      exact Finset.prod_pos (fun eg _ ↦ hpos eg)
    have hcross : (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcrossPos.ne'
    calc
      _ = ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
          ((g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
            coeff) := by
        rw [mul_inv_rev]
        field_simp
      _ = _ := by rw [hfactor]
  · rw [dite_eq_right hcompat]
    have hzero := horizontalStaircaseLeftWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
      A hL hK ha0 haw hbh mu nu hcompat
        ((regionPhysicalConfigCongr (d := d)
          (horizontalStaircaseEndPair_sdiff_leftWindow (by omega)
            ((a : ZMod width), (b : ZMod height)))).symm sigmaRight)
    dsimp only at hzero
    change coeff = 0 at hzero
    rw [hzero, mul_zero]

/-- **The right-end blue coupling is the genuine left-window block.**

Suppose the right-window boundary configuration and the end-pair boundary configuration agree on
the right external legs.  In the nested geometry with red block the right window and blue block
the left window, the red/exterior crossing-bond multiple of `threeBlockBlueCoeff` is exactly the
left window's blocked-region weight.  Its boundary data are the reference-edge coordinate of the
right-window configuration and the left external data of the end-pair configuration.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)
    (σleft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm σleft)
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) =
      regionBlockedWeight (G := torusGraph width height) A
        (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
        ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
          ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1))
        σleft := by
  dsimp only
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let Wleft := horizontalStaircaseLeftWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let hblue : g.blue = Wleft := horizontalStaircaseEndPair_sdiff_rightWindow (by omega) _
  let q₀ : VirtualConfig A := compatibleBoundaryVirtualConfig (G := torusGraph width height)
    Wright S μ ν hpos
  have hqhost : regionBoundaryLabel (G := torusGraph width height) A
      (Finset.univ \ g.red) q₀ =
        regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ := by
    simpa [g, hWS, Wright, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_host_label Wright S μ ν hpos
  have hqcompl : regionBoundaryLabel (G := torusGraph width height) A g.complement q₀ =
      regionComplementBoundaryConfig (G := torusGraph width height) A S ν := by
    simpa [g, hWS, Wright, S, q₀, nestedThreeBlockGeometry] using
      compatibleBoundaryVirtualConfig_complement_label Wright S μ ν hpos
        (horizontalStaircaseRight_endPair_boundary_compatible A hL hK ha0 haw hbh μ ν hcompat)
  have hfactor := g.crossingBondProd_smul_threeBlockBlueCoeff_eq_regionBlockedWeight
    (A := A)
    (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S ν)
    ((regionPhysicalConfigCongr (d := d) hblue).symm σleft) q₀ hqhost hqcompl
  change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) •
      g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ)
        ((regionPhysicalConfigCongr (d := d) hblue).symm σleft)
        (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) =
    regionBlockedWeight (G := torusGraph width height) A Wleft
      ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
        ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).1,
          (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).1)) σleft
  rw [hfactor]
  rw [regionBlockedWeight_congr (A := A) hblue]
  have hlabel : regionBoundaryConfigCongr (A := A) hblue
      (regionBoundaryLabel (G := torusGraph width height) A g.blue q₀) =
      regionBoundaryLabel (G := torusGraph width height) A Wleft q₀ := by
    funext f
    rfl
  rw [hlabel, Equiv.apply_symm_apply]
  rw [compatibleBoundaryVirtualConfig_leftWindow_label A hL hK ha0 haw hbh hpos μ ν hcompat]

/-- If the right-window and end-pair boundary configurations disagree on a right external leg,
then the corresponding blue coupling is zero.

Source: arXiv:1804.04964, the two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (μ : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (ν : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (hne :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh μ).2 ≠
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh ν).2)
    (σblue : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      ((horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) \
        horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    g.threeBlockBlueCoeff
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) μ)
        σblue
        (regionComplementBoundaryConfig (G := torusGraph width height) A
          (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K) ν) = 0 := by
  dsimp only
  let Wright := horizontalStaircaseRightWindow
    ((a : ZMod width), (b : ZMod height)) L K
  let S := horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair _
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  change g.threeBlockBlueCoeff
      (regionComplementBoundaryConfig (G := torusGraph width height) A Wright μ) σblue
      (regionComplementBoundaryConfig (G := torusGraph width height) A S ν) = 0
  apply g.threeBlockBlueCoeff_eq_zero_of_no_compatible_boundary
  rintro ⟨q, hqhost, hqcompl⟩
  apply hne
  funext f
  have hcompat := boundary_compatible_of_virtualConfig_labels Wright S μ ν q
    (by simpa [g, hWS, Wright, S, nestedThreeBlockGeometry] using hqhost)
    (by simpa [g, hWS, Wright, S, nestedThreeBlockGeometry] using hqcompl)
    f.1.1 f.2 f.1.2
  simpa using hcompat

/-- **Normalized right-end blue coupling.**

After the normalization appearing in `extendInsert`, the blue coupling for the right end window
vanishes unless its external boundary data agree with the right part of the end-pair boundary.
In the surviving case it is the genuine left-window blocked weight at the same reference-edge
coordinate and the left external data, multiplied by the inverse product of the exterior
interior-bond factor and the right external crossing-bond factor.

Source: arXiv:1804.04964, the end comparison in Lemma 5 at lines 2213--2252 and the two
highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_normalized_threeBlockBlueCoeff_factorization
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (mu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)) :
    let S := horizontalStaircaseEndPair
      ((a : ZMod width), (b : ZMod height)) L K
    let g := nestedThreeBlockGeometry (V := TorusVertex width height)
      (horizontalStaircaseRightWindow_subset_endPair
        ((a : ZMod width), (b : ZMod height)) (L := L) (K := K))
    (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
        g.threeBlockBlueCoeff
          (regionComplementBoundaryConfig (G := torusGraph width height) A
            (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
          ((regionPhysicalConfigCongr (d := d)
            (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
              ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
          (regionComplementBoundaryConfig (G := torusGraph width height) A S nu) =
      if _hcompat :
          (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
            (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2
        then
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
            regionBlockedWeight (G := torusGraph width height) A
              (horizontalStaircaseLeftWindow
                ((a : ZMod width), (b : ZMod height)) L K)
              ((horizontalStaircaseLeftWindowBoundaryConfigEquiv
                A hL hK ha0 haw hbh).symm
                ((horizontalStaircaseRightWindowBoundaryConfigEquiv
                  A hL hK ha0 haw hbh mu).1,
                  (horizontalStaircaseEndPairBoundaryConfigEquiv
                    A hL hK ha0 haw hbh nu).1)) sigmaLeft
        else 0 := by
  dsimp only
  let S := horizontalStaircaseEndPair
    ((a : ZMod width), (b : ZMod height)) L K
  let hWS := horizontalStaircaseRightWindow_subset_endPair
    ((a : ZMod width), (b : ZMod height)) (L := L) (K := K)
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let coeff := g.threeBlockBlueCoeff
    (regionComplementBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K) mu)
    ((regionPhysicalConfigCongr (d := d)
      (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
        ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
    (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)
  let weight := regionBlockedWeight (G := torusGraph width height) A
    (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K)
    ((horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh).symm
      ((horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).1,
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).1)) sigmaLeft
  change (regionInteriorBondProd (G := torusGraph width height) A (Finset.univ \ S) : ℂ)⁻¹ *
      coeff = if hcompat : _ then
        ((regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ) *
          (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ * weight else 0
  by_cases hcompat :
      (horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh mu).2 =
        (horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh nu).2
  · rw [dite_eq_left hcompat]
    have hfactor := horizontalStaircaseRightWindow_threeBlockBlueCoeff_factorization
      A hL hK ha0 haw hbh hpos mu nu hcompat sigmaLeft
    dsimp only at hfactor
    change (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) *
      coeff = weight at hfactor
    have houter :
        (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr
        (regionInteriorBondProd_pos (G := torusGraph width height) A
          (Finset.univ \ S) hpos).ne'
    have hcrossPos : 0 < g.swapBlueComplement.blueRedCrossingBondProd A := by
      rw [ThreeBlockGeometry.blueRedCrossingBondProd]
      exact Finset.prod_pos (fun eg _ ↦ hpos eg)
    have hcross : (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr hcrossPos.ne'
    calc
      _ = ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ) *
            (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
          ((g.swapBlueComplement.blueRedCrossingBondProd A : ℂ) * coeff) := by
        rw [mul_inv_rev]
        field_simp
      _ = _ := by rw [hfactor]
  · rw [dite_eq_right hcompat]
    have hzero := horizontalStaircaseRightWindow_threeBlockBlueCoeff_eq_zero_of_external_ne
      A hL hK ha0 haw hbh mu nu hcompat
        ((regionPhysicalConfigCongr (d := d)
          (horizontalStaircaseEndPair_sdiff_rightWindow (by omega)
            ((a : ZMod width), (b : ZMod height)))).symm sigmaLeft)
    dsimp only at hzero
    change coeff = 0 at hzero
    rw [hzero, mul_zero]

/-! ### The end-pair inserts as single-bond contractions -/

/-- **The left-window extension is a contraction across the reference edge.**

In boundary coordinates, extending an arbitrary insert on the left end window to the end pair
vanishes away from the fiber where the left external labels match.  Reindexing that surviving
fiber leaves exactly one sum, over the reference-edge coordinate: the insert on the left window
contracted with the genuine blocked tensor of the right window.  The displayed scalar is the
normalization already present in `extendInsert` and `threeBlockBlueCoeff`.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (C : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
    let hblue : S \ Wleft = Wright :=
      horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
    let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
    let sigmaRight := regionPhysicalConfigCongr (d := d) hblue
      (restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma)
    extendInsert (G := torusGraph width height) hWS C nu sigma =
      ((regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) *
        (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
        ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
          C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
            regionBlockedWeight (G := torusGraph width height) A Wright
              (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hWS : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hblue : S \ Wleft = Wright :=
    horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
  let sigmaBlue := restrictSubRegionσ (V := TorusVertex width height) (d := d)
    (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma
  let sigmaRight := regionPhysicalConfigCongr (d := d) hblue sigmaBlue
  let scalar : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  change extendInsert (G := torusGraph width height) hWS C nu sigma =
    scalar * ∑ k, C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
      regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [extendInsert]
  rw [Finset.mul_sum]
  change (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
      (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ)⁻¹ *
        (C mu sigmaLeft *
          g.threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
            sigmaBlue
            (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
    scalar * ∑ k, C (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
      regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        (regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ)⁻¹ *
          (C mu sigmaLeft *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ ?_)
      ring]
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wleft mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wleft,
        C mu sigmaLeft *
          (if _hcompat : (Eleft mu).2 = (Eend nu).1 then
            scalar * regionBlockedWeight (G := torusGraph width height) A Wright
              (Eright.symm ((Eleft mu).1, (Eend nu).2)) sigmaRight else 0)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ congrArg (C mu sigmaLeft * ·) ?_)
      have hnorm := horizontalStaircaseLeftWindow_normalized_threeBlockBlueCoeff_factorization
        A hL hK ha0 haw hbh hpos mu nu sigmaRight
      dsimp only at hnorm
      rw [Equiv.symm_apply_apply] at hnorm
      change _ = if _hcompat : (Eleft mu).2 = (Eend nu).1 then
        scalar * regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm ((Eleft mu).1, (Eend nu).2)) sigmaRight else 0 at hnorm
      exact hnorm]
  rw [sum_mul_dite_eq_sum_fiber Eleft (Eend nu).1
    (fun mu ↦ C mu sigmaLeft)
    (fun k ↦ scalar * regionBlockedWeight (G := torusGraph width height) A Wright
      (Eright.symm (k, (Eend nu).2)) sigmaRight)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  ring

/-- **The right-window extension is a contraction across the reference edge.**

This is the opposite-end form of
`horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction`.  Reindexing the unique
compatible external-label fiber leaves the genuine left-window blocked tensor contracted with
the insert on the right window over the single reference-edge coordinate.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
two highlighted open-boundary regions at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem horizontalStaircaseRightWindow_extendInsert_eq_singleBondContraction
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (C : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wright := horizontalStaircaseRightWindow s L K
    let Wleft := horizontalStaircaseLeftWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
    let hblue : S \ Wright = Wleft :=
      horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
    let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
    let sigmaLeft := regionPhysicalConfigCongr (d := d) hblue
      (restrictSubRegionσ (V := TorusVertex width height) (d := d)
        (Finset.sdiff_subset : S \ Wright ⊆ S) sigma)
    extendInsert (G := torusGraph width height) hWS C nu sigma =
      ((regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ) *
        (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹ *
        ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
          regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
            C (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wright := horizontalStaircaseRightWindow s L K
  let Wleft := horizontalStaircaseLeftWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hWS : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let hblue : S \ Wright = Wleft :=
    horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
  let g := nestedThreeBlockGeometry (V := TorusVertex width height) hWS
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hWS sigma
  let sigmaBlue := restrictSubRegionσ (V := TorusVertex width height) (d := d)
    (Finset.sdiff_subset : S \ Wright ⊆ S) sigma
  let sigmaLeft := regionPhysicalConfigCongr (d := d) hblue sigmaBlue
  let scalar : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (g.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  change extendInsert (G := torusGraph width height) hWS C nu sigma =
    scalar * ∑ k,
      regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        C (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [extendInsert]
  rw [Finset.mul_sum]
  change (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
      (regionInteriorBondProd (G := torusGraph width height) A
          (Finset.univ \ S) : ℂ)⁻¹ *
        (C mu sigmaRight *
          g.threeBlockBlueCoeff
            (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
            sigmaBlue
            (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
    scalar * ∑ k,
      regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        C (Eright.symm (k, (Eend nu).2)) sigmaRight
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        (regionInteriorBondProd (G := torusGraph width height) A
            (Finset.univ \ S) : ℂ)⁻¹ *
          (C mu sigmaRight *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu))) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ ?_)
      ring]
  rw [show (∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          ((regionInteriorBondProd (G := torusGraph width height) A
              (Finset.univ \ S) : ℂ)⁻¹ *
            g.threeBlockBlueCoeff
              (regionComplementBoundaryConfig (G := torusGraph width height) A Wright mu)
              sigmaBlue
              (regionComplementBoundaryConfig (G := torusGraph width height) A S nu)) =
      ∑ mu : RegionBoundaryConfig (G := torusGraph width height) A Wright,
        C mu sigmaRight *
          (if _hcompat : (Eright mu).2 = (Eend nu).2 then
            scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm ((Eright mu).1, (Eend nu).1)) sigmaLeft else 0)) from by
      refine Finset.sum_congr rfl (fun mu _ ↦ congrArg (C mu sigmaRight * ·) ?_)
      have hnorm := horizontalStaircaseRightWindow_normalized_threeBlockBlueCoeff_factorization
        A hL hK ha0 haw hbh hpos mu nu sigmaLeft
      dsimp only at hnorm
      rw [Equiv.symm_apply_apply] at hnorm
      change _ = if _hcompat : (Eright mu).2 = (Eend nu).2 then
        scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm ((Eright mu).1, (Eend nu).1)) sigmaLeft else 0 at hnorm
      exact hnorm]
  rw [sum_mul_dite_eq_sum_fiber Eright (Eend nu).2
    (fun mu ↦ C mu sigmaRight)
    (fun k ↦ scalar * regionBlockedWeight (G := torusGraph width height) A Wleft
      (Eleft.symm (k, (Eend nu).1)) sigmaLeft)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  ring

/-- **Equal end-pair extensions give the single-bond contraction identity.**

If an insert on the left end window and an insert on the right end window have equal extensions
to the end pair, then their boundary-coordinate forms agree after contraction over the sole shared
reference edge.  Translation invariance is used exactly once: it identifies the two external
crossing-bond normalization factors.  Their common nonzero scalar then cancels.  No injectivity of
a single vertex, of the end pair, or of its torus complement is used.

This is the contraction identity consumed by
`existsUnique_virtualOperation_of_endPair`: the two genuine end-window blocked tensors occur on
the unmodified sides, while the arbitrary inserts occur on the opposite sides.

Source: arXiv:1804.04964, the comparison of the two ends in Lemma 5 at lines 2213--2252 and the
translation-invariant two-dimensional end-window comparison at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (Cleft : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cright : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cleft =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cright)
    (nu : RegionBoundaryConfig (G := torusGraph width height) A
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K))
    (sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d)
      (horizontalStaircaseEndPair ((a : ZMod width), (b : ZMod height)) L K)) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let S := horizontalStaircaseEndPair s L K
    let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
    let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
    let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hleft sigma
    let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hright sigma
    (∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
        Cleft (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
          regionBlockedWeight (G := torusGraph width height) A Wright
            (Eright.symm (k, (Eend nu).2)) sigmaRight) =
      ∑ k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)),
        regionBlockedWeight (G := torusGraph width height) A Wleft
            (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
          Cright (Eright.symm (k, (Eend nu).2)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let hblueLeft : S \ Wleft = Wright :=
    horizontalStaircaseEndPair_sdiff_leftWindow (by omega) s
  let hblueRight : S \ Wright = Wleft :=
    horizontalStaircaseEndPair_sdiff_rightWindow (by omega) s
  let gleft := nestedThreeBlockGeometry (V := TorusVertex width height) hleft
  let gright := nestedThreeBlockGeometry (V := TorusVertex width height) hright
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let sigmaLeft := restrictSubRegionσ (V := TorusVertex width height) (d := d) hleft sigma
  let sigmaRight := restrictSubRegionσ (V := TorusVertex width height) (d := d) hright sigma
  let sigmaLeftFromBlue := regionPhysicalConfigCongr (d := d) hblueRight
    (restrictSubRegionσ (V := TorusVertex width height) (d := d)
      (Finset.sdiff_subset : S \ Wright ⊆ S) sigma)
  let sigmaRightFromBlue := regionPhysicalConfigCongr (d := d) hblueLeft
    (restrictSubRegionσ (V := TorusVertex width height) (d := d)
      (Finset.sdiff_subset : S \ Wleft ⊆ S) sigma)
  let scalarLeft : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (gleft.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  let scalarRight : ℂ := ((regionInteriorBondProd (G := torusGraph width height) A
      (Finset.univ \ S) : ℂ) *
    (gright.swapBlueComplement.blueRedCrossingBondProd A : ℂ))⁻¹
  have hsigmaLeft : sigmaLeftFromBlue = sigmaLeft := by
    funext w
    rfl
  have hsigmaRight : sigmaRightFromBlue = sigmaRight := by
    funext w
    rfl
  have hpoint := congrFun (congrFun heq nu) sigma
  rw [horizontalStaircaseLeftWindow_extendInsert_eq_singleBondContraction
      A hL hK ha0 haw hbh hpos Cleft nu sigma,
    horizontalStaircaseRightWindow_extendInsert_eq_singleBondContraction
      A hL hK ha0 haw hbh hpos Cright nu sigma] at hpoint
  change scalarLeft *
      (∑ k, Cleft (Eleft.symm (k, (Eend nu).1)) sigmaLeft *
        regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm (k, (Eend nu).2)) sigmaRightFromBlue) =
    scalarRight *
      (∑ k, regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (k, (Eend nu).1)) sigmaLeftFromBlue *
        Cright (Eright.symm (k, (Eend nu).2)) sigmaRight) at hpoint
  rw [hsigmaLeft, hsigmaRight] at hpoint
  have hcross := horizontalStaircaseEndWindows_externalCrossingBondProd_eq
    A hTI hpos hL hK ha0 haw hbh
  dsimp only at hcross
  change gleft.swapBlueComplement.blueRedCrossingBondProd A =
    gright.swapBlueComplement.blueRedCrossingBondProd A at hcross
  have hscalar : scalarLeft = scalarRight := by
    simp only [scalarLeft, scalarRight, hcross]
  rw [← hscalar] at hpoint
  have houter :
      (regionInteriorBondProd (G := torusGraph width height) A
        (Finset.univ \ S) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr
      (regionInteriorBondProd_pos (G := torusGraph width height) A
        (Finset.univ \ S) hpos).ne'
  have hcrossPos : 0 < gleft.swapBlueComplement.blueRedCrossingBondProd A := by
    rw [ThreeBlockGeometry.blueRedCrossingBondProd]
    exact Finset.prod_pos (fun eg _ ↦ hpos eg)
  have hcrossNe : (gleft.swapBlueComplement.blueRedCrossingBondProd A : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hcrossPos.ne'
  have hscalarNe : scalarLeft ≠ 0 :=
    inv_ne_zero (mul_ne_zero houter hcrossNe)
  exact mul_left_cancel₀ hscalarNe hpoint

/-- **The unique virtual operation extracted from the two end windows.**

Let the genuine blocked tensors of the two highlighted end windows be injective, and let arbitrary
inserts on those windows have equal extensions to their open end pair.  Then there is a unique
matrix `X` on the highlighted reference edge such that the left insert is obtained from the genuine
left block by inserting `X`, while the right insert is obtained from the genuine right block by the
transpose-side action of the same `X`.

The proof first uses
`singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq` to obtain the exact
single-bond contraction identity.  It then invokes
`existsUnique_virtualOperation_of_endPair`, whose operator-Schmidt argument requires linear
independence only of the two genuine blocked tensors.  In particular, neither modified insert is
assumed injective, and no injectivity is imposed on a vertex, the end pair, or its complement.

Source: arXiv:1804.04964, Lemma 5, especially the comparison of the two ends at lines 2213--2252,
and the two-dimensional open-boundary realization at lines 2415--2444 of
`Papers/1804.04964/paper_normal.tex`. -/
theorem existsUnique_virtualOperation_of_horizontalStaircaseEndPair
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hTI : IsTorusTranslationInvariant A)
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hpos : ∀ eg : Edge (torusGraph width height), 0 < A.bondDim eg)
    (hleftInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (hrightInjective : RegionBlockedTensorInjective (G := torusGraph width height) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cleft : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseLeftWindow ((a : ZMod width), (b : ZMod height)) L K))
    (Cright : RegionInsert (G := torusGraph width height) (d := d) A
      (horizontalStaircaseRightWindow ((a : ZMod width), (b : ZMod height)) L K))
    (heq :
      extendInsert (G := torusGraph width height)
          (horizontalStaircaseLeftWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cleft =
        extendInsert (G := torusGraph width height)
          (horizontalStaircaseRightWindow_subset_endPair
            ((a : ZMod width), (b : ZMod height))) Cright) :
    let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
    let Wleft := horizontalStaircaseLeftWindow s L K
    let Wright := horizontalStaircaseRightWindow s L K
    let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
    ∃! X : Matrix
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
        (Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K))) ℂ,
      (∀ (k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
          (etaLeft : HorizontalStaircaseLeftExternalBoundaryConfig A (L := L) (K := K) s)
          (sigmaLeft : RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wleft),
        Cleft (Eleft.symm (k, etaLeft)) sigmaLeft =
          ∑ j, regionBlockedWeight (G := torusGraph width height) A Wleft
              (Eleft.symm (j, etaLeft)) sigmaLeft * X j k) ∧
      ∀ (k : Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K)))
          (etaRight : HorizontalStaircaseRightExternalBoundaryConfig A (L := L) (K := K) s)
          (sigmaRight : RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wright),
        Cright (Eright.symm (k, etaRight)) sigmaRight =
          ∑ j, X k j * regionBlockedWeight (G := torusGraph width height) A Wright
            (Eright.symm (j, etaRight)) sigmaRight := by
  classical
  dsimp only
  let s : TorusVertex width height := ((a : ZMod width), (b : ZMod height))
  let Wleft := horizontalStaircaseLeftWindow s L K
  let Wright := horizontalStaircaseRightWindow s L K
  let S := horizontalStaircaseEndPair s L K
  let hleft : Wleft ⊆ S := horizontalStaircaseLeftWindow_subset_endPair s
  let hright : Wright ⊆ S := horizontalStaircaseRightWindow_subset_endPair s
  let Eleft := horizontalStaircaseLeftWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eright := horizontalStaircaseRightWindowBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Eend := horizontalStaircaseEndPairBoundaryConfigEquiv A hL hK ha0 haw hbh
  let Kedge := Fin (A.bondDim (horizontalStaircaseReferenceEdge s L K))
  let LeftExternal := HorizontalStaircaseLeftExternalBoundaryConfig A (L := L) (K := K) s
  let RightExternal := HorizontalStaircaseRightExternalBoundaryConfig A (L := L) (K := K) s
  let LeftPhysical := RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wleft
  let RightPhysical := RegionPhysicalConfig (V := TorusVertex width height) (d := d) Wright
  let Aleft : Kedge → LeftExternal × LeftPhysical → ℂ :=
    fun k p ↦ regionBlockedWeight (G := torusGraph width height) A Wleft
      (Eleft.symm (k, p.1)) p.2
  let CleftFamily : Kedge → LeftExternal × LeftPhysical → ℂ :=
    fun k p ↦ Cleft (Eleft.symm (k, p.1)) p.2
  let Aright : Kedge → RightExternal × RightPhysical → ℂ :=
    fun k p ↦ regionBlockedWeight (G := torusGraph width height) A Wright
      (Eright.symm (k, p.1)) p.2
  let CrightFamily : Kedge → RightExternal × RightPhysical → ℂ :=
    fun k p ↦ Cright (Eright.symm (k, p.1)) p.2
  let _ : Nonempty LeftExternal := ⟨fun f ↦ ⟨0, hpos f.1.1⟩⟩
  let _ : Nonempty RightExternal := ⟨fun f ↦ ⟨0, hpos f.1.1⟩⟩
  have hleftJoint : LinearIndependent ℂ
      (fun p : LeftExternal × Kedge ↦ fun sigmaLeft : LeftPhysical ↦
        regionBlockedWeight (G := torusGraph width height) A Wleft
          (Eleft.symm (p.2, p.1)) sigmaLeft) := by
    let F : LeftExternal × Kedge ≃
        RegionBoundaryConfig (G := torusGraph width height) A Wleft :=
      (Equiv.prodComm LeftExternal Kedge).trans Eleft.symm
    have hreindexed := (linearIndependent_equiv F).mpr hleftInjective
    change LinearIndependent ℂ
      (regionBlockedTensorFamily (G := torusGraph width height) A Wleft ∘ F)
    exact hreindexed
  have hrightJoint : LinearIndependent ℂ
      (fun p : RightExternal × Kedge ↦ fun sigmaRight : RightPhysical ↦
        regionBlockedWeight (G := torusGraph width height) A Wright
          (Eright.symm (p.2, p.1)) sigmaRight) := by
    let F : RightExternal × Kedge ≃
        RegionBoundaryConfig (G := torusGraph width height) A Wright :=
      (Equiv.prodComm RightExternal Kedge).trans Eright.symm
    have hreindexed := (linearIndependent_equiv F).mpr hrightInjective
    change LinearIndependent ℂ
      (regionBlockedTensorFamily (G := torusGraph width height) A Wright ∘ F)
    exact hreindexed
  have hAleft : LinearIndependent ℂ (fun k : Kedge ↦ (Aleft k :
      LeftExternal × LeftPhysical → ℂ)) := by
    exact linearIndependent_shared_of_joint
      (fun eta k sigmaLeft ↦ regionBlockedWeight (G := torusGraph width height) A Wleft
        (Eleft.symm (k, eta)) sigmaLeft) hleftJoint
  have hAright : LinearIndependent ℂ (fun k : Kedge ↦ (Aright k :
      RightExternal × RightPhysical → ℂ)) := by
    exact linearIndependent_shared_of_joint
      (fun eta k sigmaRight ↦ regionBlockedWeight (G := torusGraph width height) A Wright
        (Eright.symm (k, eta)) sigmaRight) hrightJoint
  have hcontract : ∀ (pLeft : LeftExternal × LeftPhysical)
      (pRight : RightExternal × RightPhysical),
      (∑ k : Kedge, CleftFamily k pLeft * Aright k pRight) =
        ∑ k : Kedge, Aleft k pLeft * CrightFamily k pRight := by
    intro pLeft pRight
    let nu : RegionBoundaryConfig (G := torusGraph width height) A S :=
      Eend.symm (pLeft.1, pRight.1)
    let sigma : RegionPhysicalConfig (V := TorusVertex width height) (d := d) S :=
      horizontalStaircaseEndPairPhysicalConfig s pLeft.2 pRight.2
    have hsingle :=
      singleBondContraction_eq_of_horizontalStaircaseEndPair_extendInsert_eq
        A hTI hL hK ha0 haw hbh hpos Cleft Cright heq nu sigma
    dsimp only at hsingle
    rw [Eend.apply_symm_apply,
      restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_left,
      restrictSubRegionσ_horizontalStaircaseEndPairPhysicalConfig_right (by omega)] at hsingle
    change (∑ k : Kedge, CleftFamily k pLeft * Aright k pRight) =
      ∑ k : Kedge, Aleft k pLeft * CrightFamily k pRight
    exact hsingle
  have hexists := existsUnique_virtualOperation_of_endPair
    Aleft CleftFamily Aright CrightFamily hAleft hAright hcontract
  rcases hexists with ⟨X, hX, hXunique⟩
  refine ⟨X, ⟨?_, ?_⟩, ?_⟩
  · intro k etaLeft sigmaLeft
    simpa only [Aleft, CleftFamily] using hX.1 k (etaLeft, sigmaLeft)
  · intro k etaRight sigmaRight
    simpa only [Aright, CrightFamily] using hX.2 k (etaRight, sigmaRight)
  · intro Y hY
    apply hXunique
    constructor
    · intro k pLeft
      simpa only [Aleft, CleftFamily] using hY.1 k pLeft.1 pLeft.2
    · intro k pRight
      simpa only [Aright, CrightFamily] using hY.2 k pRight.1 pRight.2

/-! ### The reference edge as a boundary edge of the first and last staircase windows

The reference edge `e` is a boundary edge of the right end window `W_0` and the left end window
`W_{L+K-1}`, hence of the first and last staircase windows `staircaseWindow s L K 0` and
`staircaseWindow s L K (L+K-1)`, which are those two windows. -/

/-- The reference edge is a boundary edge of the first staircase window `W_0` (the right end
window).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  rw [staircaseWindow_zero]
  exact isRegionBoundaryEdge_horizontalStaircaseRightWindow_referenceEdge A hL hK ha0 haw hbh

/-- The reference edge is a boundary edge of the last staircase window `W_{L+K-1}` (the left end
window).

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem isRegionBoundaryEdge_staircaseWindow_last_referenceEdge
    (A : Tensor (torusGraph width height) d) {L K a b : ℕ}
    (hL : 0 < L) (hK : 0 < K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height) :
    IsRegionBoundaryEdge (G := torusGraph width height)
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
      (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K) := by
  rw [staircaseWindow_last _ hL hK]
  exact isRegionBoundaryEdge_horizontalStaircaseLeftWindow_referenceEdge A hL hK ha0 haw hbh

/-! ### The single-bond peeling

The bond-inserted inserts on the two end windows, plugged into the end-pair equality, peel the
equality onto the single bond `e`. -/

/-- **The single-bond peeling of the staircase end-pair equality.**

Given a family of inserts `C` on the staircase windows whose deformed states all equal one common
state, with the first window's insert `C 0` the bond-inserted insert of a matrix `M` on the
reference edge `e` and the last window's insert `C (L+K-1)` the bond-inserted insert of `M'`, the
two end windows' region-inserted coefficients with `M` and `M'` inserted on `e` agree, read off any
global physical configuration `cfg`.

The theorem `regionInsertedCoeff_eq_extendInsert_bondInserted` writes each side as the assembled
deformed state of the corner-extended bond-inserted insert on the end pair `S`; the end-pair
equality `staircasePair_insert_eq_open` equates those two assembled states.  This is the
single-tensor content of the peeling: the cross-tensor gauge `Z` and the conjugation identity are
the algebra-isomorphism step that uses this equality, the residual recorded in
`docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1.

Source: arXiv:1804.04964, proof sketch at lines 2320--2445 of
`Papers/1804.04964/paper_normal.tex`; `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`, §5.1. -/
theorem regionInsertedCoeff_endWindows_eq_of_staircase {a b : ℕ}
    (h : NormalTorusArcWindowInjectivityHypotheses L K
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hUB : RegionInjectivityUnionClosure
      (regionInjectivityDataOf (G := torusGraph width height) B))
    (hpos : ∀ e : Edge (torusGraph width height), 0 < B.bondDim e)
    (hL : 2 ≤ L) (hK : 2 ≤ K) (ha0 : 1 ≤ a)
    (haw : a + 2 * L ≤ width) (hbh : b + 2 * K - 1 ≤ height)
    (hxw : 2 * L + 1 ≤ width) (hyh : 2 * K + 1 ≤ height)
    (M M' : Matrix
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
      (Fin (B.bondDim (horizontalStaircaseReferenceEdge ((a : ZMod width), (b : ZMod height)) L K)))
      ℂ)
    (C : ∀ j, RegionInsert (G := torusGraph width height) (d := d)
      B (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j))
    (common : (TorusVertex width height → Fin d) → ℂ)
    (hagree : ∀ j, j < L + K →
      deformedRegionStateAssembled (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K j) (C j) = common)
    (hC0 : C 0 = bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
      ⟨_, isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge B
        (by omega) (by omega) ha0 haw hbh⟩ M)
    (hClast : C (L + K - 1) = bondInsertedRegionInsert (G := torusGraph width height) B
      (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
      ⟨_, isRegionBoundaryEdge_staircaseWindow_last_referenceEdge B
        (by omega) (by omega) ha0 haw hbh⟩ M')
    (cfg : TorusVertex width height → Fin d) :
    regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K 0)
        ⟨_, isRegionBoundaryEdge_staircaseWindow_zero_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ M
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) =
      regionInsertedCoeff (G := torusGraph width height) B
        (staircaseWindow ((a : ZMod width), (b : ZMod height)) L K (L + K - 1))
        ⟨_, isRegionBoundaryEdge_staircaseWindow_last_referenceEdge B
          (by omega) (by omega) ha0 haw hbh⟩ M'
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg)
        (restrictRegionσ (V := TorusVertex width height) (d := d) _ cfg) := by
  -- Rewrite each side as the assembled deformed state of the corner-extended bond-inserted insert.
  rw [regionInsertedCoeff_eq_extendInsert_bondInserted
      (staircaseWindow_zero_subset_endPair _ L K) hpos, ← hC0,
    regionInsertedCoeff_eq_extendInsert_bondInserted
      (staircaseWindow_last_subset_endPair (by omega) (by omega) _) hpos, ← hClast]
  -- The end-pair equality equates the two corner-extended inserts on `S`; equal inserts give equal
  -- assembled deformed states.
  rw [staircasePair_insert_eq_open h hUB hpos hL hK hxw hyh _ C common hagree]

end Torus

end PEPS
end TNLean
