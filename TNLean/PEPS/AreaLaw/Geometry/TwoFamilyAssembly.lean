/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.BoundaryTheorem
import TNLean.PEPS.AreaLaw.Geometry.InitialPrimaryErrorSum
import TNLean.PEPS.AreaLaw.Geometry.PrimaryBirthSeparation
import TNLean.PEPS.AreaLaw.Geometry.RepairActualBirthTemplates
import TNLean.PEPS.AreaLaw.Geometry.RepairBirthLatticePoint
import TNLean.PEPS.AreaLaw.Geometry.RepairCharacteristicLengthLowerBound
import TNLean.PEPS.AreaLaw.Geometry.RepairDepth
import TNLean.PEPS.AreaLaw.Geometry.RepairDummySites
import TNLean.PEPS.AreaLaw.Geometry.RepairOrderedBirthSeparation
import TNLean.PEPS.AreaLaw.Geometry.RepairOrderedPartition
import TNLean.PEPS.AreaLaw.Geometry.RepairRankZeroAncestry
import TNLean.PEPS.AreaLaw.Geometry.RepairRetainedNonprimaryErrorSum
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalInteriors
import TNLean.PEPS.AreaLaw.Geometry.RepairTerminalPrefixSites
import TNLean.PEPS.AreaLaw.Geometry.RepairTermination
import TNLean.PEPS.AreaLaw.Geometry.RepairTotalMarkPrefixCount

/-!
# Two families with separated birth templates

This module proves Proposition 11.2 of the source. The repair construction is
run at the prescribed origin with constants fixed in the source's order: the
template coefficients, then the stopping scale, then the layer width and the
lower layer index. At an empty generation the regions of the non-dummy
identifiers that meet the cut, ordered by birth rank, form the two families.
The exceptional sites in the dummy or in terminal squares form the residual
set. Each region lies in the lattice sample of its closed birth, which carries
a template with both endpoint clearances.

The ordered clearance comes from two estimates. Earlier regions of a primary
of the same label are primaries of the same layer parity, separated by the
same-layer and nonadjacent-layer gaps. Every later identifier is separated
from earlier and peer regions of its label by Lemma 11.5 together with the
fine-clearance inequality.

## Main statements

* `twoFamilyDecomposition`: Proposition 11.2 (`prop:two-families`), for every
  pair of template constants with `Ctpl ≥ 1`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, statement lines 98–141,
  threshold order lines 756–774, and assembly lines 776–802.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

open Filter
open scoped Fin.NatCast

private theorem dist_integerPoint_eq_ambientSupDistance (t z : ℤ × ℤ) :
    dist (integerPoint t) (integerPoint z) = (Scan.ambientSupDistance t z : ℝ) := by
  simp [integerPoint, Prod.dist_eq, Real.dist_eq, Scan.ambientSupDistance]

section Primary

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
  (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- A rank-zero identifier other than the dummy is a retained primary of some
layer `k ≥ k₀`, with characteristic length `2 ^ k`. Its closed birth is at
distance at least `min (t_k, 2 ^ k / 2)` from the closed birth of every other
rank-zero identifier of the same label, by the same-layer and
nonadjacent-layer gaps. Auxiliary to area-law Section 11, `10-geometry.tex`,
lines 212–218, 563–571 and 784–786. -/
theorem exists_primaryLayer_of_repairStageBirthRank_eq_zero (n : ℕ)
    (x : (𝔇 (0 + n)).regionIndex)
    (hx : repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (0 + n) x = 0)
    (hxd : x ≠ (𝔇 (0 + n)).dummy) :
    ∃ k : ℕ, k₀ ≤ k ∧
      repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + n) x = 2 ^ k ∧
      ∀ y : (𝔇 (0 + n)).regionIndex, y ≠ x → y ≠ (𝔇 (0 + n)).dummy →
        repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (0 + n) y = 0 →
        (𝔇 (0 + n)).color y = (𝔇 (0 + n)).color x →
        ∀ p ∈ (𝔇 (0 + n)).birth x, ∀ q ∈ (𝔇 (0 + n)).birth y,
          min ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ k / 2) ≤ dist p q := by
  classical
  let hch := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let a := Classical.choose hch
  let b := Classical.choose (Classical.choose_spec hch)
  obtain ⟨⟨⟨k, hk⟩, ⟨J, hJ⟩⟩, rfl, -⟩ :=
    existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero o Λ A C k₀ hC h₀ Sstar
      n x hx hxd
  refine ⟨k, hk, ?_, ?_⟩
  · exact (repairStageCharacteristicLength_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _).trans
      rfl
  · intro y hyx hyd hy hcol p hp q hq
    obtain ⟨⟨⟨h, hh⟩, ⟨J', hJ'⟩⟩, rfl, -⟩ :=
      existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero o Λ A C k₀ hC h₀ Sstar
        n y hy hyd
    have hp' : p ∈ primaryBirthRegion o k (fineScaleIndex k) (pitchScaleIndex k)
        (boundaryEndpoints Λ A) C ((a k).val : ℤ) ((b k).val : ℤ) J :=
      (congrArg (p ∈ ·)
        (repairStage_birth_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _)).mp hp
    have hq' : q ∈ primaryBirthRegion o h (fineScaleIndex h) (pitchScaleIndex h)
        (boundaryEndpoints Λ A) C ((a h).val : ℤ) ((b h).val : ℤ) J' :=
      (congrArg (q ∈ ·)
        (repairStage_birth_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _)).mp hq
    have hcol' : (Nat.cast h : Fin 2) = Nat.cast k :=
      (repairStage_color_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _).symm.trans
        (hcol.trans (repairStage_color_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _))
    have hpar : k % 2 = h % 2 := by
      have := congrArg Fin.val hcol'
      simp only [Fin.val_natCast] at this
      exact this.symm
    have hne : (k, J) ≠ (h, J') := by
      intro hkJ
      simp only [Prod.mk.injEq] at hkJ
      obtain ⟨rfl, rfl⟩ := hkJ
      exact hyx rfl
    exact primaryBirthRegion_dist_separation_of_same_parity o k h (boundaryEndpoints Λ A) C
      (fun k ↦ ((a k).val : ℤ)) (fun k ↦ ((b k).val : ℤ)) J J' hC hpar hne p q hp' hq'

/-- The inverse hundredth powers of the primary scanner scales of any finite
set of rank-zero non-dummy identifiers have a uniform boundary-weighted bound.
The constant precedes the origin, domain, cut, width, layer index and stopping
scale. Auxiliary to area-law Section 11, `10-geometry.tex`, lines 709–715 and
796–800. -/
theorem exists_uniform_repairStage_primary_error_sum_bound {CP : ℝ} (hCP : 0 < CP) :
    ∃ M : ℝ, 0 < M ∧
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ))
        (C k₀ : ℕ) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ) (n : ℕ)
        (S : Finset (repairStage o Λ A C k₀ hC h₀ Sstar (0 + n)).regionIndex),
        (∀ x ∈ S, repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (0 + n) x = 0 ∧
          x ≠ (repairStage o Λ A C k₀ hC h₀ Sstar (0 + n)).dummy) →
        ∑ x ∈ S, (((⌈CP *
            repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + n) x ^
            (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ) ^ 100)⁻¹ ≤
          M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  obtain ⟨M, hM, hsum⟩ := exists_uniform_primaryPitchIndices_error_sum_bound hCP
  refine ⟨M, hM, fun o Λ A C k₀ hC h₀ Sstar n S hS ↦ ?_⟩
  let hch := (Classical.choose_spec exists_uniform_separated_initial_marks).2
    o Λ A C k₀ hC h₀
  let a := Classical.choose hch
  let b := Classical.choose (Classical.choose_spec hch)
  let a' : ℕ → ℤ := fun k ↦ ((a k).val : ℤ)
  let b' : ℕ → ℤ := fun k ↦ ((b k).val : ℤ)
  let Pidx := Σ k : {k : ℕ // k₀ ≤ k},
    {J : ℤ × ℤ // J ∈ primaryPitchIndices o k.val (fineScaleIndex k.val)
      (pitchScaleIndex k.val) (boundaryEndpoints Λ A) C (a' k.val) (b' k.val)}
  have hex : ∀ x : S, ∃ p : Pidx,
      repairStageOldInclusion o Λ A C k₀ hC h₀ Sstar 0 n (.inr (.inl p)) = x.val :=
    fun x ↦ (existsUnique_initialPrimary_of_repairStageBirthRank_eq_zero o Λ A C k₀ hC h₀
      Sstar n x.val (hS x.val x.property).1 (hS x.val x.property).2).exists
  choose p hp using hex
  let layer : S → ℕ := fun x ↦ (p x).1.val
  let w : ℕ → ℝ := fun k ↦
    (((⌈CP * ((2 : ℝ) ^ k) ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ) ^
      100)⁻¹
  have hterm : ∀ x : S,
      (((⌈CP * repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + n) x.val ^
          (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ) ^ 100)⁻¹ =
        w (layer x) := by
    intro x
    have hl : repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + n) x.val =
        (2 : ℝ) ^ layer x := by
      rw [← hp x]
      exact (repairStageCharacteristicLength_oldInclusion o Λ A C k₀ hC h₀ Sstar 0 n _).trans
        rfl
    rw [hl]
  rw [← Finset.sum_attach, Finset.sum_congr rfl (fun x _ ↦ hterm x), Finset.sum_comp]
  refine le_trans ?_ (hsum o Λ A C a' b' (S.attach.image layer))
  refine Finset.sum_le_sum fun k _ ↦ ?_
  rw [nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  norm_cast
  refine Finset.card_le_card_of_injOn (fun x ↦ (p x).2.val) ?_ ?_
  · intro x hx
    have hk : layer x = k := (Finset.mem_filter.mp hx).2
    have := (p x).2.property
    simp only [Finset.mem_coe]
    rw [← hk]
    exact this
  · intro x hx y hy hxy
    have hk : (p x).1 = (p y).1 :=
      Subtype.ext ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    have hpe : p x = p y := Sigma.subtype_ext hk hxy
    refine Subtype.ext ((hp x).symm.trans ?_)
    rw [hpe]
    exact hp y

end Primary

section Exceptional

variable {Λ : Finset (ℤ × ℤ)} {A : Finset (Site Λ)}
  {C k₀ : ℕ} {hC : 2 ≤ C} {h₀ : 50000000 ≤ k₀} {Sstar : ℝ}

local notation "𝔇" => repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar

/-- At an empty generation the exceptional sites are the dummy sites and the
sites of terminal squares of earlier generations. Their number is bounded by
the dummy count and the terminal-square count. Auxiliary to area-law
Section 11, `geometry:bad-sites`, `10-geometry.tex`, lines 694–707. -/
theorem card_repairStageExceptionalSites_le_of_isEmpty (N : ℕ)
    [IsEmpty (𝔇 N).markIndex] {M : ℝ}
    (hM : ∑ j ∈ Finset.range N, (Nat.card (𝔇 j).markIndex : ℝ) ≤
      M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card) :
    ((repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N).card : ℝ) ≤
      (2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) * ((edgeBoundary Λ A).card : ℝ) +
        (2 * Sstar + 1) ^ 2 * (M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card) := by
  classical
  have hsplit : repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N ⊆
      (𝔇 N).regionSites Λ A (𝔇 N).dummy ∪
        A.filter (fun x ↦ integerPoint x.val ∈
          ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar) := by
    intro x hx
    simp only [repairStageExceptionalSites, Finset.mem_filter, Set.mem_union] at hx
    rw [repairTerminalInteriors_eq_iUnion_lt_of_isEmpty dyadicOrigin Λ A C k₀ hC h₀
      Sstar N] at hx
    rcases hx with ⟨hxA, hd | ht⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hxA, hd⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hxA, ht⟩)
  have hdummy := card_repairStage_dummySites_le dyadicOrigin Λ A C k₀ hC h₀ Sstar N
  have hterm := card_repairTerminalInteriorSites_prefix_le dyadicOrigin Λ A C k₀ hC h₀
    Sstar N
  have hcard := (Finset.card_le_card hsplit).trans (Finset.card_union_le _ _)
  have hcardR :
      ((repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N).card : ℝ) ≤
      ((𝔇 N).regionSites Λ A (𝔇 N).dummy).card +
        (A.filter (fun x ↦ integerPoint x.val ∈
          ⋃ j < N, repairTerminalInteriorSet (𝔇 j).location (𝔇 j).scale Sstar)).card := by
    exact_mod_cast hcard
  have hdummyR : (((𝔇 N).regionSites Λ A (𝔇 N).dummy).card : ℝ) ≤
      (2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) * ((edgeBoundary Λ A).card : ℝ) := by
    exact_mod_cast hdummy
  have hsq : 0 ≤ (2 * Sstar + 1) ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hM hsq]

end Exceptional

end TNLean.PEPS.AreaLaw.Geometry

namespace TNLean.PEPS.AreaLaw

open Filter Geometry

/-- **Proposition 11.2** (`prop:two-families`, `10-geometry.tex` lines 98–141).
For every pair of template constants with `Ctpl ≥ 1` and every lower scale
threshold `n_* ≥ 1` there is a constant `C`, chosen before the domain and the
cut, such that every cut with positive boundary has an ordered two-family
partition with separated birth templates, `|D| ≤ C b` and `∑ nᵢ^(-100) ≤ C b`.

The constants are fixed in the order of lines 756–774: the template
coefficients `C_P, C_B`, the isolation constant and the separation constant
`c₁`, then the stopping scale `S_*`, then the layer width and the lower layer
index `k₀`. The regions are the final actual regions meeting the cut, ordered
by birth rank (lines 776–787); the error sum is split into primaries and the
remaining identifiers (lines 796–802). The lower bound `Ctpl ≥ 1` is the
standing convention that the template constant is a large positive constant
(Definition 9.3). -/
theorem twoFamilyDecomposition {D₀ Ctpl : ℝ} (hCtpl : 1 ≤ Ctpl) :
    TwoFamilyDecomposition D₀ Ctpl := by
  classical
  intro nstar hnstar
  -- Template coefficients, isolation and separation constants.
  obtain ⟨CP, CB, hCP, hCB, htpl⟩ := exists_uniform_repairStage_birth_templates Ctpl hCtpl
  obtain ⟨T₀, -, htplD⟩ := htpl D₀
  obtain ⟨T₁, hmetric⟩ :=
    exists_repairMetricHypotheses (a₀ := 1 / 4) (by norm_num) le_rfl
  obtain ⟨c₁, hc₁, T₂, hsep⟩ := exists_birthSeparation
  obtain ⟨U₁, hU₁⟩ := eventually_atTop.mp (eventually_fine_clearance hc₁ hCB.le)
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp
    (eventually_beltReplacementScaleLimit CB (show (0 : ℝ) < 1 by norm_num))
  -- The stopping scale.
  set U : ℝ := max (max U₁ U₂) (max ((nstar : ℝ) / CB) 1) with hU
  obtain ⟨KU, hKU⟩ := exists_uniform_repairStage_positive_rank_length_lower_bound U
  set Sstar : ℝ := max (max T₀ 2) (max (max T₁ T₂) U) with hSstar
  have hS2 : 2 ≤ Sstar := (le_max_right _ _).trans (le_max_left _ _)
  have hS1 : 1 < Sstar := by linarith
  have hST₀ : T₀ ≤ Sstar := (le_max_left _ _).trans (le_max_left _ _)
  have hST₁ : T₁ ≤ Sstar :=
    ((le_max_left _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hST₂ : T₂ ≤ Sstar :=
    ((le_max_right _ _).trans (le_max_left _ _)).trans (le_max_right _ _)
  have hSU : U ≤ Sstar := (le_max_right _ _).trans (le_max_right _ _)
  -- The layer width.
  set C : ℕ := ⌈4 * D₀⌉₊ + 2 with hCdef
  have hC : 2 ≤ C := by omega
  have hCD : 4 * D₀ < (C : ℝ) := by
    have := Nat.le_ceil (4 * D₀)
    rw [hCdef]
    push_cast
    linarith
  -- The lower layer index.
  obtain ⟨KT, hKT⟩ := htplD Sstar hST₀ C hCD
  obtain ⟨KM, hKM⟩ := hmetric Sstar hST₁ C
  obtain ⟨KB, hKB⟩ := hsep Sstar hST₂ C
  obtain ⟨KP, hKP⟩ := eventually_atTop.mp
    (eventually_primaryScaleLimits CP (show (0 : ℝ) < 1 / 8 by norm_num))
  obtain ⟨Kn, hKn⟩ := eventually_atTop.mp
    (le_primaryScannerScale (show (0 : ℝ) < CP by linarith) nstar)
  set k₀ : ℕ := max 50000000 (max (max KT KM) (max (max KB KU) (max KP Kn))) with hk₀
  have h₀ : 50000000 ≤ k₀ := le_max_left _ _
  have hKT₀ : KT ≤ k₀ := by omega
  have hKM₀ : KM ≤ k₀ := by omega
  have hKB₀ : KB ≤ k₀ := by omega
  have hKU₀ : KU ≤ k₀ := by omega
  have hKP₀ : KP ≤ k₀ := by omega
  have hKn₀ : Kn ≤ k₀ := by omega
  -- The counting constants.
  obtain ⟨Mt, -, hmark⟩ := exists_uniform_repairStage_markIndex_prefix_bound hS1
  obtain ⟨Mp, hMp, hprim⟩ :=
    exists_uniform_repairStage_primary_error_sum_bound (CP := CP) (by linarith)
  obtain ⟨Lq, hLq, hnonprim⟩ :=
    exists_uniform_repairStage_retained_positive_rank_error_sum_bound hS1
  have hnonprim' := hnonprim CB hCB
  set Cres : ℝ := (2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) +
    (2 * Sstar + 1) ^ 2 * (Mt * (2 * (C : ℝ) + 1) ^ 2) with hCres
  set Csum : ℝ := Mp * (2 * (C : ℝ) + 1) ^ 2 + Lq * (2 * (C : ℝ) + 1) ^ 2 with hCsum
  have hCsum0 : 0 ≤ Csum := by positivity
  refine ⟨max Cres Csum, ?_⟩
  intro Λ A hb
  have hb0 : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  -- The repair construction at the prescribed origin, and an empty generation.
  have hmh := hKM dyadicOrigin Λ A k₀ hC h₀ hKM₀
  obtain ⟨N₀, hN₀⟩ := hmh.exists_isEmpty_markIndex
  have hN : IsEmpty (repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + N₀)).markIndex := by
    rw [Nat.zero_add]
    exact hN₀
  set N : ℕ := 0 + N₀ with hNdef
  obtain ⟨P, e, hpiece, hfam, hres, hmono⟩ :=
    hmh.exists_orderedTwoFamilyPartition_of_isEmpty hS1.le hb N
  let 𝔇N := repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar N
  let Ret := 𝔇N.RetainedRegionIndex Λ A
  -- Names for ranks, lengths and scanner scales of retained identifiers.
  let rank : Ret → ℕ := fun r ↦
    repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N r.val
  let len : Ret → ℝ := fun r ↦
    repairStageCharacteristicLength dyadicOrigin Λ A C k₀ hC h₀ Sstar N r.val
  let nf : Ret → ℕ := fun r ↦
    if rank r = 0 then ⌈CP * len r ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊
    else ⌈CB * len r⌉₊
  -- Positive-rank lengths are large; rank-zero identifiers are primaries.
  have hlenU : ∀ r, rank r ≠ 0 → U ≤ len r := fun r hr ↦
    hKU dyadicOrigin Λ A C k₀ hC h₀ hKU₀ Sstar hSU N r.val (Nat.pos_of_ne_zero hr)
  have hprimary : ∀ r, rank r = 0 → ∃ k : ℕ, k₀ ≤ k ∧ len r = 2 ^ k ∧
      ∀ y : 𝔇N.regionIndex, y ≠ r.val → y ≠ 𝔇N.dummy →
        repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N y = 0 →
        𝔇N.color y = 𝔇N.color r.val →
        ∀ p ∈ 𝔇N.birth r.val, ∀ q ∈ 𝔇N.birth y,
          min ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ k / 2) ≤ dist p q := fun r hr ↦
    exists_primaryLayer_of_repairStageBirthRank_eq_zero dyadicOrigin Λ A C k₀ hC h₀ Sstar
      N₀ r.val hr r.property.1
  have hnf_primary : ∀ r, rank r = 0 → ∀ k : ℕ, len r = 2 ^ k →
      nf r = primaryScannerScale CP k := by
    intro r hr k hk
    simp only [nf, hr, ite_true, hk, primaryScannerScale]
  have hnf_pos : ∀ r, rank r ≠ 0 → nf r = ⌈CB * len r⌉₊ := by
    intro r hr
    simp only [nf, hr, ite_false]
  -- Templates for the closed births.
  have htemp : ∀ i : Fin P.pieceCount, ∃ s : ℕ, ∃ T : Template Ctpl (nf (e i)) s,
      ((s : ℝ) = if rank (e i) ≤ 1 then len (e i) else 2 * len (e i)) ∧
      (∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ 𝔇N.birth (e i).val) ∧
      T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
      ∀ y ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
        2 * (nf (e i) : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance y z : ℝ) := by
    intro i
    obtain ⟨w, hw⟩ := (e i).property.2
    have hwb : integerPoint w.val ∈ 𝔇N.birth (e i).val :=
      repairStage_current_subset_birth dyadicOrigin Λ A C k₀ hC h₀ Sstar N _
        (Finset.mem_filter.mp hw).2
    exact hKT dyadicOrigin Λ A k₀ hC h₀ hKT₀ N (e i).val (e i).property.1 w.val hwb
  choose s T hs hpts hTsep hcut using htemp
  have hlen_pos : ∀ r : Ret, 0 < len r := fun r ↦
    repairStageCharacteristicLength_pos_of_ne_dummy dyadicOrigin Λ A C k₀ hC h₀ Sstar N
      r.val r.property.1
  refine ⟨P, fun i ↦ nf (e i), s, T, ?_, ?_, ?_, hTsep, ?_, ?_, hcut, ?_, ?_⟩
  · -- The exceptional sites.
    rw [hres]
    have hexc := card_repairStageExceptionalSites_le_of_isEmpty (hC := hC) (h₀ := h₀)
      (Sstar := Sstar) N (hmark dyadicOrigin Λ A C k₀ hC h₀ (1 / 4) hmh N)
    calc ((repairStageExceptionalSites dyadicOrigin Λ A C k₀ hC h₀ Sstar N).card : ℝ)
        ≤ Cres * (edgeBoundary Λ A).card := by rw [hCres]; nlinarith [hexc]
      _ ≤ max Cres Csum * (edgeBoundary Λ A).card :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hb0
  · -- Nonempty pieces.
    intro i
    rw [hpiece]
    exact (e i).property.2
  · -- Each piece lies in its template.
    intro i x hx
    rw [hpiece] at hx
    have hxA := (Finset.mem_filter.mp hx).1
    have hxb : integerPoint x.val ∈ 𝔇N.birth (e i).val :=
      repairStage_current_subset_birth dyadicOrigin Λ A C k₀ hC h₀ Sstar N _
        (Finset.mem_filter.mp hx).2
    exact Finset.mem_filter.mpr ⟨hxA, (hpts i x.val).mpr hxb⟩
  · -- The dilation count is at most the piece size.
    intro i
    beta_reduce
    by_cases hr : rank (e i) = 0
    · obtain ⟨k, hk, hlen, -⟩ := hprimary (e i) hr
      rw [hnf_primary (e i) hr k hlen]
      have hlim := (hKP k (hKP₀.trans hk)).1
      have hsi : (s i : ℝ) = 2 ^ k := by
        rw [hs i, hlen]
        simp only [show rank (e i) ≤ 1 by omega, ite_true]
      have : (⌊(primaryScannerScale CP k : ℝ) ^
          (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ s i := by
        rw [hsi]
        have : (0 : ℝ) ≤ 2 ^ k := by positivity
        linarith
      exact_mod_cast this
    · rw [hnf_pos (e i) hr]
      have hU2 : U₂ ≤ len (e i) :=
        ((le_max_right _ _).trans (le_max_left _ _)).trans (hlenU (e i) hr)
      have hlim := hU₂ (len (e i)) hU2
      have hsi : len (e i) ≤ (s i : ℝ) := by
        rw [hs i]
        split_ifs
        · exact le_rfl
        · linarith [hlen_pos (e i)]
      have : (⌊(⌈CB * len (e i)⌉₊ : ℝ) ^
          (1 - (Exponents.geometryEll : ℝ))⌋₊ : ℝ) ≤ s i := by
        linarith
      exact_mod_cast this
  · -- The lower scale threshold.
    intro i
    beta_reduce
    by_cases hr : rank (e i) = 0
    · obtain ⟨k, hk, hlen, -⟩ := hprimary (e i) hr
      rw [hnf_primary (e i) hr k hlen]
      exact hKn k (hKn₀.trans hk)
    · rw [hnf_pos (e i) hr]
      have hUn : (nstar : ℝ) / CB ≤ len (e i) :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans (hlenU (e i) hr)
      have : (nstar : ℝ) ≤ CB * len (e i) := by
        rw [div_le_iff₀ hCB] at hUn
        linarith
      exact_mod_cast this.trans (Nat.le_ceil _)
  · -- Clearance from earlier pieces of the same family.
    intro i t ht z hz
    beta_reduce
    obtain ⟨j, hj, hzj⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨hji, hfji⟩ := (Finset.mem_filter.mp hj).2
    rw [hpiece] at hzj
    have hzc : integerPoint z.val ∈ 𝔇N.current (e j).val := (Finset.mem_filter.mp hzj).2
    have hcol : 𝔇N.color (e j).val = 𝔇N.color (e i).val := by
      exact (hfam j).symm.trans (hfji.trans (hfam i))
    have hrank : rank (e j) ≤ rank (e i) := hmono hji.le
    have hne : (e j).val ≠ (e i).val := fun h ↦
      hji.ne (e.injective (Subtype.ext h))
    have htb : integerPoint t ∈ 𝔇N.birth (e i).val := (hpts i t).mp ht
    rw [← dist_integerPoint_eq_ambientSupDistance]
    by_cases hr : rank (e i) = 0
    · obtain ⟨k, hk, hlen, hsepP⟩ := hprimary (e i) hr
      have hrj : repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N (e j).val = 0 :=
        Nat.le_zero.mp (hr ▸ hrank)
      have hzb : integerPoint z.val ∈ 𝔇N.birth (e j).val :=
        repairStage_current_subset_birth dyadicOrigin Λ A C k₀ hC h₀ Sstar N _ hzc
      have hd := hsepP (e j).val hne (e j).property.1 hrj hcol _ htb _ hzb
      rw [hnf_primary (e i) hr k hlen]
      obtain ⟨-, hβt, hβr⟩ := hKP k (hKP₀.trans hk)
      have ht0 : (0 : ℝ) < 2 ^ fineScaleIndex k := by positivity
      have hr0 : (0 : ℝ) < 2 ^ k := by positivity
      have hmin : 2 * (primaryScannerScale CP k : ℝ) ^ (Exponents.beta : ℝ) <
          min ((2 : ℝ) ^ fineScaleIndex k) ((2 : ℝ) ^ k / 2) :=
        lt_min (by linarith) (by linarith)
      exact hmin.trans_le hd
    · obtain ⟨hinit, hrep⟩ := hKB dyadicOrigin Λ A k₀ hC h₀ hKB₀
      have hzf : integerPoint z.val ∈
          repairFinalRegion dyadicOrigin Λ A C k₀ hC h₀ Sstar N (e j).val := by
        rw [repairFinalRegion_eq_current_of_isEmpty]
        exact hzc
      have hd := repairStage_birth_separation_of_rank_le dyadicOrigin Λ A C k₀ hC h₀ Sstar
        hinit hrep N (e i).val (e j).val (Nat.pos_of_ne_zero hr) hne (e j).property.1
        hrank hcol _ htb _ hzf
      rw [hnf_pos (e i) hr]
      have hU1 : U₁ ≤ len (e i) :=
        ((le_max_left _ _).trans (le_max_left _ _)).trans (hlenU (e i) hr)
      exact (hU₁ _ hU1).trans_le hd
  · -- The error sum.
    have : Finite (Ret) :=
      𝔇N.finite_retainedRegionIndex Λ A (hmh.current_pairwise_disjoint N)
    let := Fintype.ofFinite (Ret)
    let g : Ret → ℝ := fun r ↦ ((nf r : ℝ) ^ 100)⁻¹
    have hsplit : ∑ i, ((nf (e i) : ℝ) ^ 100)⁻¹ =
        ∑ r : {r : Ret // rank r = 0}, g r.val +
          ∑ r : {r : Ret // ¬ rank r = 0}, g r.val := by
      rw [Fintype.sum_subtype_add_sum_subtype]
      exact e.sum_comp g
    -- Primaries.
    have hP : ∑ r : {r : Ret // rank r = 0}, g r.val ≤
        Mp * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
      let f : {r : Ret // rank r = 0} → 𝔇N.regionIndex :=
        fun r ↦ r.val.val
      have hf : Function.Injective f := fun r r' h ↦ Subtype.ext (Subtype.ext h)
      have h := hprim dyadicOrigin Λ A C k₀ hC h₀ Sstar N₀ (Finset.univ.image f)
        (by
          intro x hx
          obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hx
          exact ⟨r.property, r.val.property.1⟩)
      rw [Finset.sum_image (fun r _ r' _ h ↦ hf h)] at h
      refine le_of_eq_of_le (Finset.sum_congr rfl fun r _ ↦ ?_) h
      simp only [g, nf, r.property, ite_true]
      rfl
    -- The remaining identifiers.
    have hQ : ∑ r : {r : Ret // ¬ rank r = 0}, g r.val ≤
        Lq * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
      have h := hnonprim' dyadicOrigin Λ A C k₀ hC h₀ (1 / 4) hmh N
      simp only at h
      rw [finsum_eq_sum_of_fintype] at h
      let ε : {r : Ret // ¬ rank r = 0} ≃
          {r : Ret // 0 < rank r} :=
        Equiv.subtypeEquivRight fun r ↦ Nat.pos_iff_ne_zero.symm
      refine le_of_eq_of_le ?_ h
      rw [← ε.sum_comp]
      refine Finset.sum_congr rfl fun r _ ↦ ?_
      simp only [g, nf, r.property, ite_false]
      rfl
    rw [hsplit]
    calc _ ≤ Mp * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card +
          Lq * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := add_le_add hP hQ
      _ = Csum * (edgeBoundary Λ A).card := by rw [hCsum]; ring
      _ ≤ max Cres Csum * (edgeBoundary Λ A).card :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hb0

end TNLean.PEPS.AreaLaw
