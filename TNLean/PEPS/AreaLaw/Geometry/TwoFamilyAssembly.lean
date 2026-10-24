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
import TNLean.PEPS.AreaLaw.Geometry.TwoFamilyExplicitThresholds

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

* `twoFamilyDecomposition`: Proposition 11.2 (`prop:two-families`), for all
  real template constants `D₀` and `Ctpl`.
* `twoFamilyDecomposition_of_one_le`: the core case `Ctpl ≥ 1`; templates for
  `max Ctpl 1` are read as templates for `Ctpl` (`Geometry.Template.ofLe`).
* `isTwoFamilyDecompositionConstant_twoFamilyConstant`: the assembly with the
  named constant `twoFamilyConstant` above the explicit thresholds.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Section 11, `10-geometry.tex`, statement lines 98–141,
  threshold order lines 756–774, and assembly lines 776–802.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

open TNLean.Lattice

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

/-- **Primary error sum with an explicit coefficient.** The inverse hundredth
powers of the primary scanner scales of any finite set of rank-zero non-dummy
identifiers have boundary-weighted sum at most
`primaryErrorSumConstant C_P (2 C₀ + 1) ^ 2 |∂A|`. Auxiliary to area-law
Section 11, `10-geometry.tex`, lines 709–715 and 796–800. -/
theorem repairStage_primary_error_sum_le {CP : ℝ} (hCP : 0 < CP) (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C)
    (h₀ : 50000000 ≤ k₀) (Sstar : ℝ) (n : ℕ)
    (S : Finset (repairStage o Λ A C k₀ hC h₀ Sstar (0 + n)).regionIndex) :
    (∀ x ∈ S, repairStageBirthRank o Λ A C k₀ hC h₀ Sstar (0 + n) x = 0 ∧
      x ≠ (repairStage o Λ A C k₀ hC h₀ Sstar (0 + n)).dummy) →
    ∑ x ∈ S, (((⌈CP *
        repairStageCharacteristicLength o Λ A C k₀ hC h₀ Sstar (0 + n) x ^
        (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ) ^ 100)⁻¹ ≤
      primaryErrorSumConstant CP * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card := by
  classical
  intro hS
  have hsum := primaryPitchIndices_error_sum_le hCP
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

/-- The inverse hundredth powers of the primary scanner scales of any finite
set of rank-zero non-dummy identifiers have a uniform boundary-weighted bound.
The constant precedes the origin, domain, cut, width, layer index and stopping
scale; it is `primaryErrorSumConstant C_P` (`repairStage_primary_error_sum_le`).
Auxiliary to area-law Section 11, `10-geometry.tex`, lines 709–715 and
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
          M * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card :=
  ⟨_, primaryErrorSumConstant_pos hCP, repairStage_primary_error_sum_le hCP⟩

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

section Separation

/-- A **birth-separation constant** `c₁`: a positive constant for which both
cases of the birth-separation lemma hold before the threshold choices. The
initial belt tiles are separated by `c₁` at all data, and the replacement
births are separated by `c₁` from every set with the two properties of a final
actual region of an older or peer identifier of the same label. The source
obtains such a constant as a minimum over finitely many rescaled patterns
(`10-geometry.tex`, lines 596–631). Auxiliary to the explicit constant of
Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`).
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
structure IsBirthSeparationConstant (c₁ : ℝ) : Prop where
  /-- The constant is positive. -/
  pos : 0 < c₁
  /-- The initial belt tiles are separated by `c₁`. Source: lines 573–582. -/
  initial : ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
    (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ),
    IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁
  /-- The local separation of a replacement birth from its comparison regions.
  Source: lines 584–659. -/
  replacement : ∀ {ι : Type} (ξ : ι → Fin 2) (σ : RepairFanSlot → ι)
    (C : RepairFanRun ξ σ) (v : ℝ × ℝ) {u : ℝ}, 1 ≤ u → ∀ Y : Set (ℝ × ℝ),
    (∀ y ∈ Y, ‖y - v‖ < 2 * u → u⁻¹ • (y - v) ∈ repairSameLabelBound ξ σ C) →
    (∀ y ∈ Y, ∀ p : Fin 3 × Fin 3, y ∉ repairSquare (v + u • repairChildOffset p) u) →
    ∀ x ∈ (fun z ↦ v + u • z) '' repairNormRunRegion ξ σ C, ∀ y ∈ Y,
      c₁ * u ^ (Exponents.rho : ℝ) ≤ ‖x - y‖

/-- A birth-separation constant exists: the smaller of the constants of the
initial and the replacement separation lemmas.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem exists_isBirthSeparationConstant : ∃ c₁ : ℝ, IsBirthSeparationConstant c₁ := by
  obtain ⟨c₃, hc₃, hI⟩ := exists_isInitialBirthSeparated
  obtain ⟨c₂, hc₂, hR⟩ := exists_repairBirth_separation
  refine ⟨min c₂ c₃, lt_min hc₂ hc₃, fun o Λ A C k₀ hC h₀ Sstar ↦
    (hI o Λ A C k₀ hC h₀ Sstar).mono (min_le_right _ _), ?_⟩
  intro ι ξ σ C v u hu Y hloc htrim x hx y hy
  exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
    (Real.rpow_nonneg (by linarith) _)).trans (hR ξ σ C v hu Y hloc htrim x hx y hy)

/-- The explicit constant `c₁ = birthTemplateSeparationConstant = 1/112` is a birth-separation
constant: the initial belt tiles are separated by it, and the replacement births are separated
by `birthSeparationConstant = 1/28 ≥ c₁`. Auxiliary to the explicit constant of Theorem 1.1
(`docs/notes/arealaw2d_explicit_constant.tex`); the source obtains `c₁` as a compactness
minimum. Source: area-law Section 11, `geometry:birth-separation`, lines 573–659. -/
theorem isBirthSeparationConstant_birthTemplateSeparationConstant :
    IsBirthSeparationConstant birthTemplateSeparationConstant := by
  refine ⟨birthTemplateSeparationConstant_pos,
    isInitialBirthSeparated_birthTemplateSeparationConstant, ?_⟩
  intro ι ξ σ C v u hu Y hloc htrim x hx y hy
  exact (mul_le_mul_of_nonneg_right birthTemplateSeparationConstant_le
    (Real.rpow_nonneg (by linarith) _)).trans
      (repairBirth_separation ξ σ C v hu Y hloc htrim x hx y hy)

/-- **Birth separation with explicit thresholds.** For a birth-separation
constant `c₁`, every stopping scale `S_* ≥ repairMarginThreshold (1/128)`, every
width and every lower layer index `k₀ ≥ fineScaleIndexThreshold S_*`, both cases
of the birth-separation lemma hold with `c₁` for the actual repair stages.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:repair-induction`, lines 471–485. -/
theorem IsBirthSeparationConstant.birthSeparated {c₁ : ℝ} (hc : IsBirthSeparationConstant c₁)
    {Sstar : ℝ} (hS : repairMarginThreshold (1 / 128) ≤ Sstar) (o : ℝ × ℝ)
    (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ) (hC : 2 ≤ C)
    (h₀ : 50000000 ≤ k₀) (hK : fineScaleIndexThreshold Sstar ≤ k₀) :
    IsInitialBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ ∧
      IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ := by
  have hM := repairMetricHypotheses_of_le (a₀ := 1 / 128) (by norm_num) (by norm_num) hS
    o Λ A C k₀ hC h₀ hK
  exact ⟨hc.initial o Λ A C k₀ hC h₀ Sstar,
    isRepairBirthSeparated_of_isUniformRepairInduction hc.replacement hM.pos
      ((one_le_repairMarginThreshold _).trans hS) hM.le_scale hM.margin
      (isUniformRepairInduction_of_le hS o Λ A C k₀ hC h₀ hK)⟩

end Separation

end TNLean.PEPS.AreaLaw.Geometry

namespace TNLean.PEPS.AreaLaw

open Filter Geometry

/-- The conclusion of Proposition 11.2 at a lower scale threshold `n_*` with
constant `C`: every cut with positive boundary has an ordered two-family
partition with separated birth templates, `|D| ≤ C b` and `∑ nᵢ^(-100) ≤ C b`.
Source: area-law Section 11, `prop:two-families`, `10-geometry.tex`,
lines 98–141. -/
def IsTwoFamilyDecompositionConstant (D₀ Ctpl : ℝ) (nstar : ℕ) (C : ℝ) : Prop :=
  ∀ Λ : Finset (ℤ × ℤ), ∀ A : Finset (Site Λ), 0 < (edgeBoundary Λ A).card →
    ∃ P : Geometry.OrderedTwoFamilyPartition A, ∃ n s : Fin P.pieceCount → ℕ,
      ∃ T : ∀ i, Geometry.Template Ctpl (n i) (s i),
        (P.residual.card : ℝ) ≤ C * (edgeBoundary Λ A).card ∧
        (∀ i, (P.piece i).Nonempty) ∧
        (∀ i, P.piece i ⊆ A.filter fun x ↦ x.val ∈ (T i).points) ∧
        (∀ i, (T i).IsSeparated D₀ (Geometry.boundaryEndpoints Λ A)) ∧
        (∀ i, ⌊(n i : ℝ) ^ (1 - (Exponents.geometryEll : ℝ))⌋₊ ≤ s i) ∧
        (∀ i, nstar ≤ n i) ∧
        (∀ i, ∀ t ∈ (T i).points, ∀ z ∈ Geometry.boundaryEndpoints Λ A,
          2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t z : ℝ)) ∧
        (∀ i, ∀ t ∈ (T i).points, ∀ x ∈ P.earlierSameFamily i,
          2 * (n i : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance t x.val : ℝ)) ∧
        ∑ i, ((n i : ℝ) ^ 100)⁻¹ ≤ C * (edgeBoundary Λ A).card

/-- Proposition 11.2 says that every lower scale threshold `n_* ≥ 1` has a
constant in the sense of `IsTwoFamilyDecompositionConstant`. -/
theorem twoFamilyDecomposition_iff (D₀ Ctpl : ℝ) :
    TwoFamilyDecomposition D₀ Ctpl ↔
      ∀ nstar : ℕ, 1 ≤ nstar → ∃ C : ℝ, IsTwoFamilyDecompositionConstant D₀ Ctpl nstar C :=
  Iff.rfl

/-- The lower bound `U = max (max U₁ U₂) (max (n_* / C_B) 1)` imposed on the
characteristic lengths of identifiers of positive birth rank: `U₁` is the
fine-clearance threshold, `U₂` the belt and replacement dilation threshold at
`ε = 1`. Source: area-law Section 11, `10-geometry.tex`, lines 761–771. -/
def twoFamilyLengthBound (c₁ CB : ℝ) (nstar : ℕ) : ℝ :=
  max (max (fineClearanceThreshold c₁ CB) (beltReplacementScaleThreshold CB 1))
    (max ((nstar : ℝ) / CB) 1)

/-- The layer width `⌈4 D₀⌉ + 2` of the two-family decomposition, which
satisfies `4 D₀ < C` and `2 ≤ C`. Source: area-law Section 11,
`10-geometry.tex`, lines 771–774. -/
def twoFamilyLayerWidth (D₀ : ℝ) : ℕ :=
  ⌈4 * D₀⌉₊ + 2

/-- The explicit part of the lower layer index of the two-family decomposition:
the fine-scale threshold for the length bound `U`, the primary scale limits at
`ε = 1/8`, and the primary scanner scale threshold for `n_*`. Source: area-law
Section 11, `10-geometry.tex`, lines 768–774. -/
def twoFamilyLayerThreshold (CP CB c₁ : ℝ) (nstar : ℕ) : ℕ :=
  max (fineScaleIndexThreshold (twoFamilyLengthBound c₁ CB nstar))
    (max (primaryScaleLimitThreshold CP (1 / 8)) (primaryScannerScaleThreshold CP nstar))

/-- The constant of the two-family decomposition: the larger of the residual
coefficient `2 (2 (C + 1) 2 ^ k₀ + 1) ^ 2 + (2 S_* + 1) ^ 2 M_t (2 C + 1) ^ 2`
and the error-sum coefficient `(M_p + L_q) (2 C + 1) ^ 2`. Here `C` is the layer
width, `k₀` the lower layer index, `S_*` the stopping scale, `M_t` the
mark-count coefficient, `M_p` the primary error-sum coefficient and `L_q` the
nonprimary error-sum coefficient. Source: area-law Section 11,
`10-geometry.tex`, lines 694–707 and 796–802. -/
def twoFamilyConstant (C k₀ : ℕ) (Sstar Mt Mp Lq : ℝ) : ℝ :=
  max ((2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) +
      (2 * Sstar + 1) ^ 2 * (Mt * (2 * (C : ℝ) + 1) ^ 2))
    (Mp * (2 * (C : ℝ) + 1) ^ 2 + Lq * (2 * (C : ℝ) + 1) ^ 2)

/-- **Proposition 11.2 with a named constant.** Fix template coefficients
`C_P ≥ 1` and `C_B > 0`, a separation constant `c₁ > 0`, a layer width `C ≥ 2`,
a stopping scale `S_* ≥ 2` at least the length bound `twoFamilyLengthBound`,
and a lower layer index `k₀ ≥ 5·10⁷` at least `twoFamilyLayerThreshold`.
Suppose that, at these data and the prescribed origin, the remembered birth
regions have templates with both endpoint clearances, the repair family
satisfies the metric hypotheses with `a₀ = 1/4` and both birth-separation
properties with `c₁`, and the mark counts, primary error sums and nonprimary
error sums are bounded with coefficients `M_t`, `M_p` and `L_q`. Then
`twoFamilyConstant C k₀ S_* M_t M_p L_q` is a constant of the two-family
decomposition at `n_*`.

The hypotheses are the conclusions of the uniform lemmas used by
`twoFamilyDecomposition_of_one_le`, specialized to these data; every
threshold that the proof itself imposes is explicit. Auxiliary to area-law
Section 11, `10-geometry.tex`, threshold order lines 756–774 and assembly
lines 776–802. -/
theorem isTwoFamilyDecompositionConstant_twoFamilyConstant
    {D₀ Ctpl CP CB c₁ Sstar Mt Mp Lq : ℝ} {nstar C k₀ : ℕ}
    (hCP : 1 ≤ CP) (hCB : 0 < CB) (hc₁ : 0 < c₁) (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀)
    (hS2 : 2 ≤ Sstar) (hSU : twoFamilyLengthBound c₁ CB nstar ≤ Sstar)
    (hk : twoFamilyLayerThreshold CP CB c₁ nstar ≤ k₀)
    (htpl : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (N : ℕ),
      let D := repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar N
      ∀ x : D.regionIndex, x ≠ D.dummy →
        ∀ w : ℤ × ℤ, integerPoint w ∈ D.birth x →
          let rank := repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N x
          let u := repairStageCharacteristicLength dyadicOrigin Λ A C k₀ hC h₀ Sstar N x
          let n : ℕ := if rank = 0 then
            ⌈CP * u ^ (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ else ⌈CB * u⌉₊
          ∃ s₀ : ℕ, ∃ T : Template Ctpl n s₀,
            (s₀ : ℝ) = (if rank ≤ 1 then u else 2 * u) ∧
              (∀ y : ℤ × ℤ, y ∈ T.points ↔ integerPoint y ∈ D.birth x) ∧
              T.IsSeparated D₀ (boundaryEndpoints Λ A) ∧
              ∀ y ∈ T.points, ∀ z ∈ boundaryEndpoints Λ A,
                2 * (n : ℝ) ^ (Exponents.beta : ℝ) < (Scan.ambientSupDistance y z : ℝ))
    (hmetric : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)),
      RepairMetricHypotheses (o := dyadicOrigin) (Λ := Λ) (A := A) (C := C) (k₀ := k₀)
        (hC := hC) (h₀ := h₀) (Sstar := Sstar) (1 / 4))
    (hsep : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)),
      IsInitialBirthSeparated dyadicOrigin Λ A C k₀ hC h₀ Sstar c₁ ∧
        IsRepairBirthSeparated dyadicOrigin Λ A C k₀ hC h₀ Sstar c₁)
    (hmark : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (N : ℕ),
      ∑ j ∈ Finset.range N,
          (Nat.card (repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar j).markIndex : ℝ) ≤
        Mt * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card)
    (hprim : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (n : ℕ)
      (S : Finset (repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + n)).regionIndex),
      (∀ x ∈ S, repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + n) x = 0 ∧
        x ≠ (repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + n)).dummy) →
      ∑ x ∈ S, (((⌈CP *
          repairStageCharacteristicLength dyadicOrigin Λ A C k₀ hC h₀ Sstar (0 + n) x ^
          (1 + 2 * (Exponents.geometryDelta : ℝ))⌉₊ : ℕ) : ℝ) ^ 100)⁻¹ ≤
        Mp * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card)
    (hnonprim : ∀ (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (N : ℕ),
      let I : Type :=
        {i : (repairStage dyadicOrigin Λ A C k₀ hC h₀ Sstar N).RetainedRegionIndex Λ A //
          0 < repairStageBirthRank dyadicOrigin Λ A C k₀ hC h₀ Sstar N i.val}
      let n : I → ℕ := fun i ↦
        ⌈CB * repairStageCharacteristicLength dyadicOrigin Λ A C k₀ hC h₀ Sstar N
          i.val.val⌉₊
      (∑ᶠ i : I, (((n i : ℝ) ^ 100)⁻¹)) ≤
        Lq * (2 * (C : ℝ) + 1) ^ 2 * (edgeBoundary Λ A).card) :
    IsTwoFamilyDecompositionConstant D₀ Ctpl nstar (twoFamilyConstant C k₀ Sstar Mt Mp Lq) := by
  classical
  have hS1 : 1 < Sstar := by linarith
  set U₁ := fineClearanceThreshold c₁ CB
  set U₂ := beltReplacementScaleThreshold CB 1
  set U : ℝ := max (max U₁ U₂) (max ((nstar : ℝ) / CB) 1)
  have hSU' : U ≤ Sstar := hSU
  have hKU₀ : fineScaleIndexThreshold U ≤ k₀ := (le_max_left _ _).trans hk
  have hKP₀ : primaryScaleLimitThreshold CP (1 / 8) ≤ k₀ :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hk
  have hKn₀ : primaryScannerScaleThreshold CP nstar ≤ k₀ :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hk
  have hKP (k : ℕ) (hk : primaryScaleLimitThreshold CP (1 / 8) ≤ k) :=
    primaryScaleLimits_of_primaryScaleLimitThreshold_le CP
      (show (0 : ℝ) < 1 / 8 by norm_num) hk
  set Cres : ℝ := (2 * (2 * ((C + 1) * 2 ^ k₀) + 1) ^ 2 : ℕ) +
    (2 * Sstar + 1) ^ 2 * (Mt * (2 * (C : ℝ) + 1) ^ 2) with hCres
  set Csum : ℝ := Mp * (2 * (C : ℝ) + 1) ^ 2 + Lq * (2 * (C : ℝ) + 1) ^ 2 with hCsum
  change IsTwoFamilyDecompositionConstant D₀ Ctpl nstar (max Cres Csum)
  intro Λ A hb
  have hb0 : (0 : ℝ) ≤ (edgeBoundary Λ A).card := Nat.cast_nonneg _
  -- The repair construction at the prescribed origin, and an empty generation.
  have hmh := hmetric Λ A
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
    repairStage_positive_rank_length_lower_bound U dyadicOrigin Λ A C k₀ hC h₀ hKU₀ Sstar
      hSU' N r.val (Nat.pos_of_ne_zero hr)
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
    exact htpl Λ A N (e i).val (e i).property.1 w.val hwb
  choose s T hs hpts hTsep hcut using htemp
  have hlen_pos : ∀ r : Ret, 0 < len r := fun r ↦
    repairStageCharacteristicLength_pos_of_ne_dummy dyadicOrigin Λ A C k₀ hC h₀ Sstar N
      r.val r.property.1
  refine ⟨P, fun i ↦ nf (e i), s, T, ?_, ?_, ?_, hTsep, ?_, ?_, hcut, ?_, ?_⟩
  · -- The exceptional sites.
    rw [hres]
    have hexc := card_repairStageExceptionalSites_le_of_isEmpty (hC := hC) (h₀ := h₀)
      (Sstar := Sstar) N (hmark Λ A N)
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
      have hlim := beltReplacementScaleLimit_of_beltReplacementScaleThreshold_le CB one_pos
        hU2
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
      exact le_primaryScannerScale_of_primaryScannerScaleThreshold_le (by linarith)
        (hKn₀.trans hk)
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
    have hcol : 𝔇N.color (e j).val = 𝔇N.color (e i).val :=
      (hfam j).symm.trans (hfji.trans (hfam i))
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
    · obtain ⟨hinit, hrep⟩ := hsep Λ A
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
      exact (fine_clearance_of_fineClearanceThreshold_le hc₁ hCB.le hU1).trans_le hd
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
      have h := hprim Λ A N₀ (Finset.univ.image f)
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
      have h := hnonprim Λ A N
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


/-- The stopping scale of the two-family decomposition: the largest of the
margin thresholds `repairMarginThreshold (1/128)` (templates and separation) and
`repairMarginThreshold (1/4)` (metric hypotheses), `2`, and the length bound
`twoFamilyLengthBound c₁ C_B n_*`. Source: area-law Section 11,
`10-geometry.tex`, lines 756–767. -/
def twoFamilyStoppingScale (c₁ CB : ℝ) (nstar : ℕ) : ℝ :=
  max (max (repairMarginThreshold (1 / 128)) (repairMarginThreshold (1 / 4)))
    (max 2 (twoFamilyLengthBound c₁ CB nstar))

/-- The lower layer index of the two-family decomposition: the largest of
`5·10⁷`, the birth-template threshold at the stopping scale (which contains the
metric and separation thresholds `fineScaleIndexThreshold S_*`), and
`twoFamilyLayerThreshold`. Source: area-law Section 11, `10-geometry.tex`,
lines 768–774. -/
def twoFamilyLowerLayerIndex (D₀ CP CB c₁ : ℝ) (nstar : ℕ) : ℕ :=
  max 50000000 (max (birthTemplateLayerThreshold D₀ CP CB (twoFamilyStoppingScale c₁ CB nstar))
    (twoFamilyLayerThreshold CP CB c₁ nstar))

/-- **The explicit constant of the two-family decomposition.** With
`C_tpl' = max C_tpl 1`, `C_P = primaryScannerConstant C_tpl'`,
`C_B = beltScannerConstant C_tpl'`, the stopping scale
`S_* = twoFamilyStoppingScale c₁ C_B n_*`, the layer width
`twoFamilyLayerWidth D₀` and the lower layer index
`twoFamilyLowerLayerIndex D₀ C_P C_B c₁ n_*`, it is `twoFamilyConstant` with the
counting coefficients `M_t = repairMarkCountConstant S_*`,
`M_p = primaryErrorSumConstant C_P` and `L_q = repairRetainedCountConstant S_*`.
The birth-separation constant `c₁` is an argument. Auxiliary to the explicit
constant of Theorem 1.1 (`docs/notes/arealaw2d_explicit_constant.tex`); the
source asserts only that a constant exists. Source: area-law Section 11,
`10-geometry.tex`, threshold order lines 756–774 and assembly lines 776–802. -/
def twoFamilyDecompositionConstant (D₀ Ctpl : ℝ) (nstar : ℕ) (c₁ : ℝ) : ℝ :=
  let CP := primaryScannerConstant (max Ctpl 1)
  let CB := beltScannerConstant (max Ctpl 1)
  let Sstar := twoFamilyStoppingScale c₁ CB nstar
  twoFamilyConstant (twoFamilyLayerWidth D₀) (twoFamilyLowerLayerIndex D₀ CP CB c₁ nstar) Sstar
    (repairMarkCountConstant Sstar) (primaryErrorSumConstant CP)
    (repairRetainedCountConstant Sstar)

/-- **Proposition 11.2 with the explicit constant, for `C_tpl ≥ 1`.** For every
birth-separation constant `c₁` and every lower scale threshold `n_*`, the
constant `twoFamilyConstant` of the explicit choices of
`twoFamilyDecompositionConstant`, at `C_tpl` itself, is a constant of the
two-family decomposition. Auxiliary to area-law Section 11, `10-geometry.tex`,
threshold order lines 756–774 and assembly lines 776–802. -/
theorem isTwoFamilyDecompositionConstant_of_one_le {D₀ Ctpl c₁ : ℝ} (hCtpl : 1 ≤ Ctpl)
    (hc : Geometry.IsBirthSeparationConstant c₁) (nstar : ℕ) :
    IsTwoFamilyDecompositionConstant D₀ Ctpl nstar
      (twoFamilyConstant (twoFamilyLayerWidth D₀)
        (twoFamilyLowerLayerIndex D₀ (primaryScannerConstant Ctpl) (beltScannerConstant Ctpl)
          c₁ nstar)
        (twoFamilyStoppingScale c₁ (beltScannerConstant Ctpl) nstar)
        (repairMarkCountConstant (twoFamilyStoppingScale c₁ (beltScannerConstant Ctpl) nstar))
        (primaryErrorSumConstant (primaryScannerConstant Ctpl))
        (repairRetainedCountConstant
          (twoFamilyStoppingScale c₁ (beltScannerConstant Ctpl) nstar))) := by
  classical
  set CP := primaryScannerConstant Ctpl
  set CB := beltScannerConstant Ctpl
  have hCP : 1 ≤ CP := one_le_primaryScannerConstant Ctpl
  have hCB : 0 < CB := beltScannerConstant_pos hCtpl
  -- The stopping scale.
  set Sstar := twoFamilyStoppingScale c₁ CB nstar
  have hS128 : repairMarginThreshold (1 / 128) ≤ Sstar :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hS4 : repairMarginThreshold (1 / 4) ≤ Sstar :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hS2 : 2 ≤ Sstar := (le_max_left _ _).trans (le_max_right _ _)
  have hSU : twoFamilyLengthBound c₁ CB nstar ≤ Sstar :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hS1 : 1 < Sstar := by linarith
  -- The layer width.
  set C : ℕ := twoFamilyLayerWidth D₀ with hCdef
  have hC : 2 ≤ C := Nat.le_add_left 2 _
  have hCD : 4 * D₀ < (C : ℝ) := by
    have := Nat.le_ceil (4 * D₀)
    rw [hCdef, twoFamilyLayerWidth]
    push_cast
    linarith
  -- The lower layer index.
  set k₀ : ℕ := twoFamilyLowerLayerIndex D₀ CP CB c₁ nstar
  have h₀ : 50000000 ≤ k₀ := le_max_left _ _
  have hKT : birthTemplateLayerThreshold D₀ CP CB Sstar ≤ k₀ :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hK₀ : twoFamilyLayerThreshold CP CB c₁ nstar ≤ k₀ :=
    (le_max_right _ _).trans (le_max_right _ _)
  have hKF : fineScaleIndexThreshold Sstar ≤ k₀ := (le_max_left _ _).trans hKT
  have hmetric (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) :=
    repairMetricHypotheses_of_le (a₀ := 1 / 4) (by norm_num) le_rfl hS4 dyadicOrigin Λ A C k₀
      hC h₀ hKF
  exact isTwoFamilyDecompositionConstant_twoFamilyConstant hCP hCB hc.pos hC h₀ hS2 hSU hK₀
    (fun Λ A N ↦ repairStage_birth_templates_of_le Ctpl hCtpl D₀ hS128 C hCD dyadicOrigin Λ A
      k₀ hC h₀ hKT N)
    hmetric
    (fun Λ A ↦ hc.birthSeparated hS128 dyadicOrigin Λ A C k₀ hC h₀ hKF)
    (fun Λ A N ↦ repairStage_markIndex_prefix_le hS1 dyadicOrigin Λ A C k₀ hC h₀ (1 / 4)
      (hmetric Λ A) N)
    (fun Λ A n S hS ↦ repairStage_primary_error_sum_le (by linarith) dyadicOrigin Λ A C k₀ hC h₀
      Sstar n S hS)
    (fun Λ A N ↦ repairStage_retained_positive_rank_error_sum_le hS1 hCB dyadicOrigin Λ A C k₀
      hC h₀ (1 / 4) (hmetric Λ A) N)

/-- A template for a larger template constant is a template for any smaller one:
the constant enters only the scale inequality `Ctpl N₀ (s₀ + 1) ≤ n`, whose
other factors are nonnegative. -/
def Geometry.Template.ofLe {Ctpl Ctpl' : ℝ} {n s₀ : ℕ} (h : Ctpl ≤ Ctpl')
    (T : Geometry.Template Ctpl' n s₀) : Geometry.Template Ctpl n s₀ where
  n_pos := T.n_pos
  s₀_pos := T.s₀_pos
  pieceCount := T.pieceCount
  pieceCount_pos := T.pieceCount_pos
  polygon := T.polygon
  sample := T.sample
  mem_sample := T.mem_sample
  piece_diameter := T.piece_diameter
  points := T.points
  nonempty := T.nonempty
  cover := T.cover
  scale := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h (Nat.cast_nonneg T.pieceCount)) (by positivity)).trans T.scale
  diameter := T.diameter

/-- A constant of the two-family decomposition for a larger template constant is
a constant for any smaller one: templates are read with `Geometry.Template.ofLe`.
Source: area-law Section 11, `prop:two-families`, `10-geometry.tex`,
lines 98–141, with Definition 9.3 (`scanner:template`). -/
theorem IsTwoFamilyDecompositionConstant.ofLe {D₀ Ctpl Ctpl' C : ℝ} {nstar : ℕ}
    (hC : IsTwoFamilyDecompositionConstant D₀ Ctpl' nstar C) (h : Ctpl ≤ Ctpl') :
    IsTwoFamilyDecompositionConstant D₀ Ctpl nstar C := by
  intro Λ A hb
  obtain ⟨P, n, s, T, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩ := hC Λ A hb
  exact ⟨P, n, s, fun i ↦ (T i).ofLe h, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉⟩

/-- **Proposition 11.2 with the explicit constant.** For all real template
constants `D₀` and `C_tpl`, every lower scale threshold `n_*` and every
birth-separation constant `c₁`, the number
`twoFamilyDecompositionConstant D₀ C_tpl n_* c₁` is a constant of the two-family
decomposition at `n_*`. Templates are built for `max C_tpl 1` and read as
templates for `C_tpl`. Auxiliary to area-law Section 11, `prop:two-families`,
`10-geometry.tex`, lines 98–141, with the threshold order of lines 756–774;
the source asserts only that a constant exists. -/
theorem isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant (D₀ Ctpl : ℝ)
    (nstar : ℕ) {c₁ : ℝ} (hc : Geometry.IsBirthSeparationConstant c₁) :
    IsTwoFamilyDecompositionConstant D₀ Ctpl nstar
      (twoFamilyDecompositionConstant D₀ Ctpl nstar c₁) :=
  (isTwoFamilyDecompositionConstant_of_one_le (le_max_right Ctpl 1) hc nstar).ofLe
    (le_max_left Ctpl 1)

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
(Definition 9.3). Every constant is explicit except the separation constant
`c₁` (`isTwoFamilyDecompositionConstant_of_one_le`). -/
theorem twoFamilyDecomposition_of_one_le {D₀ Ctpl : ℝ} (hCtpl : 1 ≤ Ctpl) :
    TwoFamilyDecomposition D₀ Ctpl := by
  intro nstar _
  obtain ⟨c₁, hc⟩ := Geometry.exists_isBirthSeparationConstant
  exact ⟨_, isTwoFamilyDecompositionConstant_of_one_le hCtpl hc nstar⟩

/-- Proposition 11.2 of the area-law manuscript (`prop:two-families`,
`10-geometry.tex` lines 98–141), for every real `D₀` and `Ctpl`, with no further
hypothesis. The constant is `twoFamilyDecompositionConstant`
(`isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant`). -/
theorem twoFamilyDecomposition (D₀ Ctpl : ℝ) : TwoFamilyDecomposition D₀ Ctpl := by
  intro nstar _
  obtain ⟨c₁, hc⟩ := Geometry.exists_isBirthSeparationConstant
  exact ⟨_, isTwoFamilyDecompositionConstant_twoFamilyDecompositionConstant D₀ Ctpl nstar hc⟩

end TNLean.PEPS.AreaLaw
