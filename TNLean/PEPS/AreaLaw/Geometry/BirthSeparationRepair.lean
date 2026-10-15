/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Geometry.BirthSeparationStar
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionStatement
import TNLean.PEPS.AreaLaw.Geometry.RepairInductionMetric

/-!
# Birth separation of the actual replacements

Every identifier of a repair stage is retained at all later stages, and its
*final actual region* is the intersection of its current regions over all
later stages. Each replacement born at a parent mark of scale `S` is compared
with every other identifier of the same stage with the same label, that is,
with every older identifier and every peer replacement. Its closed birth has
distance at least `c₁ d(S)^ρ₀` from the final actual region of each, with one
constant `c₁ > 0` chosen before the repair data.

The proof reads the two properties required by the local separation theorem
from the actual stages:

* near the parent mark, an older region lies in the isolated star of that
  mark, so after the removal of the parent square it lies in the exterior
  trapezoids of the wedges assigned to it; a peer at the same parent lies in
  its own birth; a peer at another parent is far away;
* the next generation removes the squares about the nine marks of the parent
  square from every region, including terminal squares.

The isolated stars, the separation of distinct marks, and the conclusion of
the uniform repair induction enter as the explicit premise
`IsUniformRepairInduction` (`geometry:repair-induction`).

**Scope restriction (replacement births):** the theorems here treat the births
of replacements. The births of initial belt tiles, also covered by
`geometry:birth-separation`, are not treated. Documented in
`docs/paper-gaps/arealaw2d_birth_separation_scope.tex`.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
September 24, 2026, Section 11, `geometry:birth-separation`, lines 573–659;
`geometry:repair-induction`, lines 471–485; and open actual regions and closed
births, lines 558–561.
Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

noncomputable section

namespace TNLean.PEPS.AreaLaw.Geometry

section Stages

variable (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
  (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar : ℝ)

local notation "𝔇" => repairStage o Λ A C k₀ hC h₀ Sstar

/-- An identifier of generation `j` retained at generation `j + n`.
Source: area-law Section 11, lines 398–407. -/
def repairRegionLift (j : ℕ) : (n : ℕ) → (𝔇 j).regionIndex → (𝔇 (j + n)).regionIndex
  | 0 => id
  | n + 1 => fun x ↦ (Sum.inl (repairRegionLift j n x) :
      RepairRegionIndex (j + n) (𝔇 (j + n)).scale Sstar (𝔇 (j + n)).color
        (letI : Nonempty (𝔇 (j + n)).regionIndex := ⟨(𝔇 (j + n)).dummy⟩
         repairCurrentAssignments (𝔇 (j + n)).current (𝔇 (j + n)).location
          (𝔇 (j + n)).scale))

/-- The final actual region of an identifier of generation `j`: the
intersection of its current regions at all later generations.
Source: area-law Section 11, lines 558–561 and 584–591. -/
def repairFinalRegion (j : ℕ) (x : (𝔇 j).regionIndex) : Set (ℝ × ℝ) :=
  ⋂ n, (𝔇 (j + n)).current (repairRegionLift o Λ A C k₀ hC h₀ Sstar j n x)

/-- The final actual region lies in the current region.
Source: area-law Section 11, lines 558–561. -/
theorem repairFinalRegion_subset_current (j : ℕ) (x : (𝔇 j).regionIndex) :
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j x ⊆ (𝔇 j).current x :=
  Set.iInter_subset _ 0

/-- The final actual region avoids every removal square of its own generation.
Source: area-law Section 11, lines 398–399 and 653–657. -/
theorem repairFinalRegion_subset_remnant (j : ℕ) (x : (𝔇 j).regionIndex) :
    repairFinalRegion o Λ A C k₀ hC h₀ Sstar j x ⊆
      (𝔇 j).current x \ repairRemovalSet (𝔇 j).location (𝔇 j).scale :=
  Set.iInter_subset _ 1

/-- **Birth separation of replacements** with constant `c₁`: every replacement
born at a parent mark of scale `S` has closed birth at distance at least
`c₁ d(S)^ρ₀` from the final actual region of every other identifier of its
generation with the same label, that is, of every older identifier and every
peer replacement.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–582. -/
def IsRepairBirthSeparated (c₁ : ℝ) : Prop :=
  ∀ j (x y : (𝔇 (j + 1)).regionIndex) (m : (𝔇 j).markIndex),
    repairRegionParent o Λ A C k₀ hC h₀ Sstar j x = some m → y ≠ x →
    (𝔇 (j + 1)).color y = (𝔇 (j + 1)).color x →
    ∀ z ∈ (𝔇 (j + 1)).birth x, ∀ w ∈ repairFinalRegion o Λ A C k₀ hC h₀ Sstar (j + 1) y,
      c₁ * repairHalfSide ((𝔇 j).scale m) ^ (Exponents.rho : ℝ) ≤ dist z w

end Stages

/-- **Birth separation of the actual replacements, from the repair induction.**
There is one fixed `c₁ > 0`, chosen before any repair data, with the following
property. Suppose the repair stages satisfy the uniform repair induction with
constant `a₀ > 0`, that every mark scale is at least the stopping scale
`S_* ≥ 1`, and that `d(S) ≤ (a₀ / 1000) S` for `S ≥ S_*`. Then every replacement
is separated from the final actual regions of the older and peer identifiers
of its label by `c₁ d(S)^ρ₀`.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, with
the margins of `geometry:trim-margins`, lines 380–394. -/
theorem exists_isRepairBirthSeparated_of_isUniformRepairInduction :
    ∃ c₁ > 0, ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (C k₀ : ℕ)
      (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀) (Sstar a₀ : ℝ), 0 < a₀ → 1 ≤ Sstar →
      (∀ j p, Sstar ≤ (repairStage o Λ A C k₀ hC h₀ Sstar j).scale p) →
      (∀ S, Sstar ≤ S → repairHalfSide S ≤ a₀ / 1000 * S) →
      IsUniformRepairInduction o Λ A C k₀ hC h₀ Sstar a₀ →
      IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ := by
  obtain ⟨c₁, hc₁, hsep⟩ := exists_repairBirth_separation
  refine ⟨c₁, hc₁, fun o Λ A C k₀ hC h₀ Sstar a₀ ha₀ hS1 hscale hmargin hI ↦ ?_⟩
  intro j x y m hxm hyx hcol z hz w hw
  set D := repairStage o Λ A C k₀ hC h₀ Sstar j with hD
  letI : Nonempty D.regionIndex := ⟨D.dummy⟩
  set σ := repairCurrentAssignments D.current D.location D.scale with hσ
  have hstars := hI.hasIsolatedStars j
  -- The replacement `x` is a fresh identifier born at `m`.
  obtain ⟨i, rfl⟩ | ⟨⟨n, hn⟩, ⟨⟨P, hP⟩, Cx⟩, rfl⟩ :
      (∃ i : D.regionIndex, x = Sum.inl i) ∨
        ∃ q : RepairReplacementIndex j D.scale Sstar D.color σ, x = Sum.inr q := by
    rcases x with i | q
    · exact Or.inl ⟨i, rfl⟩
    · exact Or.inr ⟨q, rfl⟩
  · simp [repairRegionParent] at hxm
  obtain rfl : P = m := by simpa [repairRegionParent] using hxm
  set v := D.location P
  set u := repairHalfSide (D.scale P)
  have hu1 : 1 ≤ u := hS1.trans hP
  have hu0 : 0 < u := by linarith
  have hSP := hscale j P
  have hmarg := hmargin _ hSP
  have hSpos : 0 < D.scale P := by linarith
  have hz' : z ∈ (fun z ↦ v + u • z) '' repairNormRunRegion D.color (σ P) Cx := hz
  refine (hsep D.color (σ P) Cx v hu1 (repairFinalRegion o Λ A C k₀ hC h₀ Sstar (j + 1) y)
    ?_ ?_ z hz' w hw).trans (by rw [dist_eq_norm])
  · -- The local same-label bound near the parent mark.
    intro w hw hnear
    have hrem := repairFinalRegion_subset_remnant o Λ A C k₀ hC h₀ Sstar (j + 1) y hw
    have hcur := repairFinalRegion_subset_current o Λ A C k₀ hC h₀ Sstar (j + 1) y hw
    rcases y with i | ⟨⟨n', hn'⟩, ⟨⟨P', hP'⟩, C'⟩⟩
    · -- An older identifier: the isolated star of the parent mark.
      have hwi : w ∈ D.current i \ repairRemovalSet D.location D.scale := hcur
      have hout : u < ‖w - v‖ := by
        by_contra hle
        push Not at hle
        exact hwi.2 (Set.mem_iUnion.mpr ⟨P, by
          rw [repairSquare, Metric.mem_closedBall, dist_eq_norm]; exact hle⟩)
      have h6 : 6 * u ≤ a₀ * D.scale P := by nlinarith
      obtain ⟨t, ht, htrap⟩ := (hstars.2 P).exists_mem_repairExteriorTrapezoid hu0 h6
        hwi.1 hnear hout
      refine Or.inl (Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨?_, htrap⟩⟩)
      have hcol' : D.color i = repairReplacementColor D.color (σ P) Cx := hcol
      have hσt : σ P t = i := ht
      simp only [repairExteriorColor, hσt, hcol', repairReplacementColor]
      generalize repairFanRunExteriorColor D.color (σ P) Cx = a
      fin_cases a <;> decide
    · by_cases hPP : P' = P
      · subst hPP
        -- A peer replacement at the same parent.
        have hC' : C' ≠ Cx := by
          rintro rfl
          exact hyx (by obtain rfl : n' = n := by omega; rfl)
        have hwb : w ∈ (fun z ↦ v + u • z) '' repairNormRunRegion D.color (σ P) C' :=
          interior_subset hcur
        obtain ⟨x', hx', rfl⟩ := hwb
        have hval : u⁻¹ • (v + u • x' - v) = x' := by
          rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hu0.ne', one_smul]
        rw [hval]
        refine Or.inr (Set.mem_iUnion.mpr ⟨C', Set.mem_iUnion.mpr ⟨⟨hC', ?_⟩, hx'⟩⟩)
        have hcol' : repairReplacementColor D.color (σ P) C' =
            repairReplacementColor D.color (σ P) Cx := hcol
        simp only [repairReplacementColor] at hcol'
        generalize repairFanRunExteriorColor D.color (σ P) C' = a at hcol'
        generalize repairFanRunExteriorColor D.color (σ P) Cx = b at hcol'
        fin_cases a <;> fin_cases b <;> simp_all
      · -- A peer replacement at another parent is far from the parent mark.
        exfalso
        have hbirth := repairStage_birth_subset_repairSquare o Λ A C k₀ hC h₀ Sstar j
          (Sum.inr ⟨⟨n', hn'⟩, ⟨⟨P', hP'⟩, C'⟩⟩) P' rfl
        have hwb : w ∈ repairSquare (D.location P') (D.scale P') :=
          hbirth (interior_subset hcur)
        rw [repairSquare, Metric.mem_closedBall, dist_eq_norm] at hwb
        have hd := hstars.1 P P' (Ne.symm hPP)
        have hmarg' := hmargin _ (hscale j P')
        have hSP' := hscale j P'
        rw [dist_eq_norm] at hd
        have htri : ‖D.location P - D.location P'‖ ≤
            ‖w - D.location P‖ + ‖w - D.location P'‖ := by
          calc ‖D.location P - D.location P'‖ =
                ‖(w - D.location P') - (w - D.location P)‖ := by congr 1; abel
            _ ≤ _ := norm_sub_le _ _
            _ = _ := add_comm _ _
        have hmax1 := le_max_left (D.scale P) (D.scale P')
        have hmax2 := le_max_right (D.scale P) (D.scale P')
        nlinarith [mul_le_mul_of_nonneg_left hmax1 ha₀.le,
          mul_le_mul_of_nonneg_left hmax2 ha₀.le]
  · -- The removal squares of the nine following marks.
    intro w hw p hwp
    have hrem := repairFinalRegion_subset_remnant o Λ A C k₀ hC h₀ Sstar (j + 1) y hw
    refine hrem.2 (Set.mem_iUnion.mpr ⟨(⟨j + 1, rfl⟩, (⟨P, hP⟩, p)), hwp⟩)

/-- **Birth-template separation of replacements, from Lemma 11.4.** If the
uniform repair induction holds, there are one fixed `c₁ > 0` and a threshold
`T` such that, for every stopping scale `S_* ≥ T` and every layer width, every
sufficiently large lower layer index gives repair stages in which every
replacement born at a parent of scale `S` has distance at least `c₁ d(S)^ρ₀`
from the final actual region of every earlier or peer identifier of its label.
Source: area-law Section 11, `geometry:birth-separation`, lines 573–659, from
`geometry:repair-induction`, lines 471–485. -/
theorem exists_isRepairBirthSeparated_of_uniformRepairInductionStatement
    (h : UniformRepairInductionStatement) :
    ∃ c₁ > 0, ∃ T : ℝ, ∀ Sstar, T ≤ Sstar → ∀ C : ℕ, ∃ K : ℕ,
      ∀ (o : ℝ × ℝ) (Λ : Finset (ℤ × ℤ)) (A : Finset (Site Λ)) (k₀ : ℕ)
        (hC : 2 ≤ C) (h₀ : 50000000 ≤ k₀), K ≤ k₀ →
          IsRepairBirthSeparated o Λ A C k₀ hC h₀ Sstar c₁ := by
  obtain ⟨c₁, hc₁, hsep⟩ := exists_isRepairBirthSeparated_of_isUniformRepairInduction
  obtain ⟨a₀, ha₀, T₁, hT₁⟩ := h
  obtain ⟨T₂, hT₂⟩ := exists_repairMetricHypotheses (a₀ := min a₀ (1 / 4))
    (lt_min ha₀ (by norm_num)) (min_le_right _ _)
  refine ⟨c₁, hc₁, max (max T₁ T₂) 1, fun Sstar hS C ↦ ?_⟩
  have hS₁ : T₁ ≤ Sstar := (le_max_left _ _).trans ((le_max_left _ _).trans hS)
  have hS₂ : T₂ ≤ Sstar := (le_max_right _ _).trans ((le_max_left _ _).trans hS)
  have hS1 : 1 ≤ Sstar := (le_max_right _ _).trans hS
  obtain ⟨K₁, hK₁⟩ := hT₁ Sstar hS₁ C
  obtain ⟨K₂, hK₂⟩ := hT₂ Sstar hS₂ C
  refine ⟨max K₁ K₂, fun o Λ A k₀ hC h₀ hK ↦ ?_⟩
  have hM := hK₂ o Λ A k₀ hC h₀ ((le_max_right _ _).trans hK)
  refine hsep o Λ A C k₀ hC h₀ Sstar a₀ ha₀ hS1 hM.le_scale (fun S hSS ↦ ?_)
    (hK₁ o Λ A k₀ hC h₀ ((le_max_left _ _).trans hK))
  have := hM.margin S hSS
  have hSpos : 0 ≤ S := by linarith
  calc repairHalfSide S ≤ min a₀ (1 / 4) / 1000 * S := this
    _ ≤ a₀ / 1000 * S := by gcongr; exact min_le_left _ _

end TNLean.PEPS.AreaLaw.Geometry
