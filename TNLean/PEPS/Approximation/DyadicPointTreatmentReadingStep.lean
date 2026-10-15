/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicPointTreatmentStep
import TNLean.PEPS.Approximation.DyadicReadingFootprints

/-!
# The point treatments with one footprint ratio

The compactness observation gives one footprint ratio `ν` for the two-owner condition of the
readings of the temporary guides near a mark at a corner of the repainted block, whether or not
that mark is treated (`exists_pointTreatment_footprintRatio_homogenize_reading`): near the mark,
the homogenization about all marks is the homogenization about that mark alone, or no
homogenization at all (`homogenize_iUnion_eq_of_notMem`). This file chooses the hole radius
`ε₀ t`, the patches of radius `u = ν t / 2`, so that `2 u = ν t`, and one bound `b₀` on the number
of net patches, and so turns every point treatment and every removal into one gate
(`exists_pointTreatment_step_reading`), with the two-owner hypotheses of `pointTreatment_step`
discharged.

## Main results

* `Approximation.exists_pointTreatment_footprintRatio_homogenize_reading`.
* `Approximation.exists_pointTreatment_step_reading`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the point treatments
  (lines 328–339), the compactness observation (lines 447–479), the point-treatment covers (lines
  481–505) and the order of the constants (lines 559–570).
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-- Near a grid corner that is not a mark, homogenizing about the marks changes nothing, when the
marks are at distance at least `n > 8 t` apart. -/
theorem homogenize_iUnion_eq_of_notMem {ι : Type*} {n t : ℝ} (hn : 0 < n) (htn : 8 * t < n)
    (M : Finset (ℤ × ℤ)) {Q : ℤ × ℤ} (hQ : Q ∉ M) (P : ι) (f : ℝ × ℝ → ι) {q : ℝ × ℝ}
    (hq : q ∈ ball (blockCorner n Q) (4 * t)) :
    homogenize (⋃ Q' ∈ M, ball (blockCorner n Q') t) P f q = f q := by
  refine homogenize_of_notMem fun h => ?_
  simp only [mem_iUnion, exists_prop] at h
  obtain ⟨Q', hQ', hq'⟩ := h
  have e : Q' ≠ Q := fun e => hQ (e ▸ hQ')
  have h1 := le_dist_blockCorner_of_ne hn e
  have h2 := dist_triangle (blockCorner n Q') q (blockCorner n Q)
  rw [mem_ball] at hq hq'
  rw [dist_comm] at hq'
  have : 0 ≤ t := by
    by_contra h
    linarith [dist_nonneg (x := q) (y := blockCorner n Q)]
  linarith

/-- **One footprint ratio for the temporary guides near a mark.** Fix `ε₀ > 0`. There is a ratio
`ν > 0` such that, for every generic displacement `v`, every reading of an unmodified guide of the
repainting of a block, homogenized on the open squares of radius `t < n / 8` about the corners of a
finite set of marks to `B` or a label of the nine blocks around the block, satisfies the two-owner
condition near every corner of the block, treated or not, with holes of radius `ε₀ t` at its true
vertices and footprints of radius `ν t`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 447–479 and 481–505. -/
theorem exists_pointTreatment_footprintRatio_homogenize_reading {ε₀ : ℝ} (hε : 0 < ε₀) :
    ∃ ν > 0, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {κ : Type} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g → ∀ (M : Finset (ℤ × ℤ)) {Q : ℤ × ℤ},
      IsBlockCornerOf S Q → ∀ P : κ, (P = B ∨ ∃ R ∈ blockWindow 1, P = lab (R + S)) →
      ∀ g' : ℝ × ℝ → κ, IsDisplacedReading g'
        (homogenize (⋃ Q' ∈ M, ball (blockCorner n Q') t) P (shiftGuide (blockCorner n S) g)) v →
      HasTwoOwnerFootprints g' (closedBall (blockCorner n Q) (2 * t))
        {c | c ∈ closedBall (blockCorner n Q) (3 * t) ∧ IsTrueVertex g' c} (ε₀ * t) (ν * t) := by
  obtain ⟨ν, hν, H⟩ := exists_template_footprintRatio_reading.{0} hε
  refine ⟨ν, hν, fun {v} hv {κ n t} hn ht htn {lab S B g} hg M {Q} hQ P hP g' hg' => ?_⟩
  by_cases hQM : Q ∈ M
  · obtain ⟨i, hinj, heq⟩ :=
      exists_template_injOn hn hg hQ ht htn (some P) fun x hx => Option.mem_some_iff.1 hx ▸ hP
    refine H hv ht i _ hinj _ _ g' (fun q hq => ?_) hg'
    rw [homogenize_iUnion_eq_of_mem_ball hn htn M hQM P _ hq]
    exact heq q hq
  · obtain ⟨i, hinj, heq⟩ := exists_template_injOn hn hg hQ ht htn none (fun x hx => by
      simp at hx)
    refine H hv ht i _ hinj _ _ g' (fun q hq => ?_) hg'
    rw [homogenize_iUnion_eq_of_notMem hn htn M hQM P _ hq]
    exact heq q hq

variable {κ Party : Type}

/-- **The point treatments as gates, with one footprint ratio.** Fix `0 < ε₀ ≤ 1/16`. There are a
ratio `ν > 0` and a bound `b₀` such that, for every generic displacement `v` and every `0 < t` with
`8 t < n`, the point treatment, or its removal, of a corner `Q₀` of the block `S`, between the
readings `g₁`, `g₂` along `v` of an unmodified guide homogenized about two sets of marks that
differ at most at `Q₀`, with holes of radius `ε₀ t` at sets of true vertices containing those
within `3 t` of `Q₀`, and patches of radius `ν t / 2`, is a circuit as in `pointTreatment_step`
for every `b ≥ b₀`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 447–505 and 559–570. -/
theorem exists_pointTreatment_step_reading {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν > 0, ∃ b₀ : ℕ, ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ} (hn : 0 < n), 0 < t → 8 * t < n →
      ∀ {lab : ℤ × ℤ → κ} {S : ℤ × ℤ} {B : κ} {g : ℝ × ℝ → κ},
      (blockBaseline hn lab S B).IsUnmodifiedGuide g →
      ∀ {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ), IsBlockCornerOf S Q₀ →
      (∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) → ∀ (L₀ : κ),
      (L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) → ∀ {g₁ g₂ : ℝ × ℝ → κ},
      IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
        (shiftGuide (blockCorner n S) g)) v →
      IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
        (shiftGuide (blockCorner n S) g)) v → ∀ (own : κ → Party) (ph : κ) (rank : κ → ℕ)
      {V V' : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g₁ c) → (∀ c ∈ V', IsTrueVertex g₂ c) →
      (∀ c ∈ closedBall (blockCorner n Q₀) (3 * t), IsTrueVertex g₁ c → c ∈ V) →
      (∀ c ∈ closedBall (blockCorner n Q₀) (3 * t), IsTrueVertex g₂ c → c ∈ V') →
      (∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V')) →
      ∀ (hole patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (hole z).center = z ∧ (hole z).scale = ε₀ * t) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * t / 2) →
      ∀ (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
        (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) → b₀ ≤ b →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)}, ‖Ω‖ ≤ 1 →
      (∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, Nonempty (hole z).Tag) →
      ∃ w : OriginalCircuit (guideFrame pos q g₁ own ph rank V hole hpV).regs
          (guideFrame pos q g₂ own ph rank V' hole hpV').regs,
        w.nonprivateCount ≤ 1 ∧
        (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑(blockParties own lab S B)) ∧
        w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
          L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
        ‖w.eval ((guideFrame pos q g₁ own ph rank V hole hpV).regIso.symm
            ((guideFrame pos q g₁ own ph rank V hole hpV).refVec Ω)) -
          (guideFrame pos q g₂ own ph rank V' hole hpV').regIso.symm
            ((guideFrame pos q g₂ own ph rank V' hole hpV').refVec Ω)‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨ν₀, hν₀, H⟩ := exists_pointTreatment_footprintRatio_homogenize_reading hε
  set ν := min ν₀ (1 / 4)
  have hν : 0 < ν := lt_min hν₀ (by norm_num)
  have hνle : ν ≤ 1 / 4 := min_le_right _ _
  have hνν : ν ≤ ν₀ := min_le_left _ _
  set b₀ : ℕ := max 53 ⌈(2 * (2 + 4 * ε₀ + ν) / ν + 1) ^ 2⌉₊
  refine ⟨ν, hν, b₀, fun {v} hv {ι _ _ q _ pos κ Party n t} hn ht htn {lab S B g} hg
    {M₁ M₂} Q₀ hQ₀ hM L₀ hL₀ {g₁ g₂} hg₁ hg₂ own ph rank {V V'} hV hV' hVc hVc' hVV'
    hole patch hhole hpatch hpV hpV' {C c b L} hL hcHole hcPatch hb {Ω} hΩ hεp hεh htag => ?_⟩
  have hQS : blockCorner n Q₀ ∈ closedBlock n S := by
    obtain ⟨h1, h2⟩ := hQ₀
    refine mem_closedSquare.2 ?_
    simp only [blockCorner, Prod.fst_sub, Prod.snd_sub]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> push_cast <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hW : closedBall (blockCorner n Q₀) (t + 2 * (ε₀ * t) + 3 * (ν * t / 2)) ⊆
      closedBall (blockCorner n Q₀) (2 * t) :=
    closedBall_subset_closedBall (by nlinarith)
  have hδ : 2 * (ν * t / 2) ≤ ν₀ * t := by nlinarith
  have hb' : (2 * (t + 2 * (ε₀ * t) + ν * t / 2) / (ν * t / 2) + 1) ^ 2 ≤ (b : ℝ) := by
    have e : 2 * (t + 2 * (ε₀ * t) + ν * t / 2) / (ν * t / 2) = 2 * (2 + 4 * ε₀ + ν) / ν := by
      field_simp
      ring
    rw [e]
    refine (Nat.le_ceil _).trans ?_
    exact_mod_cast (le_max_right _ _).trans hb
  exact pointTreatment_step hn ht (by positivity) (by positivity) (by nlinarith) hg Q₀ hQS hM L₀
    hL₀ hg₁ hg₂ own ph rank hV hV' hVV' hole patch hhole hpatch hpV hpV' hW
    (H := {c | c ∈ closedBall (blockCorner n Q₀) (3 * t) ∧ IsTrueVertex g₁ c})
    (H' := {c | c ∈ closedBall (blockCorner n Q₀) (3 * t) ∧ IsTrueVertex g₂ c})
    (fun c hc => hVc c hc.1 hc.2) (fun c hc => hVc' c hc.1 hc.2)
    ((H hv hn ht htn hg M₁ hQ₀ L₀ hL₀ g₁ hg₁).mono hδ)
    ((H hv hn ht htn hg M₂ hQ₀ L₀ hL₀ g₂ hg₂).mono hδ) hL hcHole hcPatch hb'
    ((le_max_left _ _).trans hb) hΩ hεp hεh htag

end TNLean.PEPS.Approximation
