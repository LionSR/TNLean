/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicPointTreatmentReadingStep
import TNLean.PEPS.Approximation.DyadicResizeReadingStep
import TNLean.PEPS.Approximation.GuideFramePatchData
import TNLean.PEPS.Approximation.SheetStack

/-!
# Resizes and point treatments with supplied patches

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every hole and every net
patch is the patch chosen from the supply of Proposition 4.1 at its center and its radius, the
same on every sheet (`06-geometry.tex`, lines 109–118). The step theorems of the resizes and the
point treatments take the hole and net patches as arbitrary families with bounds on their tags,
their errors on `Ω` and the existence of a tag. This file chooses these families from the supply
(`EncodedFrame.suppliedPatch`) and discharges those bounds once.

* `EncodedFrame.suppliedPatch` : the supplied patch at every center, with a radius depending on
  the center, and its center, scale, tag count, error and tag.
* `exists_resize_step_supplied`, `exists_pointTreatment_step_supplied` : the resize of a hole and
  the point treatment, or its removal, as gates, with the hole and net patches supplied and at
  most `2 b` pair sources in each monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 4.1 `prop:patch`,
  `03-patches.tex`, lines 26–49; `06-geometry.tex`, lines 109–133, 328–339, 481–505, 529–541 and
  574–583.
-/

noncomputable section

namespace TNLean.PEPS

namespace EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ}
  {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c p : ℝ} {L : ℕ}

/-- **Supplied patches.** The patch chosen from the supply of Proposition 4.1 at every center
`z`, with radius `ρ z` in `(0, B₀ log L]`. It depends only on the center and the radius, so a
given center and radius receive the same patch on every sheet.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49, and `06-geometry.tex`,
lines 109–118. -/
def suppliedPatch (S : AdaptivePatchSupply pos Ω B₀ C c p L) (ρ : ℝ × ℝ → ℝ)
    (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L) (z : ℝ × ℝ) : SquarePatch pos q :=
  patchAt S z (hρ z)

variable (S : AdaptivePatchSupply pos Ω B₀ C c p L) {ρ : ℝ × ℝ → ℝ}
  (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L)

@[simp] theorem suppliedPatch_center (z : ℝ × ℝ) : (suppliedPatch S ρ hρ z).center = z :=
  patchAt_center S z (hρ z)

@[simp] theorem suppliedPatch_scale (z : ℝ × ℝ) : (suppliedPatch S ρ hρ z).scale = ρ z :=
  patchAt_scale S z (hρ z)

theorem isSuppliedPatch_suppliedPatch (z : ℝ × ℝ) : IsSuppliedPatch S (suppliedPatch S ρ hρ z) :=
  ⟨z, ρ z, hρ z, rfl⟩

/-- Supplied patches at a center with equal radii agree. -/
theorem suppliedPatch_congr {ρ' : ℝ × ℝ → ℝ} (hρ' : ∀ z, 0 < ρ' z ∧ ρ' z ≤ B₀ * Real.log L)
    {z : ℝ × ℝ} (h : ρ z = ρ' z) : suppliedPatch S ρ hρ z = suppliedPatch S ρ' hρ' z := by
  unfold suppliedPatch
  generalize hρ z = a, hρ' z = b
  revert a b
  rw [h]
  intro a b
  rfl

/-- The patch data of supplied patches at test exponent `60`: at most `C' L^{c'}` tags, error at
most `L^{-60}` on `Ω`, and a tag, for `‖Ω‖ = 1`, `L ≥ 2` and natural `C' ≥ max 1 C`, `c' ≥ c`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49, and `06-geometry.tex`,
lines 109–124 and 574–583. -/
theorem suppliedPatch_data (S : AdaptivePatchSupply pos Ω B₀ C c 60 L) (hΩ : ‖Ω‖ = 1)
    (hL : 2 ≤ L) {C' c' : ℕ} (hC : C ≤ C') (hC' : 1 ≤ C') (hc : c ≤ c') :
    (∀ z, Fintype.card (suppliedPatch S ρ hρ z).Tag ≤ C' * L ^ c') ∧
      (∀ z, ‖act (suppliedPatch S ρ hρ z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) ∧
      ∀ z, Nonempty (suppliedPatch S ρ hρ z).Tag :=
  ⟨fun z => (isSuppliedPatch_suppliedPatch S hρ z).card_tag_le (by omega) hC hC' hc,
    fun z => by
      rw [← Approximation.GuideFrameRewrite.rpow_neg_sixty]
      exact (isSuppliedPatch_suppliedPatch S hρ z).norm_act_proj_sub_le,
    fun z => (isSuppliedPatch_suppliedPatch S hρ z).nonempty_tag hΩ hL (by norm_num)⟩

end EncodedFrame

namespace Approximation

open EncodedFrame PairEffect Set Metric

/-- **The resizes of a level as gates, with supplied patches.** In the setting of
`exists_resize_step_reading`, let the old and new hole patches and the net patches be supplied by
Proposition 4.1 at test exponent `60` (`EncodedFrame.suppliedPatch`), with hole radii `ρ z` and
`ρ' z` among `h_n`, `h_{2n}`, equal away from the resized corner `c₀`, and net radius `ν n`. Then,
for `‖Ω‖ = 1`, `L ≥ 2` and natural `C' ≥ max 1 C`, `c' ≥ c`, the resize is a circuit as in
`resize_step` with constants `C'` and `c'`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49, and `06-geometry.tex`, lines 102–133,
529–541 and 574–583. -/
theorem exists_resize_step_supplied {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ}, 0 < n → n < t → ∀ {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ}
      {g : ℝ × ℝ → κ}, IsDisplacedReading g (blockGuide (2 * n) lab) v → ∀ (own : κ → Party)
      (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g c) →
      blockCorner (2 * n) Q ∈ V →
      (∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V) →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c : ℝ} {L : ℕ}
        (P : AdaptivePatchSupply pos Ω B₀ C c 60 L), ‖Ω‖ = 1 → 2 ≤ L →
      ∀ {ρ ρ' : ℝ × ℝ → ℝ} (hρ : ∀ z, 0 < ρ z ∧ ρ z ≤ B₀ * Real.log L)
        (hρ' : ∀ z, 0 < ρ' z ∧ ρ' z ≤ B₀ * Real.log L)
        (_ : ∀ _ : ℝ × ℝ, 0 < ν * n ∧ ν * n ≤ B₀ * Real.log L),
      (∀ z, (ρ z = holeRadius ε₀ n t ∨ ρ z = holeRadius ε₀ (2 * n) t) ∧
        (ρ' z = holeRadius ε₀ n t ∨ ρ' z = holeRadius ε₀ (2 * n) t)) →
      (∀ z, z ≠ blockCorner (2 * n) Q → ρ z = ρ' z) →
      ∀ (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (suppliedPatch P ρ hρ z).outer (suppliedPatch P ρ hρ z').outer)
        (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (suppliedPatch P ρ' hρ' z).outer (suppliedPatch P ρ' hρ' z').outer)
        {C' c' b : ℕ}, C ≤ C' → 1 ≤ C' → c ≤ c' →
      (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 9 ≤ b →
      ∃ P' : Finset Party, P'.card ≤ 9 ∧
        (∀ x ∈ P', ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
        ∃ w : OriginalCircuit
          (guideFrame pos q g own ph rank V (suppliedPatch P ρ hρ) hpOld).regs
          (guideFrame pos q g own ph rank V (suppliedPatch P ρ' hρ') hpNew).regs,
        w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P') ∧
        w.IsExpansionBounded (2 * b) ((C' + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^
          (2 * b) * L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30))) ∧
        ‖w.eval ((guideFrame pos q g own ph rank V (suppliedPatch P ρ hρ) hpOld).regRef Ω) -
          (guideFrame pos q g own ph rank V (suppliedPatch P ρ' hρ') hpNew).regRef Ω‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        w.IsSourceBounded (2 * b) := by
  obtain ⟨ν', hν', H⟩ := exists_resize_step_reading_isSourceBounded hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {v} hv {ι _ _ q _ pos κ Party n t} hn hnt {lab Q g} hg own ph
    rank {V} hV hc₀ hVc {Ω B₀ C c L} P hΩ hL {ρ ρ'} hρ hρ' hu hscale hsame hpOld hpNew
    {C' c' b} hC hC' hc hb hb9 => ?_⟩
  obtain ⟨hcOld, hεOld, htagOld⟩ := suppliedPatch_data hρ P hΩ hL hC hC' hc
  obtain ⟨hcNew, -, -⟩ := suppliedPatch_data hρ' P hΩ hL hC hC' hc
  obtain ⟨hcPatch, hεPatch, -⟩ := suppliedPatch_data hu P hΩ hL hC hC' hc
  exact H ν hν hνν' hv hn hnt hg own ph rank hV hc₀ hVc (suppliedPatch P ρ hρ)
    (suppliedPatch P ρ' hρ') (suppliedPatch P (fun _ => ν * n) hu)
    (fun z => ⟨suppliedPatch_center P hρ z, suppliedPatch_center P hρ' z⟩)
    (fun z => by simpa using hscale z)
    (fun z hz => suppliedPatch_congr P hρ hρ' (hsame z hz))
    (fun z => ⟨suppliedPatch_center P hu z, suppliedPatch_scale P hu z⟩) hpOld hpNew
    (by omega) hcOld hcNew hcPatch hb hb9 hΩ.le hεPatch hεOld htagOld

/-- **The point treatments as gates, with supplied patches.** In the setting of
`exists_pointTreatment_step_reading`, let the hole patches, of radius `ε₀ t`, and the net patches,
of radius `ν t / 2`, be supplied by Proposition 4.1 at test exponent `60`
(`EncodedFrame.suppliedPatch`). Then, for `‖Ω‖ = 1`, `L ≥ 2` and natural `C' ≥ max 1 C`,
`c' ≥ c`, the point treatment, or its removal, is a circuit as in `pointTreatment_step` with
constants `C'` and `c'`.

Polynomial-PEPS manuscript, `03-patches.tex`, lines 26–49, and `06-geometry.tex`, lines 109–118,
328–339, 481–505 and 574–583. -/
theorem exists_pointTreatment_step_supplied {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
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
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)} {B₀ C c : ℝ} {L : ℕ}
        (P : AdaptivePatchSupply pos Ω B₀ C c 60 L), ‖Ω‖ = 1 → 2 ≤ L →
      ∀ (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L)
        (_ : ∀ _ : ℝ × ℝ, 0 < ν * t / 2 ∧ ν * t / 2 ≤ B₀ * Real.log L)
        (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
        (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
        {C' c' b : ℕ}, C ≤ C' → 1 ≤ C' → c ≤ c' →
      (2 * (2 + 4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 53 ≤ b →
      ∃ w : OriginalCircuit (guideFrame pos q g₁ own ph rank V (suppliedPatch P _ hr) hpV).regs
          (guideFrame pos q g₂ own ph rank V' (suppliedPatch P _ hr) hpV').regs,
        w.nonprivateCount ≤ 1 ∧
        (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑(blockParties own lab S B)) ∧
        w.IsExpansionBounded (2 * b) ((C' + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C' + 1) ^ (3 * b) * (16 * b ^ 2 * (C' + 1) ^ (6 * b) + 1) ^
          (2 * b) * L ^ (3 * b * c' + 4 * b * (3 * b * c' + 30))) ∧
        ‖w.eval ((guideFrame pos q g₁ own ph rank V (suppliedPatch P _ hr) hpV).regRef Ω) -
          (guideFrame pos q g₂ own ph rank V' (suppliedPatch P _ hr) hpV').regRef Ω‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        w.IsSourceBounded (2 * b) := by
  obtain ⟨ν', hν', H⟩ := exists_pointTreatment_step_reading_isSourceBounded hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {v} hv {ι _ _ q _ pos κ Party n t} hn ht htn {lab S B g} hg
    {M₁ M₂} Q₀ hQ₀ hM L₀ hL₀ {g₁ g₂} hg₁ hg₂ own ph rank {V V'} hV hV' hVc hVc' hVV'
    {Ω B₀ C c L} P hΩ hL hr hu hpV hpV' {C' c' b} hC hC' hc hb hb53 => ?_⟩
  obtain ⟨hcHole, hεHole, htag⟩ := suppliedPatch_data hr P hΩ hL hC hC' hc
  obtain ⟨hcPatch, hεPatch, -⟩ := suppliedPatch_data hu P hΩ hL hC hC' hc
  exact H ν hν hνν' hv hn ht htn hg Q₀ hQ₀ hM L₀ hL₀ hg₁ hg₂ own ph rank hV hV' hVc hVc' hVV'
    (suppliedPatch P _ hr) (suppliedPatch P _ hu)
    (fun z => ⟨suppliedPatch_center P hr z, suppliedPatch_scale P hr z⟩)
    (fun z => ⟨suppliedPatch_center P hu z, suppliedPatch_scale P hu z⟩) hpV hpV'
    (by omega) hcHole hcPatch hb hb53 hΩ.le hεPatch hεHole htag

end Approximation

end TNLean.PEPS
