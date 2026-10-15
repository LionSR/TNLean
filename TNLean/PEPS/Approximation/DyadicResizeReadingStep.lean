/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicReadingFootprints
import TNLean.PEPS.Approximation.DyadicResizeStep

/-!
# The resizes of a level with one footprint ratio

On entering level `n`, the protocol of Proposition 7.1 resizes the main holes of a reading of a
guide uniform on the `2n`-blocks from the radius `h_{2n}` to the radius `h_n`, one hole at a time
(`06-geometry.tex`, lines 529–541). The compactness observation gives one footprint ratio `ν` for
the two-owner condition of these readings, at every intermediate configuration
(`exists_resizing_footprintRatio_mixed_reading`), and so does every smaller ratio. For every
ratio `ν` below a threshold `ν'`, as fixed by the protocol constants, this file takes the patches
of radius `u = ν n`, so that `2 u = ν (2 n)`, and every `b` bounding the number of net patches,
and so turns every such resize into one gate (`exists_resize_step_reading`), with the two-owner
hypotheses of `resize_step` discharged.

## Main results

* `Approximation.exists_resize_step_reading_isSourceBounded`,
  `Approximation.exists_resize_step_reading`: with and without the bound of `2b` pair sources in
  every monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the hole radii (lines
  102–133), the compactness observation (lines 447–479), the hole resizing (lines 529–541) and the
  order of the constants (lines 559–570).
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-- **The resizes of a level as gates, with one footprint ratio and their pair sources.** The
conclusion of `exists_resize_step_reading`, together with the bound of `2b` pair sources in every
monomial of each gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–133, 447–479, 529–541 and 559–570;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_resize_step_reading_isSourceBounded {ε₀ : ℝ} (hε : 0 < ε₀)
    (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ}, 0 < n → n < t → ∀ {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ}
      {g : ℝ × ℝ → κ}, IsDisplacedReading g (blockGuide (2 * n) lab) v → ∀ (own : κ → Party)
      (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g c) →
      blockCorner (2 * n) Q ∈ V →
      (∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V) →
      ∀ (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (holeOld z).center = z ∧ (holeNew z).center = z) →
      (∀ z, ((holeOld z).scale = holeRadius ε₀ n t ∨
          (holeOld z).scale = holeRadius ε₀ (2 * n) t) ∧
        ((holeNew z).scale = holeRadius ε₀ n t ∨
          (holeNew z).scale = holeRadius ε₀ (2 * n) t)) →
      (∀ z, z ≠ blockCorner (2 * n) Q → holeOld z = holeNew z) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * n) →
      ∀ (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeOld z).outer (holeOld z').outer)
        (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeNew z).outer (holeNew z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) →
      (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 9 ≤ b →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)}, ‖Ω‖ ≤ 1 →
      (∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, Nonempty (holeOld z).Tag) →
      ∃ P : Finset Party, P.card ≤ 9 ∧
        (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
        ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
          (guideFrame pos q g own ph rank V holeNew hpNew).regs,
        w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
        w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
          L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
        ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
            ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
          (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
            ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        w.IsSourceBounded (2 * b) := by
  obtain ⟨ν₀, hν₀, H⟩ := exists_resizing_footprintRatio_mixed_reading.{0} hε
  refine ⟨min ν₀ (1 / 4), lt_min hν₀ (by norm_num), fun ν hν hνν' {v} hv
    {ι _ _ q _ pos κ Party n t} hn hnt {lab Q g} hg own ph rank
    {V} hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew
    {C c b L} hL hcOld hcNew hcPatch hb hb9 {Ω} hΩ hεp hεh htag => ?_⟩
  have hνle : ν ≤ 1 / 4 := hνν'.trans (min_le_right _ _)
  have hνν : ν ≤ ν₀ := hνν'.trans (min_le_left _ _)
  have hn2 : 0 < 2 * n := by positivity
  have hRle : ∀ r, r = holeRadius ε₀ n t ∨ r = holeRadius ε₀ (2 * n) t → r ≤ 2 * ε₀ * n := by
    rintro r (rfl | rfl) <;> simp only [holeRadius]
    · nlinarith [min_le_left n t]
    · nlinarith [min_le_left (2 * n) t]
  have htwo : ∀ hole : ℝ × ℝ → SquarePatch pos q, (∀ z, (hole z).scale = holeRadius ε₀ n t ∨
      (hole z).scale = holeRadius ε₀ (2 * n) t) →
      ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
        p ∈ (closedBall x (2 * (ν * n)) ∩ closedBall (blockCorner (2 * n) Q) (2 * n)) \
          ⋃ c ∈ {c | c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)) ∧ IsTrueVertex g c},
            ball c (hole c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃ := by
    intro hole hs x p₁ p₂ p₃ hp
    refine H hv hn hnt lab Q g hg (fun c => (hole c).scale) hs x p₁ p₂ p₃ fun p hp' => ?_
    obtain ⟨⟨h1, h2⟩, h3⟩ := hp p hp'
    refine ⟨⟨closedBall_subset_closedBall ?_ h1, by rwa [mul_one]⟩, by rwa [one_add_one_eq_two,
      mul_comm (2 * n) 2]⟩
    nlinarith
  have hb' : (2 * (2 * (2 * ε₀ * n) + ν * n) / (ν * n) + 1) ^ 2 ≤ (b : ℝ) := by
    have e : 2 * (2 * (2 * ε₀ * n) + ν * n) / (ν * n) = 2 * (4 * ε₀ + ν) / ν := by
      field_simp
      ring
    rwa [e]
  exact resize_step_isSourceBounded (R := 2 * ε₀ * n) hn2 (by positivity) (by positivity)
    (by nlinarith) hg own ph rank hV hc₀ hVc holeOld holeNew patch hcenter
    (fun z => ⟨hRle _ (hscale z).1, hRle _ (hscale z).2⟩) hsame hpatch
    (htwo holeOld fun z => (hscale z).1) (htwo holeNew fun z => (hscale z).2) hpOld hpNew hL
    hcOld hcNew hcPatch hb' hb9 hΩ hεp hεh htag

/-- **The resizes of a level as gates, with one footprint ratio.** Fix `0 < ε₀ ≤ 1/16`. There is
a threshold `ν' > 0` such that, for every ratio `0 < ν ≤ ν'`, every generic displacement `v`, every
`0 < n < t`
and every reading `g` along `v` of a guide uniform on the `2n`-blocks, the resize of the hole at a
grid corner `c₀` of the `2n`-grid, between hole patches centered at their points of radii `h_n`
or `h_{2n}` that agree away from `c₀`, with patches of radius `ν n`, is a circuit as in
`resize_step` for every `b ≥ 9` with `(2 (4 ε₀ + ν) / ν + 1)² ≤ b`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 102–133, 447–479, 529–541 and 559–570. -/
theorem exists_resize_step_reading {ε₀ : ℝ} (hε : 0 < ε₀) (hε₀ : ε₀ ≤ 1 / 16) :
    ∃ ν' > 0, ∀ ν : ℝ, 0 < ν → ν ≤ ν' → ∀ {v : ℝ × ℝ}, IsGenericDisplacement v →
      ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
      {κ Party : Type} {n t : ℝ}, 0 < n → n < t → ∀ {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ}
      {g : ℝ × ℝ → κ}, IsDisplacedReading g (blockGuide (2 * n) lab) v → ∀ (own : κ → Party)
      (ph : κ) (rank : κ → ℕ) {V : Finset (ℝ × ℝ)}, (∀ c ∈ V, IsTrueVertex g c) →
      blockCorner (2 * n) Q ∈ V →
      (∀ c ∈ closedBall (blockCorner (2 * n) Q) (2 * (2 * n)), IsTrueVertex g c → c ∈ V) →
      ∀ (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (holeOld z).center = z ∧ (holeNew z).center = z) →
      (∀ z, ((holeOld z).scale = holeRadius ε₀ n t ∨
          (holeOld z).scale = holeRadius ε₀ (2 * n) t) ∧
        ((holeNew z).scale = holeRadius ε₀ n t ∨
          (holeNew z).scale = holeRadius ε₀ (2 * n) t)) →
      (∀ z, z ≠ blockCorner (2 * n) Q → holeOld z = holeNew z) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * n) →
      ∀ (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeOld z).outer (holeOld z').outer)
        (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' =>
          Disjoint (holeNew z).outer (holeNew z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) →
      (2 * (4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 9 ≤ b →
      ∀ {Ω : EuclideanSpace ℂ (ι → Fin q)}, ‖Ω‖ ≤ 1 →
      (∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹) →
      (∀ z, Nonempty (holeOld z).Tag) →
      ∃ P : Finset Party, P.card ≤ 9 ∧
        (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
        ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
          (guideFrame pos q g own ph rank V holeNew hpNew).regs,
        w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
        w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) *
          (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
            L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
        w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
          L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
        ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
            ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
          (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
            ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨ν', hν', H⟩ := exists_resize_step_reading_isSourceBounded hε hε₀
  refine ⟨ν', hν', fun ν hν hνν' {v} hv {ι _ _ q _ pos κ Party n t} hn hnt {lab Q g} hg own ph rank
    {V} hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew
    {C c b L} hL hcOld hcNew hcPatch hb hb9 {Ω} hΩ hεp hεh htag => ?_⟩
  obtain ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇, -⟩ := H ν hν hνν' hv hn hnt hg own ph rank hV hc₀ hVc
    holeOld holeNew patch hcenter hscale hsame hpatch hpOld hpNew hL hcOld hcNew hcPatch hb hb9 hΩ
    hεp hεh htag
  exact ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇⟩

end TNLean.PEPS.Approximation
