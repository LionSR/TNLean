/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingSourceBound
import TNLean.PEPS.Approximation.DyadicPointTreatmentReadingStep
import TNLean.PEPS.Approximation.DyadicResizeReadingStep

/-!
# Pair sources of the resizes and point treatments

The resize of a hole (`resize_step`, and `exists_resize_step_reading` with one footprint ratio)
and the point treatment of a mark (`pointTreatment_step`, and
`exists_pointTreatment_step_reading`) are small-patch rewrites between frames of guides, read as
one gate by `GuideFrameRewrite.PlaneConditions.exists_originalCircuit`. Using
`GuideFrameRewrite.PlaneConditions.exists_originalCircuit_isSourceBounded` instead, each of these
gates also satisfies the pair-source bound `OriginalCircuit.IsSourceBounded (2b)`: every monomial
of the gate has at most `2b` pair sources, the constant of its pair-effect bound.

## Main results

* `Approximation.resize_step_isSourceBounded`.
* `Approximation.exists_resize_step_reading_isSourceBounded`.
* `Approximation.pointTreatment_step_isSourceBounded`.
* `Approximation.exists_pointTreatment_step_reading_isSourceBounded`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147; §7, `06-geometry.tex`, lines 481–505, 529–541 and 574–583; Lemma 6.3
  `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- **The resize of a hole as one gate, with its pair sources.** The conclusion of `resize_step`,
together with the bound of `2b` pair sources in every monomial of the gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218; Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147. -/
theorem resize_step_isSourceBounded [NeZero q] {N R u : ℝ} (hN : 0 < N) (hR : 0 < R)
    (hu : 0 < u) (hsep : 4 * R + 3 * u < N) {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ} {v : ℝ × ℝ}
    {g : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide N lab) v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hc₀ : blockCorner N Q ∈ V)
    (hVc : ∀ c ∈ closedBall (blockCorner N Q) (2 * N), IsTrueVertex g c → c ∈ V)
    (holeOld holeNew patch : ℝ × ℝ → SquarePatch pos q)
    (hcenter : ∀ z, (holeOld z).center = z ∧ (holeNew z).center = z)
    (hscale : ∀ z, (holeOld z).scale ≤ R ∧ (holeNew z).scale ≤ R)
    (hsame : ∀ z, z ≠ blockCorner N Q → holeOld z = holeNew z)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (htwoOld : ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (2 * u) ∩ closedBall (blockCorner N Q) N) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner N Q) (2 * N) ∧ IsTrueVertex g c},
          ball c (holeOld c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃)
    (htwoNew : ∀ x p₁ p₂ p₃ : ℝ × ℝ, (∀ p ∈ ({p₁, p₂, p₃} : Set (ℝ × ℝ)),
      p ∈ (closedBall x (2 * u) ∩ closedBall (blockCorner N Q) N) \
        ⋃ c ∈ {c | c ∈ closedBall (blockCorner N Q) (2 * N) ∧ IsTrueVertex g c},
          ball c (holeNew c).scale) → g p₁ = g p₂ ∨ g p₁ = g p₃ ∨ g p₂ = g p₃)
    (hpOld : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeOld z).outer (holeOld z').outer)
    (hpNew : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (holeNew z).outer (holeNew z').outer)
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardOld : ∀ z, Fintype.card (holeOld z).Tag ≤ C * L ^ c)
    (hcardNew : ∀ z, Fintype.card (holeNew z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (2 * R + u) / u + 1) ^ 2 ≤ b) (hb9 : 9 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (holeOld z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (holeOld z).Tag) :
    ∃ P : Finset Party, P.card ≤ 9 ∧
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + (Q.1 - 1, Q.2 - 1)))) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V holeOld hpOld).regs
        (guideFrame pos q g own ph rank V holeNew hpNew).regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V holeOld hpOld).regIso.symm
          ((guideFrame pos q g own ph rank V holeOld hpOld).refVec Ω)) -
        (guideFrame pos q g own ph rank V holeNew hpNew).regIso.symm
          ((guideFrame pos q g own ph rank V holeNew hpNew).refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  obtain ⟨G, hG, ho, hn', how, hph, hrk, hho, hhn, hpt, hUA, hUA', hA, hA', hN', hP, hP₀,
    hdesc⟩ := exists_resize_planeConditions (Party := Party) hN hR hu hsep hg own ph rank hV hc₀
      hVc holeOld holeNew patch hcenter hscale hsame hpatch htwoOld htwoNew
  subst ho how hph hrk hho hhn hpt
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hG.exists_originalCircuit_isSourceBounded (C := C)
    (c := c) (b := b) hL
    (fun a _ => hcardNew a) (fun z _ => hcardPatch z) (fun a _ => hcardOld a)
    (by exact_mod_cast hN'.trans hb) (hA.trans (by omega)) (hA'.trans (by omega))
    (hP.trans hb9) hΩ (fun z _ => hεpatch z) (fun a _ => hεhole a) hP₀ (fun z _ => htag z)
  have e₂ : G.newFrame = guideFrame pos q G.old G.own G.ph G.rank V G.holeNew hpNew := by
    rw [G.newFrame_eq hUA' hpNew, hn']
  rw [← G.oldFrame_eq hUA hpOld, ← e₂]
  exact ⟨G.parties, hP, hdesc, w, h₁, h₂, h₃, h₄, h₅, h₆⟩

/-- **The point treatment of a mark as one gate, with its pair sources.** The conclusion of
`pointTreatment_step`, together with the bound of `2b` pair sources in every monomial of the gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 481–505 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218; Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147. -/
theorem pointTreatment_step_isSourceBounded [NeZero q] {n t r u : ℝ} (hn : 0 < n) (ht : 0 < t)
    (hr : 0 < r) (hu : 0 < u) (hsep : 2 * t + 6 * r + 3 * u < n) {lab : ℤ × ℤ → κ} {S : ℤ × ℤ}
    {B : κ}
    {g : ℝ × ℝ → κ} (hg : (blockBaseline hn lab S B).IsUnmodifiedGuide g)
    {M₁ M₂ : Finset (ℤ × ℤ)} (Q₀ : ℤ × ℤ) (hQ₀ : blockCorner n Q₀ ∈ closedBlock n S)
    (hM : ∀ Q, Q ≠ Q₀ → (Q ∈ M₁ ↔ Q ∈ M₂)) (L₀ : κ)
    (hL₀ : L₀ = B ∨ ∃ R ∈ blockWindow 1, L₀ = lab (R + S)) {v : ℝ × ℝ} {g₁ g₂ : ℝ × ℝ → κ}
    (hg₁ : IsDisplacedReading g₁ (homogenize (⋃ Q ∈ M₁, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v)
    (hg₂ : IsDisplacedReading g₂ (homogenize (⋃ Q ∈ M₂, ball (blockCorner n Q) t) L₀
      (shiftGuide (blockCorner n S) g)) v) (own : κ → Party) (ph : κ) (rank : κ → ℕ)
    {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g₁ c) (hV' : ∀ c ∈ V', IsTrueVertex g₂ c)
    (hVV' : ∀ c, n - t ≤ dist c (blockCorner n Q₀) → (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {W H H' : Set (ℝ × ℝ)} (hW : closedBall (blockCorner n Q₀) (t + 2 * r + 3 * u) ⊆ W)
    (hH : ∀ c ∈ H, c ∈ V) (hH' : ∀ c ∈ H', c ∈ V')
    (htwo : HasTwoOwnerFootprints g₁ W H r (2 * u))
    (htwo' : HasTwoOwnerFootprints g₂ W H' r (2 * u))
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (t + 2 * r + u) / u + 1) ^ 2 ≤ b) (hb53 : 53 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ w : OriginalCircuit (guideFrame pos q g₁ own ph rank V hole hpV).regs
        (guideFrame pos q g₂ own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧
      (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑(blockParties own lab S B)) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g₁ own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g₁ own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g₂ own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g₂ own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  have htn : 2 * t < n := by linarith
  have hP : ∀ p, dist p (blockCorner n Q₀) ≤ t + 2 * r + 3 * u →
      own (g₁ p) ∈ blockParties own lab S B ∧ own (g₂ p) ∈ blockParties own lab S B :=
    fun p hp => ⟨own_mem_blockParties (reading_mem_blockLabels hn hg _ hL₀ hg₁ hQ₀
      (by linarith)), own_mem_blockParties (reading_mem_blockLabels hn hg _ hL₀ hg₂ hQ₀
      (by linarith))⟩
  obtain ⟨G, hG, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈, h₉, h₁₀, h₁₁, h₁₂, h₁₃, h₁₄⟩ :=
    exists_pointTreatment_planeConditions hn ht hr hu hsep hg Q₀ hM L₀ hg₁ hg₂ own ph rank hV hV'
      hVV' hole patch hhole hpatch hpV hpV' hW hH hH' htwo htwo' _ hP
      (fun a ha hd => own_mem_blockParties (tagHolder_mem_blockLabels hn hg _ hL₀ hg₁ rank ph
        (hV a ha) hQ₀ (by linarith)))
      (fun a ha hd => own_mem_blockParties (tagHolder_mem_blockLabels hn hg _ hL₀ hg₂ rank ph
        (hV' a ha) hQ₀ (by linarith)))
  have hsub : G.oldAffected ⊆ insert (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t) :=
    fun a ha => mem_insert_rimFinset_of_isTrueVertex hn ht.le htn hg M₁ L₀ hg₁ Q₀
      (hV a (h₁₀ ▸ Finset.mem_union_right _ ha)) (h₁₂ a ha)
  have hsub' : G.newAffected ⊆ insert (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t) :=
    fun a ha => mem_insert_rimFinset_of_isTrueVertex hn ht.le htn hg M₂ L₀ hg₂ Q₀
      (hV' a (h₁₁ ▸ Finset.mem_union_right _ ha)) (h₁₃ a ha)
  have hcard := (Finset.card_insert_le (blockCorner n Q₀) (rimFinset (blockCorner n Q₀) t)).trans
    (Nat.succ_le_succ (card_rimFinset_le (blockCorner n Q₀) t))
  have hold : G.oldAffected.card ≤ b := (Finset.card_le_card hsub).trans (hcard.trans hb53)
  have hnew : G.newAffected.card ≤ b := (Finset.card_le_card hsub').trans (hcard.trans hb53)
  subst h₁ h₂ h₃ h₄ h₅ h₆ h₈
  have hparties : G.parties.card ≤ b :=
    h₉ ▸ (card_blockParties_le _ _ _ _).trans (by omega)
  obtain ⟨w, w₁, w₂, w₃, w₄, w₅, w₆⟩ := hG.exists_originalCircuit_isSourceBounded (C := C)
    (c := c) (b := b) hL
    (fun a _ => h₇ ▸ hcardHole a) (fun z _ => hcardPatch z) (fun a _ => hcardHole a)
    (by exact_mod_cast h₁₄.trans hb) hold hnew hparties hΩ (fun z _ => hεpatch z)
    (fun a _ => hεhole a) (by rw [h₉]; exact ⟨_, mem_blockParties.2 (Or.inl rfl)⟩)
    (fun z _ => htag z)
  have e₂ : G.newFrame = guideFrame pos q G.new G.own G.ph G.rank V' G.holeOld hpV' :=
    guideFrame_congr h₁₁ h₇ _ _
  rw [← G.oldFrame_eq h₁₀ hpV, ← e₂]
  exact ⟨w, w₁, h₉ ▸ w₂, w₃, w₄, w₅, w₆⟩

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

/-- **The point treatments as gates, with one footprint ratio and their pair sources.** The
conclusion of `exists_pointTreatment_step_reading`, together with the bound of `2b` pair sources
in every monomial of each gate.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339, 447–505 and 559–570; Theorem 5.2,
item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_pointTreatment_step_reading_isSourceBounded {ε₀ : ℝ} (hε : 0 < ε₀)
    (hε₀ : ε₀ ≤ 1 / 16) :
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
      ∀ (hole patch : ℝ × ℝ → SquarePatch pos q),
      (∀ z, (hole z).center = z ∧ (hole z).scale = ε₀ * t) →
      (∀ z, (patch z).center = z ∧ (patch z).scale = ν * t / 2) →
      ∀ (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
        (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
        {C c b L : ℕ}, 1 ≤ L → (∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c) →
      (∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c) →
      (2 * (2 + 4 * ε₀ + ν) / ν + 1) ^ 2 ≤ (b : ℝ) → 53 ≤ b →
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
          (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
        w.IsSourceBounded (2 * b) := by
  obtain ⟨ν₀, hν₀, H⟩ := exists_pointTreatment_footprintRatio_homogenize_reading hε
  refine ⟨min ν₀ (1 / 4), lt_min hν₀ (by norm_num), fun ν hν hνν' {v} hv
    {ι _ _ q _ pos κ Party n t} hn ht htn {lab S B g} hg
    {M₁ M₂} Q₀ hQ₀ hM L₀ hL₀ {g₁ g₂} hg₁ hg₂ own ph rank {V V'} hV hV' hVc hVc' hVV'
    hole patch hhole hpatch hpV hpV' {C c b L} hL hcHole hcPatch hb hb53 {Ω} hΩ hεp hεh htag => ?_⟩
  have hνle : ν ≤ 1 / 4 := hνν'.trans (min_le_right _ _)
  have hνν : ν ≤ ν₀ := hνν'.trans (min_le_left _ _)
  have hQS : blockCorner n Q₀ ∈ closedBlock n S := by
    obtain ⟨h1, h2⟩ := hQ₀
    refine mem_closedSquare.2 ?_
    simp only [blockCorner, Prod.fst_sub, Prod.snd_sub]
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rw [h1, h2] <;> push_cast <;>
      refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith
  have hW : closedBall (blockCorner n Q₀) (t + 2 * (ε₀ * t) + 3 * (ν * t / 2)) ⊆
      closedBall (blockCorner n Q₀) (2 * t) :=
    closedBall_subset_closedBall (by nlinarith)
  have hδ : 2 * (ν * t / 2) ≤ ν * t := le_of_eq (by ring)
  have hb' : (2 * (t + 2 * (ε₀ * t) + ν * t / 2) / (ν * t / 2) + 1) ^ 2 ≤ (b : ℝ) := by
    have e : 2 * (t + 2 * (ε₀ * t) + ν * t / 2) / (ν * t / 2) = 2 * (2 + 4 * ε₀ + ν) / ν := by
      field_simp
      ring
    rwa [e]
  exact pointTreatment_step_isSourceBounded hn ht (by positivity) (by positivity) (by nlinarith)
    hg Q₀ hQS hM L₀
    hL₀ hg₁ hg₂ own ph rank hV hV' hVV' hole patch hhole hpatch hpV hpV' hW
    (H := {c | c ∈ closedBall (blockCorner n Q₀) (3 * t) ∧ IsTrueVertex g₁ c})
    (H' := {c | c ∈ closedBall (blockCorner n Q₀) (3 * t) ∧ IsTrueVertex g₂ c})
    (fun c hc => hVc c hc.1 hc.2) (fun c hc => hVc' c hc.1 hc.2)
    ((H ν hν hνν hv hn ht htn hg M₁ hQ₀ L₀ hL₀ g₁ hg₁).mono hδ)
    ((H ν hν hνν hv hn ht htn hg M₂ hQ₀ L₀ hL₀ g₂ hg₂).mono hδ) hL hcHole hcPatch hb'
    hb53 hΩ hεp hεh htag

end TNLean.PEPS.Approximation
