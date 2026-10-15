/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicResizeRewrite
import TNLean.PEPS.Approximation.GuideFrameRewriteCircuit

/-!
# The resize of a hole as one gate

Combining the plane conditions of the resize of one hole (`exists_resize_planeConditions`) with
the small-patch rewrite between frames of guides as one gate
(`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`): the resize of the hole at a grid
corner `c₀`, from the frame of the reading `g` with hole patches `holeOld` at `V` to the frame of
the same reading with hole patches `holeNew`, is an original circuit with at most one nonprivate
gate whose participants are parties of the labels of the nine blocks around the block below and
to the left of `c₀`, with reference-vector error at most `(2b + 1) L^{-20}` (`resize_step`).

## Main results

* `Approximation.resize_step_isSourceBounded`, `Approximation.resize_step`: with and without
  the bound of `2b` pair sources in every monomial.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`, lines 529–541 and
  574–583; Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric

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

/-- **The resize of a hole as one gate.** In the setting of `exists_resize_planeConditions`,
suppose moreover that every hole patch of the two frames and every patch has at most `C L^c`
cylinder terms, that every patch and every old hole patch has error at most `L^{-60}` on `Ω`, with
`‖Ω‖ ≤ 1`, that every old hole patch has a tag, and that `b` is at least `9` and the number
`(2 (2 R + u) / u + 1)²` of net patches. There is a set of at most `9` parties, those of the
labels of the nine blocks around the block `Q - (1, 1)`, and an original circuit from the
registers of the frame of `g` with hole patches `holeOld` at `V` to those of the frame of `g` with
hole patches `holeNew` at `V`, with at most one nonprivate gate, all participants in that set,
expansion bounds as in `GuideFrameRewrite.PlaneConditions.exists_originalCircuit`, and
reference-vector error at most `(2b + 1) L^{-20}`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 529–541 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem resize_step [NeZero q] {N R u : ℝ} (hN : 0 < N) (hR : 0 < R) (hu : 0 < u)
    (hsep : 4 * R + 3 * u < N) {lab : ℤ × ℤ → κ} {Q : ℤ × ℤ} {v : ℝ × ℝ} {g : ℝ × ℝ → κ}
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
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇, -⟩ := resize_step_isSourceBounded hN hR hu hsep hg own
    ph rank hV hc₀ hVc holeOld holeNew patch hcenter hscale hsame hpatch htwoOld htwoNew hpOld hpNew
    hL hcardOld hcardNew hcardPatch hb hb9 hΩ hεpatch hεhole htag
  exact ⟨P, h₁, h₂, w, h₃, h₄, h₅, h₆, h₇⟩

end TNLean.PEPS.Approximation
