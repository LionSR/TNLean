/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingRewrite
import TNLean.PEPS.Approximation.GuideFrameRewriteCircuit

/-!
# The direct repainting of a square as one gate

Combining the plane conditions of the direct repainting
(`exists_directRepainting_planeConditions`) with the small-patch rewrite between frames of guides
as one gate (`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`): the direct repainting of
a block, from the frame of the old reading with holes at `V` to the frame of the new reading with
holes at `V'`, is an original circuit with at most one nonprivate gate whose participants are
parties of labels of the nine blocks around the repainted block, with reference-vector error at
most `(2b + 1) L^{-20}` (`directRepainting_step`).

## Main results

* `Approximation.guideFrame_congr`: the frame of a guide depends on its set of centers only.
* `Approximation.directRepainting_step`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`, lines 507–527 and
  574–583; Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218.
-/

open Set Metric

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

/-- The frame of a guide depends only on its set of centers and its patches. -/
theorem guideFrame_congr {g : ℝ × ℝ → κ} {own : κ → Party} {ph : κ} {rank : κ → ℕ}
    {V V' : Finset (ℝ × ℝ)} {patch patch' : ℝ × ℝ → SquarePatch pos q} (h : V = V')
    (hp : patch = patch')
    (hV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch z).outer (patch z').outer)
    (hV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (patch' z).outer (patch' z').outer) :
    guideFrame pos q g own ph rank V patch hV = guideFrame pos q g own ph rank V' patch' hV' := by
  subst h hp
  rfl

/-- **The direct repainting of a block as one gate.** In the setting of
`exists_directRepainting_planeConditions`, suppose moreover that every hole and every patch has
at most `C L^c` cylinder terms and error at most `L^{-60}` on `Ω`, with `‖Ω‖ ≤ 1`, that every hole
has a tag, and that `b` is at least `18` and the number `(2 (n / 2 + 2 r + u) / u + 1)²` of net
patches. There is a set of at most `18` parties, those of the labels of the nine blocks around `S`,
and an original circuit from the registers of the frame of `g` with holes at
`V` to those of the frame of `g'` with holes at `V'`, with at most one nonprivate gate, all
participants in that set, expansion bounds as in
`GuideFrameRewrite.PlaneConditions.exists_originalCircuit`, and reference-vector error at most
`(2b + 1) L^{-20}`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218. -/
theorem directRepainting_step [NeZero q] {n r u : ℝ} (hn : 0 < n) (hr : 0 < r) (hu : 0 < u)
    (hsep : 3 * u + 4 * r < n) {lab lab' : ℤ × ℤ → κ} {S : ℤ × ℤ}
    (hlab : ∀ Q, Q ≠ S → lab' Q = lab Q) {v : ℝ × ℝ} {g g' : ℝ × ℝ → κ}
    (hg : IsDisplacedReading g (blockGuide n lab) v)
    (hg' : IsDisplacedReading g' (blockGuide n lab') v) (own : κ → Party) (ph : κ)
    (rank : κ → ℕ) {V V' : Finset (ℝ × ℝ)} (hV : ∀ c ∈ V, IsTrueVertex g c)
    (hV' : ∀ c ∈ V', IsTrueVertex g' c)
    (hVc : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g c → c ∈ V)
    (hVc' : ∀ c ∈ closedBall (blockCorner n S) (3 * n), IsTrueVertex g' c → c ∈ V')
    (hVV' : ∀ c ∉ squareCorners n S, (c ∈ V ↔ c ∈ V'))
    (hole patch : ℝ × ℝ → SquarePatch pos q)
    (hhole : ∀ z, (hole z).center = z ∧ (hole z).scale = r)
    (hpatch : ∀ z, (patch z).center = z ∧ (patch z).scale = u)
    (htwo : HasTwoOwnerFootprints g (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g c} r (2 * u))
    (htwo' : HasTwoOwnerFootprints g' (closedBall (blockCorner n S) (2 * n))
      {c | c ∈ closedBall (blockCorner n S) (3 * n) ∧ IsTrueVertex g' c} r (2 * u))
    (hpV : (V : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    (hpV' : (V' : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer)
    {C c b L : ℕ} (hL : 1 ≤ L) (hcardHole : ∀ z, Fintype.card (hole z).Tag ≤ C * L ^ c)
    (hcardPatch : ∀ z, Fintype.card (patch z).Tag ≤ C * L ^ c)
    (hb : (2 * (n / 2 + 2 * r + u) / u + 1) ^ 2 ≤ b) (hb18 : 18 ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z, ‖act (patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεhole : ∀ z, ‖act (hole z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (htag : ∀ z, Nonempty (hole z).Tag) :
    ∃ P : Finset Party, P.card ≤ 18 ∧
      (∀ x ∈ P, ∃ Q ∈ nineBlocks S, x = own (lab Q) ∨ x = own (lab' Q)) ∧
      ∃ w : OriginalCircuit (guideFrame pos q g own ph rank V hole hpV).regs
        (guideFrame pos q g' own ph rank V' hole hpV').regs,
      w.nonprivateCount ≤ 1 ∧ (∀ γ, (↑(w.participants γ) : Set Party) ⊆ ↑P) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval ((guideFrame pos q g own ph rank V hole hpV).regIso.symm
          ((guideFrame pos q g own ph rank V hole hpV).refVec Ω)) -
        (guideFrame pos q g' own ph rank V' hole hpV').regIso.symm
          ((guideFrame pos q g' own ph rank V' hole hpV').refVec Ω)‖ ≤
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ := by
  obtain ⟨G, hG, ho, hn', how, hph, hrk, hho, hhn, hpt, hUA, hUA', hA, hA', hN, hP, hP₀,
    hdesc⟩ := exists_directRepainting_planeConditions (Party := Party) hn hr hu hsep hlab hg hg'
      own ph rank hV hV' hVc hVc' hVV' hole patch hhole hpatch htwo htwo'
  subst ho hn' how hph hrk hho hpt
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅⟩ := hG.exists_originalCircuit (C := C) (c := c) (b := b) hL
    (fun a _ => hhn ▸ hcardHole a) (fun z _ => hcardPatch z) (fun a _ => hcardHole a)
    (by exact_mod_cast hN.trans hb) (hA.trans (by omega)) (hA'.trans (by omega))
    (hP.trans hb18) hΩ (fun z _ => hεpatch z) (fun a _ => hεhole a) hP₀ (fun z _ => htag z)
  have e₁ : G.oldFrame = guideFrame pos q G.old G.own G.ph G.rank V G.holeOld hpV :=
    guideFrame_congr hUA rfl _ _
  have e₂ : G.newFrame = guideFrame pos q G.new G.own G.ph G.rank V' G.holeOld hpV' :=
    guideFrame_congr hUA' hhn _ _
  rw [← e₁, ← e₂]
  exact ⟨G.parties, hP, hdesc, w, h₁, h₂, h₃, h₄, h₅⟩

end TNLean.PEPS.Approximation
