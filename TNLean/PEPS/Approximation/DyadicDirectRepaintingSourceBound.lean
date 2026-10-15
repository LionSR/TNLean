/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicDirectRepaintingStep
import TNLean.PEPS.Approximation.PartyGateSourceBound

/-!
# Pair sources of the small-patch rewrites and of the direct repainting

Every monomial of the expansion of Lemma 6.3 has at most `2m` normalized pair sources, one per
patch vertex with open output legs (`SmallPatchRewrite.exists_allowed_monomial_approx_refVec`).
Reading the expansion as one gate keeps this bound
(`PartyGate.exists_originalCircuit_isSourceBounded`). This file adds the pair-source bound
`OriginalCircuit.IsSourceBounded (2b)` to the gate of the small-patch rewrite
(`SmallPatchRewrite.exists_originalCircuit_refVec_isSourceBounded`), to the rewrite between
frames of guides (`GuideFrameRewrite.PlaneConditions.exists_originalCircuit_isSourceBounded`) and
to the direct repainting of a block (`directRepainting_step_isSourceBounded`). The constant `2b`
is the constant of the pair-effect bound of the same gates, so one constant bounds the pair
sources and the pair effects of every monomial, as in Theorem 5.2, item 3.

## Main results

* `EncodedFrame.SmallPatchRewrite.exists_originalCircuit_refVec_isSourceBounded`.
* `Approximation.GuideFrameRewrite.PlaneConditions.exists_originalCircuit_isSourceBounded`.
* `Approximation.directRepainting_step_isSourceBounded`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2, item 3, `04-compression.tex`,
  lines 143–147; Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218; §7,
  `06-geometry.tex`, lines 507–527 and 574–583.
-/

open Set Metric
open scoped Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS

open PairEffect

namespace EncodedFrame.SmallPatchRewrite

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  (R : SmallPatchRewrite pos q Party) [NeZero q]

/-- **Lemma 6.3, the small-patch rewrite as one gate, with its pair sources.** The conclusion of
`exists_originalCircuit_refVec`, together with the bound of `2b` pair sources in every monomial
of the gate.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_originalCircuit_refVec_isSourceBounded (hR : R.Conditions) {C c b L : ℕ}
    (hL : 1 ≤ L) (hnew : ∀ h ∈ R.newAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hpatch : ∀ P ∈ R.patches, Fintype.card P.Tag ≤ C * L ^ c)
    (hold : ∀ h ∈ R.oldAffected, Fintype.card h.patch.Tag ≤ C * L ^ c)
    (hm : R.patches.length ≤ b) (hrold : R.oldAffected.length ≤ b)
    (hrnew : R.newAffected.length ≤ b) (hparties : R.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ P ∈ R.patches, ‖act P.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ h ∈ R.oldAffected, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hS₀ : R.parties.Nonempty) (hne : Nontrivial (Mem R.oldFrame.regs)) :
    ∃ (w : OriginalCircuit R.oldFrame.regs R.newFrame.regs)
      (Ma : Matrix R.newFrame.Layout R.oldFrame.Layout ℂ), ‖Ma‖ ≤ 1 ∧
      ‖Ma - R.rewrite‖ ≤ ((L : ℝ) ^ 30)⁻¹ ∧
      ‖act Ma (R.oldFrame.refVec Ω) - R.newFrame.refVec Ω‖ ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      (∀ z, R.newFrame.regIso (w.eval z) = act Ma (R.oldFrame.regIso z)) ∧
      w.nonprivateCount ≤ 1 ∧ (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑R.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      w.IsSourceBounded (2 * b) := by
  classical
  obtain ⟨-, G, hG, hGp, Ma, hMa1, hMa, href, hz⟩ :=
    R.exists_allowed_monomial_approx_refVec hR hL hnew hpatch hold hm hrold hrnew hparties hΩ
      hεpatch hεold
  have hsum : ∀ (z : Mem R.oldFrame.regs) (K : PartyGate R.oldFrame.regs R.newFrame.regs),
      R.newFrame.regIso (gate (toGate K) z) =
        (K.map fun p => p.1 • R.newFrame.regIso (p.2.toEffectChain.eval z)).sum := by
    intro z K
    induction K with
    | nil => exact map_zero _
    | cons p K ih =>
        change R.newFrame.regIso ((p.1 • p.2.toEffectChain.eval + gate (toGate K)) z) = _
        rw [_root_.add_apply, map_add, ih, _root_.smul_apply,
          LinearIsometryEquiv.map_smul, List.map_cons, List.sum_cons]
  have hgate : ∀ z, R.newFrame.regIso (gate (toGate G) z) = act Ma (R.oldFrame.regIso z) :=
    fun z => (hsum z G).trans (hz z)
  have hN : ‖gate (toGate G)‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
    rw [← LinearIsometryEquiv.norm_map R.newFrame.regIso, hgate, one_mul,
      ← LinearIsometryEquiv.norm_map R.oldFrame.regIso z]
    exact norm_act_le_of_norm_le_one hMa1 _
  obtain ⟨w, hw, hcount, hpart, hexp, hmono, hsrc⟩ :=
    PartyGate.exists_originalCircuit_isSourceBounded R.parties hS₀ (R.restrict_regs_eq hR) G
      (fun m hm => (hGp m hm).2.1)
      (fun m hm => R.fixesOutside_of_mem hR m.2 (hGp m hm).2.2.1 (hGp m hm).2.2.2.1) hN hne
  refine ⟨w, Ma, hMa1, hMa, href, fun z => by rw [hw, hgate], hcount, hpart,
    hexp _ _ (fun m hm => (hGp m hm).2.2.2.2.2) ?_, w.isMonomialBounded_mono hmono hG,
    hsrc _ fun m hm => (hGp m hm).2.2.2.2.1⟩
  refine (List.sum_le_length_nsmul _ 1 fun x hx => ?_).trans ?_
  · obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    exact (hGp m hm).1
  · rw [List.length_map, nsmul_eq_mul, mul_one]
    exact_mod_cast hG

end EncodedFrame.SmallPatchRewrite

namespace Approximation

open EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {κ Party : Type}

namespace GuideFrameRewrite

variable {G : GuideFrameRewrite pos q κ Party} [NeZero q]

/-- **A small-patch rewrite between frames of guides as one gate, with its pair sources.** The
conclusion of `PlaneConditions.exists_originalCircuit`, together with the bound of `2b` pair
sources in every monomial of the gate.

Polynomial-PEPS manuscript, Lemma 6.3 `lem:small-rewrite`, `05-frames.tex`, lines 188–218;
Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem PlaneConditions.exists_originalCircuit_isSourceBounded (h : G.PlaneConditions)
    {C c b L : ℕ} (hL : 1 ≤ L)
    (hnew : ∀ a ∈ G.newAffected, Fintype.card (G.holeNew a).Tag ≤ C * L ^ c)
    (hpatch : ∀ z ∈ G.centers, Fintype.card (G.patch z).Tag ≤ C * L ^ c)
    (hold : ∀ a ∈ G.oldAffected, Fintype.card (G.holeOld a).Tag ≤ C * L ^ c)
    (hm : G.centers.card ≤ b) (hrold : G.oldAffected.card ≤ b) (hrnew : G.newAffected.card ≤ b)
    (hparties : G.parties.card ≤ b)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ ≤ 1)
    (hεpatch : ∀ z ∈ G.centers, ‖act (G.patch z).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hεold : ∀ a ∈ G.oldAffected, ‖act (G.holeOld a).proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hS₀ : G.parties.Nonempty)
    (htag : ∀ z ∈ G.untouched ∪ G.oldAffected, Nonempty (G.holeOld z).Tag) :
    ∃ w : OriginalCircuit G.oldFrame.regs G.newFrame.regs, w.nonprivateCount ≤ 1 ∧
      (∀ g, (↑(w.participants g) : Set Party) ⊆ ↑G.parties) ∧
      w.IsExpansionBounded (2 * b) ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^
        (2 * b) * L ^ (3 * b * c + 4 * b * (3 * b * c + 30)) : ℕ) ∧
      w.IsMonomialBounded ((C + 1) ^ (3 * b) * (16 * b ^ 2 * (C + 1) ^ (6 * b) + 1) ^ (2 * b) *
        L ^ (3 * b * c + 4 * b * (3 * b * c + 30))) ∧
      ‖w.eval (G.oldFrame.regIso.symm (G.oldFrame.refVec Ω)) -
          G.newFrame.regIso.symm (G.newFrame.refVec Ω)‖ ≤ (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  set R := G.toSmallPatchRewrite h.untouched_agree
  have hR := h.conditions
  have hne : Nontrivial (Mem R.oldFrame.regs) := R.oldFrame.nontrivial_mem_regs fun h' hh' => by
    rcases List.mem_append.1 hh' with hh' | hh' <;> obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hh'
    · exact htag z (Finset.mem_union_left _ (Finset.mem_toList.1 hz))
    · exact htag z (Finset.mem_union_right _ (Finset.mem_toList.1 hz))
  obtain ⟨c₀, Ma, -, -, href, hc₀, hcount, hpart, hexp, hmono, hsrc⟩ :=
    R.exists_originalCircuit_refVec_isSourceBounded hR hL
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hnew a (Finset.mem_toList.1 ha))
      (fun P hP => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
                      exact hpatch z (Finset.mem_toList.1 hz))
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hold a (Finset.mem_toList.1 ha))
      (by simpa [R, toSmallPatchRewrite] using hm) (by simpa [R, toSmallPatchRewrite] using hrold)
      (by simpa [R, toSmallPatchRewrite] using hrnew) hparties hΩ
      (fun P hP => by obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hP
                      exact hεpatch z (Finset.mem_toList.1 hz))
      (fun h' hh' => by obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hh'
                        exact hεold a (Finset.mem_toList.1 ha)) hS₀ hne
  obtain ⟨w₁, hw₁, -, hr₁⟩ := Frame.exists_permWord G.oldFrame R.oldFrame rfl
    G.perm_oldFrame_holes
  have hp₃ : R.newFrame.holes.Perm G.newFrame.holes := by
    change (G.untouched.toList.map (G.holeAt G.old G.holeOld) ++ _).Perm _
    rw [G.map_holeAt_untouched h.untouched_agree]
    exact G.perm_newFrame_holes.symm
  obtain ⟨w₃, hw₃, hn₃, hr₃⟩ := Frame.exists_permWord R.newFrame G.newFrame rfl hp₃
  have h₁ := Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₁
  have h₃ := Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₃
  refine ⟨(w₁.toOriginalCircuit hw₁.isAllowed).comp (c₀.comp (w₃.toOriginalCircuit
    hw₃.isAllowed)), ?_, ?_, ?_, ?_, ?_,
    ⟨OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h₁ _, hsrc,
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h₃ _⟩⟩
  · simp only [OriginalCircuit.nonprivateCount, h₁, h₃, zero_add, add_zero]
    exact hcount
  · rintro (g | g | g)
    · exact Word.participants_toOriginalCircuit_subset _ _ (hw₁.usesOnly _) g
    · exact hpart g
    · exact Word.participants_toOriginalCircuit_subset _ _ (hw₃.usesOnly _) g
  · exact ⟨Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw₁.sourceCount_eq _ _, hexp,
      Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _ hw₃.sourceCount_eq _ _⟩
  · exact ⟨Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
      hw₁.sourceCount_eq _, hmono,
      Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _ hw₃.sourceCount_eq _⟩
  · simp only [OriginalCircuit.eval, ContinuousLinearMap.comp_apply,
      Word.eval_toOriginalCircuit, hr₁]
    rw [← hr₃, ← map_sub, hn₃, ← R.newFrame.regIso.norm_map, map_sub,
      LinearIsometryEquiv.apply_symm_apply, hc₀, LinearIsometryEquiv.apply_symm_apply]
    exact href

end GuideFrameRewrite

/-- **The direct repainting of a block as one gate, with its pair sources.** The conclusion of
`directRepainting_step`, together with the bound of `2b` pair sources in every monomial of the
gate; `2b` is also the bound on its pair effects.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 507–527 and 574–583; Lemma 6.3
`lem:small-rewrite`, `05-frames.tex`, lines 188–218; Theorem 5.2, item 3, `04-compression.tex`,
lines 143–147. -/
theorem directRepainting_step_isSourceBounded [NeZero q] {n r u : ℝ} (hn : 0 < n) (hr : 0 < r)
    (hu : 0 < u) (hsep : 3 * u + 4 * r < n) {lab lab' : ℤ × ℤ → κ} {S : ℤ × ℤ}
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
      (∀ x ∈ P, ∃ R ∈ blockWindow 1, x = own (lab (R + S)) ∨ x = own (lab' (R + S))) ∧
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
        (2 * b + 1) * ((L : ℝ) ^ 20)⁻¹ ∧
      w.IsSourceBounded (2 * b) := by
  obtain ⟨G, hG, ho, hn', how, hph, hrk, hho, hhn, hpt, hUA, hUA', hA, hA', hN, hP, hP₀,
    hdesc⟩ := exists_directRepainting_planeConditions (Party := Party) hn hr hu hsep hlab hg hg'
      own ph rank hV hV' hVc hVc' hVV' hole patch hhole hpatch htwo htwo'
  subst ho hn' how hph hrk hho hpt
  obtain ⟨w, h₁, h₂, h₃, h₄, h₅, h₆⟩ := hG.exists_originalCircuit_isSourceBounded (C := C)
    (c := c) (b := b) hL (fun a _ => hhn ▸ hcardHole a) (fun z _ => hcardPatch z)
    (fun a _ => hcardHole a) (by exact_mod_cast hN.trans hb) (hA.trans (by omega))
    (hA'.trans (by omega)) (hP.trans hb18) hΩ (fun z _ => hεpatch z) (fun a _ => hεhole a) hP₀
    (fun z _ => htag z)
  have e₁ := G.oldFrame_eq hUA hpV
  have e₂ : G.newFrame = guideFrame pos q G.new G.own G.ph G.rank V' G.holeOld hpV' :=
    guideFrame_congr hUA' hhn _ _
  rw [← e₁, ← e₂]
  exact ⟨G.parties, hP, hdesc, w, h₁, h₂, h₃, h₄, h₅, h₆⟩

end Approximation

end TNLean.PEPS
