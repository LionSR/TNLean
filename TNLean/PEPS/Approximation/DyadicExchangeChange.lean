/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicBandStepChanges
import TNLean.PEPS.Approximation.GuideFrameRewriteCircuit

/-!
# The lens exchange as a change of two treated sheets

Along an edge `e` of a square repainted at a large scale, the protocol of Proposition 7.1 of the
polynomial-PEPS manuscript exchanges the assignments of the main and the auxiliary sheet on the
lens `Y`, after homogenizing both sheets to `C_e` about the two endpoints of `e`
(`06-geometry.tex`, lines 193–212 and 389–430). Both treated sheets are `C_e` on a neighborhood of
the boundary of the lens, so the exchanged guides are the treated guides pieced together along
`∂Y`, and each hole lies on one side of `∂Y` and moves with its sheet. This file proves that the
exchange is a bounded change from the frames of the two treated sheets before it to the frames of
the treated guides after it, conditional on Proposition 3.4 through `IsAngularScale`:

* `IsDisplacedReading.eq_piecewise` : the reading of a guide pieced along a common corridor is
  the pieced reading;
* `edgeExchange_hasPairChange_of` : the exchange, for the frames of sampled guides of any
  repainting baseline.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the auxiliary sheet and
  the lens exchange (lines 183–212), the point treatment and the exchange (lines 328–339 and
  389–430); Lemma 6.6 `lem:exchange`, `05-frames.tex`.
-/

noncomputable section

open Set Metric Filter Topology

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

section Readings

variable {κ : Type*} {H₁ H₂ f₁ f₂ g : ℝ × ℝ → κ} {d : ℝ × ℝ} {Y U : Set (ℝ × ℝ)} {C : κ}

open Classical in
/-- **The reading of a pieced guide.** Let `Y` and `U` be open, with the boundary of `Y` in `U`,
and let two labellings both be `C` on `U`. Then the reading, moved by `d`, of the labelling equal
to the second on `Y` and to the first elsewhere is the reading of the second at the points moved
into `Y` and the reading of the first at the others.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 76–80 and 389–419. -/
theorem IsDisplacedReading.eq_piecewise (hY : IsOpen Y) (hU : IsOpen U) (hYU : frontier Y ⊆ U)
    (h₁U : ∀ p ∈ U, H₁ p = C) (h₂U : ∀ p ∈ U, H₂ p = C)
    (hf₁ : IsDisplacedReading f₁ (shiftGuide d H₁) ((1 : ℝ), (1 : ℝ)))
    (hf₂ : IsDisplacedReading f₂ (shiftGuide d H₂) ((1 : ℝ), (1 : ℝ)))
    (hg : IsDisplacedReading g (shiftGuide d fun p => if p ∈ Y then H₂ p else H₁ p)
      ((1 : ℝ), (1 : ℝ))) :
    g = fun p => if p - d ∈ Y then f₂ p else f₁ p := by
  funext p
  have hcont : Continuous fun x : ℝ × ℝ => x - d := continuous_id.sub continuous_const
  by_cases hpY : p - d ∈ Y
  · have hV : (fun x => x - d) ⁻¹' Y ∈ 𝓝 p := (hY.preimage hcont).mem_nhds hpY
    obtain ⟨ε, e1, e2, hmem⟩ :=
      ((hg p).and ((hf₂ p).and (tendsto_add_smul_nhdsGT p _ hV))).exists
    have hmem' : p + ε • ((1 : ℝ), (1 : ℝ)) - d ∈ Y := hmem
    rw [if_pos hpY, e1, e2]
    simp only [shiftGuide, hmem', ite_true]
  · rw [if_neg hpY]
    by_cases hpU : p - d ∈ U
    · have hV : (fun x => x - d) ⁻¹' U ∈ 𝓝 p := (hU.preimage hcont).mem_nhds hpU
      obtain ⟨ε, e1, e2, e3, hmem⟩ :=
        ((hg p).and ((hf₁ p).and ((hf₂ p).and (tendsto_add_smul_nhdsGT p _ hV)))).exists
      have hmem' : p + ε • ((1 : ℝ), (1 : ℝ)) - d ∈ U := hmem
      rw [e1, e2]
      simp only [shiftGuide]
      split_ifs <;> rw [h₁U _ hmem'] <;> first | rw [h₂U _ hmem'] | rfl
    · have hcl : p - d ∉ closure Y := fun h =>
        hpU (hYU ⟨h, by rwa [hY.interior_eq]⟩)
      have hV : (fun x => x - d) ⁻¹' (closure Y)ᶜ ∈ 𝓝 p :=
        (isClosed_closure.isOpen_compl.preimage hcont).mem_nhds hcl
      obtain ⟨ε, e1, e2, hmem⟩ :=
        ((hg p).and ((hf₁ p).and (tendsto_add_smul_nhdsGT p _ hV))).exists
      have hmem' : p + ε • ((1 : ℝ), (1 : ℝ)) - d ∉ Y := fun h => hmem (subset_closure h)
      rw [e1, e2]
      simp only [shiftGuide, hmem', ite_false]

/-- A reading of a labelling that is `C` on an open set is `C` there. -/
theorem IsDisplacedReading.eq_of_mem_open {H f : ℝ × ℝ → κ} (hU : IsOpen U)
    (hHU : ∀ p ∈ U, H p = C) (hf : IsDisplacedReading f (shiftGuide d H) ((1 : ℝ), (1 : ℝ)))
    {p : ℝ × ℝ} (hp : p - d ∈ U) : f p = C := by
  have hV : (fun x => x - d) ⁻¹' U ∈ 𝓝 p :=
    (hU.preimage (continuous_id.sub continuous_const)).mem_nhds hp
  obtain ⟨ε, e1, hmem⟩ := ((hf p).and (tendsto_add_smul_nhdsGT p _ hV)).exists
  have hmem' : p + ε • ((1 : ℝ), (1 : ℝ)) - d ∈ U := hmem
  rw [e1]
  exact hHU _ hmem'

end Readings

section PairChanges

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
  {Party : Type}

/-- **A bounded change of two frames with bounded pair sources.** An original circuit from the
registers of `F₁, F₂` to those of `F₁', F₂'` that is a bounded change from the product of their
reference vectors, with at most `rs` pair sources in each monomial.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 572–583. -/
def HasPairChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (F₁ F₂ F₁' F₂' : Frame pos q Party)
    (S : Set Party) (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ w : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs),
    w.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω) ∧ w.IsSourceBounded rs

/-- **Reordering the holes after a change of two frames.** The holes of an encoded frame are
listed in a fixed order of their tags; frames with the same ownership assignment and the same
holes in another order are related by a reordering of tensor factors. So a change into `N₁, N₂`
is such a change into frames with the owners of `N₁, N₂` and their holes reordered.

Polynomial-PEPS manuscript, `05-frames.tex` (the order of the tags) and `06-geometry.tex`,
lines 662–667. -/
theorem HasPairChange.reorder {Ω : EuclideanSpace ℂ (ι → Fin q)} {F₁ F₂ N₁ N₂ G₁ G₂ : Frame pos q Party}
    {S : Set Party} {r K rs : ℕ} {ε : ℝ} (h : HasPairChange Ω F₁ F₂ N₁ N₂ S r K rs ε)
    (ho₁ : N₁.owner = G₁.owner) (hp₁ : N₁.holes.Perm G₁.holes) (ho₂ : N₂.owner = G₂.owner)
    (hp₂ : N₂.holes.Perm G₂.holes) : HasPairChange Ω F₁ F₂ G₁ G₂ S r K rs ε := by
  obtain ⟨c, hc, hs⟩ := h
  obtain ⟨w₁, hw₁, -, he₁⟩ := Frame.exists_permWord N₁ G₁ ho₁ hp₁
  obtain ⟨w₂, hw₂, -, he₂⟩ := Frame.exists_permWord N₂ G₂ ho₂ hp₂
  set c₁ := w₁.toOriginalCircuit hw₁.isAllowed
  set c₂ := w₂.toOriginalCircuit hw₂.isAllowed
  have h₁ := Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₁
  have h₂ := Word.nonprivateCount_toOriginalCircuit_of_isReordering hw₂
  set e : OriginalCircuit (N₁.regs ++ N₂.regs) (G₁.regs ++ G₂.regs) :=
    .comp (c₁.appendTail N₂.regs) (OriginalCircuit.frameList G₁.regs c₂)
  have he0 : e.nonprivateCount = 0 := by
    change (c₁.appendTail N₂.regs).nonprivateCount +
      (OriginalCircuit.frameList G₁.regs c₂).nonprivateCount = 0
    rw [OriginalCircuit.nonprivateCount_appendTail, OriginalCircuit.nonprivateCount_frameList,
      h₁, h₂]
  have heval : e.eval (pairRef N₁ N₂ Ω) = pairRef G₁ G₂ Ω := by
    change (OriginalCircuit.frameList G₁.regs c₂).eval ((c₁.appendTail N₂.regs).eval
      ((appendIso N₁.regs N₂.regs).symm (N₁.regRef Ω ⊗ₜ N₂.regRef Ω))) =
      (appendIso G₁.regs G₂.regs).symm (G₁.regRef Ω ⊗ₜ G₂.regRef Ω)
    rw [OriginalCircuit.eval_appendTail_appendIso_symm,
      OriginalCircuit.eval_frameList_appendIso_symm, Word.eval_toOriginalCircuit,
      Word.eval_toOriginalCircuit]
    exact congrArg₂ (fun x y => (appendIso G₁.regs G₂.regs).symm (x ⊗ₜ y)) (he₁ Ω) (he₂ Ω)
  have hE : ∀ (s : ℝ), e.IsExpansionBounded r s := fun s =>
    ⟨OriginalCircuit.isExpansionBounded_appendTail _ _
        (Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hw₁.sourceCount_eq r s),
      OriginalCircuit.isExpansionBounded_frameList _
        (Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hw₂.sourceCount_eq r s) _⟩
  have hM : e.IsMonomialBounded K :=
    ⟨OriginalCircuit.isMonomialBounded_appendTail _ _
        (Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hw₁.sourceCount_eq K),
      OriginalCircuit.isMonomialBounded_frameList _
        (Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hw₂.sourceCount_eq K) _⟩
  refine ⟨c.comp e, ?_, hs, OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero he0 rs⟩
  rw [← heval]
  exact hc.comp_right e he0 (hE _) hM

open Classical in
/-- **The holes after an exchange of two guide frames.** Let `f₁, f₂` both be `C` on an open set
containing the boundary of `Y'`, and keep the holes of the frame of `f₁` centered outside `Y'` and
those of the frame of `f₂` centered inside `Y'`. These are, up to order, the holes of the frame of
the labelling equal to `f₂` on `Y'` and to `f₁` elsewhere, at its true vertices.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 389–398 and 415–419; the frames after an
exchange, `05-frames.tex`, lines 462–464. -/
theorem guideFrame_exchange_holes_perm {κ : Type*} {C : κ} {f₁ f₂ : ℝ × ℝ → κ}
    {Y' U' : Set (ℝ × ℝ)} (hU' : IsOpen U') (hYU' : frontier Y' ⊆ U')
    (h₁U : ∀ p ∈ U', f₁ p = C) (h₂U : ∀ p ∈ U', f₂ p = C) {own : κ → Party} {ph : κ}
    {rank : κ → ℕ} {V₁ V₂ W : Finset (ℝ × ℝ)} (hV₁ : ∀ z, z ∈ V₁ ↔ IsTrueVertex f₁ z)
    (hV₂ : ∀ z, z ∈ V₂ ↔ IsTrueVertex f₂ z)
    (hW : ∀ z, z ∈ W ↔ IsTrueVertex (fun p => if p ∈ Y' then f₂ p else f₁ p) z)
    {hole : ℝ × ℝ → SquarePatch pos q}
    {hd₁ : (V₁ : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}
    {hd₂ : (V₂ : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}
    {hdW : (W : Set (ℝ × ℝ)).Pairwise fun z z' => Disjoint (hole z).outer (hole z').outer}
    (out : Hole pos q Party → Bool) (hout : ∀ z o, out ⟨hole z, o⟩ = decide (z ∉ Y')) :
    ((guideFrame pos q f₁ own ph rank V₁ hole hd₁).holes.filter out ++
      (guideFrame pos q f₂ own ph rank V₂ hole hd₂).holes.filter fun h => !out h).Perm
      (guideFrame pos q (fun p => if p ∈ Y' then f₂ p else f₁ p) own ph rank W hole hdW).holes := by
  have key := isTrueVertex_piecewise_iff hU' hYU' h₁U h₂U
  have e₁ : (guideFrame pos q f₁ own ph rank V₁ hole hd₁).holes.filter out =
      (V₁.toList.filter fun z => decide (z ∉ Y')).map
        fun z => (⟨hole z, own (tagHolder rank (fun p => if p ∈ Y' then f₂ p else f₁ p) ph z)⟩ : Hole pos q Party) := by
    simp only [guideFrame, List.filter_map]
    rw [List.filter_congr (q := fun z => decide (z ∉ Y')) fun z _ => by simp [hout]]
    refine List.map_congr_left fun z hz => ?_
    obtain ⟨hz, hzY⟩ := List.mem_filter.1 hz
    have hzY' : z ∉ Y' := by simpa using hzY
    have hv := (hV₁ z).1 (Finset.mem_toList.1 hz)
    rw [tagHolder_congr ((key z).2.2 hzY' hv)]
  have e₂ : (guideFrame pos q f₂ own ph rank V₂ hole hd₂).holes.filter (fun h => !out h) =
      (V₂.toList.filter fun z => decide (z ∈ Y')).map
        fun z => (⟨hole z, own (tagHolder rank (fun p => if p ∈ Y' then f₂ p else f₁ p) ph z)⟩ : Hole pos q Party) := by
    simp only [guideFrame, List.filter_map]
    rw [List.filter_congr (q := fun z => decide (z ∈ Y')) fun z _ => by simp [hout]]
    refine List.map_congr_left fun z hz => ?_
    obtain ⟨hz, hzY⟩ := List.mem_filter.1 hz
    have hzY' : z ∈ Y' := by simpa using hzY
    have hv := (hV₂ z).1 (Finset.mem_toList.1 hz)
    rw [tagHolder_congr ((key z).2.1 hzY' hv)]
  rw [e₁, e₂, ← List.map_append]
  refine List.Perm.map _ ((List.perm_ext_iff_of_nodup ?_ W.nodup_toList).2 fun z => ?_)
  · refine List.Nodup.append (V₁.nodup_toList.filter _) (V₂.nodup_toList.filter _) ?_
    intro z hz₁ hz₂
    have h1 := (List.mem_filter.1 hz₁).2
    have h2 := (List.mem_filter.1 hz₂).2
    simp only [decide_eq_true_eq] at h1 h2
    exact h1 h2
  · simp only [List.mem_append, List.mem_filter, Finset.mem_toList, decide_eq_true_eq, hV₁, hV₂,
      hW, (key z).1]
    tauto

end PairChanges

end TNLean.PEPS.Approximation
