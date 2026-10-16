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
    rw [ite_eq_left hpY, e1, e2]
    simp only [shiftGuide, hmem', ite_true]
  · rw [ite_eq_right hpY]
    by_cases hpU : p - d ∈ U
    · have hV : (fun x => x - d) ⁻¹' U ∈ 𝓝 p := (hU.preimage hcont).mem_nhds hpU
      obtain ⟨ε, e1, e2, hmem⟩ :=
        ((hg p).and ((hf₁ p).and (tendsto_add_smul_nhdsGT p _ hV))).exists
      have hmem' : p + ε • ((1 : ℝ), (1 : ℝ)) - d ∈ U := hmem
      rw [e1, e2]
      simp only [shiftGuide]
      split_ifs <;> simp only [h₁U _ hmem', h₂U _ hmem']
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

/-- **A bounded change of two frames with bounded pair sources.** For arbitrary finite sites,
positions, parties, `q ≥ 1` and vector `Ω`, an original circuit between the concatenated frame
registers satisfies `IsBoundedChange` on the pair reference vectors and `IsSourceBounded rs`.
At each nonprivate expansion, the former bounds both monomial count and absolute coefficient
sum by `K`, with at most `r` pair effects per monomial; the latter bounds pair sources per
monomial by `rs`. The natural
bounds may be zero, the error is any real number, and `Ω` need not be normalized.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 39–41, 389–430 and 572–583. -/
def HasPairChange (Ω : EuclideanSpace ℂ (ι → Fin q)) (F₁ F₂ F₁' F₂' : Frame pos q Party)
    (S : Set Party) (r K rs : ℕ) (ε : ℝ) : Prop :=
  ∃ w : OriginalCircuit (F₁.regs ++ F₂.regs) (F₁'.regs ++ F₂'.regs),
    w.IsBoundedChange S r K ε (pairRef F₁ F₂ Ω) (pairRef F₁' F₂' Ω) ∧ w.IsSourceBounded rs

section Bounds

variable {Ω : EuclideanSpace ℂ (ι → Fin q)} {S : Set Party} {r K rs : ℕ} {ε ε' : ℝ}

/-- A change of two frames remains bounded when its error bound is enlarged. -/
lemma HasPairChange.mono_error {F₁ F₂ F₁' F₂' : Frame pos q Party}
    (h : HasPairChange Ω F₁ F₂ F₁' F₂' S r K rs ε) (hε : ε ≤ ε') :
    HasPairChange Ω F₁ F₂ F₁' F₂' S r K rs ε' :=
  let ⟨w, hw, hs⟩ := h
  ⟨w, hw.mono subset_rfl le_rfl le_rfl hε, hs⟩

end Bounds

/-- **Reordering the holes after a change of two frames.** The holes of an encoded frame are
listed in a fixed order of their tags; frames with the same ownership assignment and the same
holes in another order are related by a reordering of tensor factors. So a change into `N₁, N₂`
is such a change into frames with the owners of `N₁, N₂` and their holes reordered.

Polynomial-PEPS manuscript, `05-frames.tex` (the order of the tags) and `06-geometry.tex`,
lines 662–667. -/
theorem HasPairChange.reorder {Ω : EuclideanSpace ℂ (ι → Fin q)}
    {F₁ F₂ N₁ N₂ G₁ G₂ : Frame pos q Party}
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

omit [NeZero q] in
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
        fun z => (⟨hole z, own (tagHolder rank (fun p => if p ∈ Y' then f₂ p else f₁ p) ph z)⟩ :
          Hole pos q Party) := by
    simp only [guideFrame, List.filter_map]
    rw [List.filter_congr (q := fun z => decide (z ∉ Y')) fun z _ => by simp [hout]]
    refine List.map_congr_left fun z hz => ?_
    obtain ⟨hz, hzY⟩ := List.mem_filter.1 hz
    have hzY' : z ∉ Y' := by simpa using hzY
    have hv := (hV₁ z).1 (Finset.mem_toList.1 hz)
    rw [tagHolder_congr ((key z).2.2 hzY' hv)]
  have e₂ : (guideFrame pos q f₂ own ph rank V₂ hole hd₂).holes.filter (fun h => !out h) =
      (V₂.toList.filter fun z => decide (z ∈ Y')).map
        fun z => (⟨hole z, own (tagHolder rank (fun p => if p ∈ Y' then f₂ p else f₁ p) ph z)⟩ :
          Hole pos q Party) := by
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

section Exchange

variable {k q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {ε₀ B₀ C c : ℝ}

/-- **The lens exchange for sampled guides, conditional on Proposition 3.4.** Assume `q ≥ 1`, a
gapped ground state, and the exponent-`60` angular-scale condition with `L₀' ≤ L`, `m₀ ≥ 2`,
`A₀ ≥ 1` and `a ≤ angularConstant / 2`. Take any guide-label repainting baseline, edge list,
edge and translation, with `0 < t = D log L ≤ n ≤ A₀ * L` and
`2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2`. Read the four translated endpoint-treated
guides: starting main and auxiliary before, first main and exchanged auxiliary after. Use their
exact finite true-vertex sets, an exponent-`60` adaptive supply and radius
`0 < ε₀ * t ≤ B₀ * log L`, with pairwise-disjoint outer samples within each set. For any owner
map and rank, the supplied frames admit a pair change with participants in any set containing
the neighbor owner and error `4 L⁻³⁰`, for all natural `r, K, rs`, including zero. No pair
source or nonprivate gate is needed. The edge list may repeat edges and may contain the edge
being exchanged.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 389–430 and 440–445; Lemma 6.6
`lem:exchange`, `05-frames.tex`. -/
theorem edgeExchange_hasPairChange_of (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀)
    (ha : a ≤ angularConstant / 2) (Bl : RepaintingBaseline GuideLabel) (E : List SquareEdge)
    (e : SquareEdge) (d : ℝ × ℝ) (ht : 0 < D * Real.log L) (htn : D * Real.log L ≤ Bl.n)
    (hnL : Bl.n ≤ A₀ * L) (hε : 2 * ε₀ * (angularConstant + 1) ≤ angularConstant / 2)
    {fm fa gm ga : ℝ × ℝ → GuideLabel}
    (hfm : IsDisplacedReading fm (shiftGuide d (Bl.treatedStartMain (D * Real.log L) E e))
      ((1 : ℝ), (1 : ℝ)))
    (hfa : IsDisplacedReading fa (shiftGuide d (Bl.treatedAux (D * Real.log L) e))
      ((1 : ℝ), (1 : ℝ)))
    (hgm : IsDisplacedReading gm (shiftGuide d (homogenize (edgeTreated Bl.n e (D * Real.log L))
      (Bl.nbrLabel e) (Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))))
      ((1 : ℝ), (1 : ℝ)))
    (hga : IsDisplacedReading ga (shiftGuide d (homogenize (edgeTreated Bl.n e (D * Real.log L))
      (Bl.nbrLabel e) (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel
        (Bl.nbrLabel e))))) ((1 : ℝ), (1 : ℝ)))
    {Vm Va Wm Wa : Finset (ℝ × ℝ)} (hVm : ∀ z, z ∈ Vm ↔ IsTrueVertex fm z)
    (hVa : ∀ z, z ∈ Va ↔ IsTrueVertex fa z) (hWm : ∀ z, z ∈ Wm ↔ IsTrueVertex gm z)
    (hWa : ∀ z, z ∈ Wa ↔ IsTrueVertex ga z)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    (hdm : (Vm : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (hda : (Va : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (hdm' : (Wm : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (hda' : (Wa : Set (ℝ × ℝ)).Pairwise fun z z' =>
      Disjoint (suppliedPatch P _ hr z).outer (suppliedPatch P _ hr z').outer)
    (own : GuideLabel → ProtocolParty k) (rank : GuideLabel → ℕ) {S : Set (ProtocolParty k)}
    (hCS : own (Bl.nbrLabel e) ∈ S) {r K rs : ℕ} :
    HasPairChange Ω
      (guideFrame (cellCenterPos L) q fm own guidePlaceholder rank Vm (suppliedPatch P _ hr) hdm)
      (guideFrame (cellCenterPos L) q fa own guidePlaceholder rank Va (suppliedPatch P _ hr) hda)
      (guideFrame (cellCenterPos L) q gm own guidePlaceholder rank Wm (suppliedPatch P _ hr) hdm')
      (guideFrame (cellCenterPos L) q ga own guidePlaceholder rank Wa (suppliedPatch P _ hr) hda')
      S r K rs (4 * (L : ℝ) ^ (-30 : ℤ)) := by
  classical
  set t := D * Real.log L with ht_def
  set Y := edgeLens Bl.n e with hY_def
  set U := thickening (angularConstant * t) (frontier Y) with hU_def
  have hδ : 0 < angularConstant * t := mul_pos angularConstant_pos ht
  have hYo : IsOpen Y := isOpen_edgeBand _ _ _ _
  have hUo : IsOpen U := isOpen_thickening
  have hYU : frontier Y ⊆ U := self_subset_thickening hδ _
  have hcorr : ∀ p ∈ U, Bl.treatedStartMain t E e p = Bl.nbrLabel e ∧
      Bl.treatedAux t e p = Bl.nbrLabel e := fun p hp => Bl.exchange_corridor htn E e hp
  -- the guides after the exchange are the treated guides pieced along the lens
  have hpm : homogenize (edgeTreated Bl.n e t) (Bl.nbrLabel e)
      (Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) =
      fun p => if p ∈ Y then Bl.treatedAux t e p else Bl.treatedStartMain t E e p := by
    rw [← Bl.lensExchange_mainGuide E e]
    funext p
    simp only [homogenize, RepaintingBaseline.treatedAux, RepaintingBaseline.treatedStartMain]
    split_ifs <;> rfl
  have hpa : homogenize (edgeTreated Bl.n e t) (Bl.nbrLabel e)
      (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))) =
      fun p => if p ∈ Y then Bl.treatedStartMain t E e p else Bl.treatedAux t e p := by
    rw [← Bl.lensExchange_auxGuide E e]
    funext p
    simp only [homogenize, RepaintingBaseline.treatedAux, RepaintingBaseline.treatedStartMain]
    split_ifs <;> rfl
  rw [hpm] at hgm
  rw [hpa] at hga
  have hgm' := IsDisplacedReading.eq_piecewise hYo hUo hYU (fun p hp => (hcorr p hp).1)
    (fun p hp => (hcorr p hp).2) hfm hfa hgm
  have hga' := IsDisplacedReading.eq_piecewise hYo hUo hYU (fun p hp => (hcorr p hp).2)
    (fun p hp => (hcorr p hp).1) hfa hfm hga
  -- the same at the level of the readings
  set Y' : Set (ℝ × ℝ) := Homeomorph.subRight d ⁻¹' Y with hY'_def
  set U' : Set (ℝ × ℝ) := Homeomorph.subRight d ⁻¹' U with hU'_def
  have hU'o : IsOpen U' := hUo.preimage (Homeomorph.subRight d).continuous
  have hYU' : frontier Y' ⊆ U' := by
    rw [hY'_def, ← Homeomorph.preimage_frontier]
    exact preimage_mono hYU
  have hfmU : ∀ p ∈ U', fm p = Bl.nbrLabel e := fun p hp =>
    hfm.eq_of_mem_open hUo (fun x hx => (hcorr x hx).1) hp
  have hfaU : ∀ p ∈ U', fa p = Bl.nbrLabel e := fun p hp =>
    hfa.eq_of_mem_open hUo (fun x hx => (hcorr x hx).2) hp
  have hgm'' : gm = fun p => if p ∈ Y' then fa p else fm p := hgm'
  have hga'' : ga = fun p => if p ∈ Y' then fm p else fa p := hga'
  -- each hole lies on one side of the lens boundary
  set Gm := guideFrame (cellCenterPos L) q fm own guidePlaceholder rank Vm (suppliedPatch P _ hr)
    hdm
  set Ga := guideFrame (cellCenterPos L) q fa own guidePlaceholder rank Va (suppliedPatch P _ hr)
    hda
  have hside : ∀ hl ∈ Gm.holes ++ Ga.holes, ∃ z, hl.patch = suppliedPatch P _ hr z ∧
      (closedBall (z - d) (2 * ε₀ * t) ⊆ Y ∨ closedBall (z - d) (2 * ε₀ * t) ⊆ Yᶜ) := by
    intro hl hhl
    rcases List.mem_append.1 hhl with hhl | hhl
    · obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hhl
      exact ⟨z, rfl, Bl.outerHole_subset_or_subset_compl ht htn hε E e
        (Or.inl (hfm.sub_isTrueVertex ((hVm z).1 hz)))⟩
    · obtain ⟨z, hz, rfl⟩ := mem_holes_guideFrame.1 hhl
      exact ⟨z, rfl, Bl.outerHole_subset_or_subset_compl ht htn hε E e
        (Or.inr (hfa.sub_isTrueVertex ((hVa z).1 hz)))⟩
  have hball : ∀ z (x : SquareLatticeVertex L L), x ∈ (suppliedPatch P _ hr z).outer →
      cellCenterPos L x - d ∈ closedBall (z - d) (2 * ε₀ * t) := fun z x hx => by
    rw [mem_outer_iff, suppliedPatch_center, suppliedPatch_scale] at hx
    rw [mem_closedBall, dist_sub_right]
    linarith
  have hcen : ∀ z, z - d ∈ closedBall (z - d) (2 * ε₀ * t) := fun z =>
    mem_closedBall_self (by have := (hr 0).1; nlinarith)
  set out : Hole (cellCenterPos L) q (ProtocolParty k) → Bool :=
    fun hl => decide (hl.patch.center - d ∉ Y)
  have hout : ∀ hl ∈ Gm.holes ++ Ga.holes, out hl = true →
      Disjoint (hl.patch.outer : Set (SquareLatticeVertex L L))
        (lensSample (cellCenterPos L) Bl.n e d) := by
    intro hl hhl ho
    obtain ⟨z, hpz, hs⟩ := hside hl hhl
    have hz : z - d ∉ Y := by simpa [out, hpz] using ho
    have hs' : closedBall (z - d) (2 * ε₀ * t) ⊆ Yᶜ := hs.resolve_left fun h => hz (h (hcen z))
    rw [hpz]
    exact Set.disjoint_left.2 fun x hx hxY =>
      hs' (hball z x hx) ((mem_lensSample x).1 (Finset.mem_coe.1 hxY))
  have hin : ∀ hl ∈ Gm.holes ++ Ga.holes, out hl = false →
      (hl.patch.outer : Set (SquareLatticeVertex L L)) ⊆
        lensSample (cellCenterPos L) Bl.n e d := by
    intro hl hhl ho
    obtain ⟨z, hpz, hs⟩ := hside hl hhl
    have hz : z - d ∈ Y := by simpa [out, hpz] using ho
    have hs' : closedBall (z - d) (2 * ε₀ * t) ⊆ Y := hs.resolve_right fun h => h (hcen z) hz
    rw [hpz]
    exact fun x hx => Finset.mem_coe.2 ((mem_lensSample x).2 (hs' (hball z x hx)))
  obtain ⟨w, hw, hu, hs, herr⟩ := edgeExchange_step_guideFrame hD hLL hΩ
    (fun v => cellCenterPos_eq_sitePosition_add v) hm₀ ha Bl E e d ((1 : ℝ), (1 : ℝ)) ht htn
    hnL hε hfm hfa (V₁ := Vm) (V₂ := Va) (hV₁ := hdm) (hV₂ := hda) (fun z hz => (hVm z).1 hz)
    (fun z hz => (hVa z).1 hz) (fun z _ => ⟨suppliedPatch_center P hr z, by simp⟩)
    (fun z _ => ⟨suppliedPatch_center P hr z, by simp⟩) out hout hin (fun x hx y hy => by
      have hx' := ((TwoSheetExchange.mem_tSet_iff _ _ x).1 hx).1
      have hy' := ((TwoSheetExchange.mem_tSet_iff _ _ y).1 hy).1
      have hxY := (mem_lensSample x).1 hx'
      have hyY := (mem_lensSample y).1 hy'
      have := dist_le_of_mem_closure_edgeLens (s := edgeLens Bl.n e) subset_rfl
        (subset_closure hxY) (subset_closure hyY)
      rw [dist_sub_right] at this
      exact this.trans (le_mul_of_one_le_left Bl.n_pos.le hA₀))
  rw [← pairRef_eq_twoLayoutIso_symm, ← pairRef_eq_twoLayoutIso_symm] at herr
  have h0 : (w.toOriginalCircuit hw).nonprivateCount = 0 :=
    (w.nonprivateCount_toOriginalCircuit hw).trans hs
  have hpair : HasPairChange Ω Gm Ga _ _ S r K rs (4 * (L : ℝ) ^ (-30 : ℤ)) :=
    ⟨w.toOriginalCircuit hw,
      { nonprivateCount_le := h0.le.trans zero_le_one
        participants_subset := fun g => (w.participants_toOriginalCircuit_subset hw hu g).trans
          (by rintro x rfl; exact hCS)
        isExpansionBounded := Word.isExpansionBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hs r K
        isMonomialBounded := Word.isMonomialBounded_toOriginalCircuit_of_sourceCount_eq_zero _ _
          hs K
        norm_eval_sub_le := by rwa [w.eval_toOriginalCircuit] },
      OriginalCircuit.isSourceBounded_of_nonprivateCount_eq_zero h0 rs⟩
  have hout' : ∀ z o, out ⟨suppliedPatch P _ hr z, o⟩ = decide (z ∉ Y') := fun z o => by
    simp [out, Y']
  refine hpair.reorder ?_ ?_ ?_ ?_
  · funext x
    rw [guideFrame_owner, hgm'']
    simp only [TwoSheetExchange.ofFrames, mem_lensSample, guideFrame_owner]
    simp only [hY_def] at hY'_def
    by_cases hx : cellCenterPos L x - d ∈ edgeLens Bl.n e <;>
      simp only [hx, hY'_def, Set.mem_preimage, Homeomorph.subRight_apply, ↓reduceIte]
  · rw [hgm'']
    exact guideFrame_exchange_holes_perm hU'o hYU' hfmU hfaU hVm hVa (hgm'' ▸ hWm) out hout'
  · funext x
    rw [guideFrame_owner, hga'']
    simp only [TwoSheetExchange.ofFrames, mem_lensSample, guideFrame_owner]
    simp only [hY_def] at hY'_def
    by_cases hx : cellCenterPos L x - d ∈ edgeLens Bl.n e <;>
      simp only [hx, hY'_def, Set.mem_preimage, Homeomorph.subRight_apply, ↓reduceIte]
  · rw [hga'']
    exact guideFrame_exchange_holes_perm hU'o hYU' hfaU hfmU hVa hVm (hga'' ▸ hWa) out hout'

/-- **The lens exchange as a change of two treated sheets, conditional on Proposition 3.4.** Assume
`q ≥ 1`, a gapped ground state, and the exponent-`60` angular-scale condition with `L₀' ≤ L`,
`m₀ ≥ 2` and `A₀ ≥ 1`. At the protocol constants, take `L ≥ 2`, `2 ^ k < 2 * L`, an
exponent-`60` adaptive patch supply, any rank, any already-repainted set and a repaintable square
`R` of side `n = 2 ^ j > K₀ t`, where `t = D log L`. For any edge list and edge `e`, treat all
four guides with the neighboring label about the endpoints of `e`: starting main and auxiliary
before, first main and exchanged auxiliary after. Their frames admit a pair change with
participants in any set containing the neighboring party and error `4 L⁻³⁰`, for all natural
`r, K, rs`, including zero. No pair source or nonprivate gate is needed. The list may repeat
or contain `e`, and there is no premise that `R` is absent from the already-repainted set.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–221, 328–339, 389–430 and 440–445;
Lemma 6.6 `lem:exchange`, `05-frames.tex`. -/
theorem edgeExchange_hasPairChange (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀') (hLL : L₀' ≤ L)
    (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 2 ≤ m₀) (hA₀ : 1 ≤ A₀) {K₀ ν : ℝ}
    (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hk2 : 2 ^ k < 2 * L)
    (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
    (R : RepaintedSquare k) (hlarge : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ))
    (done : Set (ℤ × ℤ)) (E : List SquareEdge) (e : SquareEdge)
    {S : Set (ProtocolParty k)}
    (hCS : labelParty R (protocolLevelLabels k R.1.1 done (e.nbrBlock R.1.index)) ∈ S)
    {r K rs : ℕ} :
    let Bl := blockBaseline (n := (2 : ℝ) ^ (R.1.1 : ℕ)) (by positivity)
      (protocolLevelLabels k R.1.1 done) R.1.index (newParty Sum.inl R.1.1 R.1.index)
    HasPairChange Ω
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
        (Bl.mainGuide E e (edgeStartWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
        (Bl.auxGuide e (auxWord Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
        (Bl.mainGuide E e (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))
      (treatedFrame (q := q) P rank R (hc.treatedRadius_bounds hL)
        (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
        (Bl.auxGuide e (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e))))
      S r K rs (4 * (L : ℝ) ^ (-30 : ℤ)) := by
  have hr := hc.treatedRadius_bounds hL
  intro Bl
  have hℓ : 0 < Real.log L := Real.log_pos (by exact_mod_cast hL)
  have ht : 0 < D * Real.log L := mul_pos hc.D_pos hℓ
  obtain ⟨hfm, hmm, hdm, hFm⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, _, Or.inl rfl, rfl⟩))))
    (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
  obtain ⟨hfa, hma, hda, hFa⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, _, Or.inr (Or.inr (Or.inr (Or.inl rfl))), rfl⟩))))
    (e.endpointBlocks R.1.index) (Bl.nbrLabel e)
  obtain ⟨hgm, hmm', hdm', hFm'⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inr (Or.inl ⟨E, e, _, Or.inr (Or.inl rfl), rfl⟩))))
    (e.endpointBlocks R.1.index) (Bl.nbrLabel e) (g := Bl.mainGuide E e
      (mainWordOne Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))
  obtain ⟨hga, hma', hda', hFa'⟩ := treatedFrame_spec (q := q) P rank R hc hL hlarge done
    (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩))))
    (e.endpointBlocks R.1.index) (Bl.nbrLabel e) (g := Bl.auxGuide e
      (auxWordExchanged Bl.oldLabel Bl.finalLabel (Bl.nbrLabel e)))
  rw [homogenize_endpointBlocks] at hfm hfa hgm hga
  rw [hFm, hFa, hFm', hFa']
  exact edgeExchange_hasPairChange_of hD hLL hΩ hm₀ hA₀ hc.a_le Bl E e
    (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index) ht
    (by change D * Real.log L ≤ (2 : ℝ) ^ (R.1.1 : ℕ); nlinarith [hc.twenty_le_K₀, hlarge, ht])
    (le_mul_of_one_le_left (by positivity) hA₀ |>.trans' (R.side_le hk2))
    hc.ε₀_small hfm hfa hgm hga hmm hma hmm' hma' P hr hdm hda hdm' hda' _ rank hCS

end Exchange

end TNLean.PEPS.Approximation
