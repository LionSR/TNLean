/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLargeRepaintingChain
import TNLean.PEPS.Approximation.DyadicProtocolFromEvents

/-!
# The memory through a large-scale repainting

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript the memory before each event
is the main frame followed by one frame for each auxiliary sheet of the schedule: frozen once its
repainting is done, and before that an idle raw copy held by its future owner (`06-geometry.tex`,
lines 183–186 and 653–667). This file shows that the `189` changes of a large-scale repainting
pass the memory from its state before the repainting to its state after it, once the frozen
frames of its edges are the auxiliary frames left by the edge constructions and the idle copies
are held by the parties of the labels across the edges.

* `nodup_auxIndices`, `mem_auxIndices` : the auxiliary indices;
* `exists_largeRepainting_segment` : the `189` changes from one state to the next.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the repainting by
  levels (lines 82–100), the edge construction (lines 142–221) and the memory (lines 572–583 and
  653–667).
-/

noncomputable section

open Set

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### The auxiliary indices -/

/-- The auxiliary indices of one event: the four edges of a large-scale repainting. -/
def eventAuxIndices (large : DyadicSquare k → Bool) : ProtocolEvent k →
    List (ProtocolEvent k × RepaintOp)
  | .inl S => if large S then SquareEdge.list.map fun e => (.inl S, .auxInit e) else []
  | .inr _ => []

/-- Filtering the operations of a large repainting for auxiliary initialization gives
the four edge initializations in edge order. -/
theorem filter_largeRepaintingOps :
    largeRepaintingOps.filter (fun o => o.IsAuxInit) = SquareEdge.list.map RepaintOp.auxInit := by
  simp [largeRepaintingOps, edgeOps, BulkOp.ops, SquareEdge.list, RepaintOp.IsAuxInit,
    List.filter_append, List.filter_map, Function.comp_def, List.filter_false]

/-- The auxiliary indices concatenate the auxiliary indices of each scheduled event. -/
theorem auxIndices_eq (large : DyadicSquare k → Bool) :
    auxIndices k large = (eventSchedule k).flatMap (eventAuxIndices large) := by
  simp only [auxIndices, protocolSchedule, List.filter_flatMap]
  refine List.flatMap_congr fun e _ => ?_
  rw [List.filter_map]
  rcases e with S | J
  · by_cases hS : large S
    · simp only [eventOps, eventAuxIndices, hS, ite_true]
      rw [show ((fun x : ProtocolEvent k × RepaintOp => x.2.IsAuxInit) ∘
          fun o => ((Sum.inl S : ProtocolEvent k), o)) = fun o => o.IsAuxInit from rfl,
        filter_largeRepaintingOps, List.map_map]
      rfl
    · simp [eventOps, eventAuxIndices, hS, RepaintOp.IsAuxInit]
  · simp [eventOps, eventAuxIndices, RepaintOp.IsAuxInit]

/-- An auxiliary index assigned to an event has that event as its first component. -/
theorem fst_of_mem_eventAuxIndices {large : DyadicSquare k → Bool} {e : ProtocolEvent k}
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ eventAuxIndices large e) : x.1 = e := by
  rcases e with S | J
  · simp only [eventAuxIndices] at hx
    split_ifs at hx
    · obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
      rfl
    · simp at hx
  · simp [eventAuxIndices] at hx

/-- The list of auxiliary indices has no repetitions. -/
theorem nodup_auxIndices (large : DyadicSquare k → Bool) : (auxIndices k large).Nodup := by
  rw [auxIndices_eq, List.nodup_flatMap]
  refine ⟨fun e _ => ?_, (nodup_eventSchedule k).imp fun {e e'} hne => ?_⟩
  · rcases e with S | J
    · simp only [eventAuxIndices]
      split_ifs
      · exact List.Nodup.map (fun f f' h => by simpa using h) (by decide)
      · exact List.nodup_nil
    · exact List.nodup_nil
  · rw [Function.onFun, List.disjoint_left]
    intro x hx hx'
    exact hne ((fst_of_mem_eventAuxIndices hx).symm.trans (fst_of_mem_eventAuxIndices hx'))

/-- Each edge initialization of a scheduled repainting designated large belongs to
the auxiliary indices. -/
theorem mem_auxIndices {large : DyadicSquare k → Bool} {S : DyadicSquare k}
    (hS : (Sum.inl S : ProtocolEvent k) ∈ eventSchedule k) (hl : large S = true)
    (e : SquareEdge) :
    ((Sum.inl S : ProtocolEvent k), RepaintOp.auxInit e) ∈ auxIndices k large := by
  rw [auxIndices_eq]
  refine List.mem_flatMap.2 ⟨_, hS, ?_⟩
  simp only [eventAuxIndices, hl, ite_true, List.mem_map]
  exact ⟨e, by cases e <;> simp [SquareEdge.list], rfl⟩

/-- An auxiliary index whose event repaints a square is an edge initialization of
that square. -/
theorem eq_auxInit_of_mem_auxIndices {large : DyadicSquare k → Bool}
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ auxIndices k large) {S : DyadicSquare k}
    (h : x.1 = .inl S) : ∃ e, x = ((Sum.inl S : ProtocolEvent k), RepaintOp.auxInit e) := by
  rw [auxIndices_eq] at hx
  obtain ⟨e', -, hx⟩ := List.mem_flatMap.1 hx
  rcases e' with S' | J
  · simp only [eventAuxIndices] at hx
    split_ifs at hx
    · obtain ⟨f, -, rfl⟩ := List.mem_map.1 hx
      exact ⟨f, by rw [← h]⟩
    · simp at hx
  · simp [eventAuxIndices] at hx

/-! ### The segment -/

variable {q : ℕ} [NeZero q] {J Δ a A₀ D L₀' : ℝ} {m₀ : ℕ} {L : ℕ}
  {h : SquareHamiltonian L q J} {E₀ : ℝ} {Ω : StateSpace L q} {K₀ ε₀ ν B₀ C c : ℝ}

/-- **The memory through a large-scale repainting, conditional on Proposition 3.4.** At the
constants of the protocol with `L ≤ 2 ^ k < 2 L`, let the event number `i` repaint a square `S` of
side `n = 2 ^ j > K₀ t`, `t = D log L`, with its point treatments bounded changes. Suppose that
before `S` the idle copy of the auxiliary sheet of each edge `e` of `S` is held by the party of
the label across `e`, and that its frozen frame is the auxiliary frame left by the edge
construction. Then `189` bounded changes with the bounds of the small-patch rewrites pass the
memory from its state before the event to its state after it.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100, 142–221, 572–583 and 653–667. -/
theorem exists_largeRepainting_segment (hD : IsAngularScale q J Δ a A₀ m₀ 60 D L₀')
    (hLL : L₀' ≤ L) (hΩ : h.IsGappedGroundState E₀ Ω Δ) (hm₀ : 4 ≤ m₀)
    (hA₀ : 1 ≤ A₀) (hc : IsProtocolConstants K₀ ε₀ ν a D B₀) (hL : 2 ≤ L) (hkL : L ≤ 2 ^ k)
    (hk2 : 2 ^ k < 2 * L) (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L)
    (rank : GuideLabel → ℕ) (R₀ : RepaintedSquare k) (ht : 0 < D * Real.log L)
    (hB : ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    (frozen : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k))
    (auxOwner : ProtocolEvent k × RepaintOp → ProtocolParty k) {i : ℕ}
    (hi : i < (eventSchedule k).length) {S : DyadicSquare k}
    (he : (eventSchedule k)[i] = .inl S) (hlarge : largeSquare K₀ (D * Real.log L) S = true)
    {b K : ℕ} (hb : 2 ≤ b) (hK : 1 ≤ K)
    (hpt : ∀ hS : (S.1 : ℕ) < k, IsPointTreatable P rank ⟨S, hS⟩
      (fun _ => ⟨mul_pos hc.ε₀_pos ht, hB⟩) (repaintedBlocks k i S.1)
      {p | EventUses (.inl S) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹))
    (hfrozen : ∀ (hS : (S.1 : ℕ) < k) (e : SquareEdge), frozen (.inl S, .auxInit e) =
      auxFinal P rank ⟨S, hS⟩ (fun _ => ⟨mul_pos hc.ε₀_pos ht, hB⟩) (repaintedBlocks k i S.1) e)
    (howner : ∀ (hS : (S.1 : ℕ) < k) (e : SquareEdge), auxOwner (.inl S, .auxInit e) =
      labelParty ⟨S, hS⟩ ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).nbrLabel e)) :
    ∃ seg : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)),
      seg 0 = protocolState P rank R₀ hc.ε₀_pos ht hB (largeSquare K₀ (D * Real.log L)) frozen
        auxOwner i ∧
      seg 189 = protocolState P rank R₀ hc.ε₀_pos ht hB (largeSquare K₀ (D * Real.log L)) frozen
        auxOwner (i + 1) ∧
      ∀ j < 189, HasSourceBoundedChange Ω (seg j) (seg (j + 1)) (ℓ := []) (1 : ℂ)
        {p | EventUses (.inl S) p} (2 * b) K (2 * b) ((2 * b + 1) * ((L : ℝ) ^ 20)⁻¹) := by
  classical
  have hS : (S.1 : ℕ) < k := by
    have := isScheduled_getElem hi; rw [he] at this; exact this
  have hk : 1 ≤ k := by omega
  set R : RepaintedSquare k := ⟨S, hS⟩
  set t := D * Real.log L
  set large := largeSquare (k := k) K₀ t
  set done := repaintedBlocks k i S.1
  have hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L :=
    fun _ => ⟨mul_pos hc.ε₀_pos ht, hB⟩
  have hl : K₀ * t < (2 : ℝ) ^ (R.1.1 : ℕ) := by
    simpa [large, largeSquare] using hlarge
  have hρ : ∀ _ : ℝ × ℝ, 0 < holeRadius ε₀ ((2 : ℝ) ^ (S.1 : ℕ)) t ∧
      holeRadius ε₀ ((2 : ℝ) ^ (S.1 : ℕ)) t ≤ B₀ * Real.log L :=
    fun _ => holeRadius_mem hc.ε₀_pos ht hB (by positivity)
  have hSmem : (Sum.inl S : ProtocolEvent k) ∈ eventSchedule k := he ▸ List.getElem_mem hi
  have hnotin : (Sum.inl S : ProtocolEvent k) ∉ (eventSchedule k).take i :=
    he ▸ getElem_notMem_take hi
  set xs : SquareEdge → ProtocolEvent k × RepaintOp := fun e => (.inl S, .auxInit e)
  have hxs : ∀ e, xs e ∈ auxIndices k large := mem_auxIndices hSmem hlarge
  have hinj : Function.Injective xs := fun e e' h => by simpa [xs] using h
  set idle : ProtocolEvent k × RepaintOp → Frame (cellCenterPos L) q (ProtocolParty k) :=
    fun x => Frame.raw fun _ => auxOwner x
  have hA : ∀ e, auxState frozen idle i (xs e) =
      Frame.raw fun _ => labelParty R ((repaintBaseline R done).nbrLabel e) := fun e => by
    unfold auxState
    rw [ite_eq_right hnotin]
    exact congrArg Frame.raw (funext fun _ => howner hS e)
  obtain ⟨seg, h0, h1, hseg⟩ := isStepChain_largeRepainting hD hLL hΩ hm₀ hA₀ hc hL hk2 P
    rank R hl done hr hb hK (hpt hS) (nodup_auxIndices large) xs hxs hinj hA
    (repaintBaseline R done).oldLabel (repaintBaseline R done).oldLabel
  refine ⟨seg, ?_, ?_, hseg⟩
  · rw [h0]
    simp only [protocolState]
    refine congrArg₂ (· :: ·) ?_ rfl
    rw [mainState_of_lt _ _ _ _ _ _ hi, he]
    exact (levelFrame_eq_treatedFrame_guide P rank R hc hL hkL hl R₀ done _).symm
  · rw [h1]
    simp only [protocolState]
    refine congrArg₂ (· :: ·) ?_ ?_
    · rw [← eventMain_inl_succ P rank R₀ hc.ε₀_pos ht hB hk hi he]
      exact treatedFrame_completedGuide_eq_levelFrame P rank R hc hL hkL hl R₀ done
        (fun e => by cases e <;> simp) _
    · refine List.map_congr_left fun y hy => ?_
      have hsucc : ∀ y : ProtocolEvent k × RepaintOp,
          y.1 ∈ (eventSchedule k).take (i + 1) ↔ y.1 ∈ (eventSchedule k).take i ∨ y.1 = .inl S :=
        fun y => by rw [take_succ_eventSchedule hi, List.mem_append, List.mem_singleton, he]
      by_cases hyS : y.1 = .inl S
      · obtain ⟨f, rfl⟩ := eq_auxInit_of_mem_auxIndices hy hyS
        have hfz : auxState frozen idle (i + 1) (xs f) = frozen (xs f) := by
          simp only [auxState, (hsucc (xs f)).2 (Or.inr rfl), ite_true]
        change _ = auxState frozen idle (i + 1) (xs f)
        rw [hfz, hfrozen hS f]
        cases f <;> simp [Function.update_of_ne, hinj.ne, xs] <;> rfl
      · have hne : ∀ e, y ≠ xs e := fun e h => hyS (by rw [h])
        rw [Function.update_of_ne (hne _), Function.update_of_ne (hne _),
          Function.update_of_ne (hne _), Function.update_of_ne (hne _)]
        simp only [auxState, hsucc y, hyS, or_false]
        rfl

end TNLean.PEPS.Approximation
