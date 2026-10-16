/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicLargeRepaintingSegment
import TNLean.PEPS.Approximation.DyadicFrozenHoleCount

/-!
# The frozen auxiliary frames and their owners

In the protocol of Proposition 7.1 of the polynomial-PEPS manuscript every auxiliary sheet belongs
to one edge of one large-scale repainting. Before that repainting it is an idle raw copy held by
the party of the label across its edge, and after it the sheet is retired with the frame left by
the lens exchange (`06-geometry.tex`, lines 183–187, 620–624 and 653–667). This file defines these
frames and owners for the whole schedule and proves that their holes satisfy the frame
constraint, with at most two holes per frozen frame. The total bound `10080 L ^ 3` is obtained
when the protocol is assembled in `DyadicProtocolConsequences`.

* `scheduleIndex` : the position of an event in the schedule;
* `protocolFrozen`, `protocolAuxOwner` : the frozen frame and the idle owner of each auxiliary
  sheet;
* `norm_act_proj_sub_le_of_mem_holes_protocolFrozen` : the frame constraint of the frozen holes;
* `length_holes_protocolFrozen_le` : at most two holes per frozen frame.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the auxiliary sheets
  (lines 183–187), frozen auxiliary frames (lines 620–624) and the counts (lines 649–667).
-/

noncomputable section

open Set

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-- The position of an event in the schedule. -/
def scheduleIndex (e : ProtocolEvent k) : ℕ := (eventSchedule k).idxOf e

/-- The position of the event at index `i` in the schedule is `i`. -/
theorem scheduleIndex_getElem {i : ℕ} (hi : i < (eventSchedule k).length) :
    scheduleIndex (eventSchedule k)[i] = i :=
  (nodup_eventSchedule k).idxOf_getElem i hi

variable {L q : ℕ} {Ω : StateSpace L q} {B₀ C c : ℝ}
  (P : AdaptivePatchSupply (cellCenterPos L) Ω B₀ C c 60 L) (rank : GuideLabel → ℕ)
  {ε₀ t : ℝ} (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * t ∧ ε₀ * t ≤ B₀ * Real.log L)

/-- **The frozen auxiliary frames.** The auxiliary sheet of the edge `e` of the repainting of a
square `S` is frozen with the auxiliary guide of the exchanged auxiliary word, treated at no mark,
at the stage of the level of `S` at which `S` is repainted. Other indices carry the raw frame of
the root party; they do not occur.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 198–214 and 620–624. -/
def protocolFrozen (x : ProtocolEvent k × RepaintOp) :
    Frame (cellCenterPos L) q (ProtocolParty k) :=
  match x with
  | (.inl S, .auxInit e) =>
    if hS : (S.1 : ℕ) < k then
      treatedFrame P rank ⟨S, hS⟩ hr ∅
        ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).nbrLabel e)
        ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).auxGuide e
          (auxWordExchanged
            (repaintBaseline ⟨S, hS⟩ (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).oldLabel
            (repaintBaseline ⟨S, hS⟩ (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).finalLabel
            ((repaintBaseline ⟨S, hS⟩
              (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).nbrLabel e)))
    else Frame.raw fun _ => .inl (rootSquare k)
  | _ => Frame.raw fun _ => .inl (rootSquare k)

/-- **The owners of the idle auxiliary copies.** The auxiliary sheet of the edge `e` of the
repainting of a square `S` is held, until that repainting, by the party of the label across `e`
at the stage at which `S` is repainted.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–187 and 653–667. -/
def protocolAuxOwner (x : ProtocolEvent k × RepaintOp) : ProtocolParty k :=
  match x with
  | (.inl S, .auxInit e) =>
    if hS : (S.1 : ℕ) < k then
      labelParty ⟨S, hS⟩
        ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k (scheduleIndex (.inl S)) S.1)).nbrLabel e)
    else .inl (rootSquare k)
  | _ => .inl (rootSquare k)

/-- At a scheduled repainting, an edge's frozen frame is its exchanged auxiliary guide
treated at no mark at that stage. -/
theorem protocolFrozen_auxInit {i : ℕ} (hi : i < (eventSchedule k).length) {S : DyadicSquare k}
    (he : (eventSchedule k)[i] = .inl S) (hS : (S.1 : ℕ) < k) (e : SquareEdge) :
    protocolFrozen (q := q) P rank hr (.inl S, .auxInit e) =
      treatedFrame P rank ⟨S, hS⟩ hr ∅
        ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).nbrLabel e)
        ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).auxGuide e
          (auxWordExchanged (repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).oldLabel
            (repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).finalLabel
            ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).nbrLabel e))) := by
  have hidx : scheduleIndex (k := k) (.inl S) = i := by rw [← he, scheduleIndex_getElem hi]
  simp only [protocolFrozen, hS, dite_true, hidx]

/-- At a scheduled repainting, the idle copy of an edge is held by the party of the
label across that edge. -/
theorem protocolAuxOwner_auxInit {i : ℕ} (hi : i < (eventSchedule k).length)
    {S : DyadicSquare k} (he : (eventSchedule k)[i] = .inl S) (hS : (S.1 : ℕ) < k)
    (e : SquareEdge) :
    protocolAuxOwner (.inl S, .auxInit e) =
      labelParty ⟨S, hS⟩ ((repaintBaseline ⟨S, hS⟩ (repaintedBlocks k i S.1)).nbrLabel e) := by
  have hidx : scheduleIndex (k := k) (.inl S) = i := by rw [← he, scheduleIndex_getElem hi]
  simp only [protocolAuxOwner, hS, dite_true, hidx]

/-- **The frozen holes satisfy the frame constraint.** Every hole of a frozen frame carries a
supplied patch, whose projector moves `Ω` by at most `L⁻⁶⁰`.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 114–118 and 620–624; Proposition 4.1. -/
theorem norm_act_proj_sub_le_of_mem_holes_protocolFrozen (hL : 1 ≤ L)
    (x : ProtocolEvent k × RepaintOp) {h : Hole (cellCenterPos L) q (ProtocolParty k)}
    (hh : h ∈ (protocolFrozen (q := q) P rank hr x).holes) :
    ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹ := by
  have hpow : (L : ℝ) ^ (-(60 : ℝ)) = ((L : ℝ) ^ 60)⁻¹ := by
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  have key : ∀ {R : RepaintedSquare k} {M : Finset (ℤ × ℤ)} {L₀ : GuideLabel}
      {g : ℝ × ℝ → GuideLabel}, h ∈ (treatedFrame (q := q) P rank R hr M L₀ g).holes →
      ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹ := fun {R M L₀ g} hh => by
    unfold treatedFrame at hh
    split_ifs at hh with hd
    · obtain ⟨z, -, rfl⟩ := mem_holes_guideFrame.1 hh
      rw [← hpow]
      exact norm_act_proj_patchAt_sub_le P z (hr z)
    · simp [Frame.raw] at hh
  rcases x with ⟨S | J, o⟩
  · cases o with
    | auxInit e =>
      dsimp only [protocolFrozen] at hh
      split_ifs at hh
      · exact key hh
      · simp [Frame.raw] at hh
    | _ => simp [protocolFrozen, Frame.raw] at hh
  · simp [protocolFrozen, Frame.raw] at hh

/-- **At most two holes on a frozen frame.** At the constants of the protocol, the frozen frame of
an auxiliary sheet of the schedule carries at most two holes: they sit at true vertices of the
reading of the auxiliary guide with the exchanged word, which has at most two.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 108–112, 620–624 and 653–655. -/
theorem length_holes_protocolFrozen_le {K₀ ν a D : ℝ} (hc : IsProtocolConstants K₀ ε₀ ν a D B₀)
    (hL : 2 ≤ L)
    (hr : ∀ _ : ℝ × ℝ, 0 < ε₀ * (D * Real.log L) ∧ ε₀ * (D * Real.log L) ≤ B₀ * Real.log L)
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ auxIndices k (largeSquare K₀ (D * Real.log L))) :
    (protocolFrozen (q := q) P rank hr x).holes.length ≤ 2 := by
  classical
  obtain ⟨S, hxS, hlS⟩ := exists_large_of_mem_auxIndices hx
  obtain ⟨e, rfl⟩ := eq_auxInit_of_mem_auxIndices hx hxS
  dsimp only [protocolFrozen]
  split_ifs with hS
  · set R : RepaintedSquare k := ⟨S, hS⟩
    set done := repaintedBlocks k (scheduleIndex (.inl S)) S.1
    have hl : K₀ * (D * Real.log L) < (2 : ℝ) ^ (R.1.1 : ℕ) := by
      simpa [largeSquare] using hlS
    obtain ⟨hf, hmem, hd, hF⟩ := treatedFrame_spec (q := q) P rank R hc hL hl done
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨e, _, Or.inr (Or.inr (Or.inr (Or.inr rfl))), rfl⟩))))
      ∅ ((repaintBaseline R done).nbrLabel e)
    rw [hF, length_holes_guideFrame]
    set G := shiftGuide (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index)
      ((repaintBaseline R done).auxGuide e (auxWordExchanged (repaintBaseline R done).oldLabel
        (repaintBaseline R done).finalLabel ((repaintBaseline R done).nbrLabel e)))
    have hG : homogenize (⋃ Q ∈ (∅ : Finset (ℤ × ℤ)),
        Metric.ball (blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) Q) (D * Real.log L))
        ((repaintBaseline R done).nbrLabel e) G = G := by
      funext p
      simp [homogenize]
    rw [hG] at hf
    set d := blockCorner ((2 : ℝ) ^ (R.1.1 : ℕ)) R.1.index
    set p₁ := e.point (repaintBaseline R done).n 0 0 + d
    set p₂ := e.point (repaintBaseline R done).n (repaintBaseline R done).n 0 + d
    have hsub : treatedVertices k R.1.1 (D * Real.log L) ∅ (treatedGuide R.1.1 R.1.index
        (D * Real.log L) ∅ ((repaintBaseline R done).nbrLabel e)
        ((repaintBaseline R done).auxGuide e (auxWordExchanged (repaintBaseline R done).oldLabel
          (repaintBaseline R done).finalLabel ((repaintBaseline R done).nbrLabel e)))) ⊆
        {p₁, p₂} := fun z hz => by
      have h1 := isTrueVertex_shiftGuide_iff.1 (hf.isTrueVertex ((hmem z).1 hz))
      have h2 := (repaintBaseline R done).isTrueVertex_auxGuide_subset e
        (W := auxWordExchanged (repaintBaseline R done).oldLabel
          (repaintBaseline R done).finalLabel ((repaintBaseline R done).nbrLabel e))
        (by simp [auxWords]) h1
      rcases h2 with h2 | h2
      · exact Finset.mem_insert.2 (Or.inl (by rw [← sub_add_cancel z d, h2]))
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
          (by rw [← sub_add_cancel z d, h2])))
    exact (Finset.card_le_card hsub).trans Finset.card_le_two
  · simp [Frame.raw]

end TNLean.PEPS.Approximation
