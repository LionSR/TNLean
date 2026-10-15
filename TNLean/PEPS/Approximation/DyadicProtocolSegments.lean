/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolAssembly
import TNLean.PEPS.Approximation.SheetStackSourceBoundedChange

/-!
# The trajectory of the dyadic protocol from its events

The schedule of Proposition 7.1 of the polynomial-PEPS manuscript is a list of events, the
repaintings of the squares and the resizes of the holes at the grid corners, each cut into a
fixed list of changes (`06-geometry.tex`, lines 82–100, 127–131 and 572–583). This file joins the
changes of the events into one trajectory of the sheets, and turns such a trajectory into a
protocol with the bounds of §8.

* `exists_frames_of_segments` : if the sheets pass, during each event, from its starting stack to
  the starting stack of the next event by bounded changes whose participants the event uses, then
  there is one sequence of stacks along the whole schedule whose consecutive stages are joined by
  such changes.
* `exists_isDistributionProtocol_of_hasSourceBoundedChange` : the form of
  `exists_isDistributionProtocol_of_frames` in which each change of the schedule is only known to
  exist.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 12–53, and its proof: the levels and the repaintings (lines 82–100),
  the resizes (lines 127–131), the counts (lines 572–583 and 649–652), the initial copies
  (lines 658–667) and the final reference (lines 669–681).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
  {Party : Type} {Ω : EuclideanSpace ℂ (ι → Fin q)} {ℓ : Layout Party} {ξ : Mem ℓ}
  {r K rs : ℕ} {ε : ℝ}

/-- **Joining the changes of the events.** Let `es` be a list of events, each with a list of
changes `ops e`, and let `b i` be the stack of sheets at the start of the event number `i`. If,
for each event, stacks `seg i j` lead from `b i` to `b (i + 1)` through as many bounded changes as
the event has changes, with participants in `U` of the event, then one sequence of stacks leads
from `b 0` to the stack after the last event, and its change number `t` has its participants in
`U` of the event of the change number `t` of the schedule.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–100, 127–131 and 572–583. -/
theorem exists_frames_of_segments {E α : Type*} (U : E → Set Party) (ops : E → List α) :
    ∀ (es : List E) (b : ℕ → List (Frame pos q Party))
      (seg : ℕ → ℕ → List (Frame pos q Party)), (∀ i, seg i 0 = b i) →
      (∀ i (hi : i < es.length), seg i (ops es[i]).length = b (i + 1)) →
      (∀ i (hi : i < es.length), ∀ j < (ops es[i]).length,
        HasSourceBoundedChange Ω (seg i j) (seg i (j + 1)) ξ (U es[i]) r K rs ε) →
      ∃ st : ℕ → List (Frame pos q Party), st 0 = b 0 ∧
        st (es.flatMap fun e => (ops e).map (e, ·)).length = b es.length ∧
        ∀ t (ht : t < (es.flatMap fun e => (ops e).map (e, ·)).length),
          HasSourceBoundedChange Ω (st t) (st (t + 1)) ξ
            (U ((es.flatMap fun e => (ops e).map (e, ·))[t]).1) r K rs ε
  | [], b, _, _, _, _ => ⟨b, rfl, rfl, fun t ht => absurd ht (by simp)⟩
  | e :: es, b, seg, h0, hm, hstep => by
    obtain ⟨st', h0', hm', hstep'⟩ := exists_frames_of_segments U ops es (fun i => b (i + 1))
      (fun i => seg (i + 1)) (fun i => h0 (i + 1)) (fun i hi => hm (i + 1) (by simpa using hi))
      (fun i hi => hstep (i + 1) (by simpa using hi))
    set m := (ops e).length with hm_def
    have hseg : seg 0 m = st' 0 := by rw [h0']; exact hm 0 (by simp)
    let st : ℕ → List (Frame pos q Party) := fun t => if t ≤ m then seg 0 t else st' (t - m)
    have hst : ∀ t, m ≤ t → st t = st' (t - m) := fun t ht => by
      rcases ht.lt_or_eq with ht | rfl
      · simp only [st, show ¬t ≤ m by omega, ite_false]
      · simp only [st, le_refl, ite_true, Nat.sub_self, hseg]
    have hlen : ((e :: es).flatMap fun e => (ops e).map (e, ·)).length =
        m + (es.flatMap fun e => (ops e).map (e, ·)).length := by
      simp [List.flatMap_cons, hm_def]
    refine ⟨st, by simp only [st, Nat.zero_le, ite_true, h0], ?_, fun t ht => ?_⟩
    · rw [hlen, hst _ (Nat.le_add_right _ _), Nat.add_sub_cancel_left, hm']
      rfl
    · rw [hlen] at ht
      simp only [List.flatMap_cons]
      rcases Nat.lt_or_ge t m with htm | htm
      · rw [List.getElem_append_left (by simpa using htm)]
        simp only [List.getElem_map]
        have h1 : st t = seg 0 t := by simp only [st, htm.le, ite_true]
        have h2 : st (t + 1) = seg 0 (t + 1) := by simp only [st, show t + 1 ≤ m from htm, ite_true]
        rw [h1, h2]
        exact hstep 0 (by simp) t htm
      · rw [List.getElem_append_right (by simpa using htm)]
        rw [hst t htm, hst (t + 1) (by omega), show t + 1 - m = t - m + 1 by omega]
        simpa [hm_def] using hstep' (t - m) (by omega)

/-- **A protocol from the existence of the changes.** The form of
`exists_isDistributionProtocol_of_frames` in which each change of the schedule is a bounded change
of the sheets with at most `rs` pair sources in each monomial, given by its existence.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, `06-geometry.tex`, lines 12–53,
and its proof, lines 572–681; Theorem 5.2, item 3, `04-compression.tex`, lines 143–147. -/
theorem exists_isDistributionProtocol_of_hasSourceBoundedChange {L k : ℕ} (hL : 2 ≤ L)
    (hkL : L ≤ 2 ^ k) (hk2 : 2 ^ k < 2 * L) (large : DyadicSquare k → Bool)
    {Ω : StateSpace L q} (hΩ : ‖Ω‖ = 1)
    (st : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)))
    (holder : Frame (cellCenterPos L) q (ProtocolParty k) → ProtocolParty k)
    (hraw : ∀ F ∈ st 0, F.holes = []) (hown : ∀ F ∈ st 0, ∀ x, F.owner x = holder F)
    {kK : ℕ} {C : ℝ}
    (hc : ∀ t (ht : t < (protocolSchedule k large).length),
      HasSourceBoundedChange Ω (st t) (st (t + 1)) (ℓ := []) (1 : ℂ)
        {p | EventUses ((protocolSchedule k large)[t]).1 p} r K rs ε)
    (M : Frame (cellCenterPos L) q (ProtocolParty k))
    (Fs : List (Frame (cellCenterPos L) q (ProtocolParty k)))
    (hfin : st (protocolSchedule k large).length = M :: Fs)
    (hMown : ∀ v, M.owner v = .inl (unitSquare hkL v)) (hM : ∀ h ∈ M.holes, h.patch.outer = ∅)
    (hε : ∀ F ∈ Fs, ∀ h ∈ F.holes, ‖act h.patch.proj Ω - Ω‖ ≤ ((L : ℝ) ^ 60)⁻¹)
    (hholes : (Fs.map fun F => (F.holes.length : ℝ)).sum ≤ C * (L : ℝ) ^ 3)
    (hC : 5042 ≤ C) (hK : (K : ℝ) ≤ C * (L : ℝ) ^ kK) (hεC : ε ≤ C / (L : ℝ) ^ 20) :
    ∃ D : DyadicProtocol L q (ProtocolParty k),
      D.IsDistributionProtocol Ω C (64 * 189) kK r ∧
        ∀ t < D.changes, (D.step t).IsSourceBounded rs := by
  classical
  set n := (protocolSchedule k large).length with hn
  set st' : ℕ → List (Frame (cellCenterPos L) q (ProtocolParty k)) := fun t => st (min t n)
  have hst' : ∀ t ≤ n, st' t = st t := fun t ht => by simp only [st', min_eq_left ht]
  have hall : ∀ t, HasSourceBoundedChange Ω (st' t) (st' (t + 1)) (ℓ := []) (1 : ℂ)
      (if h : t < n then {p | EventUses ((protocolSchedule k large)[t]).1 p} else ∅) r K rs
      (max ε 0) := fun t => by
    by_cases h : t < n
    · rw [hst' t h.le, hst' (t + 1) h]
      simp only [h, dite_true]
      exact (hc t h).mono le_rfl le_rfl le_rfl le_rfl (le_max_left _ _)
    · have h1 : st' t = st n := by simp only [st', min_eq_right (not_lt.1 h)]
      have h2 : st' (t + 1) = st n := by simp only [st', min_eq_right (by omega : n ≤ t + 1)]
      rw [h1, h2]
      exact hasSourceBoundedChange_refl _ _ _ _ _ _ (le_max_right _ _)
  refine exists_isDistributionProtocol_of_frames hL hkL hk2 large hΩ st' holder
    (by simpa [st'] using hraw) (by simpa [st'] using hown) (fun t => (hall t).choose)
    (fun t ht => ?_) (fun t ht => ?_) M Fs (by rw [hst' n le_rfl]; exact hfin) hMown hM hε
    hholes hC hK (max_le hεC (by positivity))
  · have ht' : t < n := ht
    exact (hall t).choose_spec.1.mono (fun p hp => by simpa [ht'] using hp) le_rfl le_rfl le_rfl
  · exact (hall t).choose_spec.2

end TNLean.PEPS.Approximation
