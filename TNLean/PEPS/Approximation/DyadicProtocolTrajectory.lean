/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolChanges

/-!
# Bounded changes along the schedule of the dyadic protocol

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript performs the changes of its
schedule one after the other. If every change is a bounded change of the sheets, in the sense of
`EncodedFrame.HasBoundedChange`, the changes can be chosen once and for all
(`EncodedFrame.exists_steps_of_hasBoundedChange`), and two consequences of item 2 and item 4 of
the proposition follow from the counts of the schedule:

* the actual vector after the changes stays within `5040 C L⁻¹⁷` of the reference vector of the
  sheets, when each change has error at most `C L⁻²⁰` and `2 ^ k < 2 L`, because the schedule has
  at most `5040 L³` changes (`norm_trajectory_sub_stackVec_le`);
* every party participates in at most `64 · 189` nonprivate gates over the whole schedule, when
  each change has at most one nonprivate gate whose participants are parties its event uses
  (`card_participation_le_of_eventUses`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`, items 2 and
  4, `06-geometry.tex`, lines 25–41, and lines 572–631 (bounded gates, the precision of each
  change and the lifetime participation); the telescoping of §8.1, `07-assembly.tex`,
  lines 33–40, as in `norm_protocol_sub_reference_le`.
-/

noncomputable section

open Finset

namespace TNLean.PEPS

namespace EncodedFrame

open TNLean.Lattice.PartyCircuit

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {Party : Type}
  {pos : ι → ℝ × ℝ}

/-- **Choosing the changes.** If each pair of consecutive stages of a sequence of lists of frames
is joined by a bounded change, there is one original circuit for each change, with these bounds.
-/
theorem exists_steps_of_hasBoundedChange {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (st : ℕ → List (Frame pos q Party)) {ℓ : Layout Party} {ξ : Mem ℓ} (S : ℕ → Set Party)
    {r K : ℕ} {ε : ℝ} (h : ∀ t, HasBoundedChange Ω (st t) (st (t + 1)) ξ (S t) r K ε) :
    ∃ step : (t : ℕ) → OriginalCircuit (stackRegs (st t) ℓ) (stackRegs (st (t + 1)) ℓ),
      ∀ t, (step t).IsBoundedChange (S t) r K ε (stackVec Ω (st t) ξ)
        (stackVec Ω (st (t + 1)) ξ) :=
  ⟨fun t => (h t).choose, fun t => (h t).choose_spec⟩

end EncodedFrame

namespace Approximation

open EncodedFrame TNLean.Lattice.PartyCircuit

/-- **The accumulated error of the schedule.** Let `2 ^ k < 2 L` with `L ≥ 1`, let
`n` be at most the number of changes of the schedule, and let each of the first `n` changes
`step t` take the reference vector of the sheets within `C L⁻²⁰` of the next one. Then the
actual vector `x n`, started at the initial reference vector, stays within `5040 C L⁻¹⁷` of the
reference vector.

Polynomial-PEPS manuscript, Proposition 7.1, items 2 and 4, `06-geometry.tex`, lines 25 and
39–41, and the telescoping of §8.1, `07-assembly.tex`, lines 33–40. -/
theorem norm_trajectory_sub_stackVec_le {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}
    [NeZero q] {Party : Type} {pos : ι → ℝ × ℝ} {Ω : EuclideanSpace ℂ (ι → Fin q)}
    {k L : ℕ} (hk : 2 ^ k < 2 * L) (hL : 1 ≤ L) (large : DyadicSquare k → Bool) {n : ℕ}
    (hn : n ≤ (protocolSchedule k large).length) (st : ℕ → List (Frame pos q Party))
    {ℓ : Layout Party} {ξ : Mem ℓ}
    (step : (t : ℕ) → OriginalCircuit (stackRegs (st t) ℓ) (stackRegs (st (t + 1)) ℓ))
    {C : ℝ} (hC : 0 ≤ C)
    (hstep : ∀ t < n, ‖(step t).eval (stackVec Ω (st t) ξ) - stackVec Ω (st (t + 1)) ξ‖ ≤
      C / (L : ℝ) ^ 20)
    (x : (t : ℕ) → Mem (stackRegs (st t) ℓ)) (hx₀ : x 0 = stackVec Ω (st 0) ξ)
    (hx : ∀ t < n, x (t + 1) = (step t).eval (x t)) :
    ‖x n - stackVec Ω (st n) ξ‖ ≤ 5040 * C / (L : ℝ) ^ 17 := by
  have hn' : (n : ℝ) ≤ 5040 * (L : ℝ) ^ 3 :=
    (Nat.cast_le.2 hn).trans (length_protocolSchedule_le_cube hk large)
  have key : ∀ m ≤ n, ‖x m - stackVec Ω (st m) ξ‖ ≤ m * (C / (L : ℝ) ^ 20) := by
    intro m
    induction m with
    | zero => intro; simp [hx₀]
    | succ m ih =>
      intro hm
      have hc : ‖(step m).eval (x m - stackVec Ω (st m) ξ)‖ ≤ ‖x m - stackVec Ω (st m) ξ‖ :=
        (step m).norm_eval_le_norm _
      rw [hx m hm, ← sub_add_sub_cancel _ ((step m).eval (stackVec Ω (st m) ξ)), ← map_sub]
      refine (norm_add_le _ _).trans ?_
      push_cast
      linarith [ih (Nat.le_of_succ_le hm), hstep m hm]
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  refine (key n le_rfl).trans ?_
  calc (n : ℝ) * (C / (L : ℝ) ^ 20) ≤ 5040 * (L : ℝ) ^ 3 * (C / (L : ℝ) ^ 20) :=
        mul_le_mul_of_nonneg_right hn' (by positivity)
    _ = 5040 * C / (L : ℝ) ^ 17 := by field_simp

/-- **Lifetime participation along the schedule.** Let each change `step t` of the schedule have
at most one nonprivate gate, whose participants are parties used by the event of the change.
Then every party participates in at most `64 · 189` nonprivate gates of the schedule.

Polynomial-PEPS manuscript, Proposition 7.1 `prop:protocol`, item 2, `06-geometry.tex`,
lines 31–32, and the lifetime argument, lines 572–631. -/
theorem card_participation_le_of_eventUses {k : ℕ} {large : DyadicSquare k → Bool}
    (lay : ℕ → Layout (ProtocolParty k))
    (step : (t : ℕ) → OriginalCircuit (lay t) (lay (t + 1)))
    (hc : ∀ t : Fin (protocolSchedule k large).length, (step t).nonprivateCount ≤ 1)
    (hP : ∀ t : Fin (protocolSchedule k large).length, ∀ g,
      (↑((step t).participants g) : Set (ProtocolParty k)) ⊆
        {p | EventUses ((protocolSchedule k large)[t]).1 p})
    (p : ProtocolParty k) :
    #{γ : Σ t : Fin (protocolSchedule k large).length, (step t).nonprivateLocations |
        p ∈ (step γ.1).participants γ.2} ≤ 64 * (189 * 1) := by
  classical
  refine participation_le_of_schedule (Γ := Σ t : Fin (protocolSchedule k large).length,
    (step t).nonprivateLocations) Sigma.fst (fun t => ?_) p _ fun γ hγ => hP γ.1 γ.2 hγ
  refine (card_le_card (t := univ.image
    (Sigma.mk (β := fun t : Fin (protocolSchedule k large).length =>
      (step t).nonprivateLocations) t)) ?_).trans ?_
  · rintro ⟨t', g⟩ h
    obtain rfl : t' = t := by simpa using h
    exact mem_image_of_mem _ (mem_univ _)
  · exact card_image_le.trans (card_univ.trans_le ((step t).card_nonprivateLocations.trans_le
      (hc t)))

end Approximation

end TNLean.PEPS
