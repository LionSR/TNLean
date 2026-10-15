/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolSegments
import TNLean.PEPS.Approximation.DyadicProtocolStateTransitions

/-!
# The dyadic protocol from its large-scale repaintings

The memory of the protocol of Proposition 7.1 of the polynomial-PEPS manuscript is the main frame
followed by one copy of `Ω` for each change of the schedule that initializes an auxiliary sheet:
idle before the repainting that uses it and frozen after it (`06-geometry.tex`, lines 183–186 and
653–667). The resizes and the direct repaintings change only the main frame, by one small-patch
rewrite each (`TNLean.PEPS.Approximation.DyadicLevelEvents`). This file assembles the protocol
from these changes and from the changes of the large-scale repaintings, which are hypotheses here:

* `auxIndices`, `auxState`, `protocolState` : the auxiliary indices, the auxiliary frames before
  each event, and the memory before each event;
* `exists_isDistributionProtocol_of_largeRepaintings` : if every large-scale repainting passes the
  memory from its state before to its state after by `189` bounded changes whose participants the
  repainting uses, and the frozen frames satisfy the frame constraint and carry at most `C L³`
  holes, then there is a protocol with the bounds of §8.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Proposition 7.1 `prop:protocol`,
  `06-geometry.tex`, lines 12–53, and its proof, lines 82–241, 507–541 and 572–681.
-/

noncomputable section

open Set

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

variable {k : ℕ}

/-! ### The auxiliary sheets -/

/-- The auxiliary indices: the changes of the schedule that initialize an auxiliary sheet.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186 and 649–652. -/
abbrev auxIndices (k : ℕ) (large : DyadicSquare k → Bool) : List (ProtocolEvent k × RepaintOp) :=
  (protocolSchedule k large).filter fun x => x.2.IsAuxInit

/-- An auxiliary index belongs to a large-scale repainting. -/
theorem exists_large_of_mem_auxIndices {large : DyadicSquare k → Bool}
    {x : ProtocolEvent k × RepaintOp} (hx : x ∈ auxIndices k large) :
    ∃ S, x.1 = .inl S ∧ large S = true := by
  obtain ⟨hx, hax⟩ := List.mem_filter.1 hx
  obtain ⟨e, -, hx⟩ := List.mem_flatMap.1 hx
  obtain ⟨o, ho, rfl⟩ := List.mem_map.1 hx
  rcases e with S | J
  · refine ⟨S, rfl, ?_⟩
    by_contra hS
    simp only [eventOps, hS, ite_false, List.mem_singleton] at ho
    subst ho
    simp [RepaintOp.IsAuxInit] at hax
  · simp only [eventOps, List.mem_singleton] at ho
    subst ho
    simp [RepaintOp.IsAuxInit] at hax

open Classical in
/-- **The auxiliary frames before an event.** Before the event number `i`, the auxiliary sheet of
the index `x` is frozen if its repainting is among the first `i` events, and idle otherwise.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 183–186 and 653–667. -/
def auxState {X : Type*} (frozen idle : ProtocolEvent k × RepaintOp → X) (i : ℕ)
    (x : ProtocolEvent k × RepaintOp) : X :=
  if x.1 ∈ (eventSchedule k).take i then frozen x else idle x

/-- An event other than a large-scale repainting freezes no auxiliary sheet. -/
theorem auxState_succ {X : Type*} {large : DyadicSquare k → Bool}
    (frozen idle : ProtocolEvent k × RepaintOp → X) {i : ℕ}
    (hi : i < (eventSchedule k).length)
    (hne : ∀ S, (eventSchedule k)[i] = .inl S → large S = false) :
    (auxIndices k large).map (auxState frozen idle (i + 1)) =
      (auxIndices k large).map (auxState frozen idle i) := by
  classical
  refine List.map_congr_left fun x hx => ?_
  obtain ⟨S, hS, hlS⟩ := exists_large_of_mem_auxIndices hx
  have hne' : x.1 ≠ (eventSchedule k)[i] := by
    intro h
    rw [hS] at h
    have := hne S h.symm
    rw [hlS] at this
    exact Bool.noConfusion this
  simp only [auxState, take_succ_eventSchedule hi, List.mem_append, List.mem_singleton, hne',
    or_false]

end TNLean.PEPS.Approximation
