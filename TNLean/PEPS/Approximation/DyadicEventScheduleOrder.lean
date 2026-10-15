/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicProtocolSchedule

/-!
# The order of the events of the dyadic protocol

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript passes through the levels
`n = N / 2, …, 1`; entering a level it resizes the holes at the grid corners, and then it repaints
the squares of the level (`06-geometry.tex`, lines 82–100 and 127–131). The list
`eventSchedule k` orders the events by their rank, `2 (k - j)` for the resizes entering level
`2 ^ j` and `2 (k - j) + 1` for the repaintings of that level. This file proves the consequences of
this order used to follow the main guide along the schedule, for `k ≥ 1`:

* every rank from `2` to `2 k + 1` is the rank of some event (`exists_isScheduled_rank`), and the
  ranks of the events lie in that range (`two_le_rank`, `rank_le`);
* consecutive events have equal or consecutive ranks (`rank_getElem_succ_le`), the first event has
  rank `2` and the last rank `2 k + 1`;
* the events before the event number `i` are those of smaller rank and some of its own rank
  (`mem_take_of_rank_lt`, `rank_le_of_mem_take`).

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`, lines 82–100 and
  127–131.
-/

namespace TNLean.PEPS.Approximation

open Finset

variable {k : ℕ}

namespace ProtocolEvent

/-- A scheduled event has rank at least `2`. -/
theorem two_le_rank {e : ProtocolEvent k} (he : e.IsScheduled) : 2 ≤ e.rank := by
  rcases e with S | J
  · change (S.1 : ℕ) < k at he
    simp only [rank, level, Sum.elim_inl]
    omega
  · change 0 < (J.1 : ℕ) at he
    have := J.1.isLt
    simp only [rank, level, Sum.elim_inr]
    omega

/-- A scheduled event has rank at most `2 k + 1`. -/
theorem rank_le (e : ProtocolEvent k) : e.rank ≤ 2 * k + 1 := by
  rcases e with S | J <;> simp only [rank, level, Sum.elim_inl, Sum.elim_inr] <;> omega

/-- The rank of a repainting is odd and that of a resize is even. -/
theorem rank_inl (S : DyadicSquare k) :
    ProtocolEvent.rank (Sum.inl S : ProtocolEvent k) = 2 * (k - S.1) + 1 :=
  rfl

theorem rank_inr (J : DyadicJunction k) :
    ProtocolEvent.rank (Sum.inr J : ProtocolEvent k) = 2 * (k - ((J.1 : ℕ) - 1)) := by
  simp [rank, level]

end ProtocolEvent

/-- **Every rank occurs.** For `k ≥ 1`, every rank from `2` to `2 k + 1` is the rank of a scheduled
event: a resize at the origin for an even rank, a repainting of the square at the origin for an
odd rank.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 82–87 and 127–128. -/
theorem exists_isScheduled_rank {r : ℕ} (h2 : 2 ≤ r) (hr : r ≤ 2 * k + 1) :
    ∃ e : ProtocolEvent k, e.IsScheduled ∧ e.rank = r := by
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' r
  · refine ⟨.inr ⟨⟨k - m + 1, by omega⟩, ⟨0, by positivity⟩, ⟨0, by positivity⟩⟩, ?_, ?_⟩
    · change 0 < k - m + 1; omega
    · rw [ProtocolEvent.rank_inr]; simp only; omega
  · refine ⟨.inl ⟨⟨k - m, by omega⟩, ⟨0, by positivity⟩, ⟨0, by positivity⟩⟩, ?_, ?_⟩
    · change k - m < k; omega
    · rw [ProtocolEvent.rank_inl]; simp only; omega

theorem rank_getElem_le_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < (eventSchedule k).length) :
    ((eventSchedule k)[i]'(hij.trans_lt hj)).rank ≤ ((eventSchedule k)[j]).rank := by
  rcases hij.lt_or_eq with h | rfl
  · exact List.pairwise_iff_getElem.1 (pairwise_rank_eventSchedule k) i j _ hj h
  · exact le_rfl

theorem isScheduled_getElem {i : ℕ} (hi : i < (eventSchedule k).length) :
    ((eventSchedule k)[i]).IsScheduled :=
  mem_eventSchedule.1 (List.getElem_mem hi)

/-- **Events of a smaller rank come earlier.** A scheduled event of rank smaller than that of the
event number `i` is among the first `i` events. -/
theorem mem_take_of_rank_lt {i : ℕ} (hi : i < (eventSchedule k).length) {e : ProtocolEvent k}
    (he : e.IsScheduled) (hr : e.rank < ((eventSchedule k)[i]).rank) :
    e ∈ (eventSchedule k).take i := by
  obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.1 (mem_eventSchedule.2 he)
  rcases Nat.lt_or_ge m i with h | h
  · exact List.mem_take_iff_getElem.2 ⟨m, by omega, rfl⟩
  · exact absurd (rank_getElem_le_of_le h hm) (not_le.2 hr)

/-- **Earlier events have no larger rank.** -/
theorem rank_le_of_mem_take {i : ℕ} (hi : i < (eventSchedule k).length) {e : ProtocolEvent k}
    (he : e ∈ (eventSchedule k).take i) : e.rank ≤ ((eventSchedule k)[i]).rank := by
  obtain ⟨m, hm, rfl⟩ := List.mem_take_iff_getElem.1 he
  exact rank_getElem_le_of_le (by omega) hi

/-- **Consecutive events have equal or consecutive ranks.** -/
theorem rank_getElem_succ_le {i : ℕ} (hi : i + 1 < (eventSchedule k).length) :
    ((eventSchedule k)[i + 1]).rank ≤ ((eventSchedule k)[i]).rank + 1 := by
  by_contra! h
  have h2 := ProtocolEvent.two_le_rank (isScheduled_getElem (k := k) (i := i) (by omega))
  obtain ⟨e, he, her⟩ := exists_isScheduled_rank (k := k)
    (r := ((eventSchedule k)[i]).rank + 1) (by omega)
    (by have := ProtocolEvent.rank_le ((eventSchedule k)[i + 1]); omega)
  have hmem := mem_take_of_rank_lt hi he (by omega)
  obtain ⟨m, hm, hme⟩ := List.mem_take_iff_getElem.1 hmem
  have := rank_getElem_le_of_le (k := k) (i := m) (j := i) (by omega) (by omega)
  rw [hme] at this
  omega

end TNLean.PEPS.Approximation
