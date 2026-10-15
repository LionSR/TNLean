/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.Fin
import TNLean.PEPS.Approximation.DyadicEdgeBands
import TNLean.PEPS.Approximation.DyadicHierarchyCounts

/-!
# The event and operation schedule of the dyadic distribution protocol

The protocol of Proposition 7.1 (`prop:protocol`) passes from the assignment by `2n`-squares to
the assignment by `n`-squares for `n = N / 2, N / 4, …, 1`, where `N = 2 ^ k` is the padded side
(`06-geometry.tex, lines 82–90`). Entering level `n`, it first resizes the hole at every grid
corner of the guide uniform on `2n`-blocks, one hole at a time (lines 127–131), and then
repaints the `n`-squares one at a time (lines 85–87). This file fixes that schedule and counts
its changes.

* An *event* is a repainting of a non-root square or the resize of a hole at a grid corner of
  scale at least one: an element of `DyadicSquare k ⊕ DyadicJunction k`, the type of events of
  the lifetime count `card_gates_le_of_uses`. The list `eventSchedule k` contains every such
  event once, ordered by descending level, with the resizes of a level before its repaintings.
* An event is cut into changes (`RepaintOp`). A resize is one small-patch rewrite (lines
  529–541). Every grid corner of positive scale gets its resize event, also a corner that is
  not a true vertex of the guide (such as a corner of the root square) and so carries no hole,
  or whose radius does not change; there the resize is the identity change. This keeps the
  events indexed by the junctions. A square with `n ≤ K₀ t` is repainted directly by one
  small-patch rewrite (lines 507–527). A larger square is repainted by the edge construction
  (lines 142–221): the central birth, then along each of the four edges the initialization of
  a fresh auxiliary sheet, three auxiliary births, the lens exchange and four main births or
  deaths. Every bulk
  operation is preceded by the homogenization of each involved sheet at each of its marks and
  followed by its removal, one mark and one sheet at a time (lines 330–339, 495–496): four marks
  for the central birth and two for an edge operation, two sheets for the exchange and one
  otherwise.
* Every event has at most `189` changes, so the schedule has at most `189` times the number of
  squares and junctions, which is at most `5040 L ^ 3` when `2 ^ k < 2 L` (lines 576–579,
  649–652).

Which squares are repainted by the edge construction is a parameter `large`; the source takes
the squares with `n > K₀ t` (line 137). The guides and patch data of each change are those of
`TNLean.PEPS.Approximation.DyadicLevelSchedule`, `TNLean.PEPS.Approximation.DyadicPatchRewriteGates`
and `TNLean.PEPS.Approximation.DyadicLargeRepaintingGates`; this file only orders the changes.

## Main results

* `TNLean.PEPS.Approximation.eventSchedule`, `TNLean.PEPS.Approximation.mem_eventSchedule`,
  `TNLean.PEPS.Approximation.nodup_eventSchedule`,
  `TNLean.PEPS.Approximation.pairwise_rank_eventSchedule`: the events in order.
* `TNLean.PEPS.Approximation.protocolSchedule`: the changes in order.
* `TNLean.PEPS.Approximation.length_eventOps_le`: at most `189` changes per event.
* `TNLean.PEPS.Approximation.length_protocolSchedule_le_cube`: at most `5040 L ^ 3` changes.
* `TNLean.PEPS.Approximation.card_filter_event_le`: at most `189` changes of any one event.

## References

* Polynomial-PEPS manuscript (Sept 24 2026), §7, `06-geometry.tex`: the repainting by levels
  (lines 82–100), the resizing of holes (lines 127–131), the edge construction (lines 142–221),
  the point treatment (lines 330–339, 481–505), direct repaintings and resizes (lines 507–541),
  and the counts (lines 572–579, 649–656).
-/

namespace TNLean.PEPS.Approximation

open Finset

/-! ### Events -/

/-- An event of the protocol on the hierarchy of `[0, 2 ^ k] ^ 2`: the repainting of a square or
the resize of the hole at a grid corner.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–90, 127–131`. -/
abbrev ProtocolEvent (k : ℕ) : Type := DyadicSquare k ⊕ DyadicJunction k

namespace ProtocolEvent

variable {k : ℕ}

/-- The level `j` at which an event is performed, for level side `2 ^ j`: a square of scale `j`
is repainted at level `2 ^ j`, and the holes at the grid corners of scale `j + 1` are resized on
entering level `2 ^ j`.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–87, 127–131,
529–533`. -/
def level : ProtocolEvent k → ℕ
  | .inl S => S.1
  | .inr J => J.1 - 1

/-- The events performed by the protocol: the repaintings of the non-root squares, and the resizes
at the grid corners of positive scale.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–84, 127–131`:
the levels are `n = N / 2, …, 1`. -/
def IsScheduled : ProtocolEvent k → Prop
  | .inl S => (S.1 : ℕ) < k
  | .inr J => 0 < (J.1 : ℕ)

instance : DecidablePred (IsScheduled (k := k)) := fun e => by
  cases e <;> unfold IsScheduled <;> infer_instance

/-- The position of an event in the schedule: levels in descending order, and within a level the
resizes before the repaintings.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–87, 127–128`:
“Before entering a new hierarchy level, resize existing main-sheet holes”. -/
def rank (e : ProtocolEvent k) : ℕ := 2 * (k - e.level) + Sum.elim (fun _ => 1) (fun _ => 0) e

end ProtocolEvent

/-- The events of the protocol in the order in which they are performed. The order among the
events of one rank, the blocks of one level, is not prescribed by the source.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–87, 127–131`. -/
noncomputable def eventSchedule (k : ℕ) : List (ProtocolEvent k) :=
  ((univ.filter ProtocolEvent.IsScheduled).toList).mergeSort fun a b => a.rank ≤ b.rank

/-- An event occurs in the schedule exactly when it is performed. -/
@[simp]
theorem mem_eventSchedule {k : ℕ} {e : ProtocolEvent k} : e ∈ eventSchedule k ↔ e.IsScheduled := by
  simp [eventSchedule]

/-- Every event occurs in the schedule at most once. -/
theorem nodup_eventSchedule (k : ℕ) : (eventSchedule k).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.2 (nodup_toList _)

/-- The schedule is ordered by rank: descending level, and resizes before repaintings within a
level. -/
theorem pairwise_rank_eventSchedule (k : ℕ) :
    (eventSchedule k).Pairwise fun a b => a.rank ≤ b.rank := by
  have h := List.pairwise_mergeSort (le := fun a b : ProtocolEvent k => decide (a.rank ≤ b.rank))
    (fun a b c hab hbc => by simp only [decide_eq_true_eq] at *; omega)
    (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
    (univ.filter ProtocolEvent.IsScheduled).toList
  simpa [eventSchedule] using h

/-- The schedule has at most one event for each square and each junction. -/
theorem length_eventSchedule_le (k : ℕ) :
    (eventSchedule k).length ≤ Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k) :=
  by
  rw [eventSchedule, List.length_mergeSort, length_toList, ← Fintype.card_sum]
  exact card_filter_le _ _

/-! ### Changes -/

/-- A bulk operation of the edge construction of a large-scale repainting: the central birth, the
three births on the auxiliary sheet of an edge, the lens exchange of an edge, and the four deaths
and births on the main sheet of an edge.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 159–221`. -/
inductive BulkOp
  | central
  | auxBirth (e : SquareEdge) (i : Fin 3)
  | exchange (e : SquareEdge)
  | mainStep (e : SquareEdge) (i : Fin 4)
  deriving DecidableEq

namespace BulkOp

/-- The number of marks of a bulk operation: the four corners for the central birth, the two
endpoints of the edge otherwise.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 163–166, 174`. -/
def marks : BulkOp → ℕ
  | central => 4
  | _ => 2

/-- The number of sheets of a bulk operation: two for the exchange, one otherwise.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 330–335`. -/
def sheets : BulkOp → ℕ
  | exchange _ => 2
  | _ => 1

end BulkOp

/-- A change of the protocol: the initialization of the auxiliary sheet of an edge, the
homogenization of one sheet at one mark of a bulk operation, the bulk operation itself, the
removal of that homogenization, a direct repainting, or the resize of one hole.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 185–186, 328–339,
507–541`. -/
inductive RepaintOp
  | auxInit (e : SquareEdge)
  | treat (o : BulkOp) (m : Fin 4) (σ : Fin 2)
  | bulk (o : BulkOp)
  | untreat (o : BulkOp) (m : Fin 4) (σ : Fin 2)
  | direct
  | resize
  deriving DecidableEq

/-- The pairs of a mark and a sheet treated around a bulk operation, one mark and one sheet at a
time.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 330–335, 495–496`. -/
def BulkOp.treated (o : BulkOp) : List (Fin 4 × Fin 2) :=
  (([0, 1, 2, 3] : List (Fin 4)).filter fun m : Fin 4 => decide ((m : ℕ) < o.marks)).flatMap
    fun m => (([0, 1] : List (Fin 2)).filter fun σ : Fin 2 => decide ((σ : ℕ) < o.sheets)).map
      (m, ·)

/-- The changes of one bulk operation: homogenize, operate, remove the homogenization.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 330–339`. -/
def BulkOp.ops (o : BulkOp) : List RepaintOp :=
  o.treated.map (fun p => .treat o p.1 p.2) ++ [.bulk o] ++
    o.treated.map fun p => .untreat o p.1 p.2

/-- The four edges, in the order in which they are processed. -/
def SquareEdge.list : List SquareEdge := [.bottom, .right, .top, .left]

/-- The changes along one edge: a fresh auxiliary sheet, its three births, the lens exchange, and
the four main deaths and births.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 183–221`. -/
def edgeOps (e : SquareEdge) : List RepaintOp :=
  .auxInit e :: (([0, 1, 2] : List (Fin 3)).flatMap fun i => (BulkOp.auxBirth e i).ops) ++
    (BulkOp.exchange e).ops ++
      ([0, 1, 2, 3] : List (Fin 4)).flatMap fun i => (BulkOp.mainStep e i).ops

/-- The changes of a large-scale repainting: the central birth, then the four edges.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 159–166, 183–221`. -/
def largeRepaintingOps : List RepaintOp :=
  BulkOp.central.ops ++ SquareEdge.list.flatMap edgeOps

/-- A bulk operation with `m` marks on `σ` sheets has `2 m σ + 1` changes. -/
theorem BulkOp.length_ops (o : BulkOp) : o.ops.length = 2 * (o.marks * o.sheets) + 1 := by
  have h : o.treated.length = o.marks * o.sheets := by cases o <;> rfl
  simp only [ops, List.length_append, List.length_map, List.length_singleton, h]
  ring

/-- An edge has `45` changes. -/
theorem length_edgeOps (e : SquareEdge) : (edgeOps e).length = 45 := by
  simp [edgeOps, BulkOp.length_ops, BulkOp.marks, BulkOp.sheets]

/-- A large-scale repainting has `189` changes. -/
theorem length_largeRepaintingOps : largeRepaintingOps.length = 189 := by
  simp [largeRepaintingOps, length_edgeOps, BulkOp.length_ops, BulkOp.marks, BulkOp.sheets,
    SquareEdge.list]

/-- The changes of an event: the large-scale repainting or the direct repainting of a square, and
the single resize at a junction. At a junction that carries no hole, or whose radius does not
change, the resize is the identity change.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 137–140, 507–541`. -/
def eventOps {k : ℕ} (large : DyadicSquare k → Bool) : ProtocolEvent k → List RepaintOp
  | .inl S => if large S then largeRepaintingOps else [.direct]
  | .inr _ => [.resize]

/-- **Changes per event.** Every event has at most `189` changes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 572–577`: “each
repainting, and each junction resize, uses a uniformly bounded number of linked gates and
parties.” -/
theorem length_eventOps_le {k : ℕ} (large : DyadicSquare k → Bool) (e : ProtocolEvent k) :
    (eventOps large e).length ≤ 189 := by
  rcases e with S | J
  · simp only [eventOps]
    split_ifs <;> simp [length_largeRepaintingOps]
  · simp [eventOps]

/-- The changes of the protocol in order, each with its event.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 82–100, 127–131,
142–221, 328–339, 507–541`. -/
noncomputable def protocolSchedule (k : ℕ) (large : DyadicSquare k → Bool) :
    List (ProtocolEvent k × RepaintOp) :=
  (eventSchedule k).flatMap fun e => (eventOps large e).map (e, ·)

/-! ### Counts -/

/-- The schedule has at most `189` changes for each square and each junction. -/
theorem length_protocolSchedule_le (k : ℕ) (large : DyadicSquare k → Bool) :
    (protocolSchedule k large).length ≤
      189 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)) := by
  rw [protocolSchedule, List.length_flatMap]
  refine (List.sum_le_length_nsmul _ 189 fun n hn => ?_).trans ?_
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hn
    simpa using length_eventOps_le large e
  · rw [List.length_map, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ (length_eventSchedule_le k)

/-- **At most `C L ³` changes.** With `2 ^ k < 2 L`, the schedule has at most `5040 L ^ 3`
changes.

Source: Polynomial-PEPS manuscript (Sept 24 2026), Proposition 7.1 `prop:protocol`, item 2,
`06-geometry.tex, line 25`, and the counts, lines 649–652. -/
theorem length_protocolSchedule_le_cube {k L : ℕ} (hk : 2 ^ k < 2 * L)
    (large : DyadicSquare k → Bool) :
    ((protocolSchedule k large).length : ℝ) ≤ 5040 * (L : ℝ) ^ 3 := by
  have h1 := length_protocolSchedule_le k large
  have h2 := three_mul_schedule_le_cube hk 189
  have h3 : 3 * (protocolSchedule k large).length ≤ 3 * (5040 * L ^ 3) := by omega
  exact_mod_cast Nat.le_of_mul_le_mul_left h3 (by norm_num)

/-- Positions of a list satisfying a predicate are counted by `List.countP`. -/
private theorem card_filter_getElem_eq_countP {α : Type*} (p : α → Prop) [DecidablePred p] :
    ∀ l : List α, #{t : Fin l.length | p l[t]} = l.countP fun a => decide (p a)
  | [] => by simp
  | a :: l => by
    change #{t : Fin (l.length + 1) | p (a :: l)[t]} = _
    rw [Fin.card_filter_univ_succ', List.countP_cons, add_comm]
    simp only [Fin.getElem_fin, Fin.val_zero, List.getElem_cons_zero, Fin.val_succ,
      List.getElem_cons_succ]
    rw [← card_filter_getElem_eq_countP p l]
    split_ifs <;> simp_all

/-- **Changes of one event.** At most `189` changes of the schedule belong to any one event.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 572–577`. -/
theorem card_filter_event_le (k : ℕ) (large : DyadicSquare k → Bool) (e : ProtocolEvent k) :
    #{t : Fin (protocolSchedule k large).length | ((protocolSchedule k large)[t]).1 = e} ≤
      189 := by
  rw [card_filter_getElem_eq_countP (fun x : ProtocolEvent k × RepaintOp => x.1 = e),
    protocolSchedule, List.countP_flatMap]
  have key : ∀ e', ((eventOps large e').map (e', ·)).countP (fun a => decide (a.1 = e)) =
      if e' = e then (eventOps large e').length else 0 := by
    intro e'
    split_ifs with h
    · subst h; simp
    · simp [h]
  simp only [Function.comp_def, key]
  have hl := nodup_eventSchedule k
  generalize eventSchedule k = l at hl ⊢
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.nodup_cons] at hl
    simp only [List.map_cons, List.sum_cons]
    split_ifs with h
    · subst h
      rw [List.sum_eq_zero fun n hn => ?_, add_zero]
      · exact length_eventOps_le large a
      · obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hn
        simp [ne_of_mem_of_not_mem hb hl.1]
    · simpa using ih hl.2

/-! ### Auxiliary sheets -/

/-- The change initializing an auxiliary sheet.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 185–186`. -/
def RepaintOp.IsAuxInit : RepaintOp → Bool
  | .auxInit _ => true
  | _ => false

/-- A bulk operation initializes no auxiliary sheet. -/
theorem BulkOp.countP_isAuxInit_ops (o : BulkOp) : o.ops.countP RepaintOp.IsAuxInit = 0 := by
  simp [BulkOp.ops, List.countP_eq_zero, RepaintOp.IsAuxInit]

/-- An edge initializes one auxiliary sheet. -/
theorem countP_isAuxInit_edgeOps (e : SquareEdge) : (edgeOps e).countP RepaintOp.IsAuxInit = 1 := by
  simp [edgeOps, List.countP_cons, List.countP_append, BulkOp.countP_isAuxInit_ops,
    RepaintOp.IsAuxInit]

/-- An event initializes at most four auxiliary sheets. -/
theorem countP_isAuxInit_eventOps_le {k : ℕ} (large : DyadicSquare k → Bool)
    (e : ProtocolEvent k) : (eventOps large e).countP RepaintOp.IsAuxInit ≤ 4 := by
  rcases e with S | J
  · simp only [eventOps]
    split_ifs
    · simp [largeRepaintingOps, BulkOp.countP_isAuxInit_ops,
        countP_isAuxInit_edgeOps, SquareEdge.list]
    · simp [RepaintOp.IsAuxInit]
  · simp [eventOps, RepaintOp.IsAuxInit]

/-- **Auxiliary sheets.** The schedule initializes at most four auxiliary sheets for each square
and junction, `O(L ^ 2)` in all.

Source: Polynomial-PEPS manuscript (Sept 24 2026), `06-geometry.tex, lines 576, 649–652`:
“four auxiliary sheets at most per repainting”. -/
theorem countP_isAuxInit_protocolSchedule_le (k : ℕ) (large : DyadicSquare k → Bool) :
    (protocolSchedule k large).countP (fun x => x.2.IsAuxInit) ≤
      4 * (Fintype.card (DyadicSquare k) + Fintype.card (DyadicJunction k)) := by
  rw [protocolSchedule, List.countP_flatMap]
  refine (List.sum_le_length_nsmul _ 4 fun n hn => ?_).trans ?_
  · obtain ⟨e, -, rfl⟩ := List.mem_map.1 hn
    simpa [List.countP_map, Function.comp_def] using countP_isAuxInit_eventOps_le large e
  · rw [List.length_map, smul_eq_mul, mul_comm]
    exact Nat.mul_le_mul_left _ (length_eventSchedule_le k)

end TNLean.PEPS.Approximation
