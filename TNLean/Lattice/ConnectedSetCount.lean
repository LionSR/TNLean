/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting

/-!
# Counting connected vertex sets in a graph of bounded degree

The cluster expansion of Hastings, *Solving gapped Hamiltonians locally*
(arXiv:cond-mat/0508554v3, `proj3new.tex`, lines 1227–1254, ending at
eq. `perc2`) uses that the number of clusters of `n` sites on a regular lattice
of `N` sites is at most `N x ^ n` for some constant `x`, the classical count of
lattice animals (Klarner, Canad. J. Math. 19 (1967) 851). This file proves the
count for an arbitrary finite simple graph of maximum degree at most `Δ`: at
most `Δ ^ (2 (n - 1))` connected vertex sets of size `n` contain a given vertex,
and at most `N Δ ^ (2 (n - 1))` connected vertex sets have size `n`. The source
leaves `x` unspecified; the bound in that form holds with `x = max 1 (Δ ^ 2)`,
including graphs of degree zero.

The proof traverses a set: every connected set `S` of `n` vertices containing
`v` is the vertex set of a closed walk from `v` of length exactly `2 (n - 1)`,
obtained by adding the vertices of `S` one at a time, each through an edge
from the vertices already reached, with a detour out and back along that edge.
The walk determines `S`, and at most `Δ ^ L` walks of length `L` start at `v`.

## Main results

* `TNLean.Lattice.card_connected_induce_mem_le`: the count through one vertex.
* `TNLean.Lattice.card_connected_induce_le`: the sharper total count.
* `TNLean.Lattice.card_connected_induce_le_exponential`: the source form `N x ^ n`,
  with `x = max 1 (Δ ^ 2)`.
-/

namespace TNLean.Lattice

open Finset SimpleGraph

variable {V : Type*}

/-- Inserting a detour `w → u → w` at a vertex `w` of a closed walk lengthens it by
two and adds exactly the vertex `u` to its vertex set. -/
theorem exists_detour_walk (G : SimpleGraph V) {v w u : V} (p : G.Walk v v)
    (hw : w ∈ p.support) (hwu : G.Adj w u) :
    ∃ q : G.Walk v v, q.length = p.length + 2 ∧
      ∀ x, x ∈ q.support ↔ x ∈ p.support ∨ x = u := by
  classical
  refine ⟨(p.takeUntil w hw).append (.cons hwu (.cons hwu.symm (p.dropUntil w hw))), ?_, ?_⟩
  · have h := congrArg Walk.length (p.take_spec hw)
    rw [Walk.length_append] at h
    simp only [Walk.length_append, Walk.length_cons]
    omega
  · intro x
    conv_rhs => rw [← p.take_spec hw]
    simp only [Walk.mem_support_append_iff, Walk.support_cons, List.mem_cons]
    have := (p.dropUntil w hw).start_mem_support
    grind

/-- A finite vertex set `S` containing `v` that induces a connected subgraph is the
vertex set of a closed walk from `v` of length exactly `2 (|S| - 1)`. -/
theorem exists_closedWalk_support_toFinset_eq [DecidableEq V] (G : SimpleGraph V)
    {S : Finset V} {v : V} (hv : v ∈ S) (hS : (G.induce (S : Set V)).Connected) :
    ∃ p : G.Walk v v, p.length = 2 * (#S - 1) ∧ p.support.toFinset = S := by
  suffices h : ∀ k, 1 ≤ k → k ≤ #S → ∃ T ⊆ S, #T = k ∧
      ∃ p : G.Walk v v, p.length = 2 * (k - 1) ∧ p.support.toFinset = T by
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := h #S (card_pos.2 ⟨v, hv⟩) le_rfl
    exact ⟨p, hp, hpT.trans (eq_of_subset_of_card_le hTS hT.ge)⟩
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨{v}, by simpa using hv, by simp, .nil, by simp, by simp⟩
  | succ k hk ih =>
    intro hkS
    obtain ⟨T, hTS, hT, p, hp, hpT⟩ := ih (by omega)
    obtain ⟨b, hbS, hbT⟩ : ∃ b ∈ S, b ∉ T := not_subset.1 fun h =>
      by have := card_le_card h; omega
    obtain ⟨W⟩ := hS.preconnected (⟨v, by simpa using hv⟩ : (S : Set V))
      ⟨b, by simp [hbS]⟩
    obtain ⟨d, -, hdT, hdT'⟩ := W.exists_boundary_dart {x | x.1 ∈ T}
      (by simp [← hpT]) (by simpa using hbT)
    have hadj : G.Adj d.fst.1 d.snd.1 := d.adj
    obtain ⟨q, hq, hqsupp⟩ := exists_detour_walk G p (by simpa [← hpT] using hdT) hadj
    refine ⟨insert d.snd.1 T, insert_subset (by simp) hTS,
      by rw [card_insert_of_notMem hdT', hT], q, by rw [hq, hp]; omega, ?_⟩
    ext x
    simp [hqsupp, ← hpT, or_comm]

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- In a graph of maximum degree at most `Δ`, there are at most `Δ ^ L` walks of length
`L` between two given vertices. -/
theorem card_finsetWalkLength_le_pow {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (L : ℕ)
    (u x : V) : #(G.finsetWalkLength L u x) ≤ Δ ^ L := by
  induction L generalizing u with
  | zero =>
    rw [finsetWalkLength]
    split_ifs with h
    · subst h; simp
    · simp
  | succ L ih =>
    rw [finsetWalkLength]
    refine card_biUnion_le.trans ?_
    calc ∑ w : G.neighborSet u, #((G.finsetWalkLength L w x).map _)
        ≤ ∑ _w : G.neighborSet u, Δ ^ L :=
          Finset.sum_le_sum fun w _ => by rw [card_map]; exact ih w
      _ ≤ Δ ^ (L + 1) := by
        rw [sum_const, card_univ, card_neighborSet_eq_degree, smul_eq_mul, pow_succ,
          mul_comm]
        exact Nat.mul_le_mul_left _ (hΔ u)

/-- **Connected sets through a vertex** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a finite graph of maximum degree at most `Δ`, at
most `Δ ^ (2 (n - 1))` vertex sets of size `n` that contain `v` induce a connected
subgraph. -/
theorem card_connected_induce_mem_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (v : V) (n : ℕ) :
    #{S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Δ ^ (2 * (n - 1)) := by
  have key : ∀ S ∈ ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
      Finset (Finset V)), ∃ p : G.Walk v v,
        p.length = 2 * (n - 1) ∧ p.support.toFinset = S := by
    intro S hS
    simp only [mem_filter, mem_univ, true_and] at hS
    obtain ⟨hv, rfl, hc⟩ := hS
    exact exists_closedWalk_support_toFinset_eq G hv hc
  choose! f hf using key
  calc _ ≤ #(G.finsetWalkLength (2 * (n - 1)) v v) := by
        refine card_le_card_of_injOn f (fun S hS => ?_) (fun S hS T hT h => ?_)
        · simpa [mem_finsetWalkLength_iff] using (hf S hS).1
        · rw [← (hf S hS).2, h, (hf T hT).2]
    _ ≤ _ := card_finsetWalkLength_le_pow G hΔ _ v v

/-- **Connected sets of a given size** (Hastings, arXiv:cond-mat/0508554v3, lines
1227–1254, after Klarner 1967). In a graph on `N` vertices of maximum degree at most
`Δ`, at most `N Δ ^ (2 (n - 1))` vertex sets of size `n` induce a connected subgraph. -/
theorem card_connected_induce_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * Δ ^ (2 * (n - 1)) := by
  calc _ ≤ #(univ.biUnion fun v : V =>
        ({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V))) := by
        refine card_le_card fun S hS => ?_
        simp only [mem_filter, mem_univ, true_and] at hS
        obtain ⟨⟨v, hv⟩⟩ := hS.2.nonempty
        simp only [mem_biUnion, mem_univ, mem_filter, true_and]
        exact ⟨v, by simpa using hv, hS.1, hS.2⟩
    _ ≤ ∑ v : V, #({S : Finset V | v ∈ S ∧ #S = n ∧ (G.induce (S : Set V)).Connected} :
          Finset (Finset V)) := card_biUnion_le
    _ ≤ ∑ _v : V, Δ ^ (2 * (n - 1)) := Finset.sum_le_sum fun v _ =>
        card_connected_induce_mem_le G hΔ v n
    _ = _ := by simp

/-- The exponential cluster count used in Hastings, arXiv:cond-mat/0508554v3,
lines 1227–1254. The constant `max 1 (Δ ^ 2)` also covers edgeless graphs,
whose connected singleton sets must still be counted. -/
theorem card_connected_induce_le_exponential {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (n : ℕ) :
    #{S : Finset V | #S = n ∧ (G.induce (S : Set V)).Connected} ≤
      Fintype.card V * (max 1 (Δ ^ 2)) ^ n := by
  refine (card_connected_induce_le G hΔ n).trans (Nat.mul_le_mul_left _ ?_)
  rw [pow_mul]
  exact (pow_le_pow_left' (le_max_right 1 (Δ ^ 2)) (n - 1)).trans
    (pow_le_pow_right' (le_max_left 1 (Δ ^ 2)) (Nat.sub_le n 1))

end TNLean.Lattice
