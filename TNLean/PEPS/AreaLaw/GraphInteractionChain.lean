/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.List.Chain

/-!
# Interaction chains in the domain graph

A list of interaction supports with consecutive nonempty intersections gives a walk between
any site of the first support and any site of the last support. The length of that walk is at
most the sum of the graph ranges of the supports. For a common range $R$, a chain containing
$m + 1$ supports therefore has length at most $(m + 1)R$.

All walks are in the supplied graph. For an induced domain graph, their vertices may leave an
interaction support but remain in the domain. No connectedness assumption on the domain is
needed. The extended graph distance records infinity between distinct connected components.

## Main statements

* `exists_walk_length_le_sum_of_isChain`: the length bound with separate support ranges.
* `edist_le_mul_of_isChain`: the uniform range bound, counting the first support.
* `not_isChain_of_connectedComponent_ne`: distinct components have no interaction chain.

## References and provenance

OpenAI, *A two-dimensional area law from a global spectral gap*, Lemma 4.1,
`build/sections/03-quasilocal.tex`, lines 99--113, at immutable commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a` of `openai/math`.
The proofs below are independently written from the paper's interaction-chain argument;
no Lean declaration or proof is copied or adapted from OpenAI's implementation.
-/

namespace TNLean.PEPS.AreaLaw

variable {V : Type*} {G : SimpleGraph V} {X : Set V} {supports : List (Set V)}
  {x y : V} {R : ℕ}

/-- A chain of overlapping supports joins its first and last sites by a walk whose length
is at most the sum of the individual support ranges in the supplied graph.

Source: the interaction-chain step of OpenAI's area-law paper, Lemma 4.1,
`03-quasilocal.tex`, lines 99--104. This allows a separate range for each support. -/
theorem exists_walk_length_le_sum_of_isChain (ranges : Set V → ℕ)
    (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ ranges A)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ∃ p : G.Walk x y, p.length ≤ ((X :: supports).map ranges).sum := by
  induction supports generalizing X x y with
  | nil =>
    obtain ⟨p, hp⟩ := hrange X (by simp) x hx y (by simpa using hy)
    exact ⟨p, by simpa using hp⟩
  | cons Y supports ih =>
    obtain ⟨hoverlap, htail⟩ := List.isChain_cons_cons.mp hchain
    obtain ⟨z, hzX, hzY⟩ := hoverlap
    obtain ⟨p, hp⟩ := hrange X (by simp) x hx z hzX
    obtain ⟨q, hq⟩ := ih (X := Y) (x := z) (y := y) htail
      (fun A hA ↦ hrange A (List.mem_cons_of_mem X hA)) hzY (by simpa using hy)
    refine ⟨p.append q, ?_⟩
    simpa using Nat.add_le_add hp hq

/-- For a common graph range $R$, a chain with $m + 1$ supports gives a walk of length
at most $(m + 1)R$. The initial support contributes one range allowance.

Source: OpenAI's area-law paper, Lemma 4.1, `03-quasilocal.tex`, lines 99--104. -/
theorem exists_walk_length_le_mul_of_isChain
    (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ∃ p : G.Walk x y, p.length ≤ (supports.length + 1) * R := by
  simpa [List.sum_const_nat, Nat.add_mul, Nat.add_comm] using
    exists_walk_length_le_sum_of_isChain (fun _ ↦ R) hchain hrange hx hy

/-- An interaction chain of graph range $R$ bounds the extended distance by its number
of supports times $R$, without a connectedness assumption on the graph.

Source: OpenAI's area-law paper, Lemma 4.1, `03-quasilocal.tex`, lines 99--104. -/
theorem edist_le_mul_of_isChain
    (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    G.edist x y ≤ (((supports.length + 1) * R : ℕ) : ℕ∞) := by
  obtain ⟨p, hp⟩ := exists_walk_length_le_mul_of_isChain hchain hrange hx hy
  exact p.edist_le.trans (ENat.natCast_le_natCast.mpr hp)

/-- The first and last sites of a finite-range interaction chain lie in the same
connected component of the supplied graph.

Source: the infinite-distance case of OpenAI's area-law paper, Lemma 4.1,
`03-quasilocal.tex`, lines 111--113. -/
theorem reachable_of_isChain
    (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    G.Reachable x y := by
  obtain ⟨p, _⟩ := exists_walk_length_le_mul_of_isChain hchain hrange hx hy
  exact p.reachable

/-- Every finite-range interaction chain preserves the connected component of its sites.

Source: OpenAI's area-law paper, Lemma 4.1, `03-quasilocal.tex`, lines 111--113. -/
theorem connectedComponent_eq_of_isChain
    (hchain : List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports))
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    G.connectedComponentMk x = G.connectedComponentMk y :=
  SimpleGraph.ConnectedComponent.sound (reachable_of_isChain hchain hrange hx hy)

/-- No finite-range interaction chain joins sites in distinct connected components.

Source: OpenAI's area-law paper, Lemma 4.1, `03-quasilocal.tex`, lines 111--113. -/
theorem not_isChain_of_connectedComponent_ne
    (hcomponents : G.connectedComponentMk x ≠ G.connectedComponentMk y)
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ¬ List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports) :=
  fun hchain ↦ hcomponents (connectedComponent_eq_of_isChain hchain hrange hx hy)

/-- Infinite graph distance excludes every finite-range interaction chain.

Source: OpenAI's area-law paper, Lemma 4.1, `03-quasilocal.tex`, lines 111--113. -/
theorem not_isChain_of_edist_eq_top (hdistance : G.edist x y = ⊤)
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ¬ List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports) := by
  intro hchain
  have hbound := edist_le_mul_of_isChain hchain hrange hx hy
  rw [hdistance] at hbound
  exact (ENat.natCast_ne_top ((supports.length + 1) * R)) (top_le_iff.mp hbound)

/-- A chain whose total range allowance is below the graph distance cannot reach
the specified final site. This includes infinite graph distance.

Source: the chain indicator in OpenAI's area-law paper, Lemma 4.1,
`03-quasilocal.tex`, lines 103--110. -/
theorem not_isChain_of_mul_lt_edist
    (hdistance : (((supports.length + 1) * R : ℕ) : ℕ∞) < G.edist x y)
    (hrange : ∀ A ∈ X :: supports, ∀ u ∈ A, ∀ v ∈ A,
      ∃ p : G.Walk u v, p.length ≤ R)
    (hx : x ∈ X) (hy : y ∈ (X :: supports).getLast (by simp)) :
    ¬ List.IsChain (fun A B : Set V ↦ (A ∩ B).Nonempty) (X :: supports) :=
  fun hchain ↦ (not_le_of_gt hdistance) (edist_le_mul_of_isChain hchain hrange hx hy)

end TNLean.PEPS.AreaLaw
