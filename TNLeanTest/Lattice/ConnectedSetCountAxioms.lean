/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ConnectedSetCount
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the count of connected vertex sets in a graph
of bounded degree. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.exists_detour_walk,
    ``TNLean.Lattice.exists_closedWalk_support_toFinset_eq,
    ``TNLean.Lattice.card_finsetWalkLength_le_pow,
    ``TNLean.Lattice.card_connected_induce_mem_le,
    ``TNLean.Lattice.card_connected_induce_le,
    ``TNLean.Lattice.card_connected_induce_le_exponential] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

open Finset

-- The source-shaped bound must include singleton clusters in an edgeless graph.
example {V : Type*} [Fintype V] [DecidableEq V] (n : ℕ) :
    #{S : Finset V | S.card = n ∧ ((⊥ : SimpleGraph V).induce (S : Set V)).Connected} ≤
      Fintype.card V := by
  classical
  simpa using TNLean.Lattice.card_connected_induce_le_exponential (⊥ : SimpleGraph V)
    (Δ := 0) (by simp) n
