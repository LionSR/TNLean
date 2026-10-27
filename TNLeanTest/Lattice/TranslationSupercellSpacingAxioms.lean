/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TranslationSupercellSpacing
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Presence and permitted-axiom checks for the supercell translations that carry a site far
away. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
      ``TNLean.Lattice.pow_mem_supercell,
      ``SimpleGraph.natAbs_valMinAbs_sub_le_edist,
      ``TNLean.Lattice.exists_lt_natAbs_valMinAbs_add,
      ``TNLean.Lattice.exists_mem_supercell_lt_edist_add,
      ``TNLean.Lattice.exists_mem_supercell_lt_edist_add_ring] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

/-- A range-two coordinate jump can traverse a single graph edge. -/
example : (2 : ℕ∞) ≤ (2 : ℕ∞) * (⊤ : SimpleGraph (Fin 3)).edist 0 2 := by
  exact SimpleGraph.natAbs_valMinAbs_sub_le_edist (Γ := ⊤) (n := 5) (R := 2)
    (Nat.succ_pos 1) (fun i : Fin 3 ↦ (i.val : ZMod 5)) (by decide) 0 2
