/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ClusterExpansion.LocalIndexCount
import TNLean.Lattice.IntegerLatticeBallCount
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Foundation checks and empty-support regression for Hastings' local index ranges. -/

open TNLean.Lattice TNLean.Lattice.ClusterExpansion

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``ProductForm.restrict, ``ProductForm.card_index_restrict,
      ``clusterProductForm, ``localClusterProductForm,
      ``card_clusterIndexSet_le, ``IsValidCluster.subset_centres_ball,
      ``exists_productForm_truncatedExp_card_index,
      ``exists_productForm_truncatedExp_pow_card_index,
      ``exists_productForm_truncatedExp_card_index_of_polynomial_growth,
      ``exists_productForm_truncatedExp_pow_card_index_of_polynomial_growth,
      ``card_centres_integerLattice_ball_le, ``card_centres_ball_le_polynomial_of_dist_le,
      ``card_centres_ball_le_polynomial_of_isometry] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

-- Arbitrarily many scalar terms contribute no cluster labels at any site.
example {σ κ : Type*} [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    {q : ℕ} (near : σ → σ → Prop) (i : σ) :
    (clusterIndexSet (q := q) (fun _ : κ ↦ (∅ : Finset σ)) near i).card ≤
      2 * (q * q) := by
  simpa only [Finset.card_empty, pow_zero, Nat.one_add] using
    card_clusterIndexSet_le (q := q) (fun _ : κ ↦ (∅ : Finset σ)) near i ∅
      (fun C _ hi ↦ by
        obtain ⟨k, _, hk⟩ := Finset.mem_biUnion.mp hi
        exact (Finset.notMem_empty i hk).elim)
