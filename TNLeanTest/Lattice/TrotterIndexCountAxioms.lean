/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.TrotterIndexCount
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Kernel-foundation checks for the actual per-site indices of Hastings' Trotter form. -/

open TNLean.Lattice QuantumCircuit

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[``ProductForm.ofSupported, ``ProductForm.card_index_ofSupported,
      ``exists_productForm_list_prod_card_index, ``exists_productForm_trotterProduct_card_index,
      ``exists_productForm_trotterProduct_card_index_of_dist_le] do
    unless (← Lean.getEnv).contains decl do
      throwError "Missing declaration {decl}"
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
    Lean.logInfo m!"{decl}: {axioms}"

-- Scalar factors supported on no site introduce no index components, at any number of steps.
example {ι κ : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q]
    (H : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ) (c : κ → ι)
    (hH : ∀ k, H k ∈ supportedOperators q (∅ : Set ι)) (seq : List κ) (β : ℝ) (n : ℕ) :
    ∃ P : ProductForm q (fun _ _ : ι ↦ False)
        (((seq.map fun k ↦ NormedSpace.exp ((-((β : ℂ) / n)) • H k)).prod) ^ n),
      ∀ i, Fintype.card (P.Index i) ≤ 1 := by
  have hH' : ∀ k, H k ∈ supportedOperators q ((∅ : Finset ι) : Set ι) := by
    simpa only [Finset.coe_empty] using hH
  obtain ⟨P, hP⟩ := exists_productForm_trotterProduct_card_index
    (near := fun _ _ : ι ↦ False) H (fun _ ↦ ∅) c
    (by simp) hH' seq 0 (by simp) β n
  refine ⟨P, fun i ↦ ?_⟩
  simpa only [Nat.mul_zero, pow_zero] using hP i
