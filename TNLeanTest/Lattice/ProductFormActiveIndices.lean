/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.ProductFormActiveIndices
import TNLean.Lattice.ProductForm.Metric
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Boundary cases for the supported-factor index count and actual product expansion. -/

open TNLean.Lattice TNLean.Lattice.Locality

-- An empty site set still has a one-dimensional configuration space. An empty
-- auxiliary alphabet is allowed because there is a unique empty assignment.
example (n : ℕ) :
    ∃ P : Locality.ProductForm (fun _ : Fin 0 ↦ Set.univ) (fun _ ↦ 0)
      (1 : Matrix (Fin 0 → Fin 0) (Fin 0 → Fin 0) ℂ), Fintype.card P.Index = 0 := by
  obtain ⟨P, hP⟩ := exists_productForm_list_pow_of_isSupportedOn
    (fun _ : Fin 0 ↦ Set.univ) (fun _ ↦ 0) (by simp)
    (fun _ ↦ ∅) (by simp) (fun _ ↦ 0) (fun i ↦ Fin.elim0 i) [] n 0
    (fun j ↦ Fin.elim0 j)
  exact ⟨{ P with eq_sum := by simpa using P.eq_sum }, hP⟩

-- A zero physical dimension is handled internally, including an empty
-- auxiliary alphabet and arbitrary operators on the empty configuration space.
example (A : Fin 1 → Matrix (Fin 1 → Fin 0) (Fin 1 → Fin 0) ℂ) :
    ∃ P : Locality.ProductForm (fun _ : Fin 1 ↦ Set.univ) (fun _ ↦ 0)
      (A 0), Fintype.card P.Index = 0 := by
  obtain ⟨P, hP⟩ := exists_productForm_list_pow_of_isSupportedOn
    (fun _ : Fin 1 ↦ Set.univ) (fun _ ↦ 0) (by simp)
    (fun _ ↦ Finset.univ) (by simp) A
    (fun _ ↦ ⟨fun x ↦ Fin.elim0 (x 0), fun x ↦ Fin.elim0 (x 0)⟩)
    [0] 1 0 (by intro j; have : j = 0 := Subsingleton.elim _ _; simp [this])
  exact ⟨{ P with eq_sum := by simpa using P.eq_sum }, hP⟩

-- Zero steps give the identity on a nonempty physical state space and need
-- exactly one value per site, irrespective of the list of factors.
example (L : List (Fin 1)) :
    ∃ P : Locality.ProductForm (fun _ : Fin 1 ↦ Set.univ) (fun _ ↦ 2)
      (1 : Matrix (Fin 1 → Fin 2) (Fin 1 → Fin 2) ℂ), Fintype.card P.Index = 1 := by
  exact exists_productForm_list_pow_of_isSupportedOn
    (fun _ : Fin 1 ↦ Set.univ) (fun _ ↦ 2) (by simp)
    (fun _ ↦ Finset.univ) (by simp) (fun _ ↦ 0)
    (by intro i; constructor <;> intros <;> rfl) L 0 1 (by simp)

-- No active occurrence has one assignment, even at physical dimension zero.
example : Fintype.card
    ((trotterActiveOccurrences (fun _ : Fin 1 ↦ ∅) 3 0) → Fin 0 × Fin 0) = 1 := by
  rw [card_trotterActiveIndices]
  simp

-- A repeated list is counted with multiplicity, rather than treated as one sweep.
example : ([0, 0, 0] : List (Fin 1)).countP (fun _ ↦ true) = 3 := by decide

-- Unequal local dimensions are retained throughout the actual product expansion.
-- Two full-support factors need at most (3²)² = 81 common index values.
private def unequalDimensions (j : Fin 2) : ℕ := if j = 0 then 2 else 3

example (A : Fin 2 → Matrix ((j : Fin 2) → Fin (unequalDimensions j))
    ((j : Fin 2) → Fin (unequalDimensions j)) ℂ)
    (hA : ∀ i, Entropy.IsSupportedOn (A i) Finset.univ) :
    ∃ P : Locality.ProductForm (fun _ : Fin 2 ↦ Set.univ) unequalDimensions
      (A 0 * A 1), Fintype.card P.Index = 81 := by
  obtain ⟨P, hP⟩ := exists_productForm_list_pow_of_isSupportedOn
    (fun _ : Fin 2 ↦ Set.univ) unequalDimensions (by simp)
    (fun _ ↦ Finset.univ) (by simp) A hA [0, 1] 1 81
    (by intro j; fin_cases j <;> decide)
  exact ⟨{ P with eq_sum := by simpa using P.eq_sum }, hP⟩

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for decl in #[
    ``TNLean.Lattice.card_trotterActiveIndices,
    ``TNLean.Lattice.Locality.productFormOfSiteIndices,
    ``TNLean.Lattice.Locality.productFormOfSupported,
    ``TNLean.Lattice.Locality.HasProductForm.mul,
    ``TNLean.Lattice.Locality.isSupportedOn_exp_smul,
    ``TNLean.Lattice.Locality.hasProductForm_trotterProduct_of_metric,
    ``TNLean.Lattice.Locality.exists_productForm_list_pow_of_isSupportedOn,
    ``TNLean.Lattice.Locality.exists_productForm_trotter_card_bound,
    ``TNLean.Lattice.Locality.exists_productForm_metric_trotter_card_bound] do
    let axioms ← Lean.collectAxioms decl
    unless axioms.all (allowed.contains ·) do
      throwError "Unexpected axioms for {decl}: {axioms}"
