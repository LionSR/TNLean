/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MatrixHermitianSum
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-! Regressions for Hermitian partial sums, including empty and proper subsets. -/

section

variable {ι n α : Type*} [AddCommMonoid α] [StarAddMonoid α]

example {s : Finset ι} {A : ι → Matrix n n α}
    (hA : ∀ i ∈ s, (A i).IsHermitian) :
    (∑ i ∈ (∅ : Finset ι), A i).IsHermitian :=
  Matrix.isHermitian_sum_of_subset hA (Finset.empty_subset s)

example {s : Finset ι} {A : ι → Matrix n n α}
    (hA : ∀ i ∈ s, (A i).IsHermitian) : (∑ i ∈ s, A i).IsHermitian :=
  Matrix.isHermitian_sum_of_subset hA (Finset.Subset.refl s)

-- A proper subset, with no hypothesis on terms outside the larger finite set.
example {A : ℕ → Matrix n n α} (h₀ : (A 0).IsHermitian) (h₁ : (A 1).IsHermitian) :
    (∑ i ∈ ({0} : Finset ℕ), A i).IsHermitian := by
  apply Matrix.isHermitian_sum_of_subset (s := {0, 1})
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact h₀
    · exact h₁
  · exact Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _)

end

run_cmd do
  let axioms ← Lean.collectAxioms ``Matrix.isHermitian_sum_of_subset
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  unless axioms.all (allowed.contains ·) do
    throwError "Unexpected axioms: {axioms}"
  Lean.logInfo m!"Matrix.isHermitian_sum_of_subset: {axioms}"
