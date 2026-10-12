/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OriginalCircuit
import TNLean.PEPS.Approximation.FiniteRegisterMemories

/-!
# Finite coordinates of the original product input

Each party's entire original private memory is finite-dimensional, without a
numerical dimension bound. Their actual ordered tensor product therefore has
finite orthonormal coordinates. No separability within one party is required.

Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 17–19 and 137–139.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
thm:compression; Theorem 5.2 and its proof.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized; no upstream Lean proof text reused.
-/


noncomputable section
namespace TNLean.PEPS.PairEffect.ProductInput
variable {P : Type} [Fintype P]

/-- The memory of the actual whole-party input layout is finite-dimensional
whenever each original party memory is finite-dimensional. This includes an
empty party set and zero-dimensional factors. -/
theorem finiteDimensional_wholePartyMem (H : P → HSpace)
    (hH : ∀ p, FiniteDimensional ℂ (H p)) :
    FiniteDimensional ℂ (Mem (wholePartyLayout H)) := by
  apply Layout.finiteDimensional_mem_of_registers
  intro r hr
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hr
  exact hH p

end TNLean.PEPS.PairEffect.ProductInput
