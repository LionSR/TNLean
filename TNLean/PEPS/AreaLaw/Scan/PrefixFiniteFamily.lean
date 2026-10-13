/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison

/-!
# A fixed finite family of positive-depth prefixes

For a fixed finite region, integer-valued depth function and natural upper
cutoff, every smaller integer cutoff selects a member of the same finite family.
This family is fixed before histories and replica parameters are chosen.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, `scanner:fronts`, lines 83–124, and Lemma 9.1(2), lines 243–250,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
The proofs are written independently from the manuscript; no upstream Lean
proof is copied or adapted.
-/

namespace TNLean.PEPS.AreaLaw.Scan

variable {V : Type*}

/-- Replacing an integer cutoff by its nonnegative part preserves the
positive-depth prefix. No sign condition on the depth function is required. -/
theorem positiveDepthPrefix_toNat (A : Finset V) (depth : V → ℤ) (j : ℤ) :
    positiveDepthPrefix A depth (j.toNat : ℤ) = positiveDepthPrefix A depth j := by
  apply Finset.ext
  intro x
  simp only [positiveDepthPrefix, Finset.mem_filter, Int.ofNat_toNat, le_max_iff]
  grind

/-- Every integer cutoff below a fixed natural upper cutoff selects a member
of the same finite family of positive-depth prefixes. -/
theorem positiveDepthPrefix_mem_range_fin_of_le (A : Finset V) (depth : V → ℤ)
    {L : ℕ} {j : ℤ} (hj : j ≤ (L : ℤ)) :
    positiveDepthPrefix A depth j ∈ Set.range
      (fun i : Fin (L + 1) ↦ positiveDepthPrefix A depth (i.val : ℤ)) := by
  refine ⟨⟨j.toNat, Nat.lt_succ_of_le (Int.toNat_le.mpr hj)⟩, ?_⟩
  exact positiveDepthPrefix_toNat A depth j

end TNLean.PEPS.AreaLaw.Scan
