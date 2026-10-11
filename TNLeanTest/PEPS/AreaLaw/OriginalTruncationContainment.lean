/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Scan.PrefixComparison
import TNLean.PEPS.AreaLaw.Scan.DesignatedSampling

/-!
# Positive-depth prefixes in the compact collar

Every positive-depth prefix whose threshold is at most the collar depth lies
in the original compact truncation set. The proof below is unfinished.

Source: OpenAI, *A two-dimensional area law from a global spectral gap*,
`08-scanner.tex`, lines 43–59 and 244–251,
at `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw.Scan.CollarScan

/-- Every positive-depth comparison prefix below the collar depth lies in the
same truncation set. Source: 08-scanner.tex, lines 43–59 and 244–251. -/
theorem positiveDepthPrefix_subset_truncationSet {V I : Type*}
    (S : CollarScan V I) {j : ℤ} {L : ℕ} (hj : j ≤ (L : ℤ)) :
    positiveDepthPrefix S.A S.depth j ⊆ S.truncationSet L := by
  classical
  intro x hx
  obtain ⟨hxA, _, hxj⟩ := Finset.mem_filter.mp hx
  exact Finset.mem_filter.mpr ⟨hxA, le_trans hxj hj⟩

end TNLean.PEPS.AreaLaw.Scan.CollarScan
