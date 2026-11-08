/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.Basic

/-!
# The union of adjacent intervals

The actual parent interval is the union of its two adjacent children.
-/

namespace TNLean.MPS.AreaLaw

variable {L : ℕ}

/-- Two adjacent intervals `[a, b)` and `[b, c)` with `a ≤ b ≤ c` make up `[a, c)`. -/
theorem interval_union_interval {a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    interval L a b ∪ interval L b c = interval L a c := by
  ext x
  simp only [Finset.mem_union, mem_interval]
  omega

end TNLean.MPS.AreaLaw
