/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CanonicalNormalization

/-!
# Positive physical dimension of a normalized tensor

On a nonzero bond space, trace-preserving normalization excludes an empty
physical alphabet. Source: DCCSP17, arXiv:1708.00029, Section 2.1,
left-canonical normalization.
-/

namespace MPSTensor
variable {d D : ℕ}

/-- A left-canonical tensor on a nonzero bond space has nonzero physical
dimension. Source: DCCSP17, arXiv:1708.00029, Section 2.1,
left-canonical normalization. -/
theorem IsLeftCanonical.physDim_ne_zero [NeZero D] {A : MPSTensor d D}
    (hA : IsLeftCanonical A) : d ≠ 0 := by
  intro hd
  subst d
  simp [IsLeftCanonical, Kraus.IsTP] at hA

end MPSTensor
