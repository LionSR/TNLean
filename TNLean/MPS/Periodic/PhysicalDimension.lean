/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Defs
import TNLean.MPS.Core.PhysicalDimension

/-!
# Positive physical dimension of a normalized periodic tensor

The prescribed peripheral spectrum makes the bond space nonzero. The
left-canonical normalization then excludes an empty physical alphabet.

Source: arXiv:1708.00029, Section 2.1.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- A normalized periodic tensor has nonzero physical dimension. An empty
physical alphabet would make the left-canonical sum zero, whereas its bond
dimension is nonzero.

Source: arXiv:1708.00029, Section 2.1, left-canonical normalization. -/
theorem IsPeriodic.physDim_ne_zero {m : ℕ} {A : MPSTensor d D}
    (hA : IsPeriodic m A) : d ≠ 0 := by
  let : NeZero D := ⟨hA.bondDim_ne_zero⟩
  exact hA.leftCanonical.physDim_ne_zero

end MPSTensor
