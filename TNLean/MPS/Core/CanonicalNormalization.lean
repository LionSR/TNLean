/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Defs

/-!
# Canonical normalization of an MPS tensor

Left-canonical normalization conditions for MPS tensors are used in the
canonical-form and periodic theories.
-/

open scoped Matrix BigOperators

namespace MPSTensor

variable {d D : ℕ}

/-- Left-canonical, equivalently trace-preserving, normalization of an MPS
tensor. -/
def IsLeftCanonical (A : MPSTensor d D) : Prop :=
  ∑ i : Fin d, (A i)ᴴ * A i = 1

end MPSTensor
