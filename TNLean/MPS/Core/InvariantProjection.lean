/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Kraus.InvariantProjection
import TNLean.MPS.Core.Word

/-!
# Invariant orthogonal projections for matrix product tensors

A matrix product tensor is irreducible when its matrix family has no nontrivial
invariant orthogonal projection. This file preserves the established MPS names
for the two finite-family predicates.

## Main declarations

* `MPSTensor.HasInvariantProj` states that a tensor has a nontrivial invariant
  orthogonal projection.
* `MPSTensor.IsIrreducibleTensor` states that no such projection exists.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- A matrix product tensor has a nontrivial invariant orthogonal projection if its
finite matrix family has one. -/
def HasInvariantProj (A : MPSTensor d D) : Prop :=
  Kraus.HasInvariantProj A

/-- A matrix product tensor is irreducible if its finite matrix family has no nontrivial
invariant orthogonal projection. -/
def IsIrreducibleTensor (A : MPSTensor d D) : Prop :=
  ¬ HasInvariantProj A

end MPSTensor
