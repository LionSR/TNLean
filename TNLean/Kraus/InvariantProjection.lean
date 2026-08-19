/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Kraus.Word

/-!
# Invariant orthogonal projections and irreducibility of a finite Kraus family

This file carries the word-evaluation layer of the channel side:
`HasInvariantProj` and `IsIrreducibleTensor`, the predicates used by the
canonical-form iterated block-decomposition argument to detect a nontrivial
invariant orthogonal projection for a finite Kraus family. It is part of
issue #6560's extraction of a Kraus-family-only library out of `TNLean`'s
matrix-product-state development.

The consequences of these predicates (rescaling and conjugation invariance,
the cast lemmas, and the iterated block-decomposition capstone
`exists_irreducible_blockDecomp`) stay on the matrix-product-state side, in
`TNLean/MPS/CanonicalForm/Reduction.lean`.

**Pending:** these declarations keep `namespace MPSTensor` for this PR
(issue #6560 phase 1b, PR-W1a). The rename to `namespace Kraus` is deferred
to a dedicated mechanical sweep across the ~429 files that reference this
vocabulary repo-wide; see `TNLean/Kraus/Word.lean`'s module docstring.

## Main declarations

* `HasInvariantProj` — existence of a nontrivial invariant orthogonal projection
* `IsIrreducibleTensor` — no nontrivial invariant orthogonal projection exists
-/

namespace MPSTensor

variable {d D : ℕ}

/-- `HasInvariantProj A` holds if there is a *nontrivial* invariant orthogonal projection for `A`:
a Hermitian idempotent `P` with `P ≠ 0`, `P ≠ 1`, and `(1 - P) * A i * P = 0` for every `i`.

This is the negation of "irreducible with respect to invariant subspaces". -/
def HasInvariantProj (A : MPSTensor d D) : Prop :=
  ∃ P : Matrix (Fin D) (Fin D) ℂ,
    IsOrthogonalProjection P ∧ P ≠ 0 ∧ P ≠ 1 ∧ (∀ i : Fin d, (1 - P) * A i * P = 0)

/-- `IsIrreducibleTensor A` holds if `A` admits no nontrivial invariant orthogonal projection.
This is the "irreducible" condition used in the canonical-form reduction. -/
def IsIrreducibleTensor (A : MPSTensor d D) : Prop :=
  ¬ HasInvariantProj A

end MPSTensor
