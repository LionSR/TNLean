/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Channel.FixedPoint.SupportInvariance
import TNLean.Channel.Irreducible.Basic
import TNLean.Kraus.Word

/-!
# Invariant orthogonal projections and irreducibility of a finite Kraus family

This file carries the word-evaluation layer of the channel side:
`HasInvariantProj` and `IsIrreducibleTensor`, the predicates used by the
canonical-form iterated block-decomposition argument to detect a nontrivial
invariant orthogonal projection for a finite Kraus family. It is part of
the extraction of a Kraus-family-only library out of `TNLean`'s
matrix-product-state development.

The consequences of these predicates (rescaling and conjugation invariance,
the cast lemmas, and the iterated block-decomposition capstone
`exists_irreducible_blockDecomp`) stay on the matrix-product-state side, in
`TNLean/MPS/CanonicalForm/Reduction.lean`.

The established predicates remain in `namespace MPSTensor` because the
canonical-form development uses these names throughout. A change of namespace
belongs with a simultaneous change of those declarations.

## Main declarations

* `HasInvariantProj` — existence of a nontrivial invariant orthogonal projection
* `IsIrreducibleTensor` — no nontrivial invariant orthogonal projection exists
* `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleTensor` — tensor irreducibility implies
  irreducibility of the associated finite Kraus map
* `Kraus.isIrreducibleTensor_of_isIrreducibleMap_mapLM` — the converse implication
-/

namespace MPSTensor

variable {d D : ℕ}

/-- `HasInvariantProj A` holds if there is a *nontrivial* invariant orthogonal projection for `A`:
a Hermitian idempotent `P` with `P ≠ 0`, `P ≠ 1`, and `(1 - P) * A i * P = 0` for every `i`.

This is the negation of "irreducible with respect to invariant subspaces". -/
def HasInvariantProj (A : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ∃ P : Matrix (Fin D) (Fin D) ℂ,
    IsOrthogonalProjection P ∧ P ≠ 0 ∧ P ≠ 1 ∧ (∀ i : Fin d, (1 - P) * A i * P = 0)

/-- `IsIrreducibleTensor A` holds if `A` admits no nontrivial invariant orthogonal projection.
This is the "irreducible" condition used in the canonical-form reduction. -/
def IsIrreducibleTensor (A : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop :=
  ¬ HasInvariantProj A

end MPSTensor

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A finite Kraus family with no nontrivial invariant orthogonal projection defines an
irreducible Kraus map. -/
theorem isIrreducibleMap_mapLM_of_isIrreducibleTensor
    (K : Fin d → Mat) (hIrr : MPSTensor.IsIrreducibleTensor K) :
    IsIrreducibleMap (mapLM K) := by
  intro P hProj hInv
  have hLower : ∀ i : Fin d, (1 - P) * K i * P = 0 :=
    invariance_implies_lowerZero K P hProj fun X => by
      simpa only [mapLM_apply] using hInv X
  by_contra h_neither
  push Not at h_neither
  exact hIrr ⟨P, hProj, h_neither.1, h_neither.2, hLower⟩

/-- If the finite Kraus map is irreducible, then its Kraus family has no nontrivial
invariant orthogonal projection. -/
theorem isIrreducibleTensor_of_isIrreducibleMap_mapLM
    (K : Fin d → Mat) (hIrr : IsIrreducibleMap (mapLM K)) :
    MPSTensor.IsIrreducibleTensor K := by
  intro ⟨P, hProj, hP0, hP1, hLower⟩
  have hInv : ∀ X, P * mapLM K (P * X * P) * P = mapLM K (P * X * P) := fun X => by
    simpa only [mapLM_apply] using lowerZero_implies_invariance K P hProj hLower X
  exact (hIrr P hProj hInv).elim hP0 hP1

end Kraus
