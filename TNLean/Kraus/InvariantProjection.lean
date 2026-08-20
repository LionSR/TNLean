/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.OrthogonalProjection
import TNLean.Channel.FixedPoint.SupportInvariance
import TNLean.Channel.Irreducible.Basic

/-!
# Invariant orthogonal projections for finite matrix families

A finite family of square matrices is irreducible when it has no nontrivial
invariant subspace. In finite dimension, this is equivalent to the absence of
a nontrivial invariant orthogonal projection.

## Main declarations

* `Kraus.HasInvariantProj` states that a finite matrix family has a nontrivial
  invariant orthogonal projection.
* `Kraus.IsIrreducibleFamily` states that no such projection exists.
* `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` shows that an irreducible
  family defines an irreducible Kraus map.
* `Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM` proves the converse.
-/

namespace Kraus

variable {d D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- A finite matrix family has a nontrivial invariant orthogonal projection if there is a
Hermitian idempotent $P$, distinct from $0$ and $1$, such that
$(1-P)K_iP=0$ for every family index $i$. -/
def HasInvariantProj (K : Fin d → Mat) : Prop :=
  ∃ P : Mat,
    IsOrthogonalProjection P ∧ P ≠ 0 ∧ P ≠ 1 ∧ (∀ i : Fin d, (1 - P) * K i * P = 0)

/-- A finite matrix family is irreducible if it has no nontrivial invariant orthogonal
projection. -/
def IsIrreducibleFamily (K : Fin d → Mat) : Prop :=
  ¬ HasInvariantProj K

/-- A finite matrix family with no nontrivial invariant orthogonal projection defines an
irreducible Kraus map. -/
theorem isIrreducibleMap_mapLM_of_isIrreducibleFamily
    (K : Fin d → Mat) (hIrr : IsIrreducibleFamily K) :
    IsIrreducibleMap (mapLM K) := by
  intro P hProj hInv
  have hLower : ∀ i : Fin d, (1 - P) * K i * P = 0 :=
    invariance_implies_lowerZero K P hProj fun X => by
      simpa only [mapLM_apply] using hInv X
  by_contra h_neither
  push Not at h_neither
  exact hIrr ⟨P, hProj, h_neither.1, h_neither.2, hLower⟩

/-- If the finite Kraus map is irreducible, then its matrix family has no nontrivial
invariant orthogonal projection. -/
theorem isIrreducibleFamily_of_isIrreducibleMap_mapLM
    (K : Fin d → Mat) (hIrr : IsIrreducibleMap (mapLM K)) :
    IsIrreducibleFamily K := by
  intro ⟨P, hProj, hP0, hP1, hLower⟩
  have hInv : ∀ X, P * mapLM K (P * X * P) * P = mapLM K (P * X * P) := fun X => by
    simpa only [mapLM_apply] using lowerZero_implies_invariance K P hProj hLower X
  exact (hIrr P hProj hInv).elim hP0 hP1

end Kraus
