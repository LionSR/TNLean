/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SourceOwnerMap

/-!
# Affected parties and a single exterior owner

Each affected party remains a separate owner, while all exterior parties acquire
one common owner. A pair source survives this grouping precisely when at least
one endpoint is affected. The ordered inventory retains each surviving
occurrence, including its halfspaces and vector; distinct pair labels are not
required.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 383–427.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

namespace TNLean.PEPS.PairEffect

variable {P : Type}

/-- Keep each affected party as a distinct owner and identify all exterior
parties with `none`. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
def affectedOwner (A : P → Bool) (p : P) : Option {p // A p = true} :=
  if h : A p = true then some ⟨p, h⟩ else none

/-- The common exterior owner consists exactly of the unaffected parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
@[simp] theorem affectedOwner_eq_none (A : P → Bool) (p : P) :
    affectedOwner A p = none ↔ A p = false := by
  cases h : A p <;> simp [affectedOwner, h]

/-- Two parties acquire the same owner exactly when they were equal or both
were exterior. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
theorem affectedOwner_eq_iff (A : P → Bool) (p q : P) :
    affectedOwner A p = affectedOwner A q ↔
      p = q ∨ (A p = false ∧ A q = false) := by
  by_cases hp : A p = true <;> by_cases hq : A q = true <;>
    simp_all only [Bool.not_eq_true, affectedOwner, ↓reduceDIte, Option.some.injEq,
      Subtype.ext_iff, Bool.true_eq_false, Bool.false_eq_true, reduceCtorEq,
      and_self, and_true, and_false, or_false, or_true, false_iff]
  all_goals rintro rfl; simp_all

/-- A source survives exactly when at least one endpoint is affected. This
includes every corrected pair with two affected endpoints, as well as every
pair crossing to the exterior. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 383–417. -/
theorem PairSource.affectedOwner_ne_iff (A : P → Bool) (s : PairSource P) :
    affectedOwner A s.left ≠ affectedOwner A s.right ↔
      A s.left = true ∨ A s.right = true := by
  rw [ne_eq, affectedOwner_eq_iff]
  cases A s.left <;> simp [s.distinct]

namespace SourceInventory

/-- The surviving occurrences are exactly the original sources with at least
one affected endpoint, with their halfspaces and vectors unchanged. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem mem_mapOwner_affectedOwner (A : P → Bool) (S : SourceInventory P)
    (t : PairSource (Option {p // A p = true})) :
    t ∈ mapOwner (affectedOwner A) S ↔
      ∃ s ∈ S, ∃ h : A s.left = true ∨ A s.right = true,
        t = ⟨affectedOwner A s.left, affectedOwner A s.right,
          (s.affectedOwner_ne_iff A).mpr h, s.leftSpace, s.rightSpace, s.vector⟩ := by
  rw [mem_mapOwner]
  constructor
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, (s.affectedOwner_ne_iff A).mp h, rfl⟩
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, (s.affectedOwner_ne_iff A).mpr h, rfl⟩

/-- The ordered pair labels are obtained by retaining exactly the occurrences
with an affected endpoint. This list identity retains multiplicities, even when
different original pairs acquire the same new pair label. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–417. -/
theorem map_partyPair_affectedOwner (A : P → Bool) (S : SourceInventory P) :
    (mapOwner (affectedOwner A) S).map PairSource.partyPair =
      (S.filter (fun s ↦ A s.left || A s.right)).map
        (fun s ↦ Sym2.map (affectedOwner A) s.partyPair) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    cases hl : A s.left <;> cases hr : A s.right <;>
      simp [mapOwner_cons, PairSource.mapOwner, affectedOwner_eq_iff,
        s.distinct, hl, hr, ih, PairSource.partyPair]

/-- No pair sources survive exactly when both endpoints of each original
source are exterior. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–417. -/
theorem mapOwner_affectedOwner_eq_nil_iff (A : P → Bool) (S : SourceInventory P) :
    mapOwner (affectedOwner A) S = [] ↔
      ∀ s ∈ S, A s.left = false ∧ A s.right = false := by
  rw [mapOwner_eq_nil_iff]
  exact forall₂_congr fun s _ ↦ by simp [affectedOwner_eq_iff, s.distinct]

end SourceInventory

end TNLean.PEPS.PairEffect
