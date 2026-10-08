/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PairSourceGrouping

/-!
# Pair sources after grouping parties

An arbitrary map of parties can turn a pair source into a local preparation.
The remaining pair-source inventory keeps precisely those occurrences whose
new owners are distinct, with their original halfspaces, vectors, and order.
Different original pairs can become the same pair, so no distinctness of the
new pair labels is asserted.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, the separation into affected and exterior parties,
lines 383–427.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-block-contraction.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect

variable {P Q : Type}

/-- Retain a pair source exactly when its new owners differ. The halfspaces
and vector are unchanged. Sources whose owners merge become local preparations.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
def PairSource.mapOwner (f : P → Q) (s : PairSource P) : Option (PairSource Q) := by
  classical
  exact if h : f s.left = f s.right then none else
    some ⟨f s.left, f s.right, h, s.leftSpace, s.rightSpace, s.vector⟩

namespace SourceInventory

/-- The ordered inventory of sources that remain nonlocal after grouping parties.
This records source occurrences, without combining newly coincident pairs.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
def mapOwner (f : P → Q) (S : SourceInventory P) : SourceInventory Q :=
  S.filterMap (PairSource.mapOwner f)

@[simp] theorem mapOwner_nil (f : P → Q) : mapOwner f [] = [] := rfl

@[simp] theorem mapOwner_cons (f : P → Q) (s : PairSource P) (S : SourceInventory P) :
    mapOwner f (s :: S) =
      match s.mapOwner f with
      | none => mapOwner f S
      | some t => t :: mapOwner f S := by
  cases h : s.mapOwner f <;> simp [mapOwner, h]

@[simp] theorem mapOwner_append (f : P → Q) (S T : SourceInventory P) :
    mapOwner f (S ++ T) = mapOwner f S ++ mapOwner f T := List.filterMap_append

/-- Membership retains the complete original source data, with only its two
owners changed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 383–427. -/
theorem mem_mapOwner (f : P → Q) (S : SourceInventory P) (t : PairSource Q) :
    t ∈ mapOwner f S ↔ ∃ s ∈ S, ∃ h : f s.left ≠ f s.right,
      t = ⟨f s.left, f s.right, h, s.leftSpace, s.rightSpace, s.vector⟩ := by
  classical
  simp only [mapOwner, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, ht⟩
    by_cases h : f s.left = f s.right
    · simp [PairSource.mapOwner, h] at ht
    · exact ⟨s, hs, h, (Option.some.inj (by simpa [PairSource.mapOwner, h] using ht)).symm⟩
  · rintro ⟨s, hs, h, rfl⟩
    exact ⟨s, hs, by simp [PairSource.mapOwner, h]⟩

/-- Every surviving source remains normalized because its vector is unchanged.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem IsNormalized.mapOwner {S : SourceInventory P} (hS : S.IsNormalized)
    (f : P → Q) : (mapOwner f S).IsNormalized := by
  intro t ht
  obtain ⟨s, hs, h, rfl⟩ := (mem_mapOwner f S t).mp ht
  exact hS s hs

/-- No pair sources remain exactly when every original source becomes internal
to one new party. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 409–427. -/
theorem mapOwner_eq_nil_iff (f : P → Q) (S : SourceInventory P) :
    mapOwner f S = [] ↔ ∀ s ∈ S, f s.left = f s.right := by
  classical
  simp [mapOwner, PairSource.mapOwner]

open Classical in
/-- The pair labels are exactly the non-diagonal images of the original labels,
with their occurrence order and multiplicity retained. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem map_partyPair_mapOwner (f : P → Q) (S : SourceInventory P) :
    (mapOwner f S).map PairSource.partyPair =
      (S.map PairSource.partyPair).filterMap
        (fun k ↦ if (Sym2.map f k).IsDiag then none else some (Sym2.map f k)) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
    by_cases h : f s.left = f s.right
    all_goals simp [mapOwner_cons, PairSource.mapOwner, PairSource.partyPair, h, ih]

/-- A surviving pair is a non-diagonal image of an original pair. No injectivity
or distinctness of the original pair labels is required. Source: polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 383–427. -/
theorem mem_partyPair_mapOwner (f : P → Q) (S : SourceInventory P) (k : Sym2 Q) :
    k ∈ (mapOwner f S).map PairSource.partyPair ↔
      ¬k.IsDiag ∧ ∃ e ∈ S.map PairSource.partyPair, Sym2.map f e = k := by
  classical
  rw [map_partyPair_mapOwner, List.mem_filterMap]
  constructor
  · rintro ⟨e, he, hk⟩
    by_cases hd : (Sym2.map f e).IsDiag
    · simp [hd] at hk
    · have heq : Sym2.map f e = k := by simpa [hd] using hk
      exact ⟨heq ▸ hd, e, he, heq⟩
  · rintro ⟨hk, e, he, rfl⟩
    exact ⟨e, he, by simp [hk]⟩

end SourceInventory

end TNLean.PEPS.PairEffect
