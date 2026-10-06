/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.TorusDualRectangleFlux
import TNLean.PEPS.TorusLabelledBondGeometry

/-!
# A one-site collar around the rectangular swept support

The lifted bounds leave a whole native neighbor layer around every swept site.
Consequently a bond crossing the region boundary has neither endpoint in the
swept support. This is a restricted finite bulk geometry for SCP10,
arXiv:1001.3807v3, Lemma 6.14, not an arbitrary-region avoidance result.
-/

namespace TNLean.PEPS

variable {width height : ℕ} [NeZero width] [NeZero height]
local notation "X" => TorusVertex width height

/-- An embedded rectangular dual patch with one extra lifted coordinate in each
period; its collar occupies coordinates zero through side length plus one. -/
structure TorusDualCollar (width height : ℕ) where
  /-- The patch swept by the supported square homotopy. -/
  patch : TorusDualRectangle width height
  /-- The closed horizontal collar interval is embedded. -/
  cols_lt : patch.cols + 1 < width
  /-- The closed vertical collar interval is embedded. -/
  rows_lt : patch.rows + 1 < height

/-- The translated closed one-site collar, including its boundary. -/
def TorusDualCollar.region (C : TorusDualCollar width height) : Set X :=
  {v | ∃ i ≤ C.patch.cols + 1, ∃ j ≤ C.patch.rows + 1,
    v = (torusRectCoord C.patch.origin.1 i, torusRectCoord C.patch.origin.2 j)}

/-- The original primal sites swept by the rectangular square moves. -/
def TorusDualCollar.swept (C : TorusDualCollar width height) : Set X :=
  torusRectInterior C.patch.origin.1 C.patch.origin.2 C.patch.cols C.patch.rows

/-- The collar contains its lower-left corner even for a zero-width swept patch. -/
theorem TorusDualCollar.origin_mem (C : TorusDualCollar width height) :
    C.patch.origin ∈ C.region :=
  ⟨0, by omega, 0, by omega, by simp [torusRectCoord]⟩

/-- The collar projection is injective on the stated closed lifted rectangle. -/
theorem TorusDualCollar.injective (C : TorusDualCollar width height)
    {a b : ℕ × ℕ} (ha : a.1 ≤ C.patch.cols + 1 ∧ a.2 ≤ C.patch.rows + 1)
    (hb : b.1 ≤ C.patch.cols + 1 ∧ b.2 ≤ C.patch.rows + 1)
    (he : (torusRectCoord C.patch.origin.1 a.1, torusRectCoord C.patch.origin.2 a.2) =
      (torusRectCoord C.patch.origin.1 b.1, torusRectCoord C.patch.origin.2 b.2)) : a = b :=
  (TorusDualRectangle.mk C.patch.origin (C.patch.cols + 1) (C.patch.rows + 1)
    C.cols_lt C.rows_lt).injective ha hb he

/-- Every swept site and each of its four native neighbors lie in the collar. -/
theorem TorusDualCollar.neighbors_mem (C : TorusDualCollar width height)
    {v : X} (hv : v ∈ C.swept) :
    v ∈ C.region ∧ (v.1 + 1, v.2) ∈ C.region ∧ (v.1 - 1, v.2) ∈ C.region ∧
      (v.1, v.2 + 1) ∈ C.region ∧ (v.1, v.2 - 1) ∈ C.region := by
  rcases hv with ⟨i, hi, j, hj, rfl⟩
  refine ⟨⟨i + 1, by omega, j + 1, by omega, rfl⟩,
    ⟨i + 2, by omega, j + 1, by omega, ?_⟩,
    ⟨i, by omega, j + 1, by omega, ?_⟩,
    ⟨i + 1, by omega, j + 2, by omega, ?_⟩,
    ⟨i + 1, by omega, j, by omega, ?_⟩⟩
  all_goals simp [torusRectCoord_eq, Nat.cast_add, add_assoc]

/-- Every labelled bond incident to the swept support is internal to the collar. -/
theorem TorusDualCollar.incident_internal (C : TorusDualCollar width height)
    (e : TorusLabelledBond width height)
    (he : torusLabelledBondTail e ∈ C.swept ∨ torusLabelledBondHead e ∈ C.swept) :
    torusLabelledBondTail e ∈ C.region ∧ torusLabelledBondHead e ∈ C.region := by
  rcases e with ⟨⟨x, y⟩, d⟩
  cases d
  · change (x, y) ∈ C.swept ∨ (x + 1, y) ∈ C.swept at he
    change (x, y) ∈ C.region ∧ (x + 1, y) ∈ C.region
    rcases he with ht | hh
    · exact ⟨(C.neighbors_mem ht).1, (C.neighbors_mem ht).2.1⟩
    · exact ⟨by simpa using (C.neighbors_mem hh).2.2.1, (C.neighbors_mem hh).1⟩
  · change (x, y + 1) ∈ C.swept ∨ (x, y) ∈ C.swept at he
    change (x, y + 1) ∈ C.region ∧ (x, y) ∈ C.region
    rcases he with ht | hh
    · exact ⟨(C.neighbors_mem ht).1, by simpa using (C.neighbors_mem ht).2.2.2.2⟩
    · exact ⟨(C.neighbors_mem hh).2.2.2.1, (C.neighbors_mem hh).1⟩

/-- Noninternal bonds, hence all crossing bonds, have both endpoints off the sweep. -/
theorem TorusDualCollar.noninternal_outside (C : TorusDualCollar width height)
    (e : TorusLabelledBond width height)
    (he : ¬ (torusLabelledBondTail e ∈ C.region ∧ torusLabelledBondHead e ∈ C.region)) :
    torusLabelledBondTail e ∉ C.swept ∧ torusLabelledBondHead e ∉ C.swept :=
  ⟨fun h ↦ he (C.incident_internal e (.inl h)),
    fun h ↦ he (C.incident_internal e (.inr h))⟩

end TNLean.PEPS
