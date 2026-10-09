/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DistributedSourceComposition

/-!
# Gate occurrences and common source positions

Gate occurrences distinguish repeated uses of the same operation. Each source
position consists of a gate occurrence and one of that gate's fixed source
slots, independently of all monomial choices. The parties at both endpoints
belong to the actual participant set of that occurrence.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 342–364.

Independently formalized from the manuscript; no upstream Lean proof text is
reused.
-/

noncomputable section

namespace TNLean.PEPS.PairEffect.SourceCircuit

variable {P : Type}

/-- Nonprivate gate occurrences, retaining their positions in the composition.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 342–364. -/
def gateLocations : {a b : Layout P} → SourceCircuit a b → Type
  | _, _, .id _ => Empty
  | _, _, .comp w v => gateLocations w ⊕ gateLocations v
  | _, _, .localMap .. => Empty
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ _ _ => Unit
  | _, _, .swap .. => Empty
  | _, _, .frame _ w => gateLocations w

/-- A finite composition has finitely many nonprivate gate occurrences, even
when the global party type is infinite. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
instance gateLocationsFintype : {a b : Layout P} →
    (w : SourceCircuit a b) → Fintype (gateLocations w)
  | _, _, .id _ => inferInstanceAs (Fintype Empty)
  | _, _, .comp w v => by
      letI := gateLocationsFintype w
      letI := gateLocationsFintype v
      exact inferInstanceAs (Fintype (gateLocations w ⊕ gateLocations v))
  | _, _, .localMap .. => inferInstanceAs (Fintype Empty)
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ _ _ => inferInstanceAs (Fintype Unit)
  | _, _, .swap .. => inferInstanceAs (Fintype Empty)
  | _, _, .frame _ w => gateLocationsFintype w

/-- The fixed number of source positions of the gate at an occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–267 and 342–355. -/
def slotCount : {a b : Layout P} → (w : SourceCircuit a b) → gateLocations w → ℕ
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim (slotCount w) (slotCount v)
  | _, _, .localMap .. => Empty.elim
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ _ G _ => fun _ ↦ G.slots.length
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => slotCount w

/-- A source position is its gate occurrence together with its common slot.
There is no monomial label in this index. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
def sourceLocations {a b : Layout P} (w : SourceCircuit a b) : Type :=
  Σ g : gateLocations w, Fin (slotCount w g)

/-- Every occurrence has finitely many common slots, so the full set of source
positions is finite. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–355. -/
instance sourceLocationsFintype {a b : Layout P} (w : SourceCircuit a b) :
    Fintype (sourceLocations w) := inferInstanceAs (Fintype (Σ g, Fin (slotCount w g)))

/-- The actual participating parties of a nonprivate gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 356–364. -/
def participants : {a b : Layout P} → (w : SourceCircuit a b) →
    gateLocations w → Finset P
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim (participants w) (participants v)
  | _, _, .localMap .. => Empty.elim
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ _ _ => fun _ ↦ Finset.univ.map owner
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => participants w

/-- The two original parties of a source position, transported by its gate's
participant embedding. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
def endpoints : {a b : Layout P} → (w : SourceCircuit a b) → sourceLocations w → P × P
  | _, _, .id _ => fun e ↦ nomatch e.1
  | _, _, .comp w v => by
      rintro ⟨g, i⟩
      cases g with
      | inl g => exact endpoints w ⟨g, i⟩
      | inr g => exact endpoints v ⟨g, i⟩
  | _, _, .localMap .. => fun e ↦ nomatch e.1
  | _, _, @SourceCircuit.gate _ _ _ _ _ owner _ _ _ G _ => fun e ↦
      (owner (G.slots.get e.2).left, owner (G.slots.get e.2).right)
  | _, _, .swap .. => fun e ↦ nomatch e.1
  | _, _, .frame _ w => endpoints w

/-- Both endpoints of each source position participate in its own gate
occurrence. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 342–364. -/
theorem endpoints_mem_participants {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) :
    (endpoints w e).1 ∈ participants w e.1 ∧
      (endpoints w e).2 ∈ participants w e.1 := by
  induction w with
  | id a => exact nomatch e.1
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ⟨g, i⟩
      | inr g => exact ihv ⟨g, i⟩
  | localMap => exact nomatch e.1
  | @gate C ι _ _ owner a b c G tail =>
      rcases e with ⟨g, i⟩
      exact ⟨Finset.mem_map_of_mem owner (Finset.mem_univ _),
        Finset.mem_map_of_mem owner (Finset.mem_univ _)⟩
  | swap => exact nomatch e.1
  | frame r w ih =>
      rcases e with ⟨g, i⟩
      exact ih ⟨g, i⟩

/-- Distinct endpoints remain distinct under the gate's participant embedding.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–245 and 342–364. -/
theorem endpoints_ne {a b : Layout P} (w : SourceCircuit a b)
    (e : sourceLocations w) : (endpoints w e).1 ≠ (endpoints w e).2 := by
  induction w with
  | id a => exact nomatch e.1
  | comp w v ihw ihv =>
      rcases e with ⟨g, i⟩
      cases g with
      | inl g => exact ihw ⟨g, i⟩
      | inr g => exact ihv ⟨g, i⟩
  | localMap => exact nomatch e.1
  | @gate C ι _ _ owner a b c G tail =>
      rcases e with ⟨g, i⟩
      exact fun h ↦ (G.slots.get i).distinct (owner.injective h)
  | swap => exact nomatch e.1
  | frame r w ih =>
      rcases e with ⟨g, i⟩
      exact ih ⟨g, i⟩

/-- The original monomial labels at one nonprivate gate occurrence.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
def branchLabels : {a b : Layout P} → (w : SourceCircuit a b) → gateLocations w → Type
  | _, _, .id _ => Empty.elim
  | _, _, .comp w v => Sum.elim (branchLabels w) (branchLabels v)
  | _, _, .localMap .. => Empty.elim
  | _, _, @SourceCircuit.gate _ _ ι _ _ _ _ _ _ _ _ => fun _ ↦ ι
  | _, _, .swap .. => Empty.elim
  | _, _, .frame _ w => branchLabels w

/-- The labels at an occurrence are precisely its original finite branch set.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 351–381. -/
instance branchLabelsFintype : {a b : Layout P} → (w : SourceCircuit a b) →
    (g : gateLocations w) → Fintype (branchLabels w g)
  | _, _, .id _ => fun g ↦ nomatch g
  | _, _, .comp w v => by
      intro g
      cases g with
      | inl g => exact branchLabelsFintype w g
      | inr g => exact branchLabelsFintype v g
  | _, _, .localMap .. => fun g ↦ nomatch g
  | _, _, @SourceCircuit.gate _ _ ι _ _ _ _ _ _ _ _ =>
      fun _ ↦ inferInstanceAs (Fintype ι)
  | _, _, .swap .. => fun g ↦ nomatch g
  | _, _, .frame _ w => branchLabelsFintype w

/-- The original scalar coefficients at a gate occurrence, before any choice of
affected parties. Source: polynomial-PEPS Theorem 5.2,
`eq:compression-choice-cost`, `04-compression.tex`, lines 351–381. -/
def branchCoefficient : {a b : Layout P} → (w : SourceCircuit a b) →
    (g : gateLocations w) → branchLabels w g → ℂ
  | _, _, .id _ => fun g ↦ nomatch g
  | _, _, .comp w v => by
      intro g
      cases g with
      | inl g => exact branchCoefficient w g
      | inr g => exact branchCoefficient v g
  | _, _, .localMap .. => fun g ↦ nomatch g
  | _, _, @SourceCircuit.gate _ _ _ _ _ _ _ _ c _ _ => fun _ ↦ c
  | _, _, .swap .. => fun g ↦ nomatch g
  | _, _, .frame _ w => branchCoefficient w

/-- A gate occurrence is touched when one of its actual participants is affected.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 356–364. -/
def IsTouched (A : P → Bool) {a b : Layout P} (w : SourceCircuit a b)
    (g : gateLocations w) : Prop := ∃ p ∈ participants w g, A p = true

/-- The occurrence predicate is exactly the gate condition used by the partial
monomial choices. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 356–381. -/
theorem isTouched_gate_iff (A : P → Bool) {C ι : Type} [Fintype C] [Fintype ι]
    (owner : C ↪ P) {a b : Layout C} {c : ι → ℂ}
    (G : PreparedSourceGate c a b) (tail : Layout P) :
    IsTouched A (.gate owner G tail) () ↔ ∃ p : C, A (owner p) = true := by
  simp [IsTouched, participants]

end TNLean.PEPS.PairEffect.SourceCircuit
