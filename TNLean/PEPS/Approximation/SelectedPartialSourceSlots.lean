/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.ActualSourceRegisters
import TNLean.PEPS.Approximation.IncidentGateLabels
import TNLean.PEPS.Approximation.PartyTensorMaps

/-! # Selected source slots in the singleton and all-party groupings

The selected half-registers have the same original order and Euclidean spaces
whether the exterior of one party is grouped together or every party is retained.
The comparison uses only original source positions and their dimensions. It does
not require a monomial choice, including at gates with empty branch index sets.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 253–267, 342–417 and 409–434.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect.SourceCircuit
variable {P : Type}

/-- The prescribed endpoint spaces recover the fixed partial-slot layout,
without choosing any branch labels or prepared source vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267
and 342–417. -/
theorem slotLayout_partialSlots_eq_layout (A : P → Bool) {a b : Layout P}
    (w : SourceCircuit a b) :
    SourceInventory.slotLayout (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) =
        (partialSlots A w).layout := by
  let R := partialSlots A w
  have hU : (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1)) =
      (fun i : Fin R.length ↦ (R.get i).leftSpace) :=
    funext fun i ↦ (partialSlot_spec A w i).2.2.1.symm
  have hV : (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)) =
      (fun i : Fin R.length ↦ (R.get i).rightSpace) :=
    funext fun i ↦ (partialSlot_spec A w i).2.2.2.symm
  rw [hU, hV]
  exact (SourceInventory.layout_ofSlots_eq R _ _ (fun _ ↦ 0)
    (fun i ↦ (R.get i).vector)).trans
      (congrArg SourceInventory.layout (List.ofFn_get R))

/-- Selecting one original party gives the same ordered source half-registers
in the singleton and all-party groupings, after the canonical owner relabelling.
The slots use the actual original dimensions and position equivalence; no global
monomial choices are assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 253–267,
383–417 and 409–434. -/
theorem mapOwner_atParty_partialSlots_eq_allResidualSourceLayout {a b : Layout P}
    (w : SourceCircuit a b) (p : P) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    Layout.mapOwner lift (Layout.atParty q
      (SourceInventory.slotLayout (partialSlots A w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)))) =
      Layout.atParty (some ⟨p, rfl⟩) w.allResidualSourceLayout := by
  classical
  intro A hp q lift
  change Layout.mapOwner lift (Layout.atParty q
    (SourceInventory.slotLayout (partialSlots A w)
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).1))
      (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv A w i).1).2)))) =
    Layout.atParty (some ⟨p, rfl⟩)
      (SourceInventory.slotLayout (partialSlots (fun _ ↦ true) w)
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (fun _ ↦ true) w i).1).1))
        (fun i ↦ euc (Fin (sourceDims w (partialSlotEquiv (fun _ ↦ true) w i).1).2)))
  rw [slotLayout_partialSlots_eq_layout, slotLayout_partialSlots_eq_layout,
    layout_partialSlots, layout_partialSlots]
  simp only [partialPositions]
  generalize sourceOrder w = L
  induction L with
  | nil => rfl
  | cons e L ih =>
      by_cases hl : (endpoints w e).1 = p <;>
        by_cases hr : (endpoints w e).2 = p <;>
        simpa [List.flatMap_cons, Layout.atParty, Layout.restrict,
          Layout.mapOwner, A, q, lift, partySelector, affectedOwner, hl, hr] using ih

/-- The selected original registers have the same order and spaces after
singleton and all-party owner grouping. Source: polynomial-PEPS Theorem 5.2,
`04-compression.tex`, lines 409–434 and 565–588. -/
theorem mapOwner_selected_originalLayout_eq (p : P) (L : Layout P) :
    let A : P → Bool := fun t ↦ partySelector (some ⟨p, rfl⟩)
      (affectedOwner (fun _ : P ↦ true) t)
    let hp : A p = true := (partySelector_affectedOwner_all_apply p p).trans
      (by classical exact decide_eq_true rfl)
    let q : Option {t : P // A t = true} := some ⟨p, hp⟩
    let lift : Option {t : P // A t = true} → Option {_t : P // true = true} :=
      fun o ↦ o.map (fun t ↦ ⟨t.1, rfl⟩)
    Layout.mapOwner lift
        (Layout.atParty q (Layout.mapOwner (affectedOwner A) L)) =
      Layout.atParty (some ⟨p, rfl⟩)
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) L) := by
  classical
  intro A hp q lift
  let all := affectedOwner (fun _ : P ↦ true)
  let qp : Option {_p : P // true = true} := some ⟨p, rfl⟩
  induction L with
  | nil => rfl
  | cons r L ih =>
      by_cases hr : r.owner = p
      · have hOne : affectedOwner A r.owner = q := by
          simp only [affectedOwner, hr, hp, q, ↓reduceDIte]
        have hAll : all r.owner = qp := by
          simp only [all, qp, affectedOwner, hr, ↓reduceDIte]
        change Layout.mapOwner lift
          (Layout.atParty q (Layout.mapOwner (affectedOwner A) (r :: L))) =
          Layout.atParty qp (Layout.mapOwner all (r :: L))
        simp only [Layout.mapOwner_cons, Layout.atParty, Layout.restrict_cons,
          hOne, hAll, decide_true, ↓reduceIte]
        exact congrArg ((⟨qp, r.space⟩ : Reg (Option {_p : P // true = true})) :: ·) ih
      · have hA : A r.owner = false := by
          change partySelector (some ⟨p, rfl⟩)
            (affectedOwner (fun _ : P ↦ true) r.owner) = false
          rw [partySelector_affectedOwner_all_apply]
          simp only [partySelector, hr, decide_false]
        have hOne : affectedOwner A r.owner ≠ q := by
          rw [(affectedOwner_eq_none A r.owner).mpr hA]
          intro h
          exact Option.noConfusion h
        have hAll : all r.owner ≠ qp := by
          intro h
          change (some ⟨r.owner, rfl⟩ : Option {_p : P // true = true}) = some ⟨p, rfl⟩ at h
          exact hr (congrArg Subtype.val (Option.some.inj h))
        change Layout.mapOwner lift
          (Layout.atParty q (Layout.mapOwner (affectedOwner A) (r :: L))) =
          Layout.atParty qp (Layout.mapOwner all (r :: L))
        simp only [Layout.mapOwner_cons, Layout.atParty, Layout.restrict_cons,
          hOne, hAll, decide_false, Bool.false_eq_true, ↓reduceIte]
        exact ih

end TNLean.PEPS.PairEffect.SourceCircuit
