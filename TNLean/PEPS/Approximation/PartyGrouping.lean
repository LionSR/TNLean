/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyTensorMaps

/-!
# Grouping all registers by party

An ordered list containing each owner exactly once determines a canonical isometric
identification between the original memory and the tensor product of the individual parties'
memories. The construction successively separates each party from the remaining registers.

Source: Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 233–251.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.PairEffect

variable {P : Type}

attribute [local instance] Classical.propDecidable

namespace Layout

/-- All registers except those owned by the specified party, in their original order. -/
def withoutParty (p : P) (ℓ : Layout P) : Layout P := by
  classical
  exact restrict (fun q ↦ !decide (q = p)) ℓ

/-- Removing one party leaves the registers of every other party unchanged. -/
theorem atParty_withoutParty (p q : P) (ℓ : Layout P) (hqp : q ≠ p) :
    atParty q (withoutParty p ℓ) = atParty q ℓ := by
  classical
  simp only [atParty, withoutParty, restrict, List.filter_filter]
  apply List.filter_congr
  intro r hr
  by_cases hrq : r.owner = q <;> simp [hrq, hqp]

@[simp] theorem mem_withoutParty (p : P) (ℓ : Layout P) (r : Reg P) :
    r ∈ withoutParty p ℓ ↔ r ∈ ℓ ∧ r.owner ≠ p := by
  classical
  simp [withoutParty, restrict]

/-- After the first party is removed, the remaining parties still cover all owners. -/
theorem owners_withoutParty {p : P} {ps : List P} {ℓ : Layout P}
    (h : ∀ r ∈ ℓ, r.owner ∈ p :: ps) :
    ∀ r ∈ withoutParty p ℓ, r.owner ∈ ps := by
  intro r hr
  have hm := (mem_withoutParty p ℓ r).mp hr
  simpa [hm.2] using h r hm.1

end Layout

/-- Removing a party not in the prescribed list leaves its grouped layout unchanged. -/
theorem partyLayout_withoutParty (ps : List P) (p : P) (ℓ : Layout P) (hp : p ∉ ps) :
    partyLayout ps (Layout.withoutParty p ℓ) = partyLayout ps ℓ := by
  apply List.map_congr_left
  intro q hq
  rw [Layout.atParty_withoutParty p q ℓ (by intro h; exact hp (h ▸ hq))]

/-- Canonically collect the registers of each party into one tensor factor. The order of the
parties is prescribed by a list without repetitions containing every register owner.
Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`, lines 233–251. -/
def groupByPartyIso : (ps : List P) → (ℓ : Layout P) → ps.Nodup →
    (∀ r ∈ ℓ, r.owner ∈ ps) → Mem ℓ ≃ₗᵢ[ℂ] Mem (partyLayout ps ℓ)
  | [], ℓ, _, h => Layout.memCongr (List.eq_nil_iff_forall_not_mem.mpr
      (fun r hr ↦ by simpa using h r hr))
  | p :: ps, ℓ, hn, h => by
      classical
      exact (Layout.partitionIso (fun q ↦ decide (q = p)) ℓ).trans
        (((groupByPartyIso ps (Layout.withoutParty p ℓ) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty h)).trans
            (Layout.memCongr (partyLayout_withoutParty ps p ℓ (List.nodup_cons.mp hn).1))).lTensor
              (Mem (Layout.atParty p ℓ)))

/-- The recursive separation of the first party in the canonical grouping isometry. -/
theorem groupByPartyIso_cons (p : P) (ps : List P) (ℓ : Layout P)
    (hn : (p :: ps).Nodup) (h : ∀ r ∈ ℓ, r.owner ∈ p :: ps) :
    groupByPartyIso (p :: ps) ℓ hn h =
      (Layout.partitionIso (fun q ↦ decide (q = p)) ℓ).trans
        (((groupByPartyIso ps (Layout.withoutParty p ℓ) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty h)).trans
            (Layout.memCongr (partyLayout_withoutParty ps p ℓ (List.nodup_cons.mp hn).1))).lTensor
              (Mem (Layout.atParty p ℓ))) := rfl

end TNLean.PEPS.PairEffect
