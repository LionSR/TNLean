/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.IntervalRegisterLayout
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Interval initialization flags fit in the common workspace

The auxiliaries initialized at the input of an interval consist of its
boundary bond registers and its interior bond and amplification registers.
The output initialization condition tests only the interior auxiliaries.
Every such set, and the joining auxiliaries at a cut, embeds in the fixed
logical auxiliary register. Its cardinality is therefore at most the size
of the common scratch pool. Actual finite selections are constructed below,
including empty selections; no enumeration witness is assumed.

Source: the interval input and image reflections in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

namespace MPUCircuit

/-- Every selected logical auxiliary set fits in the fixed auxiliary
register and its equally sized scratch pool. Source: the common-workspace
allocation in Section 5 of the circuit audit. -/
theorem card_logicalAuxiliarySupport_le {d D N : ℕ}
    (S : Set (LogicalSite d D N))
    (hS : S ⊆ Set.range (auxiliarySiteEmbedding d D N)) :
    Nat.card S ≤ auxiliarySiteCount d D N := by
  let e := Subtype.impEmbedding (· ∈ S)
    (· ∈ Set.range (auxiliarySiteEmbedding d D N)) hS
  calc
    Nat.card S ≤ Nat.card (Set.range (auxiliarySiteEmbedding d D N)) :=
      Nat.card_le_card_of_injective e e.injective
    _ = Nat.card (AuxiliarySite d D N) :=
      Nat.card_range_of_injective (auxiliarySiteEmbedding d D N).injective
    _ = auxiliarySiteCount d D N := by
      rw [Nat.card_eq_fintype_card, card_auxiliarySite]

/-- Interior initialization never selects a physical site. Source: the
interval interior condition in Section 5 of the circuit audit. -/
theorem intervalInteriorAuxiliarySupport_subset_auxiliary_range (d D N j k : ℕ) :
    intervalInteriorAuxiliarySupport d D N j k ⊆
      Set.range (auxiliarySiteEmbedding d D N) := by
  rintro (s | a) hs
  · exact hs.elim
  · exact ⟨a, rfl⟩

/-- Joining initialization never selects a physical site. Source: the
joining registers in Section 5 of the circuit audit. -/
theorem joiningAuxiliarySupport_subset_auxiliary_range (d D N m : ℕ) :
    joiningAuxiliarySupport d D N m ⊆
      Set.range (auxiliarySiteEmbedding d D N) := by
  rintro (s | a) hs
  · exact hs.elim
  · exact ⟨a, rfl⟩

/-- All logical auxiliaries of an interval, including its available boundary
bonds. These are initialized at the interval input. Source: interval input
reflections in Section 5 of the circuit audit. -/
def intervalAuxiliaryInitializationSupport (d D N j k : ℕ) :
    Set (LogicalSite d D N) :=
  intervalLogicalSupport d D N j k ∩ Set.range (auxiliarySiteEmbedding d D N)

/-- The interval input flag set is contained in the allocated logical
auxiliaries. Source: the common-workspace allocation in Section 5 of the
circuit audit. -/
theorem intervalAuxiliaryInitializationSupport_subset_auxiliary_range (d D N j k : ℕ) :
    intervalAuxiliaryInitializationSupport d D N j k ⊆
      Set.range (auxiliarySiteEmbedding d D N) :=
  fun _ hs ↦ hs.2

/-- The interval output initialization flags fit in one common pool. Source:
interval image reflections in Section 5 of the circuit audit. -/
theorem card_intervalInteriorAuxiliarySupport_le (d D N j k : ℕ) :
    Nat.card (intervalInteriorAuxiliarySupport d D N j k) ≤ auxiliarySiteCount d D N :=
  card_logicalAuxiliarySupport_le _
    (intervalInteriorAuxiliarySupport_subset_auxiliary_range d D N j k)

/-- The joining initialization flags fit in one common pool. Source: success
reflections at a joining cut in Section 5 of the circuit audit. -/
theorem card_joiningAuxiliarySupport_le (d D N m : ℕ) :
    Nat.card (joiningAuxiliarySupport d D N m) ≤ auxiliarySiteCount d D N :=
  card_logicalAuxiliarySupport_le _
    (joiningAuxiliarySupport_subset_auxiliary_range d D N m)

/-- The interval input flags, including boundary bonds, fit in one common
pool. Source: interval input reflections in Section 5 of the circuit audit. -/
theorem card_intervalAuxiliaryInitializationSupport_le (d D N j k : ℕ) :
    Nat.card (intervalAuxiliaryInitializationSupport d D N j k) ≤ auxiliarySiteCount d D N :=
  card_logicalAuxiliarySupport_le _
    (intervalAuxiliaryInitializationSupport_subset_auxiliary_range d D N j k)

/-- Consecutive enumeration of an actual logical support set. Its values are
placed in the fixed logical register, with no supplied selection witness.
Source: the selected zero-register reflections in Section 5 of the circuit
audit. -/
noncomputable def logicalSupportSites {d D N : ℕ} (S : Set (LogicalSite d D N)) :
    Fin (Nat.card S) ↪ Fin (logicalSiteCount d D N) := by
  classical
  exact (Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm :
      Fintype.card S = Nat.card S)).symm.toEmbedding.trans
    ((Function.Embedding.subtype (· ∈ S)).trans (logicalSiteEquivFin d D N).toEmbedding)

/-- The finite selection enumerates precisely the given logical support in
the fixed consecutive numbering. Source: the initialized selections in
Section 5 of the circuit audit. -/
theorem logicalSupportSites_range {d D N : ℕ} (S : Set (LogicalSite d D N)) :
    Set.range (logicalSupportSites S) = (logicalSiteEquivFin d D N) '' S := by
  classical
  unfold logicalSupportSites
  simp only [Function.Embedding.coe_trans, Equiv.coe_toEmbedding, Set.range_comp,
    Equiv.range_eq_univ, Set.image_univ, Function.Embedding.coe_subtype,
    Subtype.range_coe]

/-- Testing zero on the constructed finite selection is exactly the typed
initialization condition, without a loss or addition of flags. Source:
interval input, image, and success reflections in Section 5 of the audit. -/
theorem logicalSupportSites_initialized_iff {d D N : ℕ} (S : Set (LogicalSite d D N))
    (x : MPSTensor.Cfg d (logicalSiteCount d D N)) (z : Fin d) :
    (∀ i, x (logicalSupportSites S i) = z) ↔
      ∀ s ∈ S, x (logicalSiteEquivFin d D N s) = z := by
  refine (Set.forall_mem_range (f := (logicalSupportSites S :
    Fin (Nat.card S) → Fin (logicalSiteCount d D N))) (p := fun i ↦ x i = z)).symm.trans ?_
  rw [logicalSupportSites_range, Set.forall_mem_image]

end MPUCircuit
