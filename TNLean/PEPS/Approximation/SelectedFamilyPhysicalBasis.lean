/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyOutputCoordinates
import TNLean.PEPS.Approximation.OwnerMemoryTransport
import TNLean.PEPS.Approximation.LayoutExcludedOwners
import TNLean.Lattice.PartyCircuit.AffectedOwners

/-! # Physical party bases after selecting every original party

Selecting every original party preserves each physical register and its original
dimension. The exterior owner has no physical register and carries the canonical
scalar basis. The original singleton bases are transported by the canonical
owner identifications; no equality between independently chosen bases is assumed.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–151, 409–434 and 565–588.
-/

noncomputable section
namespace TNLean.PEPS.PairEffect
variable {P : Type}

namespace Layout

/-- Selecting all original parties leaves no register at the exterior owner.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem atParty_none_mapOwner_all (a : Layout P) :
    atParty none (mapOwner (affectedOwner (fun _ : P ↦ true)) a) = [] := by
  classical
  unfold atParty
  apply restrict_mapOwner_eq_nil
  intro p
  simp [affectedOwner]

/-- A selected party retains exactly its original registers after owner relabelling.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417. -/
theorem atParty_some_mapOwner_all (a : Layout P) (p : {_p : P // true = true}) :
    atParty (some p) (mapOwner (affectedOwner (fun _ : P ↦ true)) a) =
      mapOwner (affectedOwner (fun _ : P ↦ true)) (atParty p.val a) := by
  classical
  unfold atParty
  rw [restrict_mapOwner]
  apply congrArg (mapOwner (affectedOwner (fun _ : P ↦ true)))
  apply congrArg (fun f : P → Bool ↦ restrict f a)
  funext q
  rw [Bool.eq_iff_iff]
  simp [affectedOwner, Subtype.ext_iff]

end Layout

/-- The original physical coordinate at a selected party, with a singleton
coordinate for the empty exterior memory. No dimension is padded.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 565–588. -/
def selectedFamilyPhysicalIndex (d : P → ℕ) : Option {_p : P // true = true} → Type
  | none => PUnit
  | some p => Fin (d p.val)

instance (d : P → ℕ) (q : Option {_p : P // true = true}) :
    Fintype (selectedFamilyPhysicalIndex d q) := by
  cases q <;> dsimp [selectedFamilyPhysicalIndex] <;> infer_instance

/-- The physical party basis induced by the actual original registers. At the
exterior owner it is the scalar basis with column one.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
409–434 and 565–588. -/
def selectedFamilyPhysicalPartyBasis (d : P → ℕ) (ps : List P) (hn : ps.Nodup)
    (hc : ∀ p, p ∈ ps) (q : Option {_p : P // true = true}) :
    OrthonormalBasis (selectedFamilyPhysicalIndex d q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps)))) :=
  match q with
  | none => (OrthonormalBasis.singleton PUnit ℂ).map
      (Layout.memCongr (Layout.atParty_none_mapOwner_all (familyPhysicalLayout d ps)).symm)
  | some p => (familyPhysicalPartyBasis d ps hn p.val (hc p.val)).map
      ((Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
        (Layout.atParty p.val (familyPhysicalLayout d ps))).trans
          (Layout.memCongr
            (Layout.atParty_some_mapOwner_all (familyPhysicalLayout d ps) p).symm))

/-- The exterior physical basis has the canonical scalar column, independently
of the party set and every physical dimension.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–417 and 565–588. -/
theorem selectedFamilyPhysicalPartyBasis_none_apply_heq
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) (x : PUnit) :
    HEq (selectedFamilyPhysicalPartyBasis d ps hn hc none x) (1 : ℂ) := by
  change HEq
    (Layout.memCongr (Layout.atParty_none_mapOwner_all (familyPhysicalLayout d ps)).symm
      ((OrthonormalBasis.singleton PUnit ℂ) x)) (1 : ℂ)
  exact (Layout.memCongr_apply_heq _ _).trans
    (heq_of_eq (OrthonormalBasis.singleton_apply x))

/-- Each selected physical column is the original party column under the
canonical relabelling, without a supplied coordinate identification.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 565–588. -/
theorem selectedFamilyPhysicalPartyBasis_some_apply_heq
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (p : {_p : P // true = true}) (x : Fin (d p.val)) :
    HEq (selectedFamilyPhysicalPartyBasis d ps hn hc (some p) x)
      (familyPhysicalPartyBasis d ps hn p.val (hc p.val) x) := by
  change HEq
    (Layout.memCongr
      (Layout.atParty_some_mapOwner_all (familyPhysicalLayout d ps) p).symm
      (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
        (Layout.atParty p.val (familyPhysicalLayout d ps))
        (familyPhysicalPartyBasis d ps hn p.val (hc p.val) x)))
    (familyPhysicalPartyBasis d ps hn p.val (hc p.val) x)
  exact (Layout.memCongr_apply_heq _ _).trans (Layout.mapOwnerIso_apply_heq _ _ _)

end TNLean.PEPS.PairEffect
