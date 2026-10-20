/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedFamilyPhysicalBasis

/-!
# Local physical and private bases after selecting every original party

The actual output layout is obtained by relabelling the original physical and
private registers together. Its local basis is the tensor product of the
selected physical basis and a basis of the actual private memory, transported
along the canonical equality of register lists. The physical coordinate remains
the original party-dependent coordinate; the exterior physical coordinate is
the singleton scalar coordinate.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–151, 409–434 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}
variable {E : Option {_p : P // true = true} → Type} [∀ q, Fintype (E q)]

/-- The local physical/private basis on the actual jointly relabelled output.
Its physical index is the original index at a selected party and the singleton
index at the exterior owner. The private basis is on the actual relabelled
private registers.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
409–434 and 565–588. -/
def selectedPhysicalPrivateBasis (d : P → ℕ) (ps : List P) (hn : ps.Nodup)
    (hc : ∀ p, p ∈ ps) (garbage : Layout P)
    (bGarbage : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (q : Option {_p : P // true = true}) :
    OrthonormalBasis (selectedFamilyPhysicalIndex d q × E q) ℂ
      (Mem (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage)))) := by
  classical
  exact (partyLocalOutputBasis
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)
    (selectedFamilyPhysicalPartyBasis d ps hn hc) bGarbage q).map
      (Layout.memCongr (congrArg (Layout.atParty q)
        (Layout.mapOwner_append (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps) garbage)).symm)

/-- Each actual local output column is the canonical concatenation of its
selected physical column and its actual private column. This identification
is derived from the register-list equalities.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
409–434 and 565–588. -/
theorem selectedPhysicalPrivateBasis_apply_heq
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P)
    (bGarbage : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (q : Option {_p : P // true = true})
    (x : selectedFamilyPhysicalIndex d q) (e : E q) :
    HEq (selectedPhysicalPrivateBasis d ps hn hc garbage bGarbage q (x, e))
      ((appendIso
        (Layout.atParty q (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps)))
        (Layout.atParty q
          (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))).symm
        (selectedFamilyPhysicalPartyBasis d ps hn hc q x ⊗ₜ[ℂ] bGarbage q e)) := by
  classical
  simp only [selectedPhysicalPrivateBasis, partyLocalOutputBasis,
    OrthonormalBasis.map_apply, OrthonormalBasis.tensorProduct_apply,
    LinearIsometryEquiv.trans_apply]
  exact (Layout.memCongr_apply_heq _ _).trans (Layout.memCongr_apply_heq _ _)

end TNLean.PEPS.PairEffect
