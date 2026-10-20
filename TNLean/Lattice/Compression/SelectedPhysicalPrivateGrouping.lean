/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.SelectedPhysicalPrivateBasis
/-!
# Separating the actual grouped physical and private output bases

The local physical/private bases live on the jointly relabelled output layout.
After separating their two coordinate families, their grouped basis is the
tensor product of the separately grouped physical and private bases, transported
to that actual layout. The physical indices are the original party-dependent
indices and the exterior singleton coordinate. The private bases are arbitrary
bases on the actual private memories.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect

private theorem partyGroupedBasis_map_memCongr
    {Q : Type} [Fintype Q] [DecidableEq Q]
    {I : Q → Type} [∀ q, Fintype (I q)] {a a' : Layout Q}
    (h : a = a')
    (b : ∀ q, OrthonormalBasis (I q) ℂ (Mem (Layout.atParty q a)))
    (qs : List Q) (hn : qs.Nodup) (hc : ∀ q, q ∈ qs) :
    partyGroupedBasis a'
        (fun q ↦ (b q).map (Layout.memCongr (congrArg (Layout.atParty q) h))) qs hn hc =
      (partyGroupedBasis a b qs hn hc).map (Layout.memCongr h) := by
  cases h
  have hb : (fun q ↦ (b q).map
      (Layout.memCongr (congrArg (Layout.atParty q) (rfl : a = a)))) = b := by
    funext q
    apply DFunLike.ext
    intro i
    rfl
  rw [hb]
  apply DFunLike.ext
  intro x
  rfl

variable {P : Type} [Fintype P] [DecidableEq P]
variable {E : Option {_p : P // true = true} → Type} [∀ q, Fintype (E q)]

/-- Grouping the actual local physical/private bases separates their two
coordinate families into the tensor product of the actual physical and private
grouped bases. The specified selected-owner order may be any exhaustive order
without repetitions. No equality of independently chosen bases is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem selectedPhysicalPrivateBasis_grouped
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (garbage : Layout P)
    (bGarbage : ∀ q, OrthonormalBasis (E q) ℂ
      (Mem (Layout.atParty q
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage))))
    (qs : List (Option {_p : P // true = true})) (hnq : qs.Nodup)
    (hcq : ∀ q, q ∈ qs) :
    (partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage))
      (selectedPhysicalPrivateBasis d ps hn hc garbage bGarbage) qs hnq hcq).reindex
        (Equiv.arrowProdEquivProdArrow (Option {_p : P // true = true})
          (selectedFamilyPhysicalIndex d) E) =
      ((partyGroupedBasis
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
        (selectedFamilyPhysicalPartyBasis d ps hn hc) qs hnq hcq).tensorProduct
        (partyGroupedBasis
          (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)
          bGarbage qs hnq hcq)).map
            ((appendIso
              (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
              (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage)).symm.trans
                (Layout.memCongr (Layout.mapOwner_append
                  (affectedOwner (fun _ : P ↦ true))
                  (familyPhysicalLayout d ps) garbage).symm)) := by
  classical
  let physical := Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
    (familyPhysicalLayout d ps)
  let privateLayout := Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) garbage
  let bPhysical := selectedFamilyPhysicalPartyBasis d ps hn hc
  let bJoined := partyLocalOutputBasis physical privateLayout bPhysical bGarbage
  let h := (Layout.mapOwner_append (affectedOwner (fun _ : P ↦ true))
    (familyPhysicalLayout d ps) garbage).symm
  have hGrouped : partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true))
        (familyPhysicalLayout d ps ++ garbage))
      (selectedPhysicalPrivateBasis d ps hn hc garbage bGarbage) qs hnq hcq =
      (partyGroupedBasis (physical ++ privateLayout) bJoined qs hnq hcq).map
        (Layout.memCongr h) :=
    partyGroupedBasis_map_memCongr h bJoined qs hnq hcq
  have hAppend := partyGroupedBasis_append physical privateLayout bPhysical bGarbage qs hnq hcq
  apply DFunLike.ext
  intro xy
  rcases xy with ⟨x, y⟩
  rw [OrthonormalBasis.reindex_apply, hGrouped, OrthonormalBasis.map_apply]
  have hColumn := DFunLike.congr_fun hAppend (x, y)
  simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply] at hColumn
  simp only [OrthonormalBasis.map_apply, OrthonormalBasis.tensorProduct_apply,
    LinearIsometryEquiv.trans_apply]
  exact congrArg (Layout.memCongr h) hColumn

end TNLean.PEPS.PairEffect
