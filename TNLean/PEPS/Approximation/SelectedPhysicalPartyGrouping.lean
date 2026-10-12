/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SelectedPhysicalConfigurations
import TNLean.PEPS.Approximation.FamilyPhysicalOwnerColumns
import TNLean.PEPS.Approximation.EmptyHeadGrouping

/-!
# Grouping the original physical coordinates after selecting all parties

The prescribed party order starts with the empty exterior party and retains
the original order of all physical parties. Its grouped physical basis agrees
with the original physical basis transported by the owner isometry. The exterior
party contributes its scalar unit; no physical register is adjoined.

Source: polynomial-PEPS manuscript (September 24, 2026), Theorem 5.2,
`04-compression.tex`, lines 137–151, 409–434 and 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect
variable {P : Type}

/-- The empty exterior party precedes the original ordered physical parties.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
def selectedPartyOrder (ps : List P) : List (Option {_p : P // true = true}) :=
  none :: ps.map (affectedOwner (fun _ : P ↦ true))

/-- The selected order has no repetitions whenever the original order has none.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 565–588. -/
theorem selectedPartyOrder_nodup (ps : List P) (hn : ps.Nodup) :
    (selectedPartyOrder ps).Nodup := by
  apply List.nodup_cons.mpr
  refine ⟨by simp [affectedOwner], hn.map ?_⟩
  intro p q h
  simpa using (affectedOwner_eq_iff (fun _ : P ↦ true) p q).mp h

/-- An exhaustive original order remains exhaustive after adjoining the exterior
party, including when the original party set is empty.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 409–434 and 565–588. -/
theorem mem_selectedPartyOrder (ps : List P) (hc : ∀ p, p ∈ ps)
    (q : Option {_p : P // true = true}) : q ∈ selectedPartyOrder ps := by
  cases q with
  | none => exact List.mem_cons_self
  | some p =>
      apply List.mem_cons_of_mem
      simpa [affectedOwner] using
        List.mem_map_of_mem (f := affectedOwner (fun _ : P ↦ true)) (hc p.val)

private theorem partyListBasis_apply_heq_of_layout_eq
    {Q : Type} {I : Q → Type} [∀ q, Fintype (I q)] {a a' : Layout Q}
    (h : a = a')
    (b : ∀ q, OrthonormalBasis (I q) ℂ (Mem (Layout.atParty q a)))
    (b' : ∀ q, OrthonormalBasis (I q) ℂ (Mem (Layout.atParty q a')))
    (hb : ∀ q i, HEq (b q i) (b' q i)) (qs : List Q) (y : ∀ q, I q) :
    HEq (partyListBasis a b qs (fun i ↦ y (qs.get i)))
      (partyListBasis a' b' qs (fun i ↦ y (qs.get i))) := by
  cases h
  have hbb : b = b' := by
    funext q
    apply DFunLike.ext
    intro i
    exact eq_of_heq (hb q i)
  cases hbb
  rfl

private theorem selected_physical_grouped_column
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps)
    (x : (p : P) → Fin (d p)) :
    groupByPartyIso (selectedPartyOrder ps)
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
        (selectedPartyOrder_nodup ps hn)
        (fun r _ ↦ mem_selectedPartyOrder ps hc r.owner)
        (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps)
          (familyPhysicalListBasis d ps (fun i ↦ x (ps.get i)))) =
      partyListBasis
        (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
        (selectedFamilyPhysicalPartyBasis d ps hn hc) (selectedPartyOrder ps)
        (fun i ↦ (selectedFamilyPhysicalConfigEquiv d).symm x
          ((selectedPartyOrder ps).get i)) := by
  classical
  let f := affectedOwner (fun _ : P ↦ true)
  let qs := ps.map f
  let a := Layout.mapOwner f (familyPhysicalLayout d ps)
  let δ : Option {_p : P // true = true} → ℕ
    | none => 1
    | some p => d p.val
  let u : (q : Option {_p : P // true = true}) → Fin (δ q)
    | none => 0
    | some p => x p.val
  let y := (selectedFamilyPhysicalConfigEquiv d).symm x
  let b := selectedFamilyPhysicalPartyBasis d ps hn hc
  let z := Layout.mapOwnerIso f (familyPhysicalLayout d ps)
    (familyPhysicalListBasis d ps (fun i ↦ x (ps.get i)))
  have ha : a = familyPhysicalLayout δ qs := by
    dsimp only [a, qs, Layout.mapOwner, familyPhysicalLayout]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro p _
    rfl
  have hnqs : qs.Nodup := (List.nodup_cons.mp (selectedPartyOrder_nodup ps hn)).2
  have hδ : ∀ r ∈ familyPhysicalLayout δ qs, r.owner ∈ qs := by
    intro r hr
    exact (familyPhysicalLayout_owners δ qs) ▸
      (List.mem_map_of_mem (f := Reg.owner) hr)
  have howners : ∀ r ∈ a, r.owner ∈ qs := fun r hr ↦ hδ r (ha ▸ hr)
  let b' := fun q ↦ (b q).map (Layout.memCongr (congrArg (Layout.atParty q) ha))
  have hb : ∀ q i, HEq (b q i) (b' q i) := by
    intro q i
    exact (Layout.memCongr_apply_heq _ _).symm
  have hv : ∀ q ∈ qs, HEq (b' q (y q))
      ((EuclideanSpace.basisFun (Fin (δ q)) ℂ) (u q) ⊗ₜ[ℂ] (1 : ℂ)) := by
    intro q hq
    rcases List.mem_map.mp hq with ⟨p, _, rfl⟩
    apply (Layout.memCongr_apply_heq _ _).trans
    change HEq (selectedFamilyPhysicalPartyBasis d ps hn hc (some ⟨p, rfl⟩) (x p))
      ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ] (1 : ℂ))
    apply (selectedFamilyPhysicalPartyBasis_some_apply_heq d ps hn hc
      ⟨p, rfl⟩ (x p)).trans
    simp only [familyPhysicalPartyBasis, OrthonormalBasis.map_apply,
      LinearIsometryEquiv.trans_apply, TensorProduct.symm_ridIsometry_apply]
    exact Layout.memCongr_apply_heq _ _
  have hz : HEq z
      (familyPhysicalListBasis δ qs (fun i ↦ u (qs.get i))) :=
    mapOwnerIso_familyPhysicalListBasis_apply_heq f δ ps u
  have hsource := groupByPartyIso_familyPhysicalListBasis_eq_partyListBasis
    δ qs hnqs u b' y hv
  have htail : groupByPartyIso qs a hnqs howners z =
      partyListBasis a b qs (fun i ↦ y (qs.get i)) :=
    eq_of_heq ((groupByPartyIso_apply_heq qs ha hnqs howners hδ hz).trans
      ((heq_of_eq hsource).trans
        (partyListBasis_apply_heq_of_layout_eq ha b b' hb qs y).symm))
  have hgroup := groupByPartyIso_cons_of_owners_mem_tail_heq none qs a
    (selectedPartyOrder_nodup ps hn) howners z
  rw [htail] at hgroup
  have hunit : b none (y none) =
      Layout.memCongr (Layout.atParty_none_mapOwner_all (familyPhysicalLayout d ps)).symm
        (1 : ℂ) := by
    exact eq_of_heq ((selectedFamilyPhysicalPartyBasis_none_apply_heq
      d ps hn hc (y none)).trans
        (Layout.memCongr_apply_heq
          (Layout.atParty_none_mapOwner_all (familyPhysicalLayout d ps)).symm (1 : ℂ)).symm)
  have htensor := Layout.memCongr_tmul_heq
    (Layout.atParty_none_mapOwner_all (familyPhysicalLayout d ps)).symm
    (rfl : partyLayout qs a = partyLayout qs a) (1 : ℂ)
    (partyListBasis a b qs (fun i ↦ y (qs.get i)))
  rw [← hunit] at htensor
  change groupByPartyIso (none :: qs) a (selectedPartyOrder_nodup ps hn)
    (fun r _ ↦ mem_selectedPartyOrder ps hc r.owner) z =
    partyListBasis a b (none :: qs) (fun i ↦ y ((none :: qs).get i))
  rw [partyListBasis_cons_apply]
  exact eq_of_heq (hgroup.trans htensor.symm)

/-- The actual selected physical party basis, in the prescribed order and with
the exterior singleton coordinate removed, is the original physical basis
transported by the owner isometry. No coordinate equality is assumed.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151,
409–434 and 565–588. -/
theorem selectedFamilyPhysicalPartyBasis_grouped [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    (partyGroupedBasis
      (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
      (selectedFamilyPhysicalPartyBasis d ps hn hc) (selectedPartyOrder ps)
      (selectedPartyOrder_nodup ps hn) (mem_selectedPartyOrder ps hc)).reindex
        (selectedFamilyPhysicalConfigEquiv d) =
      (familyLabelledPhysicalBasis d ps hn hc).map
        (Layout.mapOwnerIso (affectedOwner (fun _ : P ↦ true))
          (familyPhysicalLayout d ps)) := by
  classical
  apply DFunLike.ext
  intro x
  rw [OrthonormalBasis.reindex_apply]
  simp only [partyGroupedBasis,
    OrthonormalBasis.map_apply, partyLabelledBasis_apply, familyLabelledPhysicalBasis,
    (familyPhysicalListBasis d ps).reindex_apply
      (Equiv.piCongrLeft (fun p : P ↦ Fin (d p))
        (List.Nodup.getEquivOfForallMemList ps hn hc)) x]
  apply (groupByPartyIso (selectedPartyOrder ps)
    (Layout.mapOwner (affectedOwner (fun _ : P ↦ true)) (familyPhysicalLayout d ps))
    (selectedPartyOrder_nodup ps hn)
    (fun r _ ↦ mem_selectedPartyOrder ps hc r.owner)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (selected_physical_grouped_column d ps hn hc x).symm

end TNLean.PEPS.PairEffect
