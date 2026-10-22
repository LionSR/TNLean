/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.ProtocolTerminalCoordinates
import TNLean.Lattice.PartyCircuit.OriginalCircuitLift
import TNLean.Lattice.PartyCircuit.SiteVectorAppend

/-!
# Private realization of the terminal block coordinates

The main registers at each terminal owner are packed into the prescribed block
register by a local isometry. All auxiliary registers retain their labels and
owners and are placed in their prescribed private order. The construction also
creates the one-dimensional physical factor at parties with an empty main fibre.

Source: the one-dimensional note, Part II, `part2b_mps_protocol.tex`,
`prop:sweep`, lines 355–360, and the physical trace in lines 575–583.
This result realizes only the terminal coordinate map, not the preceding sweep.

**Local fix (terminal auxiliary registers):** The physical factors comprise only
main registers. Every auxiliary register remains private at its actual retired
owner, including auxiliary registers at parties without a main block. This
distinction is recorded in
`docs/paper-gaps/tnlean_one_dimensional_band_sweep_corrections.tex`.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.MPS.AreaLaw.ChainSweep

open TNLean.Lattice.PartyCircuit TNLean.Lattice.Sheet ContinuousLinearMap

variable {L w q : ℕ}

/-! The terminal reordering is a composition of adjacent register exchanges.
Each exchange acts on the raw register labels and preserves the corresponding
basis coefficients. -/

private theorem exists_rawReordering {a b : List (RawLabel L w)} (h : a.Perm b) :
    ∃ u : Word (siteRegs q (rawOwner L w) a) (siteRegs q (rawOwner L w) b),
      u.IsReordering ∧ ∀ c : RawLabel L w → Fin q,
        u.eval (siteVec (rawOwner L w) a c) = siteVec (rawOwner L w) b c := by
  induction h with
  | nil => exact ⟨.id _, Word.isReordering_id _, fun _ ↦ rfl⟩
  | @cons x a b h ih =>
      obtain ⟨u, hu, he⟩ := ih
      refine ⟨.frame _ u, hu, fun c ↦ ?_⟩
      exact congrArg (fun z ↦ EuclideanSpace.single (c x) (1 : ℂ) ⊗ₜ z) (he c)
  | swap x y a =>
      refine ⟨.swap _ _ _, Word.isReordering_swap .., fun c ↦ ?_⟩
      exact leftCommL_tmul _ _ _
  | trans h₁ h₂ ih₁ ih₂ =>
      obtain ⟨u, hu, he⟩ := ih₁
      obtain ⟨v, hv, hf⟩ := ih₂
      exact ⟨.comp u v, hu.comp hv, fun c ↦ by
        rw [Word.eval_comp, comp_apply, he, hf]⟩

private def rawReordering {a b : List (RawLabel L w)} (h : a.Perm b) :
    Word (siteRegs q (rawOwner L w) a) (siteRegs q (rawOwner L w) b) :=
  (exists_rawReordering (q := q) h).choose

private theorem rawReordering_spec {a b : List (RawLabel L w)} (h : a.Perm b) :
    (rawReordering (q := q) h).IsReordering ∧ ∀ c : RawLabel L w → Fin q,
      (rawReordering (q := q) h).eval (siteVec (rawOwner L w) a c) =
        siteVec (rawOwner L w) b c :=
  (exists_rawReordering (q := q) h).choose_spec

private def mainFibreList (p : Party L w) : List (MainSites L w p) :=
  Finset.univ.toList

private def mainRawList (p : Party L w) : List (RawLabel L w) :=
  (mainFibreList p).map (fun x ↦ Sum.inl x.val)

private def auxiliaryRawList (L w : ℕ) : List (RawLabel L w) :=
  (Finset.univ.toList : List (AuxiliarySite L w)).map Sum.inr

private def canonicalRawOrder : List (Party L w) → List (RawLabel L w)
  | [] => auxiliaryRawList L w
  | p :: ps => mainRawList p ++ canonicalRawOrder ps

private def mainPackedInput : List (Party L w) → Layout (Party L w)
  | [] => privateLayout L w q
  | p :: ps => siteRegs q (rawOwner L w) (mainRawList p) ++ mainPackedInput ps

private theorem mainPackedInput_eq (ps : List (Party L w)) :
    mainPackedInput (q := q) ps = siteRegs q (rawOwner L w) (canonicalRawOrder ps) := by
  induction ps with
  | nil =>
      simp only [mainPackedInput, canonicalRawOrder, auxiliaryRawList, siteRegs,
        List.map_map]
      rfl
  | cons p ps ih =>
      simp only [mainPackedInput, canonicalRawOrder, siteRegs, List.map_append] at *
      rw [ih]

private theorem canonicalRawOrder_eq (ps : List (Party L w)) :
    canonicalRawOrder ps = ps.flatMap mainRawList ++ auxiliaryRawList L w := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      simp only [canonicalRawOrder, List.flatMap_cons, ih, List.append_assoc]

/-! Each main site occurs in exactly its actual owner's fibre. The auxiliary
summand is disjoint from all main fibres. Therefore an exhaustive nonrepeating
raw list has precisely the following permutation. -/
private theorem canonicalRawOrder_perm (rs : List (RawLabel L w))
    (hn : rs.Nodup) (hc : ∀ r, r ∈ rs) :
    rs.Perm (canonicalRawOrder (physicalOrder L w)) := by
  classical
  rw [canonicalRawOrder_eq]
  have hm (p : Party L w) : (mainRawList p).Nodup := by
    apply (Finset.nodup_toList (Finset.univ : Finset (MainSites L w p))).map
    intro a b h
    exact Subtype.ext (Sum.inl.inj h)
  have hd : (physicalOrder L w).Pairwise
      (fun p p' ↦ List.Disjoint (mainRawList p) (mainRawList p')) := by
    apply (Finset.nodup_toList (Finset.univ : Finset (Party L w))).imp
    intro p p' hne r hr hs
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hs
    have hv : b.val = a.val := Sum.inl.inj heq
    exact hne (a.property.symm.trans ((congrArg (mainOwner L w) hv.symm).trans b.property))
  have hflat : ((physicalOrder L w).flatMap mainRawList).Nodup :=
    List.nodup_flatMap.mpr ⟨fun p _ ↦ hm p, hd⟩
  have haux : (auxiliaryRawList L w).Nodup :=
    (Finset.nodup_toList (Finset.univ : Finset (AuxiliarySite L w))).map Sum.inr_injective
  have hdis : List.Disjoint ((physicalOrder L w).flatMap mainRawList)
      (auxiliaryRawList L w) := by
    intro r hr hs
    obtain ⟨p, hp, hr⟩ := List.mem_flatMap.mp hr
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hr
    obtain ⟨b, hb, heq⟩ := List.mem_map.mp hs
    cases heq
  apply (List.perm_ext_iff_of_nodup hn (hflat.append haux hdis)).mpr
  intro r
  constructor
  · intro _
    cases r with
    | inl x =>
        apply List.mem_append.mpr
        left
        apply List.mem_flatMap.mpr
        refine ⟨mainOwner L w x, by simp [physicalOrder], ?_⟩
        exact List.mem_map.mpr ⟨⟨x, rfl⟩, by simp [mainFibreList], rfl⟩
    | inr a =>
        apply List.mem_append.mpr
        right
        exact List.mem_map.mpr ⟨a, by simp, rfl⟩
  · intro _
    exact hc r

private def mainBlockIndex (p : Party L w) :
    Fin (mainRawList p).length ≃ MainSites L w p :=
  (finCongr (by simp [mainRawList])).trans
    (List.Nodup.getEquivOfForallMemList (mainFibreList p)
      (Finset.nodup_toList _) (by simp [mainFibreList]))

private theorem mainBlockIndex_get (p : Party L w)
    (i : Fin (mainRawList p).length) :
    (mainRawList p).get i = Sum.inl (mainBlockIndex p i).val := by
  change (List.map (fun x : MainSites L w p ↦ Sum.inl x.val)
    (mainFibreList p))[i.val] = _
  rw [List.getElem_map]
  rfl

private theorem mainRawList_owner (p : Party L w) :
    ∀ r ∈ siteRegs q (rawOwner L w) (mainRawList p), r.owner = p := by
  intro r hr
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hr
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact y.property

private def mainBlockIso (p : Party L w) :
    Mem (siteRegs q (rawOwner L w) (mainRawList p)) ≃ₗᵢ[ℂ]
      Mem [⟨p, euc (Fin (physicalDimension L w q p))⟩] :=
  ((groupIso (rawOwner L w) (mainRawList p) (mainBlockIndex p)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (blockEncoding L w q p))).trans
      (oneIso p (Fin (physicalDimension L w q p))).symm

/-! The recursion performs exactly one private isometry at each listed party;
all later physical blocks and the entire auxiliary layout are spectators. -/
private def packMain : (ps : List (Party L w)) →
    Word (mainPackedInput (q := q) ps)
      (familyPhysicalLayout (physicalDimension L w q) ps ++ privateLayout L w q)
  | [] => .id _
  | p :: ps =>
      .comp (.localMap p (mainRawList_owner p) (by simp)
        (isoL (mainBlockIso p)) (mainPackedInput ps))
        (.frame _ (packMain ps))

private theorem packMain_props (ps : List (Party L w)) :
    (packMain (q := q) ps).IsAllowed ∧
      (packMain (q := q) ps).UsesOnly Set.univ ∧
        (packMain (q := q) ps).sourceCount = 0 := by
  induction ps with
  | nil => exact ⟨trivial, trivial, rfl⟩
  | cons p ps ih =>
      refine ⟨⟨LinearIsometry.norm_toContinuousLinearMap_le _, ih.1⟩,
        ⟨Set.mem_univ p, ih.2.1⟩, ?_⟩
      change 0 + (packMain (q := q) ps).sourceCount = 0
      exact (Nat.zero_add _).trans ih.2.2

/-- A private word packing the actual terminal main fibres and leaving every
auxiliary register at its original owner. The empty main fibres give scalar
physical factors. Source: Part II, `prop:sweep`, lines 355–360. -/
def terminalRegroupingWord (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) :
    Word (siteRegs q (rawOwner L w) rs)
      (familyPhysicalOutputLayout (physicalDimension L w q)
        (physicalOrder L w) (privateLayout L w q)) :=
  .comp ((rawReordering (q := q) (canonicalRawOrder_perm rs hn hc)).castLayouts rfl
    (mainPackedInput_eq (q := q) (physicalOrder L w)).symm)
    (packMain (physicalOrder L w))

/-- Every operation in the terminal regrouping is private; no pair source is
introduced. All parties, including those with scalar physical outputs, are
retained. Source: Part II, `prop:sweep`, lines 355–360. -/
theorem terminalRegroupingWord_props (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) :
    (terminalRegroupingWord (q := q) rs hn hc).IsAllowed ∧
      (terminalRegroupingWord (q := q) rs hn hc).UsesOnly Set.univ ∧
        (terminalRegroupingWord (q := q) rs hn hc).sourceCount = 0 := by
  have hr := Word.isReordering_castLayouts
    (rawReordering_spec (q := q) (canonicalRawOrder_perm rs hn hc)).1 rfl
    (mainPackedInput_eq (q := q) (physicalOrder L w)).symm
  have hp := packMain_props (q := q) (physicalOrder L w)
  exact ⟨⟨hr.isAllowed, hp.1⟩, ⟨hr.usesOnly Set.univ, hp.2.1⟩,
    congrArg₂ (fun a b : ℕ ↦ a + b) hr.sourceCount_eq hp.2.2⟩

private def physicalColumns (ps : List (Party L w)) (c : RawLabel L w → Fin q) :
    Mem (familyPhysicalLayout (physicalDimension L w q) ps) :=
  familyPhysicalListBasis (physicalDimension L w q) ps
    (fun i ↦ blockEncoding L w q (ps.get i) (fun x ↦ c (.inl x.val)))

private theorem physicalColumns_cons (p : Party L w) (ps : List (Party L w))
    (c : RawLabel L w → Fin q) :
    physicalColumns (p :: ps) c =
      EuclideanSpace.single (blockEncoding L w q p (fun x ↦ c (.inl x.val))) (1 : ℂ) ⊗ₜ
        physicalColumns ps c := by
  simp only [physicalColumns, familyPhysicalListBasis]
  erw [OrthonormalBasis.reindex_apply, OrthonormalBasis.tensorProduct_apply',
    EuclideanSpace.basisFun_apply]
  rfl

private theorem auxiliaryRaw_siteVec (xs : List (AuxiliarySite L w))
    (h : siteRegs q (auxiliaryOwner L w) xs =
      siteRegs q (rawOwner L w) (xs.map Sum.inr)) (c : RawLabel L w → Fin q) :
    (Layout.memCongr h).symm (siteVec (rawOwner L w) (xs.map Sum.inr) c) =
      siteVec (auxiliaryOwner L w) xs (fun a ↦ c (.inr a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      let h' : siteRegs q (auxiliaryOwner L w) xs =
          siteRegs q (rawOwner L w) (xs.map Sum.inr) := by
        simp [siteRegs, List.map_map, Function.comp_def, rawOwner]
      rw [← Layout.memCongr_symm h]
      change Layout.memCongr (congrArg (⟨auxiliaryOwner L w a, euc (Fin q)⟩ :: ·) h'.symm)
        (EuclideanSpace.single (c (.inr a)) (1 : ℂ) ⊗ₜ
          siteVec (rawOwner L w) (xs.map Sum.inr) c) = _
      rw [Layout.memCongr_cons_tmul _ h'.symm, Layout.memCongr_symm h', ih h']
      rfl

private theorem packMain_siteVec (ps : List (Party L w))
    (c : RawLabel L w → Fin q) :
    (packMain (q := q) ps).eval
        ((Layout.memCongr (mainPackedInput_eq (q := q) ps)).symm
          (siteVec (rawOwner L w) (canonicalRawOrder ps) c)) =
      (appendIso (familyPhysicalLayout (physicalDimension L w q) ps)
        (privateLayout L w q)).symm
        (physicalColumns ps c ⊗ₜ siteVec (auxiliaryOwner L w)
          (Finset.univ.toList : List (AuxiliarySite L w)) (fun a ↦ c (.inr a))) := by
  induction ps with
  | nil =>
      change (Layout.memCongr (mainPackedInput_eq (q := q) [])).symm
        (siteVec (rawOwner L w) (auxiliaryRawList L w) c) = _
      erw [auxiliaryRaw_siteVec _ (mainPackedInput_eq (q := q) []) c]
      have hc : physicalColumns (q := q) [] c = (1 : ℂ) :=
        familyPhysicalListBasis_nil_apply (physicalDimension L w q) _
      change siteVec (auxiliaryOwner L w) Finset.univ.toList (fun a ↦ c (.inr a)) =
        (appendIso ([] : Layout (Party L w)) (privateLayout L w q)).symm
          (physicalColumns [] c ⊗ₜ siteVec (auxiliaryOwner L w) Finset.univ.toList
            (fun a ↦ c (.inr a)))
      erw [hc]
      let a : Mem (privateLayout L w q) :=
        siteVec (auxiliaryOwner L w) Finset.univ.toList (fun a ↦ c (.inr a))
      exact (one_smul ℂ a).symm.trans
        (appendIso_nil_symm_tmul (privateLayout L w q) (1 : ℂ) a).symm
  | cons p ps ih =>
      erw [siteVec_append (rawOwner L w) (mainRawList p) (canonicalRawOrder ps)
        (mainPackedInput ps) (mainPackedInput_eq ps) (mainPackedInput_eq (p :: ps)) c]
      change (Word.frame ⟨p, euc (Fin (physicalDimension L w q p))⟩
        (packMain (q := q) ps)).eval
        ((Word.localMap p (mainRawList_owner p) (by simp) (isoL (mainBlockIso (q := q) p))
          (mainPackedInput (q := q) ps)).eval _) = _
      erw [eval_localMap]
      simp only [isoL_apply, mainBlockIso, LinearIsometryEquiv.trans_apply]
      erw [groupIso_siteVec (rawOwner L w) (mainRawList p) (mainBlockIndex p)
        (fun x ↦ Sum.inl x.val) (mainBlockIndex_get p) c,
        EuclideanSpace.piLpCongrLeft_single]
      erw [appendIso_one_symm, Word.eval_frame, lTensor_tmul, ih, physicalColumns_cons]
      exact (appendIso_symm_cons_tmul _ _ _ _ _ _).symm

private theorem terminalRegrouping_siteVec (rs : List (RawLabel L w))
    (hn : rs.Nodup) (hc : ∀ r, r ∈ rs) (c : RawLabel L w → Fin q) :
    terminalRegrouping (q := q) rs hn hc (siteVec (rawOwner L w) rs c) =
      (appendIso (familyPhysicalLayout (physicalDimension L w q) (physicalOrder L w))
        (privateLayout L w q)).symm
        (physicalColumns (physicalOrder L w) c ⊗ₜ siteVec (auxiliaryOwner L w)
          (Finset.univ.toList : List (AuxiliarySite L w)) (fun a ↦ c (.inr a))) := by
  let R := groupIso (q := q) (rawOwner L w) rs
    (List.Nodup.getEquivOfForallMemList rs hn hc)
  let a : Mem (privateLayout L w q) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (AuxiliarySite L w → Fin q) :=
    groupIso (auxiliaryOwner L w) Finset.univ.toList
      (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
  let b := familyLabelledPhysicalBasis (physicalDimension L w q) (physicalOrder L w)
    (Finset.nodup_toList _) (by simp [physicalOrder])
  let g := (EuclideanSpace.basisFun (AuxiliarySite L w → Fin q) ℂ).map a.symm
  change (appendIso _ _).symm ((b.tensorProduct g).repr.symm
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (terminalConfigurationEquiv L w q))
      (R (siteVec (rawOwner L w) rs c)))) = _
  have hr : R (siteVec (rawOwner L w) rs c) = EuclideanSpace.single c (1 : ℂ) :=
    groupIso_siteVec (rawOwner L w) rs
      (List.Nodup.getEquivOfForallMemList rs hn hc) id (fun _ ↦ rfl) c
  erw [hr, EuclideanSpace.piLpCongrLeft_single, (b.tensorProduct g).repr_symm_single,
    OrthonormalBasis.tensorProduct_apply']
  have hb : b ((terminalConfigurationEquiv L w q c).1) =
      physicalColumns (physicalOrder L w) c := by
    dsimp only [b, familyLabelledPhysicalBasis]
    erw [OrthonormalBasis.reindex_apply]
    rfl
  have hg : g ((terminalConfigurationEquiv L w q c).2) =
      siteVec (auxiliaryOwner L w) Finset.univ.toList (fun a ↦ c (.inr a)) := by
    change a.symm ((EuclideanSpace.basisFun (AuxiliarySite L w → Fin q) ℂ)
      (fun a ↦ c (.inr a))) = _
    rw [EuclideanSpace.basisFun_apply]
    apply a.injective
    rw [a.apply_symm_apply]
    exact (groupIso_siteVec (auxiliaryOwner L w) Finset.univ.toList
      (List.Nodup.getEquivOfForallMemList _ (Finset.nodup_toList _) (by simp))
      id (fun _ ↦ rfl) (fun a ↦ c (.inr a))).symm
  erw [hb, hg]

/-- The constructed private word realizes the specified terminal coordinate
isometry on every input vector, with no product or normalization hypothesis.
Source: Part II, `prop:sweep`, lines 355–360, and Theorem B, lines 575–583. -/
theorem eval_terminalRegroupingWord (rs : List (RawLabel L w)) (hn : rs.Nodup)
    (hc : ∀ r, r ∈ rs) (Ψ : Mem (siteRegs q (rawOwner L w) rs)) :
    (terminalRegroupingWord (q := q) rs hn hc).eval Ψ =
      terminalRegrouping (q := q) rs hn hc Ψ := by
  let R := groupIso (q := q) (rawOwner L w) rs
    (List.Nodup.getEquivOfForallMemList rs hn hc)
  have he : (terminalRegroupingWord (q := q) rs hn hc).eval.toLinearMap =
      (isoL (terminalRegrouping (q := q) rs hn hc)).toLinearMap := by
    apply ((EuclideanSpace.basisFun (RawLabel L w → Fin q) ℂ).map R.symm).toBasis.ext
    intro c
    change (terminalRegroupingWord (q := q) rs hn hc).eval
      (R.symm ((EuclideanSpace.basisFun (RawLabel L w → Fin q) ℂ) c)) =
        terminalRegrouping (q := q) rs hn hc
          (R.symm ((EuclideanSpace.basisFun (RawLabel L w → Fin q) ℂ) c))
    erw [EuclideanSpace.basisFun_apply]
    have hr : R (siteVec (rawOwner L w) rs c) = EuclideanSpace.single c (1 : ℂ) :=
      groupIso_siteVec (rawOwner L w) rs
        (List.Nodup.getEquivOfForallMemList rs hn hc) id (fun _ ↦ rfl) c
    rw [← hr, R.symm_apply_apply]
    change (packMain (q := q) (physicalOrder L w)).eval
      (((rawReordering (q := q) (canonicalRawOrder_perm rs hn hc)).castLayouts rfl
        (mainPackedInput_eq (q := q) (physicalOrder L w)).symm).eval
          (siteVec (rawOwner L w) rs c)) = _
    erw [Word.eval_castLayouts]
    simp only [comp_apply, isoL_apply]
    erw [(rawReordering_spec (q := q) (canonicalRawOrder_perm rs hn hc)).2 c,
      Layout.memCongr_symm (mainPackedInput_eq (q := q) (physicalOrder L w))]
    exact (packMain_siteVec (physicalOrder L w) c).trans
      (terminalRegrouping_siteVec rs hn hc c).symm
  exact LinearMap.congr_fun he Ψ

end TNLean.MPS.AreaLaw.ChainSweep
