/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyGroupedBasis
import TNLean.PEPS.Approximation.OutputPartitionCoordinates
import TNLean.PEPS.Approximation.PartyGroupingTransport
import TNLean.PEPS.Approximation.FamilyPhysicalReadout
import TNLean.PEPS.Approximation.UnitMemoryCoordinates
import TNLean.PEPS.Approximation.PartitionOwnerNaturality

/-!
# Grouping physical and private output coordinates by party

The specified physical basis agrees with the tensor product of the singleton
party bases under the canonical grouping isometry.

The canonical grouping of the physical/private concatenation agrees with
concatenating the separately grouped physical and private basis vectors.
The party type may be empty and may include an exterior owner `none`.
No equality of local dimensions or supplied factorization is required.

## References

* *Polynomial PEPS approximation of gapped square-grid ground states*, Theorem 5.2,
  September 24, 2026; `04-compression.tex`, lines 565–588.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean.PEPS.PairEffect

variable {P : Type}
attribute [local instance] Classical.propDecidable

namespace Layout

/-- A selected first register and an excluded tail are separated by the
canonical partition, retaining the selected memory's scalar unit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151
and 565–588. -/
theorem partitionIso_selectedHead_of_tail_excluded_heq
    {P : Type} (p : P) (H : HSpace) (t : Layout P)
    (htail : ∀ r ∈ t, r.owner ≠ p) (e : H) (y : Mem t) :
    HEq (partitionIso (fun q => decide (q = p)) (⟨p, H⟩ :: t)
      (e ⊗ₜ[ℂ] y)) ((e ⊗ₜ[ℂ] (1 : ℂ)) ⊗ₜ[ℂ] y) := by
  have hfalse : ∀ r ∈ t, decide (r.owner = p) = false :=
    fun r hr => decide_eq_false (htail r hr)
  have hstep := partitionIso_cons_true_tmul (fun q => decide (q = p))
    ⟨p, H⟩ t (by simp) e y
  have hrestrict : restrict (fun q => decide (q = p)) t = [] ∧
      restrict (fun q => !decide (q = p)) t = t :=
    ⟨List.filter_eq_nil_iff.mpr (fun r hr h =>
        Bool.noConfusion ((hfalse r hr).symm.trans h)),
      List.filter_eq_self.mpr (fun r hr =>
        Eq.mpr (Bool.not_eq_true_eq_eq_false (decide (r.owner = p))) (hfalse r hr))⟩
  have hscalar : ∀ (a b : Layout P) (ha : a = []) (hb : b = t)
      (z : Mem a ⊗[ℂ] Mem b), HEq z ((1 : ℂ) ⊗ₜ[ℂ] y) →
      HEq ((TensorProduct.assocIsometry ℂ H (Mem a) (Mem b)).symm
        (e ⊗ₜ[ℂ] z)) ((e ⊗ₜ[ℂ] (1 : ℂ)) ⊗ₜ[ℂ] y) := by
    rintro a b rfl rfl z hz
    rw [eq_of_heq hz, TensorProduct.assocIsometry_symm_apply, TensorProduct.assoc_symm_tmul]
  exact hstep.trans (hscalar (restrict (fun q => decide (q = p)) t)
    (restrict (fun q => !decide (q = p)) t) hrestrict.1 hrestrict.2
    (partitionIso (fun q => decide (q = p)) t y)
    (partitionIso_of_forall_false (fun q => decide (q = p)) t hfalse y))


end Layout

/-- Equality of the two register lists preserves concatenated memory vectors.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 246–267.
This consolidates the append transports used in the corrected-source development. -/
theorem Layout.appendIso_symm_tmul_heq {a b a' b' : Layout P}
    (ha : a = a') (hb : b = b') {x : Mem a} {x' : Mem a'}
    {y : Mem b} {y' : Mem b'} (hx : HEq x x') (hy : HEq y y') :
    HEq ((appendIso a b).symm (x ⊗ₜ[ℂ] y))
      ((appendIso a' b').symm (x' ⊗ₜ[ℂ] y')) := by
  cases ha
  cases hb
  cases hx
  cases hy
  rfl

private def orderedPartyVector (a : Layout P)
    (v : ∀ p, Mem (Layout.atParty p a)) : (ps : List P) → Mem (partyLayout ps a)
  | [] => (1 : ℂ)
  | p :: ps => v p ⊗ₜ[ℂ] orderedPartyVector a v ps

private theorem orderedPartyVector_heq (a b : Layout P) (ps : List P)
    (v : ∀ p, Mem (Layout.atParty p a)) (w : ∀ p, Mem (Layout.atParty p b))
    (h : ∀ p ∈ ps, Layout.atParty p a = Layout.atParty p b)
    (hv : ∀ p ∈ ps, HEq (v p) (w p)) :
    HEq (orderedPartyVector a v ps) (orderedPartyVector b w ps) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      have hh := h p (List.mem_cons_self)
      have ht := partyLayout_eq_of_atParty_eq ps a b
        (fun q hq => h q (List.mem_cons_of_mem p hq))
      have hx : Layout.memCongr hh (v p) = w p :=
        eq_of_heq ((Layout.memCongr_apply_heq hh _).trans (hv p (List.mem_cons_self)))
      have hy : Layout.memCongr ht (orderedPartyVector a v ps) =
          orderedPartyVector b w ps :=
        eq_of_heq ((Layout.memCongr_apply_heq ht _).trans
          (ih (fun q hq => h q (List.mem_cons_of_mem p hq))
            (fun q hq => hv q (List.mem_cons_of_mem p hq))))
      exact (Layout.memCongr_tmul_heq hh ht _ _).symm.trans
        (heq_of_eq (congrArg₂ (fun x y => x ⊗ₜ[ℂ] y) hx hy))

private def localJoinedVector (a b : Layout P)
    (v : ∀ p, Mem (Layout.atParty p a)) (w : ∀ p, Mem (Layout.atParty p b))
    (p : P) : Mem (Layout.atParty p (a ++ b)) := by
  classical
  exact Layout.memCongr (Layout.restrict_append (fun q => decide (q = p)) a b).symm
    ((appendIso (Layout.atParty p a) (Layout.atParty p b)).symm (v p ⊗ₜ[ℂ] w p))

private theorem localJoinedVector_heq (a b a' b' : Layout P)
    (v : ∀ p, Mem (Layout.atParty p a)) (w : ∀ p, Mem (Layout.atParty p b))
    (v' : ∀ p, Mem (Layout.atParty p a')) (w' : ∀ p, Mem (Layout.atParty p b'))
    (p : P) (ha : Layout.atParty p a = Layout.atParty p a')
    (hb : Layout.atParty p b = Layout.atParty p b')
    (hv : HEq (v p) (v' p)) (hw : HEq (w p) (w' p)) :
    HEq (localJoinedVector a b v w p) (localJoinedVector a' b' v' w' p) := by
  classical
  exact (Layout.memCongr_apply_heq _ _).trans
    ((Layout.appendIso_symm_tmul_heq ha hb hv hw).trans
      (Layout.memCongr_apply_heq _ _).symm)

private def removeHeadVector (p : P) (a : Layout P)
    (v : ∀ q, Mem (Layout.atParty q a)) (q : P) :
    Mem (Layout.atParty q (Layout.withoutParty p a)) := by
  classical
  exact if h : q = p then 0 else
    Layout.memCongr (Layout.atParty_withoutParty p q a h).symm (v q)

private theorem removeHeadVector_heq (p : P) (a : Layout P)
    (v : ∀ q, Mem (Layout.atParty q a)) (q : P) (hq : q ≠ p) :
    HEq (removeHeadVector p a v q) (v q) := by
  classical
  simp only [removeHeadVector, dite_eq_right hq]
  exact Layout.memCongr_apply_heq (Layout.atParty_withoutParty p q a hq).symm _

private theorem orderedPartyVector_removeHead (p : P) (ps : List P) (a : Layout P)
    (v : ∀ q, Mem (Layout.atParty q a)) (hp : p ∉ ps) :
    Layout.memCongr (partyLayout_withoutParty ps p a hp)
      (orderedPartyVector (Layout.withoutParty p a) (removeHeadVector p a v) ps) =
      orderedPartyVector a v ps := by
  apply eq_of_heq
  apply (Layout.memCongr_apply_heq _ _).trans
  refine orderedPartyVector_heq _ _ ps _ _ ?_ ?_
  · intro q hq
    exact Layout.atParty_withoutParty p q a (by intro h; exact hp (h ▸ hq))
  · intro q hq
    exact removeHeadVector_heq p a v q (by intro h; exact hp (h ▸ hq))

/-- Grouping a partitioned tensor retains the first party's vector and groups the
complement over the ordered remaining parties. The list has no repetitions and
covers every register owner; it need not contain every element of the party type.
The tail memory is transported by the equality obtained on removing a party
absent from the tail list.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 233–251. -/
theorem groupByPartyIso_cons_partition_tmul
    (p : P) (ps : List P) (a : Layout P)
    (hn : (p :: ps).Nodup) (hc : ∀ r ∈ a, r.owner ∈ p :: ps)
    (x : Mem (Layout.atParty p a)) (y : Mem (Layout.withoutParty p a)) :
    groupByPartyIso (p :: ps) a hn hc
        ((Layout.partitionIso (fun q => decide (q = p)) a).symm (x ⊗ₜ[ℂ] y)) =
      x ⊗ₜ[ℂ] Layout.memCongr
        (partyLayout_withoutParty ps p a (List.nodup_cons.mp hn).1)
        (groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty hc) y) := by
  classical
  change
    (((groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
      (Layout.owners_withoutParty hc)).trans
        (Layout.memCongr (partyLayout_withoutParty ps p a (List.nodup_cons.mp hn).1))).lTensor
          (Mem (Layout.atParty p a)))
      ((Layout.partitionIso (fun q => decide (q = p)) a)
        ((Layout.partitionIso (fun q => decide (q = p)) a).symm (x ⊗ₜ[ℂ] y))) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  change
    (((groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
      (Layout.owners_withoutParty hc)).trans
        (Layout.memCongr (partyLayout_withoutParty ps p a (List.nodup_cons.mp hn).1))).lTensor
          (Mem (Layout.atParty p a))) (x ⊗ₜ[ℂ] y) =
      x ⊗ₜ[ℂ] Layout.memCongr
        (partyLayout_withoutParty ps p a (List.nodup_cons.mp hn).1)
        (groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty hc) y)
  rw [iso_lTensor_apply]
  rw [ContinuousLinearMap.lTensor_tmul]
  rfl

private theorem groupByPartyIso_symm_orderedPartyVector_cons
    (p : P) (ps : List P) (a : Layout P) (v : ∀ q, Mem (Layout.atParty q a))
    (hn : (p :: ps).Nodup) (hc : ∀ r ∈ a, r.owner ∈ p :: ps) :
    (groupByPartyIso (p :: ps) a hn hc).symm (orderedPartyVector a v (p :: ps)) =
      (Layout.partitionIso (fun q => decide (q = p)) a).symm
        (v p ⊗ₜ[ℂ]
          (groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
            (Layout.owners_withoutParty hc)).symm
              (orderedPartyVector (Layout.withoutParty p a) (removeHeadVector p a v) ps)) := by
  classical
  apply (groupByPartyIso (p :: ps) a hn hc).injective
  rw [LinearIsometryEquiv.apply_symm_apply, groupByPartyIso_cons_partition_tmul,
    LinearIsometryEquiv.apply_symm_apply,
    orderedPartyVector_removeHead p ps a v (List.nodup_cons.mp hn).1]
  rfl

/-- The actual grouping isometry commutes with physical/private concatenation
on arbitrary ordered products of local memory vectors. The empty list gives
exactly the scalar unit. -/
private theorem groupByPartyIso_append_orderedPartyVector (ps : List P) (a b : Layout P)
    (hn : ps.Nodup) (ha : ∀ r ∈ a, r.owner ∈ ps) (hb : ∀ r ∈ b, r.owner ∈ ps)
    (v : ∀ p, Mem (Layout.atParty p a)) (w : ∀ p, Mem (Layout.atParty p b)) :
    groupByPartyIso ps (a ++ b) hn
        (fun r hr => (List.mem_append.mp hr).elim (ha r) (hb r))
      ((appendIso a b).symm
        ((groupByPartyIso ps a hn ha).symm (orderedPartyVector a v ps) ⊗ₜ[ℂ]
          (groupByPartyIso ps b hn hb).symm (orderedPartyVector b w ps))) =
      orderedPartyVector (a ++ b) (localJoinedVector a b v w) ps := by
  classical
  induction ps generalizing a b with
  | nil =>
      have ea : a = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun r hr => by simpa using ha r hr)
      have eb : b = [] := List.eq_nil_iff_forall_not_mem.mpr
        (fun r hr => by simpa using hb r hr)
      subst a
      subst b
      change (1 : ℂ) * 1 = 1
      exact one_mul 1
  | cons p ps ih =>
      have hp : p ∉ ps := (List.nodup_cons.mp hn).1
      have hn' : ps.Nodup := (List.nodup_cons.mp hn).2
      let a' := Layout.withoutParty p a
      let b' := Layout.withoutParty p b
      let v' := removeHeadVector p a v
      let w' := removeHeadVector p b w
      let ga := groupByPartyIso ps a' hn' (Layout.owners_withoutParty ha)
      let gb := groupByPartyIso ps b' hn' (Layout.owners_withoutParty hb)
      let x := ga.symm (orderedPartyVector a' v' ps)
      let y := gb.symm (orderedPartyVector b' w' ps)
      have eab : Layout.withoutParty p (a ++ b) = a' ++ b' :=
        Layout.restrict_append (fun q => !decide (q = p)) a b
      have htail : HEq
          (groupByPartyIso ps (a' ++ b') hn'
            (fun r hr => (List.mem_append.mp hr).elim
              (Layout.owners_withoutParty ha r) (Layout.owners_withoutParty hb r))
            ((appendIso a' b').symm (x ⊗ₜ[ℂ] y)))
          (orderedPartyVector (a ++ b) (localJoinedVector a b v w) ps) := by
        rw [ih a' b' hn' (Layout.owners_withoutParty ha) (Layout.owners_withoutParty hb)]
        refine orderedPartyVector_heq _ _ ps _ _ ?_ ?_
        · intro q hq
          rw [← eab]
          exact Layout.atParty_withoutParty p q (a ++ b)
            (by intro h; exact hp (h ▸ hq))
        · intro q hq
          have hqp : q ≠ p := by intro h; exact hp (h ▸ hq)
          exact localJoinedVector_heq a' b' a b v' w' v w q
            (Layout.atParty_withoutParty p q a hqp)
            (Layout.atParty_withoutParty p q b hqp)
            (removeHeadVector_heq p a v q hqp) (removeHeadVector_heq p b w q hqp)
      rw [groupByPartyIso_symm_orderedPartyVector_cons,
        groupByPartyIso_symm_orderedPartyVector_cons]
      have hsplit := Layout.partitionIso_append_tmul (fun q => decide (q = p)) a b
        ((Layout.partitionIso (fun q => decide (q = p)) a).symm (v p ⊗ₜ[ℂ] x))
        ((Layout.partitionIso (fun q => decide (q = p)) b).symm (w p ⊗ₜ[ℂ] y))
      simp only [LinearIsometryEquiv.apply_symm_apply] at hsplit
      -- The remaining step transports the two components of hsplit along
      -- restrict_append, applies the recursive group isometry to the tail,
      -- and uses htail. These transports use the proved equalities of layouts.
      let z := (appendIso a' b').symm (x ⊗ₜ[ℂ] y)
      have hsplit' : Layout.partitionIso (fun q => decide (q = p)) (a ++ b)
          ((appendIso a b).symm
            ((Layout.partitionIso (fun q => decide (q = p)) a).symm (v p ⊗ₜ[ℂ] x) ⊗ₜ[ℂ]
              (Layout.partitionIso (fun q => decide (q = p)) b).symm (w p ⊗ₜ[ℂ] y))) =
          localJoinedVector a b v w p ⊗ₜ[ℂ] Layout.memCongr eab.symm z := by
        apply eq_of_heq
        exact hsplit.trans (Layout.memCongr_tmul_heq
          (Layout.restrict_append (fun q => decide (q = p)) a b).symm eab.symm _ _).symm
      have hin := congrArg
        (Layout.partitionIso (fun q => decide (q = p)) (a ++ b)).symm hsplit'
      simp only [LinearIsometryEquiv.symm_apply_apply] at hin
      rw [hin]
      refine (groupByPartyIso_cons_partition_tmul p ps (a ++ b) hn
        (fun r hr => (List.mem_append.mp hr).elim (ha r) (hb r))
        (localJoinedVector a b v w p) (Layout.memCongr eab.symm z)).trans ?_
      change localJoinedVector a b v w p ⊗ₜ[ℂ] _ = _
      apply congrArg (fun t => localJoinedVector a b v w p ⊗ₜ[ℂ] t)
      apply eq_of_heq
      apply (Layout.memCongr_apply_heq _ _).trans
      -- Eliminating only this list equality identifies the recursive group maps;
      -- proof irrelevance identifies the owner-coverage witnesses.
      have hgroup : HEq
          (groupByPartyIso ps (Layout.withoutParty p (a ++ b)) hn'
            (Layout.owners_withoutParty
              (fun r hr => (List.mem_append.mp hr).elim (ha r) (hb r)))
            (Layout.memCongr eab.symm z))
          (groupByPartyIso ps (a' ++ b') hn'
            (fun r hr => (List.mem_append.mp hr).elim
              (Layout.owners_withoutParty ha r) (Layout.owners_withoutParty hb r)) z) :=
        groupByPartyIso_apply_heq ps eab hn' _ _ (Layout.memCongr_apply_heq eab.symm z)
      exact hgroup.trans htail

private theorem partyListBasis_eq_orderedPartyVector {I : P → Type}
    [∀ p, Fintype (I p)] (a : Layout P)
    (b : ∀ p, OrthonormalBasis (I p) ℂ (Mem (Layout.atParty p a)))
    (ps : List P) (x : ∀ p, I p) :
    partyListBasis a b ps (fun i => x (ps.get i)) =
      orderedPartyVector a (fun p => b p (x p)) ps := by
  induction ps with
  | nil => exact partyListBasis_nil_apply a b _
  | cons p ps ih =>
      rw [partyListBasis_cons_apply]
      exact congrArg (fun t => b p (x p) ⊗ₜ[ℂ] t) ih

/-- A physical layout without repeated parties contains exactly one register
for each of its parties. The memory of the selected register retains its final
scalar unit. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–151 and 565–588. -/
theorem atParty_familyPhysicalLayout_of_mem
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (p : P) (hp : p ∈ ps) :
    Layout.atParty p (familyPhysicalLayout d ps) = [⟨p, euc (Fin (d p))⟩] := by
  classical
  simp [Layout.atParty, Layout.restrict, familyPhysicalLayout, List.filter_map,
    Function.comp_def, List.filter_eq, List.count_eq_one_of_mem hn hp]

/-- The specified physical basis of a party's singleton register, including
the final scalar unit of its memory. No positive-dimension assumption is
needed. Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`,
lines 137–151 and 565–588. -/
def familyPhysicalPartyBasis
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) (p : P) :
    OrthonormalBasis (Fin (d p)) ℂ
      (Mem (Layout.atParty p (familyPhysicalLayout d ps))) :=
  (EuclideanSpace.basisFun (Fin (d p)) ℂ).map
    ((TensorProduct.ridIsometry ℂ (euc (Fin (d p)))).symm.trans
      (Layout.memCongr
        (atParty_familyPhysicalLayout_of_mem d ps hn p (hc p)).symm))

/-- Grouping an ordered physical basis vector agrees with its product of local
singleton vectors. The list may contain only some parties; register coverage
is derived from the physical layout itself. Source: polynomial-PEPS Theorem
5.2, `04-compression.tex`, lines 137–151 and 565–588. -/
private theorem groupByPartyIso_familyPhysicalListBasis_eq_orderedPartyVector
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup)
    (x : (p : P) → Fin (d p))
    (v : ∀ p, Mem (Layout.atParty p (familyPhysicalLayout d ps)))
    (hv : ∀ p ∈ ps, HEq (v p)
      ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ] (1 : ℂ))) :
    groupByPartyIso ps (familyPhysicalLayout d ps) hn
        (fun _ hr => (familyPhysicalLayout_owners d ps) ▸
          (List.mem_map_of_mem (f := Reg.owner) hr))
        (familyPhysicalListBasis d ps (fun i => x (ps.get i))) =
      orderedPartyVector (familyPhysicalLayout d ps) v ps := by
  induction ps with
  | nil =>
      simp only [groupByPartyIso, familyPhysicalLayout, Layout.memCongr,
        familyPhysicalListBasis, orderedPartyVector, List.length_nil, List.get_eq_getElem]
      let I := (i : Fin 0) → Fin (d (([] : List P).get i))
      have hcast : ∀ (ft ft' : Fintype I) (hf : ft = ft')
          (B : @OrthonormalBasis I ℂ _ ℂ _ _ ft') (i : I),
          (Eq.mpr (congrArg (fun j : Fintype I => @OrthonormalBasis I ℂ _ ℂ _ _ j)
            hf) B) i = B i := by
        rintro ft ft' rfl B i
        rfl
      change (LinearIsometryEquiv.refl ℂ ℂ) _ = (1 : ℂ)
      rw [LinearIsometryEquiv.coe_refl (R := ℂ) (E := ℂ)]
      refine (hcast inferInstance _ (Subsingleton.elim _ _)
        (OrthonormalBasis.singleton I ℂ)
        (fun i => x (([] : List P).get i))).trans ?_
      simp only [OrthonormalBasis.singleton_apply]
  | cons p ps ih =>
      rw [familyPhysicalListBasis, orderedPartyVector]
      refine (congrArg
        (fun z => groupByPartyIso (p :: ps) (familyPhysicalLayout d (p :: ps)) hn
          (fun r hr => (familyPhysicalLayout_owners d (p :: ps)) ▸
            (List.mem_map_of_mem (f := Reg.owner) hr)) z)
        ((((EuclideanSpace.basisFun (Fin (d p)) ℂ).tensorProduct
          (familyPhysicalListBasis d ps)).reindex_apply
            (Fin.consEquiv (fun i => Fin (d ((p :: ps).get i))))
            (fun i => x ((p :: ps).get i))).trans
          (OrthonormalBasis.tensorProduct_apply'
            (EuclideanSpace.basisFun (Fin (d p)) ℂ) (familyPhysicalListBasis d ps)
            ((Fin.consEquiv (fun i => Fin (d ((p :: ps).get i)))).symm
              (fun i => x ((p :: ps).get i)))))).trans ?_
      change groupByPartyIso (p :: ps) (familyPhysicalLayout d (p :: ps)) hn
          (fun r hr => (familyPhysicalLayout_owners d (p :: ps)) ▸
            (List.mem_map_of_mem (f := Reg.owner) hr))
          ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ]
            familyPhysicalListBasis d ps (fun i => x (ps.get i))) =
        v p ⊗ₜ[ℂ] orderedPartyVector (familyPhysicalLayout d (p :: ps)) v ps
      change
        (((groupByPartyIso ps
          (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
          (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr =>
            (familyPhysicalLayout_owners d (p :: ps)) ▸
              (List.mem_map_of_mem (f := Reg.owner) hr)))).trans
            (Layout.memCongr (partyLayout_withoutParty ps p
              (familyPhysicalLayout d (p :: ps)) (List.nodup_cons.mp hn).1))).lTensor
                (Mem (Layout.atParty p (familyPhysicalLayout d (p :: ps)))))
          ((Layout.partitionIso (fun q => decide (q = p))
            (familyPhysicalLayout d (p :: ps)))
            ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ]
              familyPhysicalListBasis d ps (fun i => x (ps.get i)))) =
          v p ⊗ₜ[ℂ] orderedPartyVector (familyPhysicalLayout d (p :: ps)) v ps
      refine (iso_lTensor_apply
        ((groupByPartyIso ps
          (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
          (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr =>
            (familyPhysicalLayout_owners d (p :: ps)) ▸
              (List.mem_map_of_mem (f := Reg.owner) hr)))).trans
            (Layout.memCongr (partyLayout_withoutParty ps p
              (familyPhysicalLayout d (p :: ps)) (List.nodup_cons.mp hn).1)))
        ((Layout.partitionIso (fun q => decide (q = p))
          (familyPhysicalLayout d (p :: ps)))
          ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ]
            familyPhysicalListBasis d ps (fun i => x (ps.get i))))).trans ?_
      have hW : Layout.withoutParty p (familyPhysicalLayout d (p :: ps)) =
          familyPhysicalLayout d ps := by
        simpa [Layout.withoutParty, restrict_familyPhysicalLayout] using
          congrArg (familyPhysicalLayout d)
            (List.filter_eq_self.mpr (fun q hq =>
              Eq.mpr (Bool.not_eq_true_eq_eq_false (decide (q = p)))
                (decide_eq_false (fun h => (List.nodup_cons.mp hn).1 (h ▸ hq)))))
      have hP : Layout.atParty p (familyPhysicalLayout d (p :: ps)) =
          [⟨p, euc (Fin (d p))⟩] :=
        atParty_familyPhysicalLayout_of_mem d (p :: ps) hn p List.mem_cons_self
      let vTail : ∀ q, Mem (Layout.atParty q (familyPhysicalLayout d ps)) :=
        fun q => Layout.memCongr (congrArg (Layout.atParty q) hW)
          (removeHeadVector p (familyPhysicalLayout d (p :: ps)) v q)
      have hvTail : ∀ q ∈ ps, HEq (vTail q)
          ((EuclideanSpace.basisFun (Fin (d q)) ℂ) (x q) ⊗ₜ[ℂ] (1 : ℂ)) :=
        fun q hq => (Layout.memCongr_apply_heq _ _).trans
          ((removeHeadVector_heq p (familyPhysicalLayout d (p :: ps)) v q
            (fun h => (List.nodup_cons.mp hn).1 (h ▸ hq))).trans
            (hv q (List.mem_cons_of_mem p hq)))
      have hTail := ih (List.nodup_cons.mp hn).2 vTail hvTail
      have hGroupedTail :
          groupByPartyIso ps (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
              (List.nodup_cons.mp hn).2
              (Layout.owners_withoutParty (fun r hr =>
                (familyPhysicalLayout_owners d (p :: ps)) ▸
                  (List.mem_map_of_mem (f := Reg.owner) hr)))
              (Layout.memCongr hW.symm
                (familyPhysicalListBasis d ps (fun i => x (ps.get i)))) =
            orderedPartyVector (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
              (removeHeadVector p (familyPhysicalLayout d (p :: ps)) v) ps := by
        apply eq_of_heq
        refine (groupByPartyIso_apply_heq ps hW (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr =>
            (familyPhysicalLayout_owners d (p :: ps)) ▸
              (List.mem_map_of_mem (f := Reg.owner) hr)))
          (fun r hr => (familyPhysicalLayout_owners d ps) ▸
            (List.mem_map_of_mem (f := Reg.owner) hr))
          (Layout.memCongr_apply_heq hW.symm
            (familyPhysicalListBasis d ps (fun i => x (ps.get i))))).trans ?_
        refine (heq_of_eq hTail).trans ?_
        have hOrdered := orderedPartyVector_heq
          (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
          (familyPhysicalLayout d ps) ps
          (removeHeadVector p (familyPhysicalLayout d (p :: ps)) v) vTail
          (fun q _ => congrArg (Layout.atParty q) hW)
          (fun q _ => (Layout.memCongr_apply_heq
            (congrArg (Layout.atParty q) hW)
            (removeHeadVector p (familyPhysicalLayout d (p :: ps)) v q)).symm)
        exact hOrdered.symm
      have hx : Layout.memCongr hP.symm
          ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ] (1 : ℂ)) = v p :=
        eq_of_heq ((Layout.memCongr_apply_heq hP.symm _).trans
          (hv p List.mem_cons_self).symm)
      have hExcluded : ∀ r ∈ familyPhysicalLayout d ps, r.owner ≠ p :=
        fun r hr h => (List.nodup_cons.mp hn).1
          (h ▸ ((familyPhysicalLayout_owners d ps) ▸
            (List.mem_map_of_mem (f := Reg.owner) hr)))
      have hsplit := Layout.partitionIso_selectedHead_of_tail_excluded_heq
        p (euc (Fin (d p))) (familyPhysicalLayout d ps) hExcluded
        ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p))
        (familyPhysicalListBasis d ps (fun i => x (ps.get i)))
      have hsplit' :
          Layout.partitionIso (fun q => decide (q = p)) (familyPhysicalLayout d (p :: ps))
            ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ]
              familyPhysicalListBasis d ps (fun i => x (ps.get i))) =
            Layout.memCongr hP.symm
              ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ] (1 : ℂ)) ⊗ₜ[ℂ]
              Layout.memCongr hW.symm
                (familyPhysicalListBasis d ps (fun i => x (ps.get i))) :=
        eq_of_heq (hsplit.trans (Layout.memCongr_tmul_heq hP.symm hW.symm
          ((EuclideanSpace.basisFun (Fin (d p)) ℂ) (x p) ⊗ₜ[ℂ] (1 : ℂ))
          (familyPhysicalListBasis d ps (fun i => x (ps.get i)))).symm)
      rw [hsplit', hx]
      change
        (isoL ((groupByPartyIso ps
          (Layout.withoutParty p (familyPhysicalLayout d (p :: ps)))
          (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr =>
            (familyPhysicalLayout_owners d (p :: ps)) ▸
              (List.mem_map_of_mem (f := Reg.owner) hr)))).trans
            (Layout.memCongr (partyLayout_withoutParty ps p
              (familyPhysicalLayout d (p :: ps)) (List.nodup_cons.mp hn).1)))).lTensor
                (Mem (Layout.atParty p (familyPhysicalLayout d (p :: ps))))
          (v p ⊗ₜ[ℂ] Layout.memCongr hW.symm
            (familyPhysicalListBasis d ps (fun i => x (ps.get i)))) =
          v p ⊗ₜ[ℂ] orderedPartyVector (familyPhysicalLayout d (p :: ps)) v ps
      rw [ContinuousLinearMap.lTensor_tmul, isoL_apply,
        LinearIsometryEquiv.trans_apply, hGroupedTail,
        orderedPartyVector_removeHead p ps (familyPhysicalLayout d (p :: ps)) v
          (List.nodup_cons.mp hn).1]

/-- The standard ordered physical basis is the product of the actual
singleton party bases transported by the canonical grouping isometry.
No equality between independently chosen bases is assumed. Source:
polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 137–151 and 565–588.
-/
theorem familyLabelledPhysicalBasis_eq_partyGroupedBasis
    [Fintype P] [DecidableEq P]
    (d : P → ℕ) (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    familyLabelledPhysicalBasis d ps hn hc =
      partyGroupedBasis (familyPhysicalLayout d ps)
        (familyPhysicalPartyBasis d ps hn hc) ps hn hc := by
  apply DFunLike.ext
  intro x
  simp only [familyLabelledPhysicalBasis, partyGroupedBasis,
    (familyPhysicalListBasis d ps).reindex_apply
      (Equiv.piCongrLeft (fun p : P => Fin (d p))
        (List.Nodup.getEquivOfForallMemList ps hn hc)) x,
    OrthonormalBasis.map_apply, partyLabelledBasis_apply]
  change familyPhysicalListBasis d ps (fun i => x (ps.get i)) =
    (groupByPartyIso ps (familyPhysicalLayout d ps) hn (fun r _ => hc r.owner)).symm
      (partyListBasis (familyPhysicalLayout d ps) (familyPhysicalPartyBasis d ps hn hc)
        ps (fun i => x (ps.get i)))
  apply (groupByPartyIso ps (familyPhysicalLayout d ps) hn
    (fun r _ => hc r.owner)).injective
  rw [LinearIsometryEquiv.apply_symm_apply, partyListBasis_eq_orderedPartyVector]
  apply groupByPartyIso_familyPhysicalListBasis_eq_orderedPartyVector d ps hn x
  intro p _
  simp only [familyPhysicalPartyBasis, OrthonormalBasis.map_apply,
    LinearIsometryEquiv.trans_apply, TensorProduct.symm_ridIsometry_apply]
  exact Layout.memCongr_apply_heq _ _


section Bases
variable [Fintype P] [DecidableEq P]
variable {X E : P → Type} [∀ p, Fintype (X p)] [∀ p, Fintype (E p)]

/-- The canonical joint physical/private basis at one actual party. -/
def partyLocalOutputBasis (physical garbage : Layout P)
    (bPhysical : ∀ p, OrthonormalBasis (X p) ℂ (Mem (Layout.atParty p physical)))
    (bGarbage : ∀ p, OrthonormalBasis (E p) ℂ (Mem (Layout.atParty p garbage)))
    (p : P) : OrthonormalBasis (X p × E p) ℂ
      (Mem (Layout.atParty p (physical ++ garbage))) := by
  let h : Layout.atParty p physical ++ Layout.atParty p garbage =
      Layout.atParty p (physical ++ garbage) := by
    unfold Layout.atParty
    exact (Layout.restrict_append _ physical garbage).symm
  exact ((bPhysical p).tensorProduct (bGarbage p)).map
    ((appendIso (Layout.atParty p physical) (Layout.atParty p garbage)).symm.trans
      (Layout.memCongr h))

/-- The party-grouped joint basis is the physical/private product basis after
separating the two dependent coordinate families. No party needs to exist. -/
theorem partyGroupedBasis_append (physical garbage : Layout P)
    (bPhysical : ∀ p, OrthonormalBasis (X p) ℂ (Mem (Layout.atParty p physical)))
    (bGarbage : ∀ p, OrthonormalBasis (E p) ℂ (Mem (Layout.atParty p garbage)))
    (ps : List P) (hn : ps.Nodup) (hc : ∀ p, p ∈ ps) :
    (partyGroupedBasis (physical ++ garbage)
      (partyLocalOutputBasis physical garbage bPhysical bGarbage) ps hn hc).reindex
        (Equiv.arrowProdEquivProdArrow P X E) =
      ((partyGroupedBasis physical bPhysical ps hn hc).tensorProduct
        (partyGroupedBasis garbage bGarbage ps hn hc)).map
          (appendIso physical garbage).symm := by
  apply DFunLike.ext
  intro z
  rcases z with ⟨x, y⟩
  simp only [OrthonormalBasis.reindex_apply, OrthonormalBasis.map_apply,
    OrthonormalBasis.tensorProduct_apply, partyGroupedBasis, partyLabelledBasis_apply]
  rw [partyListBasis_eq_orderedPartyVector, partyListBasis_eq_orderedPartyVector,
    partyListBasis_eq_orderedPartyVector]
  apply (groupByPartyIso ps (physical ++ garbage) hn (fun r _ => hc r.owner)).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  symm
  simp only [partyLocalOutputBasis,
    OrthonormalBasis.map_apply, OrthonormalBasis.tensorProduct_apply',
    LinearIsometryEquiv.trans_apply]
  change _ = orderedPartyVector (physical ++ garbage)
    (localJoinedVector physical garbage
      (fun p => bPhysical p (x p)) (fun p => bGarbage p (y p))) ps
  exact groupByPartyIso_append_orderedPartyVector ps physical garbage hn
    (fun r _ => hc r.owner) (fun r _ => hc r.owner)
    (fun p => bPhysical p (x p)) (fun p => bGarbage p (y p))

end Bases
end TNLean.PEPS.PairEffect
