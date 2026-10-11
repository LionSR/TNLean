/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyOutputCoordinates

/-!
# A party with no registers contributes the scalar unit

For an ordered list of distinct parties, suppose all register owners belong
to the tail. The canonical grouping adjoins the unit of the scalar memory
at the head. This is the empty exterior factor in the proof of polynomial-PEPS
Theorem 5.2, `04-compression.tex`, lines 565–588.
-/

noncomputable section
open scoped TensorProduct
namespace TNLean.PEPS.PairEffect

/-- If the head owns no register, its grouping factor is the scalar unit.
Source: polynomial-PEPS Theorem 5.2, `04-compression.tex`, lines 565–588. -/
theorem groupByPartyIso_cons_of_owners_mem_tail_heq {Q : Type} (q : Q)
    (qs : List Q) (a : Layout Q) (hn : (q :: qs).Nodup)
    (ha : ∀ r ∈ a, r.owner ∈ qs) (x : Mem a) :
    HEq (groupByPartyIso (q :: qs) a hn
      (fun r hr => List.mem_cons_of_mem q (ha r hr)) x)
      ((1 : ℂ) ⊗ₜ[ℂ] groupByPartyIso qs a (List.nodup_cons.mp hn).2 ha x) := by
  classical
  have hfalse (r : Reg Q) (hr : r ∈ a) : decide (r.owner = q) = false := by
    simpa only [decide_eq_false_iff_not] using
      (fun h : r.owner = q => (List.nodup_cons.mp hn).1 (h ▸ ha r hr))
  have hpart := Layout.partitionIso_of_forall_false (fun p => decide (p = q)) a hfalse x
  have hhead : Layout.atParty q a = [] :=
    List.filter_eq_nil_iff.mpr (fun r hr => by simp [hfalse r hr])
  have htail : Layout.withoutParty q a = a :=
    List.filter_eq_self.mpr (fun r hr => by simp [hfalse r hr])
  have hpartEq : (Layout.partitionIso (fun p => decide (p = q)) a) x =
      Layout.memCongr hhead.symm (1 : ℂ) ⊗ₜ[ℂ] Layout.memCongr htail.symm x :=
    eq_of_heq (hpart.trans (Layout.memCongr_tmul_heq hhead.symm htail.symm (1 : ℂ) x).symm)
  have hgroup := groupByPartyIso_apply_heq qs htail (List.nodup_cons.mp hn).2
    (Layout.owners_withoutParty (fun r hr => List.mem_cons_of_mem q (ha r hr))) ha
    (Layout.memCongr_apply_heq htail.symm x)
  have htailGrouped :
      Layout.memCongr (partyLayout_withoutParty qs q a (List.nodup_cons.mp hn).1)
        (groupByPartyIso qs (Layout.withoutParty q a) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr => List.mem_cons_of_mem q (ha r hr)))
          (Layout.memCongr htail.symm x)) = groupByPartyIso qs a (List.nodup_cons.mp hn).2 ha x :=
    eq_of_heq ((Layout.memCongr_apply_heq _ _).trans hgroup)
  have hx : x = (Layout.partitionIso (fun p => decide (p = q)) a).symm
      (Layout.memCongr hhead.symm (1 : ℂ) ⊗ₜ[ℂ] Layout.memCongr htail.symm x) :=
    (LinearIsometryEquiv.symm_apply_apply _ x).symm.trans
      (congrArg (Layout.partitionIso (fun p => decide (p = q)) a).symm hpartEq)
  have hm := groupByPartyIso_cons_partition_tmul q qs a hn
    (fun r hr => List.mem_cons_of_mem q (ha r hr))
    (Layout.memCongr hhead.symm (1 : ℂ)) (Layout.memCongr htail.symm x)
  have hfull := (congrArg (groupByPartyIso (q :: qs) a hn
    (fun r hr => List.mem_cons_of_mem q (ha r hr))) hx).trans
    (hm.trans (congrArg (fun y => Layout.memCongr hhead.symm (1 : ℂ) ⊗ₜ[ℂ] y)
      htailGrouped))
  exact (heq_of_eq hfull).trans (Layout.memCongr_tmul_heq hhead.symm rfl (1 : ℂ)
    (groupByPartyIso qs a (List.nodup_cons.mp hn).2 ha x))

end TNLean.PEPS.PairEffect
