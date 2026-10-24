/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Compression.AbsorbedRestriction
import TNLean.Lattice.PartyCircuit.PartyFactorization
import TNLean.Lattice.PartyCircuit.PartyGrouping

/-! # Tensor factorization by actual singleton restrictions

The statements concern the explicitly constructed words, their register order,
and their restrictions to selected parties. They are auxiliary identities for
the chronological construction, before the final physical partial trace. The ordered
party list contains every party named by the word, including parties whose only
operations are scalar maps on empty memories.

Source: polynomial-PEPS, `04-compression.tex`, lines 233–267 and 342–381.
-/

noncomputable section
open scoped TensorProduct
open ContinuousLinearMap
namespace TNLean
open TNLean.Lattice.PartyCircuit
variable {P : Type}

namespace Lattice.PartyCircuit
private theorem tensor_factorization {X X' Y Y' Z Z' : HSpace}
    (A : X →L[ℂ] X') (R : Y →L[ℂ] Y') (gi : Y ≃ₗᵢ[ℂ] Z)
    (go : Y' ≃ₗᵢ[ℂ] Z') (T : Z →L[ℂ] Z')
    (h : isoL go ∘L R = T ∘L isoL gi) :
    isoL (go.lTensor X') ∘L TensorProduct.mapL A R =
      TensorProduct.mapL A T ∘L isoL (gi.lTensor X) := by
  refine clm_ext_tmul fun x y ↦ ?_
  simp only [comp_apply, TensorProduct.mapL_tmul, isoL_apply, iso_lTensor_apply,
    lTensor_tmul]
  exact congrArg (fun z ↦ A x ⊗ₜ[ℂ] z) (DFunLike.congr_fun h y)

/-- Under canonical grouping by parties, a source-free word is the tensor
product of its actual singleton restrictions. No factor is identified by
cancelling another factor, so zero local maps are included. The ordered party list
contains every party named by the word, including scalar operations on empty memories.
Source: polynomial-PEPS 04-compression.tex, lines 233–251 and 351–381. -/
theorem Word.groupByPartyIso_eval_eq_tensorRestrictions {a b : Layout P}
    (w : Word a b) (hs : w.sources = []) (ps : List P) (hn : ps.Nodup)
    (hp : ∀ p ∈ w.parties, p ∈ ps) :
    isoL (groupByPartyIso ps b hn
      (fun r hr ↦ hp r.owner (w.owners_mem_parties.2 r hr))) ∘L w.eval =
      tensorPartyMaps a b (fun p ↦ (w.restrict (partySelector p) hs).eval) ps ∘L
        isoL (groupByPartyIso ps a hn
          (fun r hr ↦ hp r.owner (w.owners_mem_parties.1 r hr))) := by
  classical
  induction ps generalizing a b with
  | nil =>
      have he : w.parties = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun p h ↦ List.not_mem_nil (hp p h))
      obtain ⟨rfl, rfl, heval⟩ := w.eq_nil_and_eval_eq_id_of_parties_eq_empty he
      change w.eval = ContinuousLinearMap.id ℂ ℂ
      exact eq_of_heq heval
  | cons p ps ih =>
      let f : P → Bool := partySelector p
      let v : Word (Layout.withoutParty p a) (Layout.withoutParty p b) :=
        w.restrict (fun q ↦ !f q) hs
      have hvp : ∀ q ∈ v.parties, q ∈ ps := by
        intro q hq
        have hm : q ∈ w.parties ∧ (!f q) = true := by
          change q ∈ (w.restrict (fun q ↦ !f q) hs).parties at hq
          rw [w.parties_restrict _ hs] at hq
          exact Finset.mem_filter.mp hq
        have hqp : q ≠ p := by simpa [f, partySelector] using hm.2
        exact (List.mem_cons.mp (hp q hm.1)).resolve_left hqp
      let C := fun q ↦ (v.restrict (partySelector q)
        (w.sources_restrict _ hs)).eval
      have hce := ih v (w.sources_restrict _ hs) (List.nodup_cons.mp hn).2 hvp
      let A : Mem (Layout.atParty p a) →L[ℂ] Mem (Layout.atParty p b) :=
        (w.restrict f hs).eval
      let B : ∀ q, Mem (Layout.atParty q a) →L[ℂ] Mem (Layout.atParty q b) :=
        fun q ↦ if hq : q = p then hq.symm ▸ A else
          isoL (Layout.memCongr (Layout.atParty_withoutParty p q b hq)) ∘L C q ∘L
            isoL (Layout.memCongr (Layout.atParty_withoutParty p q a hq)).symm
      have hB : B = fun q ↦ (w.restrict (partySelector q) hs).eval := by
        funext q
        by_cases hq : q = p
        · subst q
          exact dite_eq_left rfl
        · rw [show B q = _ from dite_eq_right hq]
          exact (Layout.eq_conj_memCongr_of_heq (Layout.atParty_withoutParty p q a hq)
            (Layout.atParty_withoutParty p q b hq) (C q) _
            (w.restrict_withoutParty_atParty_eval_heq hs p q hq)).symm
      rw [← hB]
      have hpn : p ∉ ps := (List.nodup_cons.mp hn).1
      have hBC : HEq (tensorPartyMaps (Layout.withoutParty p a)
          (Layout.withoutParty p b) C ps) (tensorPartyMaps a b B ps) := by
        apply tensorPartyMaps_heq _ _ _ _ C B ps
          (fun q hq ↦ Layout.atParty_withoutParty p q a (by intro h; exact hpn (h ▸ hq)))
          (fun q hq ↦ Layout.atParty_withoutParty p q b (by intro h; exact hpn (h ▸ hq)))
        intro q hq
        have hqp : q ≠ p := by intro h; exact hpn (h ▸ hq)
        rw [show B q = _ from dite_eq_right hqp]
        exact (Layout.conj_memCongr_heq _ _ (C q)).symm
      have hBT := Layout.eq_conj_memCongr_of_heq
        (partyLayout_withoutParty ps p a hpn) (partyLayout_withoutParty ps p b hpn)
        _ _ hBC
      let gi := groupByPartyIso ps (Layout.withoutParty p a) (List.nodup_cons.mp hn).2
        (Layout.owners_withoutParty (fun r hr ↦ hp r.owner (w.owners_mem_parties.1 r hr)))
      let go := groupByPartyIso ps (Layout.withoutParty p b) (List.nodup_cons.mp hn).2
        (Layout.owners_withoutParty (fun r hr ↦ hp r.owner (w.owners_mem_parties.2 r hr)))
      let ei := Layout.memCongr (partyLayout_withoutParty ps p a hpn)
      let eo := Layout.memCongr (partyLayout_withoutParty ps p b hpn)
      have htail : isoL (go.trans eo) ∘L v.eval =
          tensorPartyMaps a b B ps ∘L isoL (gi.trans ei) := by
        ext x
        simp only [isoL_trans, comp_apply, hBT, isoL_apply, ei,
          LinearIsometryEquiv.symm_apply_apply]
        exact congrArg eo (DFunLike.congr_fun hce x)
      let pi : Mem a ≃ₗᵢ[ℂ] Mem (Layout.atParty p a) ⊗[ℂ]
          Mem (Layout.withoutParty p a) := Layout.partitionIso f a
      let po : Mem b ≃ₗᵢ[ℂ] Mem (Layout.atParty p b) ⊗[ℂ]
          Mem (Layout.withoutParty p b) := Layout.partitionIso f b
      have hsplit : isoL po ∘L w.eval =
          TensorProduct.mapL A v.eval ∘L isoL pi := w.partitionIso_eval f hs
      change isoL (po.trans ((go.trans eo).lTensor (Mem (Layout.atParty p b)))) ∘L w.eval =
        TensorProduct.mapL (B p) (tensorPartyMaps a b B ps) ∘L
          isoL (pi.trans ((gi.trans ei).lTensor (Mem (Layout.atParty p a))))
      rw [show B p = A from dite_eq_left rfl, isoL_trans, isoL_trans,
        comp_assoc, hsplit]
      exact congrArg (fun M ↦ M ∘L isoL pi)
        (tensor_factorization A v.eval (gi.trans ei) (go.trans eo)
          (tensorPartyMaps a b B ps) htail)
end Lattice.PartyCircuit
end TNLean
