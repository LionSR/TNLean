/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.PartyGrouping
import TNLean.PEPS.Approximation.PartyFactorization

/-!
# Source-free words are tensor products of local contractions

After the registers are collected by party using the canonical grouping isometries,
every allowed word without pair sources is exactly a tensor product of contractions,
one for each participating party. Named local maps on empty memories are included in
the set of participating parties, so scalar operations are also retained.

Source: Polynomial-PEPS manuscript, Theorem 5.2, `04-compression.tex`,
equation `eq:compression-source-gate`, lines 233–251.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8769-partylocalmaps-word.exists_tensorpartymaps
Downstream declaration: TNLean.PEPS.PairEffect.Word.exists_tensorPartyMaps

Provenance-ID: 8769-partylocalmaps-word.exists_tensorpartymaps_parties
Downstream declaration: TNLean.PEPS.PairEffect.Word.exists_tensorPartyMaps_parties
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

variable {P : Type}

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

/-- An allowed source-free word is a tensor product of contractions on the individual
parties' memories under the canonical grouping isometries.
Polynomial-PEPS manuscript, Theorem 5.2, `eq:compression-source-gate`, lines 233–251. -/
theorem Word.exists_tensorPartyMaps {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) (hw : w.IsAllowed) (ps : List P) (hn : ps.Nodup)
    (hp : ∀ p ∈ w.parties, p ∈ ps) :
    ∃ B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ'),
      (∀ p, ‖B p‖ ≤ 1) ∧
      isoL (groupByPartyIso ps ℓ' hn (fun r hr ↦ hp r.owner (w.owners_mem_parties.2 r hr)))
          ∘L w.eval =
        tensorPartyMaps ℓ ℓ' B ps ∘L
          isoL (groupByPartyIso ps ℓ hn
            (fun r hr ↦ hp r.owner (w.owners_mem_parties.1 r hr))) := by
  classical
  induction ps generalizing ℓ ℓ' with
  | nil =>
      have he : w.parties = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
        (fun p h ↦ List.not_mem_nil (hp p h))
      obtain ⟨rfl, rfl, heval⟩ := w.eq_nil_and_eval_eq_id_of_parties_eq_empty he
      refine ⟨fun _ ↦ 0, fun _ ↦ by simp, ?_⟩
      change w.eval = ContinuousLinearMap.id ℂ ℂ
      exact eq_of_heq heval
  | cons p ps ih =>
      let f : P → Bool := fun q ↦ decide (q = p)
      let v : Word (Layout.withoutParty p ℓ) (Layout.withoutParty p ℓ') :=
        w.restrict (fun q ↦ !f q) hs
      have hvp : ∀ q ∈ v.parties, q ∈ ps := by
        intro q hq
        have hm : q ∈ w.parties ∧ (!f q) = true := by
          change q ∈ (w.restrict (fun q ↦ !f q) hs).parties at hq
          rw [w.parties_restrict _ hs] at hq
          exact Finset.mem_filter.mp hq
        have hqp : q ≠ p := by simpa [f] using hm.2
        exact (List.mem_cons.mp (hp q hm.1)).resolve_left hqp
      obtain ⟨C, hC, hce⟩ := ih v (w.sources_restrict _ hs)
        (w.isAllowed_restrict _ hs hw) (List.nodup_cons.mp hn).2 hvp
      let A : Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ') :=
        (w.restrict f hs).eval
      let B : ∀ q, Mem (Layout.atParty q ℓ) →L[ℂ] Mem (Layout.atParty q ℓ') :=
        fun q ↦ if hq : q = p then hq.symm ▸ A else
          isoL (Layout.memCongr (Layout.atParty_withoutParty p q ℓ' hq)) ∘L C q ∘L
            isoL (Layout.memCongr (Layout.atParty_withoutParty p q ℓ hq)).symm
      refine ⟨B, ?_, ?_⟩
      · intro q
        by_cases hq : q = p
        · subst q
          rw [show B p = A from dite_eq_left rfl]
          exact (w.restrict f hs).norm_eval_le_one (w.isAllowed_restrict f hs hw)
        · rw [show B q = _ from dite_eq_right hq, Layout.norm_conj_memCongr]
          exact hC q
      · have hpn : p ∉ ps := (List.nodup_cons.mp hn).1
        have hBC : HEq (tensorPartyMaps (Layout.withoutParty p ℓ)
            (Layout.withoutParty p ℓ') C ps) (tensorPartyMaps ℓ ℓ' B ps) := by
          apply tensorPartyMaps_heq _ _ _ _ C B ps
            (fun q hq ↦ Layout.atParty_withoutParty p q ℓ (by intro h; exact hpn (h ▸ hq)))
            (fun q hq ↦ Layout.atParty_withoutParty p q ℓ' (by intro h; exact hpn (h ▸ hq)))
          intro q hq
          have hqp : q ≠ p := by intro h; exact hpn (h ▸ hq)
          rw [show B q = _ from dite_eq_right hqp]
          exact (Layout.conj_memCongr_heq _ _ (C q)).symm
        have hBT := Layout.eq_conj_memCongr_of_heq
          (partyLayout_withoutParty ps p ℓ hpn) (partyLayout_withoutParty ps p ℓ' hpn)
          _ _ hBC
        let gi := groupByPartyIso ps (Layout.withoutParty p ℓ) (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr ↦ hp r.owner (w.owners_mem_parties.1 r hr)))
        let go := groupByPartyIso ps (Layout.withoutParty p ℓ') (List.nodup_cons.mp hn).2
          (Layout.owners_withoutParty (fun r hr ↦ hp r.owner (w.owners_mem_parties.2 r hr)))
        let ei := Layout.memCongr (partyLayout_withoutParty ps p ℓ hpn)
        let eo := Layout.memCongr (partyLayout_withoutParty ps p ℓ' hpn)
        have htail : isoL (go.trans eo) ∘L v.eval =
            tensorPartyMaps ℓ ℓ' B ps ∘L isoL (gi.trans ei) := by
          ext x
          simp only [isoL_trans, comp_apply, hBT, isoL_apply, ei,
            LinearIsometryEquiv.symm_apply_apply]
          exact congrArg eo (DFunLike.congr_fun hce x)
        let pi : Mem ℓ ≃ₗᵢ[ℂ] Mem (Layout.atParty p ℓ) ⊗[ℂ]
            Mem (Layout.withoutParty p ℓ) := Layout.partitionIso f ℓ
        let po : Mem ℓ' ≃ₗᵢ[ℂ] Mem (Layout.atParty p ℓ') ⊗[ℂ]
            Mem (Layout.withoutParty p ℓ') := Layout.partitionIso f ℓ'
        have hsplit : isoL po ∘L w.eval =
            TensorProduct.mapL A v.eval ∘L isoL pi := w.partitionIso_eval f hs
        change isoL (po.trans ((go.trans eo).lTensor (Mem (Layout.atParty p ℓ')))) ∘L w.eval =
          TensorProduct.mapL (B p) (tensorPartyMaps ℓ ℓ' B ps) ∘L
            isoL (pi.trans ((gi.trans ei).lTensor (Mem (Layout.atParty p ℓ))))
        rw [show B p = A from dite_eq_left rfl, isoL_trans, isoL_trans,
          comp_assoc, hsplit]
        exact congrArg (fun M ↦ M ∘L isoL pi)
          (tensor_factorization A v.eval (gi.trans ei) (go.trans eo)
            (tensorPartyMaps ℓ ℓ' B ps) htail)

/-- Every allowed source-free word factors over precisely its finite set of participating
parties; no auxiliary list or coverage hypothesis is required.
Polynomial-PEPS manuscript, Theorem 5.2, `eq:compression-source-gate`, lines 233–251. -/
theorem Word.exists_tensorPartyMaps_parties {ℓ ℓ' : Layout P} (w : Word ℓ ℓ')
    (hs : w.sources = []) (hw : w.IsAllowed) :
    ∃ B : ∀ p, Mem (Layout.atParty p ℓ) →L[ℂ] Mem (Layout.atParty p ℓ'),
      (∀ p, ‖B p‖ ≤ 1) ∧
      isoL (groupByPartyIso w.parties.toList ℓ' w.parties.nodup_toList
        (fun r hr ↦ Finset.mem_toList.mpr (w.owners_mem_parties.2 r hr))) ∘L w.eval =
      tensorPartyMaps ℓ ℓ' B w.parties.toList ∘L
        isoL (groupByPartyIso w.parties.toList ℓ w.parties.nodup_toList
          (fun r hr ↦ Finset.mem_toList.mpr (w.owners_mem_parties.1 r hr))) := by
  exact w.exists_tensorPartyMaps hs hw w.parties.toList w.parties.nodup_toList
    (fun p hp ↦ Finset.mem_toList.mpr hp)

end TNLean.PEPS.PairEffect
