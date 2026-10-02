/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Enumerations listing a subset first

Every finite type has an enumeration by `Fin (Fintype.card α)` whose first `|S|` indices list a
given finite subset `S` (`Finset.exists_equiv_val_lt_card_iff_mem`).
-/

namespace Finset

/-- An enumeration of a finite type listing the elements of a finite subset `S` first: the
elements of `S` are those with index below `|S|`. -/
theorem exists_equiv_val_lt_card_iff_mem {α : Type*} [Fintype α] (S : Finset α) :
    ∃ π : Fin (Fintype.card α) ≃ α, ∀ x, x.val < S.card ↔ π x ∈ S := by
  classical
  have hc : S.card + Sᶜ.card = Fintype.card α := Finset.card_add_card_compl S
  let e : Fin (S.card + Sᶜ.card) ≃ α :=
    finSumFinEquiv.symm.trans ((S.equivFin.symm.sumCongr Sᶜ.equivFin.symm).trans
      ((Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight fun _ => Finset.mem_compl)).trans
        (Equiv.sumCompl (· ∈ S))))
  have he : ∀ y, y.val < S.card ↔ e y ∈ S := fun y => by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) y
    · simp [e]
    · simpa [e, Nat.not_lt.mpr (Nat.le_add_right S.card j)] using
        Finset.mem_compl.mp (Sᶜ.equivFin.symm j).2
  exact ⟨(finCongr hc.symm).trans e, fun x => he (finCongr hc.symm x)⟩

end Finset
