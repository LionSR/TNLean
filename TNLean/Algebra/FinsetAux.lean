/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Fin

/-!
# Zero-padding finite sums over `Fin`

`Fin.sum_pad_zeros` re-indexes a sum over `Fin r` as a sum over a larger `Fin s` by
padding with zeros. This is the standard re-indexing step when a family of `r` Kraus
operators is extended to a family of `s ≥ r` operators; it was previously proved
separately in `TNLean.Channel.KrausRank` and `TNLean.Channel.KrausFreedom`.
-/

namespace Fin

/-- A sum indexed by `Fin r` can be padded by zeros to a sum over a larger `Fin s`. -/
lemma sum_pad_zeros {r s : ℕ} {β : Type*} [AddCommMonoid β]
    (f : Fin r → β) (hCard : r ≤ s) :
    ∑ j : Fin r, f j =
      ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
  symm
  have hsub :
      ∑ α ∈ Finset.univ.filter (fun α : Fin s => α.val < r),
          (if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0) =
        ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α _ hα
    have : ¬ α.val < r := by
      simpa using hα
    simp [dif_neg this]
  rw [← hsub]
  symm
  apply Finset.sum_nbij (fun j : Fin r => (⟨j.val, Nat.lt_of_lt_of_le j.isLt hCard⟩ : Fin s))
  · intro j _
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, j.isLt⟩
  · intro j₁ _ j₂ _ hj
    exact Fin.ext (Fin.mk.inj hj)
  · intro α hα
    have hα' := (Finset.mem_filter.mp (Finset.mem_coe.mp hα)).2
    exact ⟨⟨α.val, hα'⟩, Finset.mem_coe.mpr (Finset.mem_univ _), Fin.ext rfl⟩
  · intro j _
    simp [Fin.eta]

end Fin
