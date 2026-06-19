/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite initial-segment sums

This file collects small finite-sum identities for `Fin` index types.
-/

open scoped BigOperators

namespace Fin

/-- A sum over `Fin r` can be rewritten as a zero-padded sum over `Fin s`
when `r ≤ s`. -/
theorem sum_castLE_extend_zero {r s : ℕ} {β : Type*} [AddCommMonoid β]
    (f : Fin r → β) (h : r ≤ s) :
    ∑ j : Fin r, f j =
      ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
  classical
  calc
    ∑ j : Fin r, f j =
        ∑ α : { i : Fin s // (i : ℕ) < r }, f ⟨α.1.val, α.2⟩ := by
          refine Fintype.sum_equiv (Fin.castLEquiv h) f
            (fun α : { i : Fin s // (i : ℕ) < r } => f ⟨α.1.val, α.2⟩) ?_
          intro j
          simp [Fin.castLEquiv]
    _ = ∑ α ∈ (Finset.univ.filter fun α : Fin s => α.val < r),
          if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
          rw [show (Finset.univ : Finset { i : Fin s // (i : ℕ) < r }) =
              (Finset.univ : Finset (Fin s)).subtype (fun i : Fin s => (i : ℕ) < r) by
                ext α
                simp]
          have hsub :=
            Finset.sum_subtype_eq_sum_filter
              (s := (Finset.univ : Finset (Fin s)))
              (p := fun i : Fin s => (i : ℕ) < r)
              (f := fun α : Fin s =>
                if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0)
          have hleft :
              (∑ α ∈ (Finset.univ : Finset (Fin s)).subtype
                    (fun i : Fin s => (i : ℕ) < r),
                  (if hlt : (α : Fin s).val < r then f ⟨(α : Fin s).val, hlt⟩ else 0)) =
                ∑ α ∈ (Finset.univ : Finset (Fin s)).subtype
                    (fun i : Fin s => (i : ℕ) < r),
                  f ⟨(α : Fin s).val, α.2⟩ := by
            refine Finset.sum_congr rfl ?_
            intro α _
            simp [α.2]
          exact hleft.symm.trans hsub
    _ = ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
          have hfilter :=
            Finset.sum_filter
              (s := (Finset.univ : Finset (Fin s)))
              (p := fun α : Fin s => α.val < r)
              (f := fun α : Fin s =>
                if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0)
          have hright :
              (∑ α : Fin s,
                if α.val < r then
                  (if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0)
                else 0) =
                ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
            refine Finset.sum_congr rfl ?_
            intro α _
            by_cases hlt : α.val < r <;> simp [hlt]
          exact hfilter.trans hright

end Fin
