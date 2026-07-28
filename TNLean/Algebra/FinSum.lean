/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Order.Fin.Tuple

/-!
# Finite initial-segment sums

This file collects small finite-sum identities.
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
          refine Fintype.sum_equiv (Fin.castLEOrderIso h).toEquiv f
            (fun α : { i : Fin s // (i : ℕ) < r } => f ⟨α.1.val, α.2⟩) ?_
          intro j
          simp
    _ = ∑ α ∈ (Finset.univ.filter fun α : Fin s => α.val < r),
          if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
          rw [← Finset.sum_subtype_eq_sum_filter
            (s := (Finset.univ : Finset (Fin s)))
            (p := fun i : Fin s => (i : ℕ) < r)
            (f := fun α : Fin s =>
              if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0)]
          refine Finset.sum_congr ?_ ?_
          · ext α
            simp
          intro α _
          simp [α.2]
    _ = ∑ α : Fin s, if hlt : α.val < r then f ⟨α.val, hlt⟩ else 0 := by
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl ?_
          intro α _
          by_cases hlt : α.val < r <;> simp [hlt]

end Fin

namespace MPSTensor

/-- Re-index a sum over a finite family by collecting coefficients in the fibres
of a finite map. -/
lemma sum_fiber_smul
    {ι κ V : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]
    [AddCommMonoid V] [Module ℂ V]
    (φ : ι → κ) (a : ι → ℂ) (v : κ → V) :
    (∑ i : ι, a i • v (φ i)) =
      ∑ k : κ, (∑ i : ι, if φ i = k then a i else 0) • v k := by
  classical
  calc
    (∑ i : ι, a i • v (φ i)) =
        ∑ k : κ, ∑ i with φ i = k, a i • v (φ i) := by
      symm
      simpa using Finset.sum_fiberwise_eq_sum_filter
        (Finset.univ : Finset ι) (Finset.univ : Finset κ) φ
        (fun i => a i • v (φ i))
    _ = ∑ k : κ, (∑ i : ι, if φ i = k then a i else 0) • v k := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.sum_smul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : φ i = k <;> simp [h]

end MPSTensor
