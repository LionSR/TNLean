/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn

/-!
# Ordered products indexed by finite initial segments

This file collects distributivity identities for ordered, generally noncommutative products
whose factors are indexed by `Fin`.

## Main results

* `List.prod_ofFn_sum`: distributes an ordered product over finite sums.
* `List.prod_ofFn_smul`: extracts the product of scalar coefficients.
-/

open scoped BigOperators

namespace List

/-- An ordered product of finite sums is the sum over all choices of the corresponding
ordered products. -/
theorem prod_ofFn_sum {R J : Type*} [Semiring R] [Fintype J]
    {N : ℕ} (f : Fin N → J → R) :
    (List.ofFn fun n : Fin N ↦ ∑ j : J, f n j).prod =
      ∑ choice : Fin N → J, (List.ofFn fun n ↦ f n (choice n)).prod := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, ih (fun n ↦ f n.succ), Finset.sum_mul_sum]
      rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (N + 1) ↦ J),
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl (fun j _ ↦ Finset.sum_congr rfl (fun choice _ ↦ ?_))
      rw [List.ofFn_succ, List.prod_cons]
      simp [Fin.consEquiv]

/-- Scalars extract from an ordered product as their commutative product. -/
theorem prod_ofFn_smul {𝕜 R : Type*} [CommSemiring 𝕜] [Semiring R] [Algebra 𝕜 R]
    {N : ℕ} (c : Fin N → 𝕜) (A : Fin N → R) :
    (List.ofFn fun n : Fin N ↦ c n • A n).prod =
      (∏ n : Fin N, c n) • (List.ofFn A).prod := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, ih (fun n ↦ c n.succ) (fun n ↦ A n.succ),
        smul_mul_smul_comm, Fin.prod_univ_succ, List.ofFn_succ, List.prod_cons]

end List
