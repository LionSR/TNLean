/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Defs

/-!
# Cyclic window indices

This file provides index equivalences that split a periodic chain into a consecutive
window and its ordered complement, together with the corresponding product factorization.

## Main definitions

* `MPSTensor.cyclicShiftEquiv` — rotates the site indices so that a chosen site is first.
* `MPSTensor.cyclicWindowIndexEquiv` — splits the chain into a cyclic window and its
  ordered complement.

## Main results

* `MPSTensor.cyclicWindowIndexEquiv_inl` — evaluates the equivalence on a window index.
* `MPSTensor.cyclicWindowIndexEquiv_inr` — evaluates the equivalence on a complementary
  index.
* `MPSTensor.prod_cyclicWindow_complement` — factors a product into a cyclic window and
  its ordered complement.
-/

open scoped BigOperators

namespace MPSTensor

/-- Cyclically shift the indices of an \(N\)-site chain so that \(i\) becomes the
initial site. -/
def cyclicShiftEquiv (N : ℕ) (i : Fin N) : Fin N ≃ Fin N where
  toFun k := ⟨(i.val + k.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  invFun k := ⟨(k.val + N - i.val) % N, Nat.mod_lt _ (Fin.pos i)⟩
  left_inv k := by
    apply Fin.ext
    exact offset_mod_eq i.isLt k.isLt
  right_inv k := by
    apply Fin.ext
    exact add_offset_mod_eq i.isLt k.isLt

/-- Split cyclic chain indices into a window of length \(L\) starting at \(i\) and
its ordered complement. -/
def cyclicWindowIndexEquiv (L N : ℕ) (hLN : L ≤ N) (i : Fin N) :
    Fin L ⊕ Fin (N - L) ≃ Fin N :=
  finSumFinEquiv |>.trans (finCongr (Nat.add_sub_of_le hLN)) |>.trans
    (cyclicShiftEquiv N i)

/-- Evaluate the cyclic window equivalence on a window index. -/
@[simp] theorem cyclicWindowIndexEquiv_inl
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin L) :
    cyclicWindowIndexEquiv L N hLN i (Sum.inl r) =
      ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := rfl

/-- Evaluate the cyclic window equivalence on a complementary index. -/
@[simp] theorem cyclicWindowIndexEquiv_inr
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (r : Fin (N - L)) :
    cyclicWindowIndexEquiv L N hLN i (Sum.inr r) =
      ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩ := by
  apply Fin.ext
  change (i.val + (L + r.val)) % N = (i.val + L + r.val) % N
  congr 1
  omega

/-- Factor a product over a cyclic chain into a consecutive window and its
ordered complement. -/
theorem prod_cyclicWindow_complement {M : Type*} [CommMonoid M]
    (L N : ℕ) (hLN : L ≤ N) (i : Fin N) (f : Fin N → M) :
    (∏ n : Fin N, f n) =
      (∏ r : Fin L,
        f ⟨(i.val + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) *
        (∏ r : Fin (N - L),
          f ⟨(i.val + L + r.val) % N, Nat.mod_lt _ (Fin.pos i)⟩) := by
  rw [Fintype.prod_equiv
    (cyclicWindowIndexEquiv L N hLN i).symm f
    (fun x ↦ f (cyclicWindowIndexEquiv L N hLN i x))
    (fun n ↦ by simp)]
  rw [Fintype.prod_sum_type]
  simp only [cyclicWindowIndexEquiv_inl, cyclicWindowIndexEquiv_inr]

end MPSTensor
