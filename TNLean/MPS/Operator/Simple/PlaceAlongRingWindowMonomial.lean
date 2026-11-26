/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Placement.PlaceAlongMonomial
import TNLean.MPS.Operator.Simple.CommutingForm

/-!
# Periodic placement of monomial local operators

A monomial operator on an `L`-site window, placed on the periodic window
beginning at site `i` of an `N`-site chain, is again monomial
(`ManyBody.placeAlong_monomial`). Its permutation part
`ManyBody.placeAlongPerm (ManyBody.ringWindow hLN i) σ` replaces the window of a
chain configuration by the permuted window (`placeAlongPerm_ringWindow_apply`),
and its phase is the local phase evaluated on the extracted window.

For a two-site window at `j`, the extracted window is $(s_j,s_{j+1})$ and the
replacement changes exactly the sites $j$ and $j+1$.
-/

noncomputable section

open Matrix

namespace MPOTensor

variable {d : ℕ}

/-- The permutation `σ` of the configurations of a window, placed along the periodic window of
length `L` beginning at site `i` (`ManyBody.placeAlongPerm`), replaces the window of a chain
configuration by `σ` of it. -/
@[simp]
theorem placeAlongPerm_ringWindow_apply (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ : Equiv.Perm (Fin L → Fin d)) (s : Fin N → Fin d) :
    ManyBody.placeAlongPerm (X := fun _ ↦ Fin d) (ManyBody.ringWindow hLN i) σ s =
      MPSTensor.replaceWindow L hLN i s (σ (MPSTensor.extractWindow L i s)) := by
  symm
  rw [ManyBody.eq_placeAlongPerm_iff]
  refine ⟨fun v hv ↦ MPSTensor.replaceWindow_of_forall_ringWindow_ne hLN i s _ hv, ?_⟩
  funext u
  exact MPSTensor.replaceWindow_ringWindow hLN i s _ u

/-! ### Two-site windows -/

variable {N : ℕ} [NeZero N]

/-- On a chain of at least two sites, the two-site window at `j` consists of the
sites `j` and `j + 1`. -/
theorem extractWindow_two {α : Type*} (hN : 2 ≤ N) (j : Fin N) (t : Fin N → α) :
    MPSTensor.extractWindow 2 j t = ![t j, t (j + 1)] := by
  have h1 : (1 : Fin N).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  ext k
  fin_cases k
  · simp only [MPSTensor.extractWindow, Fin.zero_eta, Fin.isValue, Fin.val_zero, add_zero,
      Matrix.cons_val_zero]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt j.isLt)
  · simp only [MPSTensor.extractWindow, Fin.mk_one, Fin.isValue, Fin.val_one,
      Matrix.cons_val_one, Matrix.cons_val_fin_one]
    congr 1
    exact Fin.ext (by rw [Fin.val_add, h1])

/-- Replacing the two-site window at `j` changes exactly the sites `j` and
`j + 1`. -/
theorem replaceWindow_two_apply {α : Type*} (hN : 2 ≤ N) (j : Fin N) (s : Fin N → α)
    (w : Fin 2 → α) (k : Fin N) :
    MPSTensor.replaceWindow 2 hN j s w k =
      if k = j then w 0 else if k = j + 1 then w 1 else s k := by
  have h1 : (1 : Fin N).val = 1 := by
    rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  simp only [MPSTensor.replaceWindow]
  by_cases hkj : k = j
  · subst hkj
    have hoff : (k.val + N - k.val) % N = 0 := by
      rw [show k.val + N - k.val = N by omega, Nat.mod_self]
    rw [dite_eq_left (by rw [hoff]; norm_num), ite_eq_left rfl]
    exact congrArg w (Fin.ext hoff)
  · by_cases hk1 : k = j + 1
    · subst hk1
      have hoff : ((j + 1 : Fin N).val + N - j.val) % N = 1 := by
        rw [Fin.val_add, h1]
        exact MPSTensor.offset_mod_eq j.isLt (by omega)
      rw [dite_eq_left (by rw [hoff]; norm_num), ite_eq_right hkj, ite_eq_left rfl]
      exact congrArg w (Fin.ext hoff)
    · have hoff : ¬ (k.val + N - j.val) % N < 2 := by
        intro hlt
        have hk : k.val = (j.val + (k.val + N - j.val) % N) % N :=
          (MPSTensor.add_offset_mod_eq j.isLt k.isLt).symm
        rcases Nat.lt_succ_iff.mp hlt |>.lt_or_eq with h0 | h1'
        · have h0' : (k.val + N - j.val) % N = 0 := by omega
          rw [h0', add_zero, Nat.mod_eq_of_lt j.isLt] at hk
          exact hkj (Fin.ext hk)
        · rw [h1'] at hk
          exact hk1 (Fin.ext (by rw [Fin.val_add, h1, hk]))
      rw [dite_eq_right hoff, ite_eq_right hkj, ite_eq_right hk1]

end MPOTensor
