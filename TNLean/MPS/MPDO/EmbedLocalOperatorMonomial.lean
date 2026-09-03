/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.MonomialMatrix
import TNLean.MPS.MPDO.CommutingForm

/-!
# Periodic placement of monomial local operators

A monomial operator on an `L`-site window, placed on the periodic window
beginning at site `i` of an `N`-site chain, is again monomial. Its
permutation part replaces the window of a chain configuration by the permuted
window, and its phase is the local phase evaluated on the extracted window.

For a two-site window at `j`, the extracted window is $(s_j,s_{j+1})$ and the
replacement changes exactly the sites $j$ and $j+1$.
-/

noncomputable section

open Matrix

namespace MPOTensor

variable {d : ℕ}

/-- The permutation of chain configurations obtained by permuting the periodic
window of length `L` beginning at site `i` by `σ`. -/
def windowPerm (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N) (σ : Equiv.Perm (Fin L → Fin d)) :
    Equiv.Perm (Fin N → Fin d) where
  toFun s := MPSTensor.replaceWindow L hLN i s (σ (MPSTensor.extractWindow L i s))
  invFun s := MPSTensor.replaceWindow L hLN i s (σ.symm (MPSTensor.extractWindow L i s))
  left_inv s := by simp
  right_inv s := by simp

@[simp]
theorem windowPerm_apply (L : ℕ) {N : ℕ} (hLN : L ≤ N) (i : Fin N)
    (σ : Equiv.Perm (Fin L → Fin d)) (s : Fin N → Fin d) :
    windowPerm L hLN i σ s =
      MPSTensor.replaceWindow L hLN i s (σ (MPSTensor.extractWindow L i s)) :=
  rfl

/-- Placing a monomial window operator on a periodic chain gives a monomial chain
operator whose permutation acts on the window and whose phase is read off the
window. -/
theorem embedLocalOperator_monomial (L N : ℕ) (hLN : L ≤ N) (i : Fin N)
    (σ : Equiv.Perm (Fin L → Fin d)) (φ : (Fin L → Fin d) → ℂ) :
    embedLocalOperator (d := d) L N hLN i (monomial σ φ) =
      monomial (windowPerm L hLN i σ) fun s ↦ φ (MPSTensor.extractWindow L i s) := by
  ext t s
  rw [embedLocalOperator_apply, monomial_apply, monomial_apply, windowPerm_apply]
  by_cases h : t = MPSTensor.replaceWindow L hLN i s (σ (MPSTensor.extractWindow L i s))
  · have hagree : AgreesOutsideWindow (d := d) L hLN i t s := by
      rw [AgreesOutsideWindow, h]
      simp
    rw [ite_eq_left hagree, ite_eq_left h, ite_eq_left]
    rw [h]
    simp
  · rw [ite_eq_right h]
    by_cases hagree : AgreesOutsideWindow (d := d) L hLN i t s
    · rw [ite_eq_left hagree, ite_eq_right]
      intro hw
      apply h
      rw [← hw]
      exact hagree.symm
    · rw [ite_eq_right hagree]

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
