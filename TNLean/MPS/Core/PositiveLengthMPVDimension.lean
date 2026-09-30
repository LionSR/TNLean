/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs

/-!
# Restoring the empty-word identity

At length zero, the periodic trace of a tensor is its bond dimension.
Positive-length equality therefore extends to all lengths as soon as
the bond dimensions agree.
-/

namespace MPSTensor

/-- Positive-length matrix-product-vector equality extends to all
lengths when the two bond dimensions agree. -/
theorem sameMPV₂_of_sameMPV₂Pos_of_bondDim_eq
    {d D₁ D₂ : ℕ} (A : MPSTensor d D₁) (B : MPSTensor d D₂)
    (hSame : SameMPV₂Pos A B) (hDim : D₁ = D₂) :
    SameMPV₂ A B := by
  intro N σ
  by_cases hN : 0 < N
  · exact hSame N hN σ
  · have hNzero : N = 0 := Nat.eq_zero_of_not_pos hN
    subst N
    simp [hDim]

end MPSTensor
