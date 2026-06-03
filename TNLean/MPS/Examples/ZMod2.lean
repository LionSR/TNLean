/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.TypeTags.Finite
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Complex.Basic

/-!
# Z₂ and Z₂ × Z₂ group lemmas for MPS examples

Shared lemmas for MPS examples with `Z₂ = Multiplicative (ZMod 2)` or
`Z₂ × Z₂ = Multiplicative (ZMod 2 × ZMod 2)` symmetry.  These are reused by the
concrete cluster-state and AKLT examples, which both realise a `Z₂ × Z₂`
on-site symmetry by a pair of commuting involutions on the physical space.

## Main definitions

* `ofCommutingInvolutions` : the `Z₂ × Z₂` representation built from two
  commuting involutions `P₁`, `P₂` on a finite-dimensional space.
-/

namespace MPSTensor

/-- Every element of `Multiplicative (ZMod 2)` is either `1` or `ofAdd 1`. -/
lemma zmod2_cases (g : Multiplicative (ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd 1 := by
  fin_cases g <;> simp [Multiplicative.ext_iff] <;> tauto

lemma zmod2_one_add_one : (1 : ZMod 2) + 1 = 0 := by decide

/-- Every element of `Multiplicative (ZMod 2 × ZMod 2)` is one of the four group
elements `1`, `ofAdd (1, 0)`, `ofAdd (0, 1)`, `ofAdd (1, 1)`. -/
lemma zmod2sq_cases (g : Multiplicative (ZMod 2 × ZMod 2)) :
    g = 1 ∨ g = Multiplicative.ofAdd (1, 0) ∨ g = Multiplicative.ofAdd (0, 1) ∨
      g = Multiplicative.ofAdd (1, 1) := by
  revert g
  decide

/-! ### A `Z₂ × Z₂` representation from two commuting involutions

Given two commuting involutions `P₁`, `P₂` on a finite-dimensional space, the
two `ZMod 2` factors act by `P₁` and `P₂`.  Because `P₁² = P₂² = 1` and
`P₁P₂ = P₂P₁`, this assignment is a group homomorphism. -/

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The `Z₂ × Z₂` representation built from two commuting involutions `P₁`, `P₂`:
the first factor acts by `P₁`, the second by `P₂`.  The involution and
commutation hypotheses `h₁ : P₁ * P₁ = 1`, `h₂ : P₂ * P₂ = 1`,
`hc : P₁ * P₂ = P₂ * P₁` make the assignment a group homomorphism. -/
def ofCommutingInvolutions (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    Multiplicative (ZMod 2 × ZMod 2) →* Matrix n n ℂ where
  toFun g :=
    (if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
      (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂)
  map_one' := by simp [toAdd_one]
  map_mul' a b := by
    have key : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add]
    obtain (e1 | e1) := key (Multiplicative.toAdd a).1 <;>
      obtain (e2 | e2) := key (Multiplicative.toAdd a).2 <;>
        obtain (e3 | e3) := key (Multiplicative.toAdd b).1 <;>
          obtain (e4 | e4) := key (Multiplicative.toAdd b).2 <;>
            simp only [e1, e2, e3, e4, show (1 : ZMod 2) + 1 = 0 from by decide, add_zero,
              zero_add, one_ne_zero, ↓reduceIte, mul_one, one_mul]
    -- The eight remaining goals are equations among products of `1`, `P₁`, `P₂`,
    -- each closed using the involution facts `h₁`, `h₂` and commutation `hc`.
    · exact h₂.symm
    · exact hc
    · rw [hc, ← mul_assoc, h₂, one_mul]
    · exact h₁.symm
    · rw [← mul_assoc, h₁, one_mul]
    · rw [mul_assoc, h₂, mul_one]
    · rw [hc, mul_assoc, h₁, mul_one]
    · rw [mul_assoc, ← mul_assoc P₂ P₁ P₂, ← hc, mul_assoc P₁ P₂ P₂, h₂, mul_one, h₁]

/-- `ofCommutingInvolutions` evaluated on a group element is the corresponding
product of factors. -/
@[simp]
lemma ofCommutingInvolutions_apply (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) (g : Multiplicative (ZMod 2 × ZMod 2)) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc g =
      (if (Multiplicative.toAdd g).1 = 0 then 1 else P₁) *
        (if (Multiplicative.toAdd g).2 = 0 then 1 else P₂) := rfl

@[simp]
lemma ofCommutingInvolutions_ofAdd_10 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((1, 0) : ZMod 2 × ZMod 2)) =
      P₁ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte, mul_one]

@[simp]
lemma ofCommutingInvolutions_ofAdd_01 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((0, 1) : ZMod 2 × ZMod 2)) =
      P₂ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte, one_mul]

@[simp]
lemma ofCommutingInvolutions_ofAdd_11 (P₁ P₂ : Matrix n n ℂ) (h₁ : P₁ * P₁ = 1)
    (h₂ : P₂ * P₂ = 1) (hc : P₁ * P₂ = P₂ * P₁) :
    ofCommutingInvolutions P₁ P₂ h₁ h₂ hc (Multiplicative.ofAdd ((1, 1) : ZMod 2 × ZMod 2)) =
      P₁ * P₂ := by
  simp only [ofCommutingInvolutions_apply, toAdd_ofAdd, show (1 : ZMod 2) ≠ 0 from by decide,
    ↓reduceIte]

end MPSTensor
