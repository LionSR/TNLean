/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.QCA.LocalAlgebra
import Lean.Elab.Tactic.Omega

/-!
# Ordered physical coordinates of consecutive pairs

The two physical coordinates occur in increasing site order. This is
the common finite-coordinate identification for the two-cell matrix
algebras in GNVW, arXiv:0910.3675v2, RR2x, lines 1251–1266, and the
physical input/output spaces of Schumacher–Werner bruleU/bruleV,
quant-ph/0405174, lines 980–1001.
-/

namespace SpinChain

/-- The ordered coordinates at sites a and a+1 identify the physical
pair with two one-site coordinate spaces, in that order.
Source: GNVW RR2x, lines 1251–1266; Schumacher–Werner bruleU/bruleV. -/
def consecutivePairConfigEquiv (b : ℕ) (a : ℤ) :
    (Fin b × Fin b) ≃ Config b ({a, a + 1} : Finset ℤ) where
  toFun c x := if x.val = a then c.1 else c.2
  invFun f := (f ⟨a, by simp⟩, f ⟨a + 1, by simp⟩)
  left_inv c := by
    apply Prod.ext
    · exact ite_eq_left rfl
    · exact ite_eq_right (by omega : a + 1 ≠ a)
  right_inv f := by
    funext x
    rcases x with ⟨x, hx⟩
    have hx' : x = a ∨ x = a + 1 := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hx
    rcases hx' with rfl | rfl
    · exact ite_eq_left rfl
    · exact ite_eq_right (by omega : a + 1 ≠ a)

end SpinChain
