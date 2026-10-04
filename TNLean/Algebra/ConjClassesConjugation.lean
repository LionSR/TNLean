/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Group.Conj

/-!
# Conjugation preserves the conjugacy-class quotient

This elementary identity is used to identify flux measurements after the
accessible regular labels are conjugated by a common group element.
Source: SCP10, arXiv:1001.3807, Theorem 6.15, lines 2217–2267, and the
fluxon-braiding calculation, lines 2370–2395.
-/

namespace ConjClasses

/-- Conjugating a group element leaves its class unchanged.
Source: SCP10, Theorem 6.15 and the fluxon-braiding calculation. -/
theorem mk_conjugate {G : Type*} [Group G] (g x : G) :
    ConjClasses.mk (x * g * x⁻¹) = ConjClasses.mk g := by
  apply mk_eq_mk_iff_isConj.mpr
  exact (isConj_iff.mpr ⟨x, rfl⟩).symm

end ConjClasses
