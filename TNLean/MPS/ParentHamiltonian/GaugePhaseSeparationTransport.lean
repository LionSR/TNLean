/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.BNT.Separation

/-!
# Bond-dimension transport in sector separation

Pairwise gauge-phase inequivalence can be expressed by transporting the second
labelled tensor to the first tensor's bond dimension. This form of the existing
separation condition is used by the primitive-sector support and gap theorems.

Source: Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1606.00608,
Proposition prop:char-BNT and Theorem thm1; Nachtergaele,
arXiv:cond-mat/9410110, Section 3 and Lemma disjoint.
-/

namespace MPSTensor

/-- Read sector separation with the second tensor transported to the first
bond space. Source: CPSV16, arXiv:1606.00608, Proposition prop:char-BNT.
This is a reformulation of the existing condition, with no added assumption. -/
theorem BlocksNotGaugePhaseEquiv.forall_ne_transport {d r : ℕ} {dim : Fin r → ℕ}
    {A : ∀ j, MPSTensor d (dim j)} (hA : BlocksNotGaugePhaseEquiv A) :
    ∀ i j, i ≠ j → ∀ e : dim j = dim i, ¬ GaugePhaseEquiv (e ▸ A j) (A i) := by
  intro i j hij e
  simpa only [eqRec_eq_cast] using hA j i hij.symm e

end MPSTensor
