/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Core.CyclicTraceForcedBond

/-!
# Periodic vectors of bond-one tensors

A bond-one periodic vector is the product of its one-site scalar entries.
A nonzero letter therefore gives a nonzero vector at every positive
length, including lengths preceding any injectivity threshold.

Source: the trace-MPS definition in SPWC10, arXiv:0909.5347, and the
finite-prefix boundary of Theorem 5, local main.tex lines 850--880.
-/

open scoped BigOperators

namespace MPSTensor

variable {d N : ℕ}

/-- At bond dimension one, the periodic amplitude is the product of the
actual one-site scalar entries. Source: the trace-MPS definition used in
SPWC10, arXiv:0909.5347, Theorem 5, lines 850--880. -/
theorem mpv_apply_of_bondOne [NeZero N] (A : MPSTensor d 1) (σ : Fin N → Fin d) :
    mpv A σ = ∏ k, A (σ k) 0 0 := by
  rw [mpv_eq_prod_of_forced_bond A σ 0
    (fun g hg ↦ absurd (Subsingleton.elim g 0) hg)]
  rfl

/-- A nonzero bond-one letter supplies an actual nonzero periodic
amplitude at every positive length. No finite-length nonvanishing
hypothesis is supplied. Source: SPWC10, Theorem 5, lines 850--880,
product-state specialization of its uniform-bond branch. -/
theorem exists_mpv_ne_zero_of_bondOne (A : MPSTensor d 1)
    (hletter : ∃ i, A i ≠ 0) (hN : 0 < N) : ∃ σ : Fin N → Fin d, mpv A σ ≠ 0 := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  obtain ⟨i, hi⟩ := hletter
  have hentry : A i 0 0 ≠ 0 := by
    intro hzero
    apply hi
    ext p q
    simpa only [show p = 0 from Subsingleton.elim _ _,
      show q = 0 from Subsingleton.elim _ _, Matrix.zero_apply] using hzero
  refine ⟨fun _ ↦ i, ?_⟩
  rw [mpv_apply_of_bondOne]
  exact Finset.prod_ne_zero_iff.mpr (fun _ _ ↦ hentry)

end MPSTensor
