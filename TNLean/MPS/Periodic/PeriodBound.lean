/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.Defs
import QICLean.Channel.Semigroup.Primitivity.Helpers

/-!
# The period of a periodic tensor is at most the square of the bond dimension

The peripheral eigenvalues of the transfer map of a periodic tensor of period `m` are the
`m` distinct `m`-th roots of unity, and they are eigenvalues of an endomorphism of the
`D²`-dimensional space of `D × D` matrices. Hence `m ≤ D²`. This is the bound that makes
the device "consider `N` prime" of Pérez-García, Verstraete, Wolf, and Cirac
(arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex` lines 2092–2096) work at
every prime length `N > D²`.

## Main results

* `MPSTensor.IsPeriodic.period_le_sq` — `m ≤ D²`.
-/

namespace MPSTensor

variable {d D : ℕ}

/-- Bridge: the period of a periodic tensor of bond dimension `D` is at most `D²`. The
peripheral spectrum of its transfer map is the set of the `m` distinct `m`-th roots of unity,
and distinct eigenvalues of an endomorphism of the space of `D × D` matrices number at most
`D²`. -/
theorem IsPeriodic.period_le_sq {m : ℕ} {A : MPSTensor d D} (hA : IsPeriodic m A) :
    m ≤ D ^ 2 := by
  classical
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  obtain ⟨ω, hω⟩ := hA.primitiveRoot
  have hcard := peripheral_card_le_finrank (D := D) (Kraus.transferMap (d := d) (D := D) A)
  have hset : (peripheralEigenvalues_finite (Kraus.transferMap (d := d) (D := D) A)).toFinset =
      Polynomial.nthRootsFinset m (1 : ℂ) := by
    ext μ
    rw [Set.Finite.mem_toFinset, hA.peripheral_eq, Polynomial.mem_nthRootsFinset hA.period_pos]
    rfl
  rw [hset, hω.card_nthRootsFinset, Module.finrank_matrix] at hcard
  simpa [sq] using hcard

end MPSTensor
