/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Periodic.BlockedPeripheralFixed
import TNLean.MPS.Periodic.BlockedPeripheralMultiplicity

/-!
# Fixed-space dimension after blocking a periodic tensor

The fixed space of the `p`th transfer-map power of a period-`m` tensor has
dimension at most `gcd(m,p)`. This is the spectral bound needed to show that
each of the orbit blocks produced by `p`-site blocking is irreducible.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.Frobenius

namespace MPSTensor

/-- The fixed space of the `p`-blocked transfer map has dimension at most
the number of shift orbits of the original period.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem IsPeriodic.finrank_blocked_fixed_le_gcd
    {d D m : ℕ} (A : MPSTensor d D) (hA : IsPeriodic m A)
    {p : ℕ} (hp : 0 < p) :
    Module.finrank ℂ
      (Module.End.eigenspace (Kraus.mapLM A ^ p) 1) ≤ Nat.gcd m p := by
  have : NeZero D := ⟨hA.bondDim_ne_zero⟩
  have : NeZero m := ⟨hA.period_pos.ne'⟩
  exact finrank_eigenspace_pow_one_le_gcd (Kraus.mapLM A)
    (Kraus.isPositiveMap_mapLM A)
    (Kraus.isChannel_mapLM A hA.leftCanonical).tp
    hA.peripheral_eq
    (fun μ hμ => (hA.finrank_peripheral_eigenspace_eq_one A hμ).le)
    hp

end MPSTensor
