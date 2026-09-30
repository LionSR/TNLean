/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

/-!
# Coordinates for a cyclic step

For a cycle of length `m > 0` and a step `p`, the residues `α + p * k`
with `α < gcd m p` and `k < m / gcd m p` enumerate the cycle exactly once.
This is arXiv:1708.00029, `lem:unique-dec`, used to index the cyclic sectors
in the proof of Theorem 4.1.
-/

namespace Fin

/-- The step coordinates enumerate a finite cycle without repetition
(arXiv:1708.00029, `lem:unique-dec`). The step may be zero. -/
theorem stepOrbit_bijective (m p : ℕ) (hm : 0 < m) :
    Function.Bijective (fun x : Fin (m.gcd p) × Fin (m / m.gcd p) =>
      (⟨(x.1.val + p * x.2.val) % m, Nat.mod_lt _ hm⟩ : Fin m)) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  constructor
  · intro ⟨a, k⟩ ⟨b, l⟩ h
    have hxy : Nat.ModEq m (a.val + p * k.val) (b.val + p * l.val) :=
      congrArg Fin.val h
    have hg := hxy.of_dvd (Nat.gcd_dvd_left m p)
    have hpmod : p % m.gcd p = 0 := Nat.mod_eq_zero_of_dvd (Nat.gcd_dvd_right m p)
    have hab : a = b := by
      apply Fin.ext
      simpa [Nat.ModEq, Nat.add_mod, Nat.mul_mod, hpmod,
        Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hg
    subst b
    have hk := (Nat.ModEq.add_left_cancel' a.val hxy).cancel_left_div_gcd hm
    exact Prod.ext rfl (Fin.ext (hk.eq_of_lt_of_lt k.isLt l.isLt))
  · simp only [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_div_cancel' (Nat.gcd_dvd_left m p)

/-- The coordinates `α, k` of arXiv:1708.00029, `lem:unique-dec`, as an
equivalence with the original cyclic index. -/
noncomputable def stepOrbitEquiv (m p : ℕ) (hm : 0 < m) :
    Fin (m.gcd p) × Fin (m / m.gcd p) ≃ Fin m :=
  Equiv.ofBijective
    (fun x => ⟨(x.1.val + p * x.2.val) % m, Nat.mod_lt _ hm⟩)
    (stepOrbit_bijective m p hm)

end Fin
