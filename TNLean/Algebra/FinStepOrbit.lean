/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

/-!
# Coordinates for a cyclic step

For a cycle of length `m > 0` and a step `p`, the residues `α + p * k`
with `α < gcd m p` and `k < m / gcd m p` enumerate the cycle exactly once.
This is arXiv:1708.00029, `lem:unique-dec`, used to index the cyclic sectors
in the proof of Theorem 4.1. The same coordinates construct local factors whose
products over `p` consecutive positions are prescribed roots on these orbits.
-/

open scoped BigOperators

namespace Fin

open Fin.NatCast

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

/-- Advancing the orbit coordinate once adds the original step modulo the cycle length.
Source: arXiv:1708.00029, the calculation following `eq:Aprime-is-cPA`. -/
theorem stepOrbitEquiv_add_one (m p : ℕ) (hm : 0 < m) [NeZero m] [NeZero (m / m.gcd p)]
    (a : Fin (m.gcd p)) (k : Fin (m / m.gcd p)) :
    Fin.stepOrbitEquiv m p hm (a, k + 1) = Fin.stepOrbitEquiv m p hm (a, k) + (↑p : Fin m) := by
  have hdvd : m ∣ p * (m / m.gcd p) := by
    obtain ⟨t, ht⟩ := Nat.gcd_dvd_right m p
    refine ⟨t, ?_⟩
    nth_rw 1 [ht]
    rw [Nat.mul_assoc, Nat.mul_comm t, ← Nat.mul_assoc,
      Nat.mul_div_cancel' (Nat.gcd_dvd_left m p)]
  have hmod := (((Nat.mod_modEq (k.val + 1) (m / m.gcd p)).mul_left' p).of_dvd hdvd).add_left a.val
  apply Fin.ext
  change (a.val + p * (k + 1).val) % m =
    ((a.val + p * k.val) % m + p % m) % m
  rw [← Nat.add_mod]
  simpa only [Fin.val_add, Fin.val_one', Nat.ModEq, Nat.add_mod_mod,
    Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hmod

/-- Roots of unity assigned to step orbits are products of consecutive local phases.
Source: arXiv:1708.00029, `eq:Aprime-is-cPA` and the telescoping calculation after it. -/
theorem exists_stepOrbit_phases {G : Type*} [CommGroup G] (m p : ℕ) [NeZero m]
    (c : Fin (m.gcd p) → G) (hc : ∀ a, c a ^ (m / m.gcd p) = 1) :
    ∃ b : Fin m → G, ∀ u,
      (∏ k ∈ Finset.range p, b (u + (↑k : Fin m))) =
        c ((stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))).symm u).1 := by
  have hq : 0 < m / m.gcd p :=
    Nat.div_gcd_pos_of_pos_left p (Nat.pos_of_ne_zero (NeZero.ne m))
  let : NeZero (m / m.gcd p) := ⟨Nat.ne_of_gt hq⟩
  let e := stepOrbitEquiv m p (Nat.pos_of_ne_zero (NeZero.ne m))
  let f : Fin m → G := fun u => c (e.symm u).1 ^ (e.symm u).2.val
  have hstep (u : Fin m) : f (u + (↑p : Fin m)) = c (e.symm u).1 * f u := by
    obtain ⟨⟨a, k⟩, rfl⟩ := e.surjective u
    rw [← stepOrbitEquiv_add_one m p (Nat.pos_of_ne_zero (NeZero.ne m)) a k]
    change f (e (a, k + 1)) = c (e.symm (e (a, k))).1 * f (e (a, k))
    simp only [f, Equiv.symm_apply_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
    rw [← pow_eq_pow_mod (k.val + 1) (hc a), pow_succ, mul_comm]
  refine ⟨fun u => f (u + 1) / f u, fun u => ?_⟩
  have ht := Finset.prod_range_div (fun k : ℕ => f (u + (↑k : Fin m))) p
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_assoc, add_zero,
    hstep, mul_div_cancel_right] using ht

end Fin
