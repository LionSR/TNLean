/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LocalCircuit

/-!
# Separation of bounded sets on a ring

Two windows are separated when both gaps exceed the allowed ring displacement.
The same criterion locates a site outside the union of two backward light cones.
-/

namespace QuantumCircuit

open Fin.CommRing

variable {N : ℕ} [NeZero N]

/-- Sets lying in two intervals are separated when both cyclic gaps exceed the radius. -/
theorem isSeparatedBy_of_val_bounds {X Y : Set (Fin N)} {a w b w' s : ℕ}
    (hX : ∀ x ∈ X, a ≤ x.val ∧ x.val < a + w)
    (hY : ∀ y ∈ Y, b ≤ y.val ∧ y.val < b + w')
    (hab : a + w + s ≤ b) (hba : b + w' + s ≤ a + N) :
    IsSeparatedBy X Y s := by
  intro x hx y hy m hm heq
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_neZero N
  have h0 : 0 ≤ m % (N : ℤ) := Int.emod_nonneg _ hN.ne'
  have hv := congrArg Fin.val heq
  rw [Fin.val_add, Fin.val_intCast] at hv
  have hz : (y.val : ℤ) = ((x.val : ℤ) + m % N) % N := by
    rw [hv, Int.natCast_emod, Nat.cast_add, Int.toNat_of_nonneg h0]
  have e1 := Int.emod_add_mul_ediv ((x.val : ℤ) + m % N) N
  have e2 := Int.emod_add_mul_ediv m N
  have hdvd : (N : ℤ) ∣ (y.val : ℤ) - x.val - m :=
    ⟨-(((x.val : ℤ) + m % N) / N) - m / N, by rw [hz]; linear_combination e1 + e2⟩
  obtain ⟨hxa, hxw⟩ := hX x hx
  obtain ⟨hyb, hyw⟩ := hY y hy
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  have hpos : 0 ≤ (y.val : ℤ) - x.val - m := by omega
  have hlt : (y.val : ℤ) - x.val - m < N := by omega
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt hpos hlt hdvd
  omega

/-- Separation on the ring is symmetric. -/
theorem IsSeparatedBy.symm {X Y : Set (Fin N)} {s : ℕ} (h : IsSeparatedBy X Y s) :
    IsSeparatedBy Y X s := by
  intro y hy x hx m hm heq
  apply h x hx y hy (-m) (by simpa using hm)
  push_cast
  linear_combination -heq

/-- A separated site lies outside the backward neighbourhood. -/
theorem IsSeparatedBy.notMem_neighbourhood {X Y : Set (Fin N)} {s : ℕ}
    (h : IsSeparatedBy X Y s) {y : Fin N} (hy : y ∈ Y) : y ∉ neighbourhood X s := by
  rintro ⟨x, hx, m, hm, heq⟩
  exact h x hx y hy m hm heq

/-- Two disjoint backward light cones with a site outside their union. -/
theorem exists_separated_singletons_notMem_neighbourhood {T : ℕ} (hN : 4 * T + 4 < N) :
    ∃ i j k : Fin N, IsSeparatedBy {i} {j} (2 * T) ∧
      k ∉ neighbourhood {i} T ∪ neighbourhood {j} T := by
  let i : Fin N := ⟨0, by omega⟩
  let j : Fin N := ⟨2 * T + 2, by omega⟩
  let k : Fin N := ⟨T + 1, by omega⟩
  have hsep (x y : Fin N) (s : ℕ) (hxy : x.val + 1 + s ≤ y.val)
      (hyx : y.val + 1 + s ≤ x.val + N) : IsSeparatedBy {x} {y} s :=
    isSeparatedBy_of_val_bounds
      (fun z hz => by rcases Set.mem_singleton_iff.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      (fun z hz => by rcases Set.mem_singleton_iff.mp hz with rfl; exact ⟨le_rfl, by omega⟩)
      hxy hyx
  refine ⟨i, j, k, hsep i j (2 * T) (by dsimp [i, j]; omega) (by dsimp [i, j]; omega), ?_⟩
  have hik := hsep i k T (by dsimp [i, k]; omega) (by dsimp [i, k]; omega)
  have hkj := hsep k j T (by dsimp [k, j]; omega) (by dsimp [k, j]; omega)
  exact fun h => h.elim (hik.notMem_neighbourhood (by simp))
    (hkj.symm.notMem_neighbourhood (by simp))


end QuantumCircuit
