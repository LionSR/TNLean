/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Cyclic sums over `ZMod`

This file collects translation-invariance, triangular-counting, window-counting,
and offset-partition identities for sums over a finite cyclic group.
-/

namespace ZModCyclicSums

section CyclicSums

variable {M : Type*} [AddCommMonoid M] {N : ℕ} [NeZero N]

/-- Cyclic translation invariance: summing over the cyclic group `ZMod N`
commutes with right translation of the index. -/
theorem sum_comp_addRight (F : ZMod N → M) (d : ZMod N) :
    ∑ i, F (i + d) = ∑ i, F i := by
  simpa using Equiv.sum_comp (Equiv.addRight d) F

/-- Cyclic translation invariance: summing over the cyclic group `ZMod N`
commutes with left translation of the index. -/
theorem sum_comp_addLeft (F : ZMod N → M) (d : ZMod N) :
    ∑ i, F (d + i) = ∑ i, F i := by
  simpa using Equiv.sum_comp (Equiv.addLeft d) F

/-- Weighted triangular count, upper form.  Summing the offsets `e` with
`1 ≤ e < m - q` over all `q < m` counts each `e` with `1 ≤ e < m` exactly
`m - e` times. -/
theorem sum_range_Ico_triangular (F : ℕ → M) (m : ℕ) :
    (∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q), F e) =
      ∑ e ∈ Finset.Ico 1 m, (m - e) • F e := by
  classical
  have hExtend : ∀ q ∈ Finset.range m,
      (∑ e ∈ Finset.Ico 1 (m - q), F e) =
        ∑ e ∈ Finset.Ico 1 m, (if e ∈ Finset.Ico 1 (m - q) then F e else 0) := by
    intro q _
    have hfil : (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (m - q)) =
        Finset.Ico 1 (m - q) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have h1 : (∑ e ∈ Finset.Ico 1 (m - q), F e) =
        ∑ e ∈ (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (m - q)), F e := by
      rw [hfil]
    rw [h1, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun q hq => hExtend q hq), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hem : 1 ≤ e ∧ e < m := Finset.mem_Ico.mp he
  have hCard : ∑ q ∈ Finset.range m, (if q ∈ Finset.range (m - e) then F e else 0) =
      (m - e) • F e := by
    have hfil : (Finset.range m).filter (fun q => q ∈ Finset.range (m - e)) =
        Finset.range (m - e) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.sum_filter (s := Finset.range m), hfil, Finset.sum_const]
    congr 1
    simp
  rw [← hCard]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqm : q < m := Finset.mem_range.mp hq
  by_cases h1 : e ∈ Finset.Ico 1 (m - q)
  · by_cases h2 : q ∈ Finset.range (m - e)
    · simp [h1, h2]
    · exfalso
      simp only [Finset.mem_Ico, Finset.mem_range] at h1 h2
      omega
  · by_cases h2 : q ∈ Finset.range (m - e)
    · exfalso
      simp only [Finset.mem_Ico, Finset.mem_range] at h1 h2
      omega
    · simp [h1, h2]

/-- Weighted triangular count, lower form.  Summing the offsets `e` with
`1 ≤ e ≤ q` over all `q < m` counts each `e` with `1 ≤ e < m` exactly
`m - e` times. -/
theorem sum_range_Ico_triangular_lower (F : ℕ → M) (m : ℕ) :
    (∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1), F e) =
      ∑ e ∈ Finset.Ico 1 m, (m - e) • F e := by
  classical
  have hExtend : ∀ q ∈ Finset.range m,
      (∑ e ∈ Finset.Ico 1 (q + 1), F e) =
        ∑ e ∈ Finset.Ico 1 m, (if e ∈ Finset.Ico 1 (q + 1) then F e else 0) := by
    intro q hq
    have hqm : q < m := Finset.mem_range.mp hq
    have hfil : (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (q + 1)) =
        Finset.Ico 1 (q + 1) := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_Ico]
      omega
    have h1 : (∑ e ∈ Finset.Ico 1 (q + 1), F e) =
        ∑ e ∈ (Finset.Ico 1 m).filter (fun e => e ∈ Finset.Ico 1 (q + 1)), F e := by
      rw [hfil]
    rw [h1, Finset.sum_filter]
  rw [Finset.sum_congr rfl (fun q hq => hExtend q hq), Finset.sum_comm]
  refine Finset.sum_congr rfl fun e he => ?_
  have hem : 1 ≤ e ∧ e < m := Finset.mem_Ico.mp he
  have hCard : ∑ q ∈ Finset.range m, (if q ∈ Finset.Ico e m then F e else 0) =
      (m - e) • F e := by
    have hfil : (Finset.range m).filter (fun q => q ∈ Finset.Ico e m) =
        Finset.Ico e m := by
      refine Finset.ext fun x => ?_
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      omega
    rw [← Finset.sum_filter (s := Finset.range m), hfil, Finset.sum_const]
    congr 1
    simp
  rw [← hCard]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hqm : q < m := Finset.mem_range.mp hq
  by_cases h1 : e ∈ Finset.Ico 1 (q + 1)
  · by_cases h2 : q ∈ Finset.Ico e m
    · simp [h1, h2]
    · exfalso
      simp only [Finset.mem_Ico] at h1 h2
      omega
  · by_cases h2 : q ∈ Finset.Ico e m
    · exfalso
      simp only [Finset.mem_Ico] at h1 h2
      omega
    · simp [h1, h2]

/-- Cyclic double counting for a square window of offsets.  For any function
`T` on pairs of cyclic sites, summing `T (s + q) (s + q')` over all starting
points `s` and all pairs of offsets `q, q' < m` produces the diagonal `T i i`
with multiplicity `m`, and each ordered pair `(i, i + e)` and `(i, i - e)` with
`1 ≤ e < m` with multiplicity `m - e`. -/
theorem sum_cyclic_window_eq (T : ZMod N → ZMod N → M) (m : ℕ) :
    (∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
        T (s + q) (s + q')) =
      m • ∑ i : ZMod N, T i i +
        ∑ e ∈ Finset.Ico 1 m, (m - e) •
          ∑ i : ZMod N, (T i (i + e) + T i (i - e)) := by
  classical
  -- Translate the sum over starting points for each fixed pair of offsets.
  have hStep1 : ∀ q ∈ Finset.range m, ∀ q' ∈ Finset.range m,
      (∑ s : ZMod N, T (s + q) (s + q')) = ∑ i : ZMod N, T i (i + (q' - q)) := by
    intro q _ q' _
    have harg : ∀ s : ZMod N, (s + q) + (q' - q) = s + q' := by
      intro s
      abel
    calc (∑ s : ZMod N, T (s + q) (s + q'))
        = ∑ s : ZMod N, T (s + q) ((s + q) + (q' - q)) :=
          Finset.sum_congr rfl fun s _ => by rw [harg s]
      _ = ∑ i : ZMod N, T i (i + (q' - q)) :=
          sum_comp_addRight (fun u => T u (u + (q' - q))) q
  -- Flatten the sum over starting points to the inside.
  have hFlat : (∑ s : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
      T (s + q) (s + q')) =
      ∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m,
        T i (i + (q' - q)) := by
    conv_rhs => rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q hq => ?_
    conv_rhs => rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q' hq' => hStep1 q hq q' hq'
  -- Split each offset square into the diagonal and the two triangles.
  have hSplit : ∀ i : ZMod N,
      (∑ q ∈ Finset.range m, ∑ q' ∈ Finset.range m, T i (i + (q' - q))) =
        (∑ q ∈ Finset.range m, T i i) +
          ((∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q), T i (i + e)) +
            ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e)) := by
    intro i
    have hPer : ∀ q ∈ Finset.range m,
        (∑ q' ∈ Finset.range m, T i (i + (q' - q))) =
          T i i + ((∑ e ∈ Finset.Ico 1 (m - q), T i (i + e)) +
            ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e)) := by
      intro q hq
      have hqm : q < m := Finset.mem_range.mp hq
      have hRange : Finset.range m =
          Finset.Ico 0 q ∪ insert q (Finset.Ico (q + 1) m) := by
        have h1 : Finset.range m = Finset.Ico 0 m := Finset.range_eq_Ico m
        have h2 : Finset.Ico 0 m = Finset.Ico 0 q ∪ Finset.Ico q m :=
          (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
        have h3 : Finset.Ico q m = insert q (Finset.Ico (q + 1) m) := by
          rw [← Finset.insert_erase (Finset.mem_Ico.mpr ⟨le_refl q, by omega⟩),
            ← Nat.Ico_succ_left_eq_erase_Ico]
        rw [h1, h2, h3]
      rw [hRange, Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr
        (Finset.eq_empty_iff_forall_notMem.mpr fun x hx => by
          simp only [Finset.mem_inter, Finset.mem_Ico, Finset.mem_insert] at hx
          omega)), Finset.sum_insert (by
        intro hxs
        simp only [Finset.mem_Ico] at hxs
        omega)]
      -- The strict lower triangle reindexes by the positive offset difference.
      have hFirst : (∑ q' ∈ Finset.Ico 0 q, T i (i + (q' - q))) =
          ∑ e ∈ Finset.Ico 1 (q + 1), T i (i - e) := by
        refine Finset.sum_nbij' (fun q' => q - q') (fun e => q - e) ?_ ?_ ?_ ?_ ?_
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq' ⊢
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he ⊢
          omega
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq'
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he
          omega
        · intro q' hq'
          have hq'q : q' ≤ q := by
            simp only [Finset.mem_Ico] at hq'
            omega
          have hcast : ((q' : ZMod N) - q) = -((q - q' : ℕ) : ZMod N) := by
            have hsub : (((q - q' : ℕ) : ZMod N)) + (q' : ZMod N) = (q : ZMod N) := by
              rw [← Nat.cast_add, Nat.sub_add_cancel hq'q]
            linear_combination (norm := module) hsub
          change T i (i + (↑q' - ↑q)) = T i (i - ↑(q - q'))
          congr 1
          rw [hcast]
          abel
      -- The strict upper triangle reindexes by the positive offset difference.
      have hThird : (∑ q' ∈ Finset.Ico (q + 1) m, T i (i + (q' - q))) =
          ∑ e ∈ Finset.Ico 1 (m - q), T i (i + e) := by
        refine Finset.sum_nbij' (fun q' => q' - q) (fun e => q + e) ?_ ?_ ?_ ?_ ?_
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq' ⊢
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he ⊢
          omega
        · intro q' hq'
          simp only [Finset.mem_Ico] at hq'
          omega
        · intro e he
          simp only [Finset.mem_Ico] at he
          omega
        · intro q' hq'
          have hq'q : q < q' := by
            simp only [Finset.mem_Ico] at hq'
            omega
          change T i (i + (↑q' - ↑q)) = T i (i + ↑(q' - q))
          rw [Nat.cast_sub hq'q.le]
      rw [hFirst, hThird, sub_self, add_zero]
      ac_rfl
    rw [Finset.sum_congr rfl hPer, Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- Assemble: diagonal, then the two weighted triangles.
  rw [hFlat, Finset.sum_congr rfl fun i _ => hSplit i, Finset.sum_add_distrib,
    Finset.sum_add_distrib]
  have hDiag : (∑ i : ZMod N, ∑ q ∈ Finset.range m, T i i) = m • ∑ i : ZMod N, T i i := by
    rw [Finset.sum_comm]
    simp
  rw [hDiag]
  have hUpper : (∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (m - q),
      T i (i + e)) = ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i + e) := by
    rw [Finset.sum_congr rfl fun i _ => sum_range_Ico_triangular (fun e => T i (i + e)) m,
      Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => (Finset.smul_sum).symm
  have hLower : (∑ i : ZMod N, ∑ q ∈ Finset.range m, ∑ e ∈ Finset.Ico 1 (q + 1),
      T i (i - e)) = ∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i - e) := by
    rw [Finset.sum_congr rfl fun i _ =>
      sum_range_Ico_triangular_lower (fun e => T i (i - e)) m, Finset.sum_comm]
    exact Finset.sum_congr rfl fun e _ => (Finset.smul_sum).symm
  have hComb : (∑ e ∈ Finset.Ico 1 m, (m - e) •
        ∑ i : ZMod N, (T i (i + e) + T i (i - e))) =
      (∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i + e)) +
        (∑ e ∈ Finset.Ico 1 m, (m - e) • ∑ i : ZMod N, T i (i - e)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.sum_add_distrib, smul_add]
  rw [hUpper, hLower, ← hComb]

/-- Partition of the nonzero cyclic offsets into short offsets `1 ≤ e < m`,
the reflection `N - e` of each short offset, and middle offsets
`m ≤ k ≤ N - m`.  The partition requires `1 ≤ m ≤ N / 2`, so that the middle
interval is well placed and short offsets and their reflections are distinct. -/
theorem sum_offset_partition (F : ZMod N → M) {m : ℕ} (hm1 : 1 ≤ m) (hm : 2 * m ≤ N) :
    (∑ u ∈ (Finset.univ.erase 0 : Finset (ZMod N)), F u) =
      (∑ e ∈ Finset.Ico 1 m, (F e + F ((N - e : ℕ) : ZMod N))) +
        ∑ k ∈ Finset.Ico m (N - m + 1), F k := by
  classical
  -- Index the nonzero cyclic offsets by the integer interval `1 ≤ k < N`.
  have hBij : (∑ u ∈ Finset.univ.erase (0 : ZMod N), F u) =
      ∑ k ∈ Finset.Ico 1 N, F k := by
    refine Finset.sum_nbij' (fun u => u.val) (fun k => (k : ZMod N)) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      have hu0 : u ≠ 0 := by simpa using hu
      have hlt : u.val < N := ZMod.val_lt u
      have hne : u.val ≠ 0 := fun h0 => hu0 (by
        rw [← ZMod.natCast_zmod_val u, h0]
        simp)
      simp only [Finset.mem_Ico]
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkne : (k : ZMod N) ≠ 0 := by
        intro h0
        have hkmod : k % N = 0 := by
          rw [← ZMod.val_natCast N k, h0]
          simp
        rw [Nat.mod_eq_of_lt (by omega)] at hkmod
        omega
      exact Finset.mem_erase.2 ⟨hkne, Finset.mem_univ _⟩
    · intro u _
      exact ZMod.natCast_zmod_val u
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkN : ((k : ZMod N)).val = k % N := ZMod.val_natCast N k
      rw [hkN, Nat.mod_eq_of_lt (by omega)]
    · intro u _
      rw [ZMod.natCast_zmod_val]
  rw [hBij]
  -- Split the interval `1 ≤ k < N` into short, middle, and long offsets.
  have hUnion : (Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1)) ∪ Finset.Ico (N - m + 1) N =
      Finset.Ico 1 N := by
    have hU1 : Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1) = Finset.Ico 1 (N - m + 1) :=
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    have hU2 : Finset.Ico 1 (N - m + 1) ∪ Finset.Ico (N - m + 1) N = Finset.Ico 1 N :=
      Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)
    rw [hU1, hU2]
  have hDisj1 : Disjoint (Finset.Ico 1 m) (Finset.Ico m (N - m + 1)) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    simp only [Finset.mem_inter, Finset.mem_Ico] at hx
    omega
  have hDisj2 : Disjoint (Finset.Ico 1 m ∪ Finset.Ico m (N - m + 1))
      (Finset.Ico (N - m + 1) N) := by
    rw [Finset.disjoint_iff_inter_eq_empty]
    refine Finset.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
    simp only [Finset.mem_inter, Finset.mem_union, Finset.mem_Ico] at hx
    omega
  -- Reflect the long offsets `N - m + 1 ≤ k < N` back to short offsets.
  have hLong : (∑ k ∈ Finset.Ico (N - m + 1) N, F k) =
      ∑ e ∈ Finset.Ico 1 m, F ((N - e : ℕ) : ZMod N) := by
    refine Finset.sum_nbij' (fun k => N - k) (fun e => N - e) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_Ico] at hk ⊢
      omega
    · intro e he
      simp only [Finset.mem_Ico] at he ⊢
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      omega
    · intro e he
      simp only [Finset.mem_Ico] at he
      omega
    · intro k hk
      simp only [Finset.mem_Ico] at hk
      have hkN : N - (N - k) = k := by omega
      simp only [hkN]
  rw [← hUnion, Finset.sum_union hDisj2, Finset.sum_union hDisj1, hLong,
    Finset.sum_add_distrib]
  ac_rfl

end CyclicSums

end ZModCyclicSums
