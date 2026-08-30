/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

/-!
# Moving-window double counting

This module records the finite-sum estimate used when Nachtergaele sums the
per-index martingale inequality. Each coefficient belongs to at most \(l+1\)
of the active windows.
-/

open scoped BigOperators

namespace FrustrationFree

/--
For nonnegative coefficients \(a_m\), summing the windows
\([n-l,n]\) over \(n\in[l,N)\) counts each coefficient at most \(l+1\) times.
Thus
\[
  \sum_{n=l}^{N-1}\sum_{m=n-l}^{n}a_m
  \le (l+1)\sum_{m=0}^{N-1}a_m.
\]

The proof follows the summation after equation \(\mathrm{Enpsi2}\) in Theorem 2.1(i)
of Nachtergaele, arXiv:cond-mat/9410110, lines 1220–1255. Write
\(m=n-l+k\) with \(0\le k\le l\), reverse the sums over \(n\) and \(k\),
and for fixed \(k\) inject the shifted indices into \([0,N)\). No relation
between \(l\) and \(N\) is required, so the empty outer sum when \(l\ge N\)
is included.
-/
theorem movingWindow_sum_le (a : ℕ → ℝ) (l N : ℕ) (ha : ∀ m, 0 ≤ a m) :
    ∑ n ∈ Finset.Ico l N, ∑ m ∈ Finset.Icc (n - l) n, a m ≤
      (l + 1) * ∑ m ∈ Finset.range N, a m := by
  have hwindow (n : ℕ) (hn : l ≤ n) :
      ∑ m ∈ Finset.Icc (n - l) n, a m =
        ∑ k ∈ Finset.range (l + 1), a (n - l + k) := by
    rw [show Finset.Icc (n - l) n = Finset.Ico (n - l) (n + 1) by
      ext m
      simp only [Finset.mem_Icc, Finset.mem_Ico, Nat.lt_succ_iff]]
    rw [Finset.sum_Ico_eq_sum_range]
    rw [show n + 1 - (n - l) = l + 1 by omega]
  calc
    ∑ n ∈ Finset.Ico l N, ∑ m ∈ Finset.Icc (n - l) n, a m =
        ∑ n ∈ Finset.Ico l N, ∑ k ∈ Finset.range (l + 1), a (n - l + k) := by
          refine Finset.sum_congr rfl fun n hn ↦ ?_
          exact hwindow n (Finset.mem_Ico.mp hn).1
    _ = ∑ k ∈ Finset.range (l + 1), ∑ n ∈ Finset.Ico l N, a (n - l + k) :=
      Finset.sum_comm
    _ ≤ ∑ k ∈ Finset.range (l + 1), ∑ m ∈ Finset.range N, a m := by
      refine Finset.sum_le_sum fun k hk ↦ ?_
      have hklt : k < l + 1 := Finset.mem_range.mp hk
      let g : ℕ → ℕ := fun n ↦ n - l + k
      have hg_inj : Set.InjOn g (Finset.Ico l N) := by
        intro n hn n' hn' hEq
        simp only [g] at hEq
        have hn_ge : l ≤ n := (Finset.mem_Ico.mp hn).1
        have hn'_ge : l ≤ n' := (Finset.mem_Ico.mp hn').1
        omega
      have hg_sub : Finset.image g (Finset.Ico l N) ⊆ Finset.range N := by
        intro m hm
        rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
        simp only [Finset.mem_range, g]
        have hn_bounds := Finset.mem_Ico.mp hn
        omega
      calc
        ∑ n ∈ Finset.Ico l N, a (n - l + k) =
            ∑ m ∈ Finset.image g (Finset.Ico l N), a m := by
              symm
              exact Finset.sum_image hg_inj
        _ ≤ ∑ m ∈ Finset.range N, a m :=
          Finset.sum_le_sum_of_subset_of_nonneg hg_sub fun m _ _ ↦ ha m
    _ = (l + 1) * ∑ m ∈ Finset.range N, a m := by simp

end FrustrationFree
