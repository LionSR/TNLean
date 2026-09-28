/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.Martingale.GroupedProjections
import TNLean.MPS.ParentHamiltonian.Martingale.OpenParentGap

/-!
# Energy bounds for grouped open-chain windows

For an interaction of range \(2p\), the martingale windows ending at
\(p(n+1)\) form a subfamily of the ordinary open-chain windows. Positivity
therefore bounds their total energy by the full open-chain energy. Each window
is itself a projection, so its local gap is one.

These are conditions C1-prime and C2 in Nachtergaele,
arXiv:cond-mat/9410110, Theorem 2.1(ii), at interaction range \(2p\).
-/

open scoped BigOperators ComplexOrder InnerProductSpace

private theorem sum_grouped_le {p M : ℕ} (hp : 0 < p)
    (f : ℕ → ℝ) (hf : ∀ n, 0 ≤ f n) :
    (∑ n ∈ Finset.range M, f (p * (n + 1) - 1)) ≤
      ∑ n ∈ Finset.range (p * M), f n := by
  have hinj : Function.Injective (fun n : ℕ ↦ p * (n + 1) - 1) := by
    intro m n h
    change p * (m + 1) - 1 = p * (n + 1) - 1 at h
    have hmul : p * (m + 1) = p * (n + 1) :=
      (Nat.sub_add_cancel (show 1 ≤ p * (m + 1) from Nat.mul_pos hp (Nat.succ_pos m))).symm.trans
        ((congrArg (· + 1) h).trans
          (Nat.sub_add_cancel (show 1 ≤ p * (n + 1) from Nat.mul_pos hp (Nat.succ_pos n))))
    exact Nat.add_right_cancel (Nat.mul_left_cancel hp hmul)
  rw [← Finset.sum_image hinj.injOn]
  apply Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun i _ _ ↦ hf i)
  exact fun k hk ↦ (Finset.mem_image.mp hk).elim fun n h ↦
    h.2 ▸ Finset.mem_range.mpr
      ((Nat.sub_lt (Nat.mul_pos hp (Nat.succ_pos n)) (Nat.zero_lt_succ 0)).trans_le
        (Nat.mul_le_mul_left p (Finset.mem_range.mp h.1)))

namespace MPSTensor

variable {d D : ℕ}

/-- The grouped windows satisfy the upper and lower energy bounds in
Nachtergaele's condition C1-prime with constant one, because they form a
subfamily of the open-chain interaction terms. -/
theorem grouped_openParentHamiltonianES_C1 (A : MPSTensor d D) {p M : ℕ}
    (hp : 0 < p) (x : EuclideanSpace ℂ (Cfg d (p * M))) :
    0 ≤ ∑ n ∈ Finset.range M,
      (⟪openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M)
        (p * (n + 1)) x, x⟫_ℂ).re ∧
      (∑ n ∈ Finset.range M,
        (⟪openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M)
          (p * (n + 1)) x, x⟫_ℂ).re) ≤
        (⟪openParentHamiltonianES A (2 * p) (p * M) x, x⟫_ℂ).re := by
  refine ⟨Finset.sum_nonneg fun n _ ↦
    (openSuffixParentHamiltonianES_isPositive A (2 * p) (2 * p) (p * M)
      (p * (n + 1))).2 x, ?_⟩
  have hend (n : ℕ) : p * (n + 1) - 1 + 1 = p * (n + 1) :=
    Nat.sub_add_cancel (Nat.mul_pos hp (Nat.succ_pos n))
  have hsum := sum_grouped_le (M := M) hp
    (fun n ↦ (⟪openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M)
      (n + 1) x, x⟫_ℂ).re)
    (fun n ↦ (openSuffixParentHamiltonianES_isPositive A (2 * p) (2 * p)
      (p * M) (n + 1)).2 x)
  simp only [hend] at hsum
  exact hsum.trans (by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ 2 * p)] using
      (openParentHamiltonianES_C1_full_range_quadratic_form A (l := 2 * p - 1) x).2)

/-- Each grouped window has local gap one, including the initial zero window.
This is Nachtergaele's condition C2 for the grouped filtration at range \(2p\). -/
theorem grouped_openSuffixParentHamiltonianES_C2 (A : MPSTensor d D) {p M n : ℕ}
    (hp : 0 < p) (hn : n < M) (x : EuclideanSpace ℂ (Cfg d (p * M))) :
    ‖((LinearMap.id : EuclideanSpace ℂ (Cfg d (p * M)) →ₗ[ℂ]
        EuclideanSpace ℂ (Cfg d (p * M))) -
      groupedIntervalGroundProjectionES A p (p * M) n) x‖ ^ 2 ≤
      (⟪openSuffixParentHamiltonianES A (2 * p) (2 * p) (p * M)
        (p * (n + 1)) x, x⟫_ℂ).re := by
  have hn' : p * (n + 1) - 1 < p * M :=
    (Nat.sub_lt (Nat.mul_pos hp (Nat.succ_pos n)) Nat.zero_lt_one).trans_le
      (Nat.mul_le_mul_left p hn)
  simpa only [openIntervalGroundProjectionES, groupedIntervalGroundProjectionES,
    Nat.sub_add_cancel (by omega : 1 ≤ 2 * p),
    Nat.sub_add_cancel (Nat.mul_pos hp (Nat.succ_pos n))] using
    openSuffixParentHamiltonianES_C2_full_range_norm_sq A (l := 2 * p - 1) hn' x

end MPSTensor
