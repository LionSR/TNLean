/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Jordan block: definition, nilpotent shift, and binomial expansion

Let $D \ge 1$ be a positive integer.  Define the $D \times D$ **nilpotent upper
shift** $N$ by $N_{i,j}=1$ when $j=i+1$, $0$ otherwise, and the **Jordan
block** $J_D(\lambda) = \lambda I + N$.  Source: Wolf (2012), Chapter 8,
lines 1211--1212.

Because $\lambda I$ and $N$ commute, the binomial theorem gives the power
expansion
$$
J_D(\lambda)^n =
\sum_{k=0}^{\min\{n,\,D-1\}}
  \binom{n}{k}\,\lambda^{\,n-k}\,N^k,
$$
where terms with $k \ge D$ vanish because $N^D=0$.  Each $N^k$ is the $k$-th
superdiagonal matrix: $(N^k)_{i,j}=1$ iff $j=i+k$.

These are purely algebraic calculations; they do not involve any norm bounds.
The two-sided operator-norm estimate of Wolf Eq. (8.104) requires additional
$\ell^2$ operator-norm infrastructure and is not yet formalized.

## Main declarations

* `nilpotentShift` -- the shift matrix $N$.
* `nilpotentShift_pow_apply` -- superdiagonal power formula for $N^k$.
* `nilpotentShift_pow_D_eq_zero` -- $N^D=0$.
* `jordanBlock` -- the Jordan block $J_D(\lambda) = \lambda I + N$.
* `jordanBlock_pow` -- truncated binomial expansion of $J_D(\lambda)^n$.
-/

namespace Matrix

open scoped BigOperators

section NilpotentShift

variable (D : ℕ)

/-- The $D\times D$ nilpotent upper shift $N$:
$N_{i,j}=1$ if $j=i+1$, $0$ otherwise. -/
def nilpotentShift : Matrix (Fin D) (Fin D) ℂ :=
  fun i j => if (j : ℕ) = (i : ℕ) + 1 then (1 : ℂ) else 0

lemma nilpotentShift_apply {i j : Fin D} : nilpotentShift D i j =
    if (j : ℕ) = (i : ℕ) + 1 then (1 : ℂ) else 0 := rfl

lemma nilpotentShift_eq_one {i j : Fin D} (h : (j : ℕ) = (i : ℕ) + 1) :
    nilpotentShift D i j = 1 := by
  simp [nilpotentShift_apply, h]

lemma nilpotentShift_eq_zero {i j : Fin D} (h : (j : ℕ) ≠ (i : ℕ) + 1) :
    nilpotentShift D i j = 0 := by
  simp [nilpotentShift_apply, h]

end NilpotentShift

section NilpotentShiftPow

variable (D : ℕ)

/-- Power of the nilpotent shift: $(N^k)_{i,j}=1$ when $j=i+k$, $0$ else.
Source: Wolf (2012), Chapter 8, lines 1211--1214. -/
lemma nilpotentShift_pow_apply {k : ℕ} {i j : Fin D} :
    (nilpotentShift D ^ k) i j =
    if (j : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0 := by
  induction k generalizing i j with
  | zero => simp [Matrix.one_apply, Fin.ext_iff, eq_comm]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih, nilpotentShift_apply D]
    by_cases h_target : (j : ℕ) = (i : ℕ) + (k + 1)
    · have hpos : (i : ℕ) + k < D := by
        have j_lt : (j : ℕ) < D := j.is_lt
        omega
      let ℓ : Fin D := ⟨(i : ℕ) + k, hpos⟩
      have hℓ_val : (ℓ : ℕ) = (i : ℕ) + k := rfl
      have h_ℓ_plus_one : (j : ℕ) = (ℓ : ℕ) + 1 := by
        rw [hℓ_val]; omega
      have hsum : (∑ x : Fin D, ((if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
          (if (j : ℕ) = (x : ℕ) + 1 then (1 : ℂ) else 0))) =
          ((if (ℓ : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
           (if (j : ℕ) = (ℓ : ℕ) + 1 then (1 : ℂ) else 0)) := by
        apply Finset.sum_eq_single_of_mem ℓ (Finset.mem_univ _)
        intro x hx hxne
        by_cases hxcond : (x : ℕ) = (i : ℕ) + k
        · have : x = ℓ := Fin.ext (by omega)
          exact (hxne this).elim
        · have : (if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) = 0 := by
            rw [if_neg hxcond]
          rw [this]
          simp
      have h_val : ((if (ℓ : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
          (if (j : ℕ) = (ℓ : ℕ) + 1 then (1 : ℂ) else 0)) = 1 := by
        simp [hℓ_val, h_ℓ_plus_one]
      calc
        (∑ x : Fin D, ((if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
          (if (j : ℕ) = (x : ℕ) + 1 then (1 : ℂ) else 0))) = 1 := by
          rw [hsum, h_val]
        _ = (if (j : ℕ) = (i : ℕ) + (k + 1) then (1 : ℂ) else 0) := by
          rw [if_pos h_target]
    · have hzero : (∑ x : Fin D, ((if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
          (if (j : ℕ) = (x : ℕ) + 1 then (1 : ℂ) else 0))) = 0 := by
        apply Finset.sum_eq_zero
        intro x _
        by_cases hxcond : (x : ℕ) = (i : ℕ) + k
        · have : (if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) = 1 := by
            rw [if_pos hxcond]
          rw [this]
          have : (if (j : ℕ) = (x : ℕ) + 1 then (1 : ℂ) else 0) = 0 := by
            by_cases hjcond : (j : ℕ) = (x : ℕ) + 1
            · exfalso; apply h_target; omega
            · rw [if_neg hjcond]
          rw [this]
          simp
        · have : (if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) = 0 := by
            rw [if_neg hxcond]
          rw [this]
          simp
      calc
        (∑ x : Fin D, ((if (x : ℕ) = (i : ℕ) + k then (1 : ℂ) else 0) *
          (if (j : ℕ) = (x : ℕ) + 1 then (1 : ℂ) else 0))) = (0 : ℂ) := hzero
        _ = (if (j : ℕ) = (i : ℕ) + (k + 1) then (1 : ℂ) else 0) := by
          rw [if_neg h_target]

/-- $N^D = 0$; the nilpotent index is at most $D$.  Requires $D \ge 1$.
Source: Wolf (2012), Chapter 8, line 1211. -/
lemma nilpotentShift_pow_D_eq_zero [NeZero D] :
    nilpotentShift D ^ D = (0 : Matrix (Fin D) (Fin D) ℂ) := by
  ext i j
  rw [nilpotentShift_pow_apply D]
  split
  · rename_i h
    have hi : (i : ℕ) < D := i.is_lt
    have hj : (j : ℕ) < D := j.is_lt
    omega
  · rfl

/-- $N^k = 0$ whenever $k \ge D$. -/
lemma nilpotentShift_pow_eq_zero_of_ge_D [NeZero D] {k : ℕ} (hk : D ≤ k) :
    nilpotentShift D ^ k = (0 : Matrix (Fin D) (Fin D) ℂ) := by
  have : k = D + (k - D) := (Nat.add_sub_cancel' hk).symm
  rw [this, pow_add, nilpotentShift_pow_D_eq_zero D, zero_mul]

/-- Powers $N^k$ vanish for $k > D-1$. -/
private lemma nilpotentShift_pow_eq_zero_of_gt_sub_one [NeZero D] {k : ℕ}
    (hk : D - 1 < k) :
    nilpotentShift D ^ k = (0 : Matrix (Fin D) (Fin D) ℂ) := by
  have hkD : D ≤ k := by omega
  exact nilpotentShift_pow_eq_zero_of_ge_D D hkD

end NilpotentShiftPow

section JordanBlock

variable (D : ℕ)

/-- The Jordan block $J_D(a) = a I + N$, where $N$ is the nilpotent upper
shift.  Source: Wolf (2012), Chapter 8, lines 1211--1212. -/
def jordanBlock (a : ℂ) : Matrix (Fin D) (Fin D) ℂ :=
  a • (1 : Matrix (Fin D) (Fin D) ℂ) + nilpotentShift D

/-- $a I$ and $N$ commute, so the binomial theorem applies. -/
lemma jordanBlock_commute (a : ℂ) :
    Commute (a • (1 : Matrix (Fin D) (Fin D) ℂ)) (nilpotentShift D) := by
  have : Commute (nilpotentShift D) (a • (1 : Matrix (Fin D) (Fin D) ℂ)) :=
    (Commute.one_right (nilpotentShift D)).smul_right a
  exact this.symm

/-- The scalar-matrix identity: $a \cdot 1 = \operatorname{scalar}(a)$ as a
diagonal matrix. -/
lemma smul_one_eq_scalar (a : ℂ) :
    a • (1 : Matrix (Fin D) (Fin D) ℂ) = Matrix.scalar (Fin D) a := by
  ext i j; simp [Matrix.scalar_apply, Matrix.one_apply, Matrix.diagonal_apply]

private lemma smul_one_pow (a : ℂ) (m : ℕ) :
    (a • (1 : Matrix (Fin D) (Fin D) ℂ)) ^ m =
    (a ^ m) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  calc
    (a • (1 : Matrix (Fin D) (Fin D) ℂ)) ^ m =
        (Matrix.scalar (Fin D) a) ^ m := by rw [smul_one_eq_scalar]
    _ = Matrix.scalar (Fin D) (a ^ m) := by
      simpa using (RingHom.map_pow (Matrix.scalar (Fin D)) a m).symm
    _ = (a ^ m) • (1 : Matrix (Fin D) (Fin D) ℂ) := by rw [smul_one_eq_scalar]

private lemma natCast_matrix_eq (n : ℕ) :
    ((n : ℕ) : Matrix (Fin D) (Fin D) ℂ) =
    (n : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ) := by
  ext i j
  simp [Matrix.natCast_apply, Matrix.one_apply]

/-- One term of the commuting binomial expansion:
$(a\cdot 1)^m \, N^{\,n-m} \, \binom{n}{m}
= \bigl(\binom{n}{m} a^m\bigr) \bullet N^{\,n-m}$. -/
private lemma jordanBlock_term (a : ℂ) (n m : ℕ) :
    (a • (1 : Matrix (Fin D) (Fin D) ℂ)) ^ m *
    (nilpotentShift D) ^ (n - m) *
    (Nat.choose n m : Matrix (Fin D) (Fin D) ℂ) =
    ((Nat.choose n m : ℂ) * a ^ m) • (nilpotentShift D) ^ (n - m) := by
  calc
    (a • (1 : Matrix (Fin D) (Fin D) ℂ)) ^ m * (nilpotentShift D) ^ (n - m) *
        (Nat.choose n m : Matrix (Fin D) (Fin D) ℂ)
      = ((a ^ m) • (1 : Matrix (Fin D) (Fin D) ℂ)) *
        (nilpotentShift D) ^ (n - m) *
        (Nat.choose n m : Matrix (Fin D) (Fin D) ℂ) := by
      rw [smul_one_pow]
    _ = ((a ^ m) • (nilpotentShift D) ^ (n - m)) *
        (Nat.choose n m : Matrix (Fin D) (Fin D) ℂ) := by
      rw [Matrix.smul_mul, Matrix.one_mul]
    _ = ((a ^ m) • (nilpotentShift D) ^ (n - m)) *
        ((Nat.choose n m : ℂ) • (1 : Matrix (Fin D) (Fin D) ℂ)) := by
      rw [natCast_matrix_eq]
    _ = ((Nat.choose n m : ℂ) * a ^ m) • (nilpotentShift D) ^ (n - m) := by
      rw [Matrix.mul_smul, Matrix.mul_one, smul_smul, mul_comm]

/-- Binomial expansion of $J_D(a)^n$, truncated at $\min\{n,D-1\}$:
$$
J_D(a)^n = \sum_{k=0}^{\min\{n,\,D-1\}}
\binom{n}{k}\,a^{\,n-k}\,N^k.
$$
Terms with $k \ge D$ vanish because $N^D = 0$.
Source: Wolf (2012), Chapter 8, lines 1211--1212. -/
lemma jordanBlock_pow (a : ℂ) (n : ℕ) [NeZero D] :
    jordanBlock D a ^ n = ∑ k ∈ Finset.range (min n (D - 1) + 1),
      ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k) := by
  have h_comm := jordanBlock_commute D a
  rw [jordanBlock, h_comm.add_pow n]
  -- RHS = sum_{m=0}^n (a * I)^m * N^(n-m) * C(n,m)
  rw [Finset.sum_congr rfl (fun m hm => by rw [jordanBlock_term D a n m])]
  -- Now: sum_{m=0}^n (C(n,m) * a^m) * N^(n-m)
  -- Reindex via m -> n-m (a bijection of range (n+1))
  have h_reindex : (∑ m ∈ Finset.range (n + 1),
      ((n.choose m : ℂ) * a ^ m) • (nilpotentShift D ^ (n - m))) =
      (∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)) := by
    have hsub_one : (n + 1 : ℕ) - 1 = n := by omega
    have h_reflect := Finset.sum_range_reflect
      (fun j : ℕ => ((n.choose j : ℂ) * a ^ j) • (nilpotentShift D ^ (n - j)))
      (n + 1)
    simp only [hsub_one] at h_reflect
    -- h_reflect: sum (C(n,n-j) * a^(n-j)) * N^j = sum (C(n,j) * a^j) * N^(n-j)
    have h_reflect' : (∑ j ∈ Finset.range (n + 1),
        ((n.choose (n - j) : ℂ) * a ^ (n - j)) • (nilpotentShift D ^ j)) =
        (∑ j ∈ Finset.range (n + 1),
        ((n.choose j : ℂ) * a ^ j) • (nilpotentShift D ^ (n - j))) := by
      calc
        (∑ j ∈ Finset.range (n + 1),
            ((n.choose (n - j) : ℂ) * a ^ (n - j)) • (nilpotentShift D ^ j)) =
            (∑ j ∈ Finset.range (n + 1),
            ((n.choose (n - j) : ℂ) * a ^ (n - j)) •
            (nilpotentShift D ^ (n - (n - j)))) := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          have hj' : j ≤ n := by
            rw [Finset.mem_range] at hj; omega
          rw [Nat.sub_sub_self hj']
        _ = (∑ j ∈ Finset.range (n + 1),
            ((n.choose j : ℂ) * a ^ j) • (nilpotentShift D ^ (n - j))) := by
          simpa using h_reflect
    calc
      (∑ m ∈ Finset.range (n + 1),
          ((n.choose m : ℂ) * a ^ m) • (nilpotentShift D ^ (n - m))) =
          (∑ j ∈ Finset.range (n + 1),
          ((n.choose (n - j) : ℂ) * a ^ (n - j)) • (nilpotentShift D ^ j)) := by
        rw [← h_reflect']
      _ = (∑ k ∈ Finset.range (n + 1),
          ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)) := by
        refine Finset.sum_congr rfl (fun j hj => ?_)
        have hj' : j ≤ n := by
          rw [Finset.mem_range] at hj; omega
        rw [Nat.choose_symm hj']
  rw [h_reindex]
  -- Now: sum_{k=0}^n (C(n,k) * a^(n-k)) * N^k
  -- Truncate to k <= min(n, D-1) using nilpotence N^D = 0
  have h_trunc : (∑ k ∈ Finset.range (n + 1),
      ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)) =
      (∑ k ∈ Finset.range (min n (D - 1) + 1),
      ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)) := by
    have h_subset : Finset.range (min n (D - 1) + 1) ⊆ Finset.range (n + 1) :=
      Finset.range_subset_range.mpr (by omega)
    have h_zero : ∀ (k : ℕ), k ∈ Finset.range (n + 1) →
        k ∉ Finset.range (min n (D - 1) + 1) →
        ((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k) = 0 := by
      intro k hk hk'
      rw [Finset.mem_range] at hk hk'
      have hkD : D ≤ k := by
        have : min n (D - 1) + 1 ≤ k := by omega
        omega
      rw [nilpotentShift_pow_eq_zero_of_ge_D D hkD, smul_zero]
    rw [← Finset.sum_subset h_subset h_zero]
  rw [h_trunc]

end JordanBlock

end Matrix
