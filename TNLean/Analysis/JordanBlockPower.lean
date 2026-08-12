/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Lean.Elab.Tactic.Omega

/-!
# Jordan block: powers, nilpotent shift, and the two-sided norm estimate

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

Measuring $J_D(\lambda)^n$ in the largest singular value $\|\cdot\|_\infty$,
that is in the $\ell^2$ operator norm, the expansion yields Wolf's two-sided
estimate: for every $k_0 \le \min\{n,\,D-1\}$,
$$
|\lambda|^{\,n-k_0}\binom{n}{k_0}
  \le \bigl\|J_D(\lambda)^n\bigr\|_\infty
  \le \sum_{k=0}^{\min\{n,\,D-1\}} |\lambda|^{\,n-k}\binom{n}{k}.
$$
The left inequality reads off the $(0,k_0)$ entry of the expansion and uses
that the largest singular value dominates every entry.  The right inequality
is the triangle inequality together with $\|N\|_\infty \le 1$.
Source: Wolf (2012), Chapter 8, Eq. (8.104), lines 1197--1215.

## Main declarations

* `nilpotentShift` -- the shift matrix $N$.
* `nilpotentShift_pow_apply` -- superdiagonal power formula for $N^k$.
* `nilpotentShift_pow_D_eq_zero` -- $N^D=0$.
* `jordanBlock` -- the Jordan block $J_D(\lambda) = \lambda I + N$.
* `jordanBlock_pow` -- truncated binomial expansion of $J_D(\lambda)^n$.
* `norm_apply_le_l2_opNorm` -- the largest singular value dominates every entry.
* `l2_opNorm_nilpotentShift_le_one` -- $\|N\|_\infty \le 1$.
* `le_l2_opNorm_jordanBlock_pow` -- left inequality of Wolf Eq. (8.104).
* `l2_opNorm_jordanBlock_pow_le` -- right inequality of Wolf Eq. (8.104).
* `l2_opNorm_jordanBlock_pow_bounds` -- Wolf Eq. (8.104).
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
      rw [Matrix.mul_smul, Matrix.mul_one, smul_smul]

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

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- The largest singular value dominates every entry: $|A_{i,j}| \le \|A\|_\infty$.
Evaluating the associated Euclidean operator on the $j$-th standard basis vector
returns the $j$-th column of $A$, whose $i$-th coordinate is $A_{i,j}$.
Source: Wolf (2012), Chapter 8, lines 1213--1214. -/
lemma norm_apply_le_l2_opNorm {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (i j : n) : ‖A i j‖ ≤ ‖A‖ := by
  set x : EuclideanSpace ℂ n := PiLp.single 2 j (1 : ℂ) with hxdef
  have hx : ‖x‖ = 1 := by simp [hxdef]
  have hcol : ‖toEuclideanCLM (n := n) (𝕜 := ℂ) A x‖ ≤ ‖A‖ := by
    have h := (toEuclideanCLM (n := n) (𝕜 := ℂ) A).le_opNorm x
    rwa [hx, mul_one, l2_opNorm_toEuclideanCLM] at h
  refine le_trans (le_of_eq ?_) ((PiLp.norm_apply_le _ i).trans hcol)
  simp [hxdef, PiLp.ofLp_single]

/-- The Gram matrix of the nilpotent shift is the diagonal projection that kills
the first coordinate: $N^{\dagger}N = \operatorname{diag}(0,1,\dots,1)$. -/
lemma conjTranspose_nilpotentShift_mul_self (D : ℕ) :
    (nilpotentShift D)ᴴ * nilpotentShift D =
      diagonal (fun i : Fin D => if (i : ℕ) = 0 then (0 : ℂ) else 1) := by
  ext i j
  rw [Matrix.mul_apply, Matrix.diagonal_apply]
  have hterm : ∀ k : Fin D, (nilpotentShift D)ᴴ i k * nilpotentShift D k j =
      if (i : ℕ) = (k : ℕ) + 1 ∧ (j : ℕ) = (k : ℕ) + 1 then (1 : ℂ) else 0 := by
    intro k
    simp only [conjTranspose_apply, nilpotentShift_apply]
    split_ifs with h₁ h₂ h₃ <;> simp_all
  simp only [hterm]
  by_cases hij : i = j
  · subst hij
    by_cases hi : (i : ℕ) = 0
    · rw [if_pos rfl, if_pos hi]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [if_neg]
      omega
    · rw [if_pos rfl, if_neg hi]
      have hlt : (i : ℕ) - 1 < D := lt_of_le_of_lt (Nat.sub_le _ _) i.is_lt
      have hval : ((⟨(i : ℕ) - 1, hlt⟩ : Fin D) : ℕ) = (i : ℕ) - 1 := rfl
      rw [Finset.sum_eq_single (⟨(i : ℕ) - 1, hlt⟩ : Fin D)]
      · have hi' : (i : ℕ) = ((⟨(i : ℕ) - 1, hlt⟩ : Fin D) : ℕ) + 1 := by omega
        rw [if_pos ⟨hi', hi'⟩]
      · intro k _ hk
        rw [if_neg]
        rintro ⟨h₁, h₂⟩
        exact hk (Fin.ext (by omega))
      · intro hmem
        exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg hij]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    rintro ⟨h₁, h₂⟩
    exact hij (Fin.ext (by omega))

/-- Wolf's $\|N\|_\infty = 1$, stated as an inequality because the shift on a
one-dimensional space is zero.  Source: Wolf (2012), Chapter 8, line 1215. -/
lemma l2_opNorm_nilpotentShift_le_one (D : ℕ) : ‖nilpotentShift D‖ ≤ 1 := by
  have hsq : ‖nilpotentShift D‖ * ‖nilpotentShift D‖ ≤ 1 := by
    rw [← l2_opNorm_conjTranspose_mul_self, conjTranspose_nilpotentShift_mul_self,
      l2_opNorm_diagonal]
    refine (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => ?_
    by_cases hi : (i : ℕ) = 0 <;> simp [hi]
  nlinarith [norm_nonneg (nilpotentShift D)]

/-- Every power of the nilpotent shift is a contraction. -/
lemma l2_opNorm_nilpotentShift_pow_le_one (D : ℕ) (k : ℕ) :
    ‖nilpotentShift D ^ k‖ ≤ 1 := by
  induction k with
  | zero =>
    rw [pow_zero, ← Matrix.diagonal_one, l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by simp
  | succ k ih =>
    refine (pow_succ (nilpotentShift D) k ▸ l2_opNorm_mul _ _).trans ?_
    nlinarith [norm_nonneg (nilpotentShift D ^ k), norm_nonneg (nilpotentShift D),
      l2_opNorm_nilpotentShift_le_one D]

/-- Right inequality of Wolf Eq. (8.104):
$\|J_D(\lambda)^n\|_\infty \le \sum_{k=0}^{\min\{n,D-1\}}|\lambda|^{n-k}\binom{n}{k}$.
Source: Wolf (2012), Chapter 8, Eq. (8.104), lines 1197--1215. -/
theorem l2_opNorm_jordanBlock_pow_le (D : ℕ) [NeZero D] (a : ℂ) (n : ℕ) :
    ‖jordanBlock D a ^ n‖ ≤
      ∑ k ∈ Finset.range (min n (D - 1) + 1), ‖a‖ ^ (n - k) * (n.choose k : ℝ) := by
  rw [jordanBlock_pow]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have hnorm : ‖((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)‖ =
      ‖a‖ ^ (n - k) * (n.choose k : ℝ) * ‖nilpotentShift D ^ k‖ := by
    rw [norm_smul, norm_mul, norm_pow, Complex.norm_natCast]
    ring
  calc ‖((n.choose k : ℂ) * a ^ (n - k)) • (nilpotentShift D ^ k)‖
      = ‖a‖ ^ (n - k) * (n.choose k : ℝ) * ‖nilpotentShift D ^ k‖ := hnorm
    _ ≤ ‖a‖ ^ (n - k) * (n.choose k : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (l2_opNorm_nilpotentShift_pow_le_one D k) (by positivity)
    _ = ‖a‖ ^ (n - k) * (n.choose k : ℝ) := mul_one _

/-- Left inequality of Wolf Eq. (8.104):
$|\lambda|^{n-k_0}\binom{n}{k_0} \le \|J_D(\lambda)^n\|_\infty$ for every
$k_0 \le \min\{n,D-1\}$.  The bound reads off the entry of $J_D(\lambda)^n$ in
row $0$ and column $k_0$, which is $\lambda^{n-k_0}\binom{n}{k_0}$.
Source: Wolf (2012), Chapter 8, Eq. (8.104), lines 1197--1215. -/
theorem le_l2_opNorm_jordanBlock_pow (D : ℕ) [NeZero D] (a : ℂ) (n k₀ : ℕ)
    (hk₀ : k₀ ≤ min n (D - 1)) :
    ‖a‖ ^ (n - k₀) * (n.choose k₀ : ℝ) ≤ ‖jordanBlock D a ^ n‖ := by
  have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
  have hk₀D : k₀ < D := lt_of_le_of_lt (le_trans hk₀ (min_le_right _ _)) (by omega)
  have hmem : k₀ ∈ Finset.range (min n (D - 1) + 1) := Finset.mem_range.mpr (by omega)
  have hentry : (jordanBlock D a ^ n) ⟨0, hD⟩ ⟨k₀, hk₀D⟩ =
      (n.choose k₀ : ℂ) * a ^ (n - k₀) := by
    rw [jordanBlock_pow]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, nilpotentShift_pow_apply]
    rw [Finset.sum_eq_single k₀]
    · simp
    · intro k _ hk
      rw [if_neg (by simpa using fun h => hk (by omega)), mul_zero]
    · intro hcon
      exact absurd hmem hcon
  calc ‖a‖ ^ (n - k₀) * (n.choose k₀ : ℝ)
      = ‖(jordanBlock D a ^ n) ⟨0, hD⟩ ⟨k₀, hk₀D⟩‖ := by
        rw [hentry, norm_mul, norm_pow, Complex.norm_natCast]
        ring
    _ ≤ ‖jordanBlock D a ^ n‖ := norm_apply_le_l2_opNorm _ _ _

/-- Wolf Eq. (8.104): the two-sided estimate on the largest singular value of a
Jordan-block power.  For every $k_0 \le \min\{n, D-1\}$,
$$
|\lambda|^{\,n-k_0}\binom{n}{k_0}
  \le \bigl\|J_D(\lambda)^n\bigr\|_\infty
  \le \sum_{k=0}^{\min\{n,\,D-1\}} |\lambda|^{\,n-k}\binom{n}{k}.
$$
Source: Wolf (2012), Chapter 8, Eq. (8.104), lines 1197--1215. -/
theorem l2_opNorm_jordanBlock_pow_bounds (D : ℕ) [NeZero D] (a : ℂ) (n k₀ : ℕ)
    (hk₀ : k₀ ≤ min n (D - 1)) :
    ‖a‖ ^ (n - k₀) * (n.choose k₀ : ℝ) ≤ ‖jordanBlock D a ^ n‖ ∧
      ‖jordanBlock D a ^ n‖ ≤
        ∑ k ∈ Finset.range (min n (D - 1) + 1), ‖a‖ ^ (n - k) * (n.choose k : ℝ) :=
  ⟨le_l2_opNorm_jordanBlock_pow D a n k₀ hk₀, l2_opNorm_jordanBlock_pow_le D a n⟩

end OperatorNorm

end Matrix
