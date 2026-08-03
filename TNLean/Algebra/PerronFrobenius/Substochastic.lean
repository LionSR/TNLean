/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.LinearAlgebra.Matrix.Stochastic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Hadamard squares of primitive stochastic matrices

Let `P` be a finite nonnegative row-stochastic matrix and let `P ⊙ P` be its
Hadamard square. Powers of the Hadamard square satisfy the entrywise estimate
$$
  ((P \odot P)^k)_{ij} \leq ((P^k)_{ij})^2.
$$
If `P` is primitive and the index set has at least two elements, a positive
power of `P` has every entry strictly between zero and one. The corresponding
power of `P ⊙ P` therefore has every row sum strictly below one. Its
$L^\infty$ operator norm is less than one, and the full sequence of powers of
`P ⊙ P` converges to zero.

The passage to a positive power is necessary: a primitive stochastic matrix
may have a row containing a single nonzero entry, so the same row of `P ⊙ P`
need not have sum below one.

## Main results

* `Matrix.pow_apply_le_pow_apply_of_nonneg_of_le`: entrywise domination is
  preserved by matrix powers.
* `Matrix.pow_hadamard_self_apply_le_sq_pow_apply`: the entrywise power estimate.
* `Matrix.IsPrimitive.hadamard_self`: the Hadamard square of a primitive
  nonnegative matrix is primitive.
* `Matrix.exists_hadamard_self_pow_sum_row_lt_one`: some positive power has all
  row sums strictly below one.
* `Matrix.hadamard_self_pow_tendsto_zero`: all powers converge to zero.
* `Matrix.trace_pow_tendsto_zero_of_nonneg_le_hadamard_self`: an entrywise
  dominated nonnegative matrix has trace powers converging to zero.
-/

open scoped BigOperators Matrix Matrix.Norms.Operator

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- If two nonnegative real square matrices satisfy `S i j ≤ H i j` for every
entry, then the same entrywise inequality holds for every pair of corresponding
matrix powers. -/
theorem pow_apply_le_pow_apply_of_nonneg_of_le
    {S H : Matrix n n ℝ} (hS : ∀ i j, 0 ≤ S i j)
    (hSH : ∀ i j, S i j ≤ H i j) (k : ℕ) (i j : n) :
    (S ^ k) i j ≤ (H ^ k) i j := by
  have hH : ∀ i j, 0 ≤ H i j := fun i j ↦ (hS i j).trans (hSH i j)
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    apply Finset.sum_le_sum
    intro x _hx
    exact mul_le_mul (ih i x) (hSH x j) (hS x j)
      (Matrix.pow_apply_nonneg hH k i x)

/-- For a nonnegative real matrix `P`, every entry of `(P ⊙ P) ^ k` is at
most the square of the corresponding entry of `P ^ k`.

The induction step first bounds each product in the matrix multiplication and
then applies the inequality `∑ xᵢ² ≤ (∑ xᵢ)²` to the nonnegative
summands of the corresponding entry of `P ^ (k + 1)`. -/
theorem pow_hadamard_self_apply_le_sq_pow_apply
    {P : Matrix n n ℝ} (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) (i j : n) :
    ((P ⊙ P) ^ k) i j ≤ ((P ^ k) i j) ^ 2 := by
  induction k generalizing i j with
  | zero =>
    simp only [pow_zero]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [hij]
  | succ k ih =>
    rw [show (P ⊙ P) ^ (k + 1) = (P ⊙ P) ^ k * (P ⊙ P) by rw [pow_succ],
      show P ^ (k + 1) = P ^ k * P by rw [pow_succ]]
    simp only [Matrix.mul_apply, Matrix.hadamard_apply]
    calc
      ∑ x, ((P ⊙ P) ^ k) i x * (P x j * P x j) ≤
          ∑ x, ((P ^ k) i x * P x j) ^ 2 := by
        apply Finset.sum_le_sum
        intro x _hx
        calc
          ((P ⊙ P) ^ k) i x * (P x j * P x j) ≤
              ((P ^ k) i x) ^ 2 * (P x j * P x j) :=
            mul_le_mul_of_nonneg_right (ih i x) (mul_self_nonneg (P x j))
          _ = ((P ^ k) i x * P x j) ^ 2 := by ring
      _ ≤ (∑ x, (P ^ k) i x * P x j) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun x _ ↦
          mul_nonneg (Matrix.pow_apply_nonneg hP k i x) (hP x j)

/-- The powers of `P ⊙ P` and `P` have the same positive support when `P`
is nonnegative. -/
theorem pow_hadamard_self_apply_pos_iff
    {P : Matrix n n ℝ} (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) (i j : n) :
    0 < ((P ⊙ P) ^ k) i j ↔ 0 < (P ^ k) i j := by
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    rw [show (P ⊙ P) ^ (k + 1) = (P ⊙ P) ^ k * (P ⊙ P) by rw [pow_succ],
      show P ^ (k + 1) = P ^ k * P by rw [pow_succ]]
    simp only [Matrix.mul_apply, Matrix.hadamard_apply]
    constructor
    · intro h
      obtain ⟨x, hxmem, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg
          (fun a b ↦ mul_nonneg (hP a b) (hP a b)) k i x)
          (mul_self_nonneg (P x j)))).1 h
      have hxH : 0 < ((P ⊙ P) ^ k) i x :=
        pos_of_mul_pos_left hx (mul_self_nonneg (P x j))
      have hxP : 0 < P x j := lt_of_le_of_ne (hP x j) (mul_self_pos.mp
        (pos_of_mul_pos_right hx (Matrix.pow_apply_nonneg
          (fun a b ↦ mul_nonneg (hP a b) (hP a b)) k i x))).symm
      exact (Finset.sum_pos_iff_of_nonneg (fun x _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hP k i x) (hP x j))).2
        ⟨x, hxmem, mul_pos ((ih i x).1 hxH) hxP⟩
    · intro h
      obtain ⟨x, hxmem, hx⟩ := (Finset.sum_pos_iff_of_nonneg (fun x _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg hP k i x) (hP x j))).1 h
      have hxPk : 0 < (P ^ k) i x :=
        pos_of_mul_pos_left hx (hP x j)
      have hxP : 0 < P x j :=
        pos_of_mul_pos_right hx (Matrix.pow_apply_nonneg hP k i x)
      exact (Finset.sum_pos_iff_of_nonneg (fun x _ ↦
        mul_nonneg (Matrix.pow_apply_nonneg
          (fun a b ↦ mul_nonneg (hP a b) (hP a b)) k i x)
          (mul_self_nonneg (P x j)))).2
        ⟨x, hxmem, mul_pos ((ih i x).2 hxPk) (mul_pos hxP hxP)⟩

/-- The Hadamard square of a primitive nonnegative real matrix is primitive. -/
theorem IsPrimitive.hadamard_self {P : Matrix n n ℝ}
    (hP : P.IsPrimitive) : (P ⊙ P).IsPrimitive := by
  refine ⟨fun i j ↦ mul_nonneg (hP.nonneg i j) (hP.nonneg i j), ?_⟩
  obtain ⟨k, hk, hpos⟩ := hP.exists_pos_pow
  exact ⟨k, hk, fun i j ↦
    (pow_hadamard_self_apply_pos_iff hP.nonneg k i j).2 (hpos i j)⟩

/-- Let `P` be primitive and row-stochastic on a finite index set with at least
two elements. Some positive power of `P ⊙ P` has every row sum strictly below
one.

The nontriviality hypothesis is necessary: on a one-element index set, the
unique row-stochastic matrix is `[1]`, whose Hadamard square has every power
equal to `[1]`. -/
theorem exists_hadamard_self_pow_sum_row_lt_one [Nontrivial n]
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) :
    ∃ k > 0, ∀ i, ∑ j, ((P ⊙ P) ^ k) i j < 1 := by
  obtain ⟨k, hk, hpos⟩ := hPrim.exists_pos_pow
  refine ⟨k, hk, fun i ↦ ?_⟩
  have hPkStoch : P ^ k ∈ Matrix.rowStochastic ℝ n :=
    (Matrix.rowStochastic ℝ n).pow_mem hStoch k
  have hentry_lt_one (j : n) : (P ^ k) i j < 1 := by
    obtain ⟨x, hx⟩ := exists_ne j
    have herase : 0 < ∑ x ∈ (Finset.univ.erase j), (P ^ k) i x :=
      (Finset.sum_pos_iff_of_nonneg (fun x _ ↦
        Matrix.pow_apply_nonneg hPrim.nonneg k i x)).2
        ⟨x, Finset.mem_erase.mpr ⟨hx, Finset.mem_univ x⟩, hpos i x⟩
    calc
      (P ^ k) i j < (P ^ k) i j + ∑ x ∈ (Finset.univ.erase j), (P ^ k) i x :=
        lt_add_of_pos_right _ herase
      _ = ∑ x, (P ^ k) i x := Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)
      _ = 1 := Matrix.sum_row_of_mem_rowStochastic hPkStoch i
  calc
    ∑ j, ((P ⊙ P) ^ k) i j ≤ ∑ j, ((P ^ k) i j) ^ 2 :=
      Finset.sum_le_sum fun j _ ↦
        pow_hadamard_self_apply_le_sq_pow_apply hPrim.nonneg k i j
    _ < ∑ j, (P ^ k) i j := by
      apply Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      intro j _hj
      nlinarith [hpos i j, hentry_lt_one j]
    _ = 1 := Matrix.sum_row_of_mem_rowStochastic hPkStoch i

/-- Every power of the Hadamard square of a row-stochastic nonnegative matrix
has $L^\infty$ operator norm at most one. -/
theorem linfty_opNorm_hadamard_self_pow_le_one
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n) (k : ℕ) :
    ‖(P ⊙ P) ^ k‖ ≤ 1 := by
  rw [Matrix.linfty_opNorm_def]
  norm_cast
  rw [Finset.sup_le_iff]
  intro i _hi
  have hHnonneg (a b : n) : 0 ≤ ((P ⊙ P) ^ k) a b :=
    Matrix.pow_apply_nonneg
      (fun x y ↦ mul_nonneg
        (Matrix.nonneg_of_mem_rowStochastic hStoch)
        (Matrix.nonneg_of_mem_rowStochastic hStoch)) k a b
  simp_rw [Real.nnnorm_of_nonneg (hHnonneg i _)]
  have hPkStoch : P ^ k ∈ Matrix.rowStochastic ℝ n :=
    (Matrix.rowStochastic ℝ n).pow_mem hStoch k
  have hrow : ∑ j, ((P ⊙ P) ^ k) i j ≤ (1 : ℝ) := by
    calc
      ∑ j, ((P ⊙ P) ^ k) i j ≤ ∑ j, ((P ^ k) i j) ^ 2 :=
        Finset.sum_le_sum fun j _ ↦
          pow_hadamard_self_apply_le_sq_pow_apply
            (fun a b ↦ Matrix.nonneg_of_mem_rowStochastic hStoch) k i j
      _ ≤ (∑ j, (P ^ k) i j) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg fun j _ ↦
          Matrix.pow_apply_nonneg
            (fun a b ↦ Matrix.nonneg_of_mem_rowStochastic hStoch) k i j
      _ = 1 := by rw [Matrix.sum_row_of_mem_rowStochastic hPkStoch i]; norm_num
  rw [← NNReal.coe_le_coe]
  simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using hrow

/-- If `P` is primitive and row-stochastic on at least two indices, some
positive power of `P ⊙ P` has $L^\infty$ operator norm strictly below one. -/
theorem exists_hadamard_self_pow_linfty_opNorm_lt_one [Nontrivial n]
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) :
    ∃ k > 0, ‖(P ⊙ P) ^ k‖ < 1 := by
  obtain ⟨k, hk, hrow⟩ :=
    exists_hadamard_self_pow_sum_row_lt_one hStoch hPrim
  refine ⟨k, hk, ?_⟩
  rw [Matrix.linfty_opNorm_def]
  norm_cast
  rw [Finset.sup_lt_iff (by simp)]
  intro i _hi
  have hHnonneg (a b : n) : 0 ≤ ((P ⊙ P) ^ k) a b :=
    Matrix.pow_apply_nonneg
      (fun x y ↦ mul_nonneg
        (Matrix.nonneg_of_mem_rowStochastic hStoch)
        (Matrix.nonneg_of_mem_rowStochastic hStoch)) k a b
  simp_rw [Real.nnnorm_of_nonneg (hHnonneg i _)]
  rw [← NNReal.coe_lt_coe]
  simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using hrow i

/-- If `P` is primitive and row-stochastic on at least two indices, the powers
of its Hadamard square converge to zero in the $L^\infty$ operator norm. -/
theorem hadamard_self_pow_tendsto_zero [Nontrivial n]
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) :
    Filter.Tendsto (fun k ↦ (P ⊙ P) ^ k) Filter.atTop (nhds 0) := by
  obtain ⟨m, hm, hnorm⟩ :=
    exists_hadamard_self_pow_linfty_opNorm_lt_one hStoch hPrim
  apply squeeze_zero_norm (a := fun k ↦ ‖(P ⊙ P) ^ m‖ ^ (k / m))
  · intro k
    have hkdecomp : k = m * (k / m) + k % m := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod k m).symm
    have hpowdecomp : (P ⊙ P) ^ k =
        ((P ⊙ P) ^ m) ^ (k / m) * (P ⊙ P) ^ (k % m) := by
      calc
        (P ⊙ P) ^ k = (P ⊙ P) ^ (m * (k / m) + k % m) :=
          congrArg ((P ⊙ P) ^ ·) hkdecomp
        _ = (P ⊙ P) ^ (m * (k / m)) * (P ⊙ P) ^ (k % m) :=
          pow_add _ _ _
        _ = ((P ⊙ P) ^ m) ^ (k / m) * (P ⊙ P) ^ (k % m) := by
          rw [pow_mul]
    calc
      ‖(P ⊙ P) ^ k‖ =
          ‖((P ⊙ P) ^ m) ^ (k / m) * (P ⊙ P) ^ (k % m)‖ :=
        congrArg norm hpowdecomp
      _ ≤ ‖((P ⊙ P) ^ m) ^ (k / m)‖ * ‖(P ⊙ P) ^ (k % m)‖ :=
        norm_mul_le _ _
      _ ≤ ‖(P ⊙ P) ^ m‖ ^ (k / m) * 1 := by
        exact mul_le_mul (norm_pow_le _ _) (linfty_opNorm_hadamard_self_pow_le_one
          hStoch (k % m)) (norm_nonneg _) (pow_nonneg (norm_nonneg _) _)
      _ = ‖(P ⊙ P) ^ m‖ ^ (k / m) := mul_one _
  · exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hnorm).comp
      (Nat.tendsto_div_const_atTop (Nat.ne_of_gt hm))

/-- Under the hypotheses of `Matrix.hadamard_self_pow_tendsto_zero`, each
entry of `(P ⊙ P) ^ k` converges to zero. -/
theorem hadamard_self_pow_apply_tendsto_zero [Nontrivial n]
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) (i j : n) :
    Filter.Tendsto (fun k ↦ ((P ⊙ P) ^ k) i j) Filter.atTop (nhds 0) := by
  simpa using ((hadamard_self_pow_tendsto_zero hStoch hPrim).apply_nhds i).apply_nhds j

/-- Under the hypotheses of `Matrix.hadamard_self_pow_tendsto_zero`, the
traces of `(P ⊙ P) ^ k` converge to zero. -/
theorem trace_hadamard_self_pow_tendsto_zero [Nontrivial n]
    {P : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) :
    Filter.Tendsto (fun k ↦ Matrix.trace ((P ⊙ P) ^ k)) Filter.atTop (nhds 0) := by
  simp only [Matrix.trace]
  simpa using tendsto_finsetSum Finset.univ fun i _ ↦
    hadamard_self_pow_apply_tendsto_zero hStoch hPrim i i

/-- Let `P` be a primitive row-stochastic real matrix on at least two indices.
If a nonnegative matrix `S` is entrywise bounded above by `P ⊙ P`, then the
traces of the powers of `S` converge to zero. -/
theorem trace_pow_tendsto_zero_of_nonneg_le_hadamard_self [Nontrivial n]
    {P S : Matrix n n ℝ} (hStoch : P ∈ Matrix.rowStochastic ℝ n)
    (hPrim : P.IsPrimitive) (hS : ∀ i j, 0 ≤ S i j)
    (hSP : ∀ i j, S i j ≤ (P ⊙ P) i j) :
    Filter.Tendsto (fun k ↦ Matrix.trace (S ^ k)) Filter.atTop (nhds 0) := by
  apply squeeze_zero (g := fun k ↦ Matrix.trace ((P ⊙ P) ^ k))
  · intro k
    simp only [Matrix.trace]
    exact Finset.sum_nonneg fun i _hi ↦ Matrix.pow_apply_nonneg hS k i i
  · intro k
    simp only [Matrix.trace]
    apply Finset.sum_le_sum
    intro i _hi
    exact pow_apply_le_pow_apply_of_nonneg_of_le hS hSP k i i
  · exact trace_hadamard_self_pow_tendsto_zero hStoch hPrim

end Matrix
