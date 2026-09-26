/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Preparation.VarianceOfAverages
import TNLean.MPS.Preparation.WindowOperatorSupport

/-!
# Averages over separated windows in a state prepared by a shallow circuit

Let `ψ` be a unit vector prepared from a product vector by a local circuit of depth `T`, and
let `X` be a Hermitian operator on `w` consecutive sites. Place `X` on the windows starting at
the sites `0, Δ, 2Δ, …, (n-1)Δ` of the ring, with `w + 2T ≤ Δ` and `nΔ ≤ N`. Any two of these
windows are at ring distance larger than `2T`, so their connected correlations in `ψ` vanish,
and a weighted sum `Z = ∑ c_k X^{(k)}` with `|c_k| ≤ γ` has variance at most
`γ² · 3n · 2‖X‖²` in `ψ`.

This is the variance bound "by factorization its variance there is at most `4/n`" of the
chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696,
Theorem 1), which rests on the statement of the Supplemental Material, proof of Theorem 1,
that "every connected correlation for operators at a distance larger than `2T` vanishes".

## Main results

* `MPSPreparation.isSeparatedBy_window`: two windows of the ring with gaps larger than `s`
  on both sides are at ring distance larger than `s`.
* `MPSPreparation.inner_toLp_toEuclideanLin`: the inner-product form of `expect`.
* `MPSPreparation.norm_sub_inner_smul_sq_le_of_isPreparedInDepth`: the variance bound.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSPreparation

open MPSTensor

variable {d N : ℕ}

/-- The sites `a, …, a + w - 1` of the ring, as a set of sites. -/
def window (N a w : ℕ) : Set (Fin N) := {k : Fin N | a ≤ k.val ∧ k.val < a + w}

theorem chainWindowOperator_mem_supportedOperators_window {L a : ℕ} (ha : a < N)
    (haL : a + L ≤ N) (X : Matrix (Fin L → Fin d) (Fin L → Fin d) ℂ) :
    chainWindowOperator N a X ∈ supportedOperators d (window N a L) :=
  MPSTensor.chainWindowOperator_mem_supportedOperators ha haL X

section Ring

open Fin.CommRing

variable [NeZero N]

/-- **Separated windows.** The windows `a, …, a + w - 1` and `b, …, b + w' - 1` of the ring
of `N` sites are at ring distance larger than `s` when there are more than `s` sites between
them on both sides: `a + w + s ≤ b` and `b + w' + s ≤ a + N`.

This is the separation of the translated observables in the chapter's proof of
`thm:ldp_depth_lower_bound` ("the `2n` enlarged intervals are pairwise disjoint, also around
the ring"; arXiv:2307.01696, Supplemental Material, proof of Theorem 1, "operators at a
distance larger than `2T`"). -/
theorem isSeparatedBy_window {a w b w' s : ℕ} (hab : a + w + s ≤ b)
    (hba : b + w' + s ≤ a + N) :
    IsSeparatedBy (window N a w) (window N b w') s := by
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
  obtain ⟨hxa, hxw⟩ := hx
  obtain ⟨hyb, hyw⟩ := hy
  obtain ⟨hm1, hm2⟩ := abs_le.mp hm
  have hpos : 0 ≤ (y.val : ℤ) - x.val - m := by push_cast at hm1 hm2 ⊢; omega
  have hlt : (y.val : ℤ) - x.val - m < N := by push_cast at hm1 hm2 ⊢; omega
  have := Int.eq_zero_of_dvd_of_nonneg_of_lt hpos hlt hdvd
  push_cast at hm1 hm2 this
  omega

end Ring

/-- The expectation `expect ψ A` is the inner product `⟪ψ, A ψ⟫` in `EuclideanSpace`. -/
theorem inner_toLp_toEuclideanLin (ψ : Cfg d N → ℂ) (A : Matrix (Cfg d N) (Cfg d N) ℂ) :
    ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N)),
        Matrix.toEuclideanLin A (WithLp.toLp 2 ψ)⟫_ℂ = expect ψ A := by
  simp only [Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply, expect, dotProduct, Pi.star_apply, RCLike.star_def]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _

/-- A vector with `star ψ ⬝ᵥ ψ = 1` is a unit vector of `EuclideanSpace`. -/
theorem norm_toLp_eq_one {ψ : Cfg d N → ℂ} (hψ1 : star ψ ⬝ᵥ ψ = 1) :
    ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))‖ = 1 := by
  have h := inner_toLp_toEuclideanLin ψ 1
  simp only [Matrix.toEuclideanLin, Matrix.toLpLin_one, LinearMap.id_apply] at h
  rw [expect_one, hψ1, inner_self_eq_norm_sq_to_K] at h
  have h' : ‖(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))‖ ^ 2 = 1 :=
    Complex.ofReal_injective (by push_cast; exact h)
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h'

/-- For a unit vector `χ` and an operator `F`, `‖⟪χ, F χ⟫‖ ≤ ‖F‖`. -/
theorem norm_inner_apply_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (F : E →L[ℂ] E) {χ : E} (hχ : ‖χ‖ = 1) : ‖⟪χ, F χ⟫_ℂ‖ ≤ ‖F‖ := by
  calc ‖⟪χ, F χ⟫_ℂ‖ ≤ ‖χ‖ * (‖F‖ * ‖χ‖) :=
        (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left (F.le_opNorm χ) (norm_nonneg _))
    _ = ‖F‖ := by rw [hχ]; ring

/-- The diagonal term of the variance of a sum: for a unit vector `χ` and a matrix `X` of
operator norm at most `M`, `‖⟪χ, X X χ⟫ - ⟪χ, X χ⟫²‖ ≤ 2 M²`. -/
theorem norm_inner_sq_sub_le {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) {M : ℝ} (hX : ‖Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X‖ ≤ M)
    {χ : EuclideanSpace ℂ n} (hχ : ‖χ‖ = 1) :
    ‖⟪χ, Matrix.toEuclideanLin X (Matrix.toEuclideanLin X χ)⟫_ℂ -
        ⟪χ, Matrix.toEuclideanLin X χ⟫_ℂ * ⟪χ, Matrix.toEuclideanLin X χ⟫_ℂ‖ ≤ 2 * M ^ 2 := by
  set F := Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) X
  have h1 : ‖⟪χ, Matrix.toEuclideanLin X χ⟫_ℂ‖ ≤ M := (norm_inner_apply_le F hχ).trans hX
  have h2 : ‖⟪χ, Matrix.toEuclideanLin X (Matrix.toEuclideanLin X χ)⟫_ℂ‖ ≤ M ^ 2 := by
    have e : Matrix.toEuclideanLin X (Matrix.toEuclideanLin X χ) = (F * F) χ := rfl
    rw [e]
    refine (norm_inner_apply_le (F * F) hχ).trans ((norm_mul_le _ _).trans ?_)
    rw [sq]
    exact mul_le_mul hX hX (norm_nonneg _) ((norm_nonneg _).trans hX)
  calc _ ≤ ‖⟪χ, Matrix.toEuclideanLin X (Matrix.toEuclideanLin X χ)⟫_ℂ‖ +
        ‖⟪χ, Matrix.toEuclideanLin X χ⟫_ℂ‖ * ‖⟪χ, Matrix.toEuclideanLin X χ⟫_ℂ‖ := by
        rw [← norm_mul]; exact norm_sub_le _ _
    _ ≤ M ^ 2 + M * M :=
        add_le_add h2 (mul_le_mul h1 h1 (norm_nonneg _) ((norm_nonneg _).trans h1))
    _ = 2 * M ^ 2 := by ring

/-- Applying the product of two matrices is applying one after the other. -/
theorem toEuclideanLin_mul_apply {n : Type*} [Fintype n] [DecidableEq n]
    (X Y : Matrix n n ℂ) (v : EuclideanSpace ℂ n) :
    Matrix.toEuclideanLin (X * Y) v = Matrix.toEuclideanLin X (Matrix.toEuclideanLin Y v) := by
  change Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (X * Y) v = _
  rw [map_mul]
  rfl

/-- The window starting at `k Δ` lies in the ring when `k < n` and `w ≤ Δ`, `n Δ ≤ N`. -/
theorem window_lt_and_le {w Δ n k : ℕ} (hw : 0 < w) (hwΔ : w ≤ Δ) (hn : n * Δ ≤ N)
    (hk : k < n) : k * Δ < N ∧ k * Δ + w ≤ N := by
  have h : (k + 1) * Δ ≤ n * Δ := Nat.mul_le_mul_right _ hk
  rw [Nat.succ_mul] at h
  constructor <;> omega

section Ring

variable [NeZero N]

/-- **Variance in a state prepared by a shallow circuit.** Let `ψ` be a unit vector prepared in
depth `T`, `X` a Hermitian operator on `w` sites of operator norm at most `M`, and place `X`
on the windows starting at `k Δ`, `k < n`, with `w + 2T ≤ Δ` and `n Δ ≤ N`. For real weights
`|c_k| ≤ γ`, the sum `Z = ∑ c_k X^{(k)}` satisfies `‖(Z - ⟨Z⟩_ψ) ψ‖² ≤ γ² · 3n · 2M²`.

This is "by factorization its variance there is at most `4/n`" in the chapter's proof of
`thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696, Theorem 1), from the
vanishing of connected correlations beyond the light cone (arXiv:2307.01696, Supplemental
Material, proof of Theorem 1). -/
theorem norm_sub_inner_smul_sq_le_of_isPreparedInDepth {T w Δ n : ℕ} (hw : 0 < w)
    (hwΔ : w + 2 * T ≤ Δ) (hn : n * Δ ≤ N) {ψ : Cfg d N → ℂ} (hψ : IsPreparedInDepth T ψ)
    (hψ1 : star ψ ⬝ᵥ ψ = 1) {X : Matrix (Fin w → Fin d) (Fin w → Fin d) ℂ}
    (hX : X.IsHermitian) {M : ℝ} (hXM : ‖Matrix.toEuclideanCLM (n := Fin w → Fin d) (𝕜 := ℂ) X‖ ≤ M)
    (c : Fin n → ℝ) {γ : ℝ} (hc : ∀ k, |c k| ≤ γ) :
    ‖(∑ k : Fin n, (c k : ℂ) • Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
          (WithLp.toLp 2 ψ) -
        ⟪(WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N)),
          (∑ k : Fin n, (c k : ℂ) • Matrix.toEuclideanLin (chainWindowOperator N (k.val * Δ) X))
            (WithLp.toLp 2 ψ)⟫_ℂ • (WithLp.toLp 2 ψ : EuclideanSpace ℂ (Cfg d N))‖ ^ 2 ≤
      γ ^ 2 * (3 * n * (2 * M ^ 2)) := by
  classical
  set χ : EuclideanSpace ℂ (Cfg d N) := WithLp.toLp 2 ψ
  have hχ : ‖χ‖ = 1 := norm_toLp_eq_one hψ1
  have hΔ : w ≤ Δ := by omega
  have hwin := fun k : Fin n ↦ window_lt_and_le (N := N) hw hΔ hn k.isLt
  set Xk : Fin n → Matrix (Cfg d N) (Cfg d N) ℂ := fun k ↦ chainWindowOperator N (k.val * Δ) X
  have hnorm : ∀ k, ‖Matrix.toEuclideanCLM (n := Cfg d N) (𝕜 := ℂ) (Xk k)‖ ≤ M := fun k ↦
    (norm_toEuclideanCLM_chainWindowOperator_le (hwin k).1 (hwin k).2 X).trans hXM
  set f : ℕ → ℝ := fun j ↦ if j = 0 then 2 * M ^ 2 else 0
  have hM0 : 0 ≤ M := (norm_nonneg _).trans hXM
  have hf : ∀ j, 0 ≤ f j := fun j ↦ by simp only [f]; split_ifs <;> positivity
  have hmain := norm_sub_inner_smul_sq_le (fun k ↦ Matrix.toEuclideanLin (Xk k))
    (fun k ↦ Matrix.isSymmetric_toEuclideanLin_iff.mpr
      (chainWindowOperator_isHermitian (hwin k).1 (hwin k).2 hX)) hχ c hc f hf
    (fun k ↦ by simpa [f] using norm_inner_sq_sub_le (Xk k) (hnorm k) hχ)
    (fun k l hkl ↦ by
      have hsep : IsSeparatedBy (window N (k.val * Δ) w) (window N (l.val * Δ) w) (2 * T) := by
        have h1 : (k.val + 1) * Δ ≤ l.val * Δ := Nat.mul_le_mul_right _ hkl
        have h2 : (l.val + 1) * Δ ≤ n * Δ := Nat.mul_le_mul_right _ l.isLt
        rw [Nat.succ_mul] at h1 h2
        exact isSeparatedBy_window (by omega) (by omega)
      have hfac := expect_mul_eq_of_isPreparedInDepth hψ hψ1 hsep
        (chainWindowOperator_mem_supportedOperators_window (hwin k).1 (hwin k).2 X)
        (chainWindowOperator_mem_supportedOperators_window (hwin l).1 (hwin l).2 X)
      have hne : l.val - k.val ≠ 0 := by have := Fin.lt_def.mp hkl; omega
      simp only [f, hne, ite_false]
      rw [← toEuclideanLin_mul_apply, inner_toLp_toEuclideanLin, inner_toLp_toEuclideanLin,
        inner_toLp_toEuclideanLin, hfac, sub_self, norm_zero])
  refine hmain.trans ?_
  gcongr
  calc ∑ j ∈ Finset.range n, f j ≤ ∑ j ∈ Finset.range (n + 1), f j :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.le_succ n))
          fun j _ _ ↦ hf j
    _ = 2 * M ^ 2 := by
        simp only [f]
        rw [Finset.sum_ite_eq' (Finset.range (n + 1)) 0]
        simp

end Ring

end MPSPreparation
