/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# The variance of a weighted sum of symmetric operators

For symmetric operators `T_k`, real weights `c_k` and a unit vector `χ`, the squared norm
`‖(Z - ⟨Z⟩_χ)χ‖²` of `Z = ∑_k c_k T_k` is the double sum of the weighted connected
correlations `⟨T_k T_l⟩_χ - ⟨T_k⟩_χ ⟨T_l⟩_χ`. When these correlations are bounded by a
function `f` of the distance `l - k` of the labels, the squared norm is at most
`3 n γ² ∑_{j<n} f(j)` with `γ` a bound on the weights.

This is the step "every average of `n` of these operators, or of their pair products, has
variance at most `C₁/n`" of the chapter's proof of `thm:ldp_depth_lower_bound` (the chapter's
version of arXiv:2307.01696, Theorem 1), and the variance bound `4/n` in the circuit state
used there.
-/

open scoped InnerProductSpace BigOperators

namespace MPSPreparation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- For symmetric `S`, `T` and a unit vector `χ`, the inner product of the centred vectors
`(S - ⟨S⟩)χ` and `(T - ⟨T⟩)χ` is the connected correlation `⟨S T⟩ - ⟨S⟩⟨T⟩`
(the covariance in the chapter's proof of `thm:ldp_depth_lower_bound`; arXiv:2307.01696,
Supplemental Material, proof of Theorem 1, connected correlations). -/
theorem inner_centred_eq {S T : E →ₗ[ℂ] E} (hS : S.IsSymmetric) {χ : E} (hχ : ‖χ‖ = 1) :
    ⟪S χ - ⟪χ, S χ⟫_ℂ • χ, T χ - ⟪χ, T χ⟫_ℂ • χ⟫_ℂ =
      ⟪χ, S (T χ)⟫_ℂ - ⟪χ, S χ⟫_ℂ * ⟪χ, T χ⟫_ℂ := by
  have hreal : starRingEnd ℂ ⟪χ, S χ⟫_ℂ = ⟪χ, S χ⟫_ℂ := by
    rw [← hS χ χ]
    exact hS.conj_inner_sym χ χ
  have hχχ : ⟪χ, χ⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hχ]
    norm_num
  have hSχ : ⟪S χ, χ⟫_ℂ = ⟪χ, S χ⟫_ℂ := hS χ χ
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
    inner_smul_right, inner_smul_right, hS χ (T χ), hSχ, hχχ, hreal]
  ring

/-- A sum over labels `l` with an injective relabelling `φ` into `{0, …, n-1}` of a
nonnegative `f ∘ φ` is at most `∑_{j<n} f j`. -/
theorem sum_le_sum_range_of_injOn {n : ℕ} {s : Finset (Fin n)} {φ : Fin n → ℕ}
    (hφ : Set.InjOn φ s) (hlt : ∀ l ∈ s, φ l < n) {f : ℕ → ℝ} (hf : ∀ j, 0 ≤ f j) :
    ∑ l ∈ s, f (φ l) ≤ ∑ j ∈ Finset.range n, f j := by
  classical
  rw [← Finset.sum_image hφ]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ ↦ hf j
  intro j hj
  obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hj
  exact Finset.mem_range.mpr (hlt l hl)

/-- **Variance of a weighted sum.** Let `T_k`, `k < n`, be symmetric, `χ` a unit vector,
`|c_k| ≤ γ`, and suppose the connected correlations satisfy
`|⟨T_k T_k⟩ - ⟨T_k⟩²| ≤ f 0` and `|⟨T_k T_l⟩ - ⟨T_k⟩⟨T_l⟩| ≤ f (l - k)` for `k < l`, with
`f ≥ 0`. Then `Z = ∑ c_k T_k` satisfies `‖(Z - ⟨Z⟩)χ‖² ≤ 3 n γ² ∑_{j<n} f j`.

This is the variance bound for averages of translated observables in the chapter's proof
of `thm:ldp_depth_lower_bound` (the chapter's version of arXiv:2307.01696, Theorem 1). -/
theorem norm_sub_inner_smul_sq_le {n : ℕ} (T : Fin n → E →ₗ[ℂ] E)
    (hT : ∀ k, (T k).IsSymmetric) {χ : E} (hχ : ‖χ‖ = 1) (c : Fin n → ℝ) {γ : ℝ}
    (hc : ∀ k, |c k| ≤ γ) (f : ℕ → ℝ) (hf : ∀ j, 0 ≤ f j)
    (hdiag : ∀ k, ‖⟪χ, T k (T k χ)⟫_ℂ - ⟪χ, T k χ⟫_ℂ * ⟪χ, T k χ⟫_ℂ‖ ≤ f 0)
    (hoff : ∀ k l, k < l →
      ‖⟪χ, T k (T l χ)⟫_ℂ - ⟪χ, T k χ⟫_ℂ * ⟪χ, T l χ⟫_ℂ‖ ≤ f (l.val - k.val)) :
    ‖(∑ k, (c k : ℂ) • T k) χ - ⟪χ, (∑ k, (c k : ℂ) • T k) χ⟫_ℂ • χ‖ ^ 2 ≤
      γ ^ 2 * (3 * n * ∑ j ∈ Finset.range n, f j) := by
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hγ : 0 ≤ γ := (abs_nonneg _).trans (hc ⟨0, hn⟩)
  set v : Fin n → E := fun k ↦ T k χ - ⟪χ, T k χ⟫_ℂ • χ with hv_def
  have hZ : (∑ k, (c k : ℂ) • T k) χ - ⟪χ, (∑ k, (c k : ℂ) • T k) χ⟫_ℂ • χ =
      ∑ k, (c k : ℂ) • v k := by
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, inner_sum, inner_smul_right,
      Finset.sum_smul, v, smul_sub, Finset.sum_sub_distrib, smul_smul]
  rw [hZ]
  have hcov : ∀ k l, ⟪v k, v l⟫_ℂ = ⟪χ, T k (T l χ)⟫_ℂ - ⟪χ, T k χ⟫_ℂ * ⟪χ, T l χ⟫_ℂ :=
    fun k l ↦ inner_centred_eq (hT k) hχ
  set g : Fin n → Fin n → ℝ := fun k l ↦
    (if k < l then f (l.val - k.val) else 0) + (if l < k then f (k.val - l.val) else 0) +
      (if l = k then f 0 else 0) with hg_def
  have hpair : ∀ k l, ‖⟪v k, v l⟫_ℂ‖ ≤ g k l := by
    intro k l
    rcases lt_trichotomy k l with h | h | h
    · have e : g k l = f (l.val - k.val) := by
        simp [g, h, not_lt.mpr h.le, ne_of_gt h]
      rw [e, hcov]
      exact hoff k l h
    · subst h
      have e : g k k = f 0 := by simp [g]
      rw [e, hcov]
      exact hdiag k
    · have e : g k l = f (k.val - l.val) := by
        simp [g, h, not_lt.mpr h.le, ne_of_lt h]
      rw [e, ← inner_conj_symm, RCLike.norm_conj, hcov]
      exact hoff l k h
  have hS0 : 0 ≤ ∑ j ∈ Finset.range n, f j := Finset.sum_nonneg fun j _ ↦ hf j
  have hrow : ∀ k, ∑ l, g k l ≤ 3 * ∑ j ∈ Finset.range n, f j := by
    intro k
    simp only [g, Finset.sum_add_distrib]
    have h1 : ∑ l : Fin n, (if k < l then f (l.val - k.val) else 0) ≤
        ∑ j ∈ Finset.range n, f j := by
      rw [← Finset.sum_filter]
      refine sum_le_sum_range_of_injOn ?_ ?_ hf
      · intro l₁ hl₁ l₂ hl₂ h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl₁ hl₂
        simp only at h
        exact Fin.ext (by have := Fin.lt_def.mp hl₁; have := Fin.lt_def.mp hl₂; omega)
      · intro l _
        omega
    have h2 : ∑ l : Fin n, (if l < k then f (k.val - l.val) else 0) ≤
        ∑ j ∈ Finset.range n, f j := by
      rw [← Finset.sum_filter]
      refine sum_le_sum_range_of_injOn ?_ ?_ hf
      · intro l₁ hl₁ l₂ hl₂ h
        simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hl₁ hl₂
        simp only at h
        exact Fin.ext (by have := Fin.lt_def.mp hl₁; have := Fin.lt_def.mp hl₂; omega)
      · intro l _
        omega
    have h3 : ∑ l : Fin n, (if l = k then f 0 else 0) ≤ ∑ j ∈ Finset.range n, f j := by
      rw [Finset.sum_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ k)]
      exact Finset.single_le_sum (fun j _ ↦ hf j) (Finset.mem_range.mpr hn)
    linarith
  have hnorm : ‖∑ k, (c k : ℂ) • v k‖ ^ 2 = ‖⟪∑ k, (c k : ℂ) • v k, ∑ k, (c k : ℂ) • v k⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K, norm_pow]
    simp
  rw [hnorm, sum_inner]
  calc ‖∑ k, ⟪(c k : ℂ) • v k, ∑ l, (c l : ℂ) • v l⟫_ℂ‖
      ≤ ∑ k, ∑ l, γ ^ 2 * g k l := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ ↦ ?_)
        rw [inner_sum]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ ↦ ?_)
        rw [inner_smul_left, inner_smul_right, norm_mul, norm_mul, Complex.conj_ofReal,
          Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, ← mul_assoc]
        have hcc : |c k| * |c l| ≤ γ ^ 2 := by
          rw [sq]
          exact mul_le_mul (hc k) (hc l) (abs_nonneg _) hγ
        exact mul_le_mul hcc (hpair k l) (norm_nonneg _) (sq_nonneg _)
    _ = γ ^ 2 * ∑ k, ∑ l, g k l := by rw [Finset.mul_sum]; simp only [Finset.mul_sum]
    _ ≤ γ ^ 2 * ∑ _k : Fin n, 3 * ∑ j ∈ Finset.range n, f j :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ hrow k) (sq_nonneg _)
    _ = γ ^ 2 * (3 * n * ∑ j ∈ Finset.range n, f j) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end MPSPreparation
