/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.BigOperators
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FinCases
import TNLean.Algebra.NoSingletonWords
import TNLean.Algebra.SingletonWordCancellation
import QICLean.Analysis.MatrixTraceInequalities
import QICLean.Analysis.TraceMulBound
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Finite uniform moments of centered matrix samples

Let `X b a` be complex square matrices, with `b` ranging over a finite nonempty
set of sample labels and `a` over a finite nonempty alphabet. Suppose that
`∑ a, X b a = 0` and `‖X b a‖ ≤ R` for every `b, a`. If `ℓ = card β` and
`N = card n`, the uniform average over assignments `σ : β → α` satisfies

`𝔼 ‖ℓ⁻¹ ∑ b, X b (σ b)‖^(2p) ≤ N (p² R² / ℓ)^p`, for `p ≥ 1`.

The proof expands the alternating product `((∑ X)ᴴ * ∑ X)^p`, cancels words
with a singleton sample label, and counts the remaining words. The matrices
need not be Hermitian. This is an auxiliary finite moment estimate for LVV,
arXiv:1307.5143v1, Section 2.3.1. The sharp matrix Bernstein inequality remains
a separate result. The source's ground-energy dependence is recorded in
`docs/paper-gaps/lvv13_sampling_ground_energy.tex`.
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator ComplexOrder

namespace Matrix

variable {β A : Type*} [Fintype β] [Semiring A] [StarRing A]

private def alternatingFactor (p : ℕ) (k : Fin (p * 2)) (x : A) : A :=
  (Fin.repeat p ![star, id] k) x

open Classical in
private theorem gram_pow_eq_sum_words (p : ℕ) (X : β → A) :
    (star (∑ b, X b) * ∑ b, X b) ^ p =
      ∑ w : Fin (p * 2) → β,
        (List.ofFn fun k ↦ alternatingFactor p k (X (w k))).prod := by
  classical
  let F := MultilinearMap.mkPiAlgebraFin ℕ (p * 2) A
  have hcoords : (fun k ↦ ∑ b, alternatingFactor p k (X b)) =
      Fin.repeat p ![star (∑ b, X b), ∑ b, X b] := by
    funext k
    simp only [alternatingFactor, Fin.repeat_apply]
    generalize k.modNat = i
    fin_cases i <;> simp [star_sum]
  calc
    _ = F (fun k ↦ ∑ b, alternatingFactor p k (X b)) := by
      rw [hcoords]
      simp [F, List.prod_flatten, List.ofFn_succ]
    _ = ∑ w : Fin (p * 2) → β, F (fun k ↦ alternatingFactor p k (X (w k))) :=
      F.map_sum (fun k b ↦ alternatingFactor p k (X b))
    _ = _ := rfl

end Matrix

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem norm_pow_two_mul_le_trace_gram_pow (S : Matrix n n ℂ) {p : ℕ} (hp : p ≠ 0) :
    ‖S‖ ^ (2 * p) ≤ ((Sᴴ * S) ^ p).trace.re := by
  have hpos := Matrix.posSemidef_conjTranspose_mul_self S
  have hnorm := CFC.norm_pow ℝ (Sᴴ * S) p hp hpos.isHermitian.isSelfAdjoint
  rw [Matrix.l2_opNorm_conjTranspose_mul_self, ← pow_two, ← pow_mul] at hnorm
  rw [← hnorm]
  exact (hpos.pow p).l2_opNorm_le_trace_re

private theorem norm_trace_prod_ofFn_le [Nonempty n] {m : ℕ} (B : Fin m → Matrix n n ℂ)
    {R : ℝ} (hR : 0 ≤ R) (hB : ∀ k, ‖B k‖ ≤ R) :
    ‖(List.ofFn B).prod.trace‖ ≤ (Fintype.card n : ℝ) * R ^ m := by
  let r : NNReal := ⟨R, hR⟩
  have hn : ‖(List.ofFn B).prod‖₊ ≤ r ^ m := by
    calc
      _ ≤ (List.ofFn fun k ↦ ‖B k‖₊).prod := by
        simpa only [List.map_ofFn, Function.comp_def] using List.nnnorm_prod_le (List.ofFn B)
      _ ≤ r ^ m := by
        simpa only [List.length_ofFn] using List.prod_le_pow_length
          (List.ofFn fun k ↦ ‖B k‖₊) r (by
            intro x hx
            obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
            exact_mod_cast hB k)
  have ht := PosSemidef.one.norm_trace_mul_le (n := n) (List.ofFn B).prod
  simp only [Matrix.one_mul, Matrix.trace_one, Complex.natCast_re] at ht
  exact ht.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hn) (Nat.cast_nonneg _))

end Matrix

namespace Matrix

open Finset

open Classical in
private theorem sum_re_trace_gram_pow_le {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0) (p : ℕ) :
    (∑ σ : β → α,
      (((∑ b, X b (σ b))ᴴ * (∑ b, X b (σ b))) ^ p).trace.re) ≤
      (Fintype.card (β → α) : ℝ) * (Fintype.card n : ℝ) *
        (Fintype.card β : ℝ) ^ p * (p : ℝ) ^ (p * 2) * R ^ (p * 2) := by
  classical
  let W : Finset (Fin (p * 2) → β) := Finset.univ.filter fun w ↦
    ∀ b : β, (Finset.univ.filter fun k ↦ w k = b).card ≠ 1
  let word (w : Fin (p * 2) → β) (σ : β → α) : Matrix n n ℂ :=
    (List.ofFn fun k ↦ alternatingFactor p k (X (w k) (σ (w k)))).prod
  have hcardW : W.card ≤ Fintype.card β ^ p * p ^ (p * 2) := by
    have h := Fintype.card_even_words_without_singleton (β := β) p
    rw [Nat.mul_comm 2 p] at h
    simpa only [Fintype.card_subtype, W] using h
  have hexpand (σ : β → α) :
      ((∑ b, X b (σ b))ᴴ * (∑ b, X b (σ b))) ^ p = ∑ w, word w σ :=
    gram_pow_eq_sum_words p (fun b ↦ X b (σ b))
  have hzero (w : Fin (p * 2) → β) (hw : w ∉ W) : ∑ σ, word w σ = 0 := by
    have hnot : ¬∀ b : β, (Finset.univ.filter fun k ↦ w k = b).card ≠ 1 := by
      simpa only [W, Finset.mem_filter, Finset.mem_univ, true_and] using hw
    simp only [not_forall, not_not] at hnot
    obtain ⟨b, hb⟩ := hnot
    obtain ⟨t, ht⟩ := Finset.card_eq_one.mp hb
    have hwt : w t = b := by
      have hm : t ∈ Finset.univ.filter (fun k ↦ w k = b) := by rw [ht]; simp
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hm
    have hsingle : ∀ k, w k = w t → k = t := by
      intro k hk
      have hm : k ∈ Finset.univ.filter (fun k ↦ w k = b) := by simp [hk, hwt]
      simpa only [ht, Finset.mem_singleton] using hm
    have hcenter : ∑ a, alternatingFactor p t (X (w t) a) = 0 := by
      simp only [alternatingFactor, Fin.repeat_apply]
      generalize t.modNat = i
      fin_cases i <;> simp [← star_sum, hmean]
    exact Fintype.sum_ordered_word_eq_zero_of_singleton w t hsingle
      (fun k a ↦ alternatingFactor p k (X (w k) a)) hcenter
  have htrace :
      (∑ σ : β → α,
        (((∑ b, X b (σ b))ᴴ * (∑ b, X b (σ b))) ^ p).trace.re) =
      ∑ w ∈ W, ∑ σ : β → α, (word w σ).trace.re := by
    simp_rw [hexpand, Matrix.trace_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    symm
    apply Finset.sum_subset (Finset.subset_univ W)
    intro w _ hw
    have h := congrArg (fun M : Matrix n n ℂ ↦ M.trace.re) (hzero w hw)
    simpa only [Matrix.trace_sum, Complex.re_sum, Matrix.trace_zero, Complex.zero_re] using h
  have hwordbound (w : Fin (p * 2) → β) (σ : β → α) :
      (word w σ).trace.re ≤ (Fintype.card n : ℝ) * R ^ (p * 2) := by
    refine (Complex.re_le_norm _).trans (Matrix.norm_trace_prod_ofFn_le _ hR ?_)
    intro k
    simp only [alternatingFactor, Fin.repeat_apply]
    generalize k.modNat = i
    fin_cases i <;> simpa using hX (w k) (σ (w k))
  have hWreal : (W.card : ℝ) ≤ (Fintype.card β : ℝ) ^ p * (p : ℝ) ^ (p * 2) := by
    exact_mod_cast hcardW
  calc
    _ = ∑ w ∈ W, ∑ σ : β → α, (word w σ).trace.re := htrace
    _ ≤ ∑ _w ∈ W, ∑ _σ : β → α, (Fintype.card n : ℝ) * R ^ (p * 2) :=
      Finset.sum_le_sum fun w _ ↦ Finset.sum_le_sum fun σ _ ↦ hwordbound w σ
    _ = (W.card : ℝ) * (Fintype.card (β → α) : ℝ) *
        (Fintype.card n : ℝ) * R ^ (p * 2) := by simp [mul_assoc]
    _ ≤ ((Fintype.card β : ℝ) ^ p * (p : ℝ) ^ (p * 2)) *
        (Fintype.card (β → α) : ℝ) * (Fintype.card n : ℝ) * R ^ (p * 2) := by
      gcongr
    _ = _ := by ring

end Matrix

namespace Matrix

open Classical in
private theorem sum_norm_sum_pow_le {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p) :
    (∑ σ : β → α, ‖∑ b, X b (σ b)‖ ^ (2 * p)) ≤
      (Fintype.card (β → α) : ℝ) * (Fintype.card n : ℝ) *
        (Fintype.card β : ℝ) ^ p * (p : ℝ) ^ (2 * p) * R ^ (2 * p) := by
  classical
  have hspec :
      (∑ σ : β → α, ‖∑ b, X b (σ b)‖ ^ (2 * p)) ≤
      ∑ σ : β → α,
        (((∑ b, X b (σ b))ᴴ * (∑ b, X b (σ b))) ^ p).trace.re :=
    Finset.sum_le_sum fun σ _ ↦ Matrix.norm_pow_two_mul_le_trace_gram_pow _ hp.ne'
  simpa only [Nat.mul_comm p 2] using hspec.trans (sum_re_trace_gram_pow_le X hR hX hmean p)

open Classical in
private theorem average_norm_sum_pow_le {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p) :
    (∑ σ : β → α, ‖∑ b, X b (σ b)‖ ^ (2 * p)) /
        (Fintype.card (β → α) : ℝ) ≤
      (Fintype.card n : ℝ) * (Fintype.card β : ℝ) ^ p *
        (p : ℝ) ^ (2 * p) * R ^ (2 * p) := by
  classical
  have hcard : 0 < (Fintype.card (β → α) : ℝ) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hcard).mpr
  calc
    _ ≤ (Fintype.card (β → α) : ℝ) * (Fintype.card n : ℝ) *
        (Fintype.card β : ℝ) ^ p * (p : ℝ) ^ (2 * p) * R ^ (2 * p) :=
      sum_norm_sum_pow_le X hR hX hmean hp
    _ = _ := by ring

open Classical in
/-- A finite uniform matrix moment estimate. For centered samples with operator norm at
most `R`, the `2p`-th moment of their sample mean is at most
`card n * (p² R² / card β)^p`. No Hermiticity assumption is imposed on the samples.

This is an auxiliary moment estimate for the sampled projection in LVV,
arXiv:1307.5143v1, Section 2.3.1. It is weaker than the sharp matrix Bernstein
inequality and does not establish the source's sampling construction. -/
theorem average_norm_average_pow_le_of_centered {α β n : Type*} [Fintype α] [Fintype β]
    [Fintype n] [DecidableEq n] [Nonempty α] [Nonempty β] [Nonempty n]
    (X : β → α → Matrix n n ℂ) {R : ℝ} (hR : 0 ≤ R)
    (hX : ∀ b a, ‖X b a‖ ≤ R) (hmean : ∀ b, ∑ a, X b a = 0)
    {p : ℕ} (hp : 0 < p) :
    (∑ σ : β → α, ‖(Fintype.card β : ℂ)⁻¹ • ∑ b, X b (σ b)‖ ^ (2 * p)) /
        (Fintype.card (β → α) : ℝ) ≤
      (Fintype.card n : ℝ) *
        ((p : ℝ) ^ 2 * R ^ 2 / (Fintype.card β : ℝ)) ^ p := by
  classical
  have hcard : (Fintype.card β : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ = (Fintype.card β : ℝ)⁻¹ ^ (2 * p) *
        ((∑ σ : β → α, ‖∑ b, X b (σ b)‖ ^ (2 * p)) /
          (Fintype.card (β → α) : ℝ)) := by
      simp only [norm_smul, norm_inv, Complex.norm_natCast, mul_pow, ← Finset.mul_sum]
      ring
    _ ≤ (Fintype.card β : ℝ)⁻¹ ^ (2 * p) *
        ((Fintype.card n : ℝ) * (Fintype.card β : ℝ) ^ p *
          (p : ℝ) ^ (2 * p) * R ^ (2 * p)) :=
      mul_le_mul_of_nonneg_left (average_norm_sum_pow_le X hR hX hmean hp) (by positivity)
    _ = _ := by
      simp only [div_pow, mul_pow, ← pow_mul, inv_pow, two_mul, pow_add]
      field_simp [hcard]

end Matrix
