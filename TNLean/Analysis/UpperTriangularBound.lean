/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Cases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
/-!
# Upper-triangular power bound — Wolf Eqs. (8.103) and (8.105)

We formalise the noncommutative upper-triangular word estimate
(Wolf Eq. 8.105) for an arbitrary submultiplicative ring seminorm,
together with the coarse and refined power bounds (Wolf Eq. 8.103).

## Main results

* `Matrix.wolf_eq_105_seminorm` — the word-expansion bound for all `n`
* `Matrix.wolf_eq_103` — the coarse constant `(D-1)n^{D-1}` under `D-1 ≤ n`
* `Matrix.wolf_eq_103_refined` — the binomial-coefficient constant under `2(D-1) ≤ n`

## References

* Wolf (2012), *Quantum Channels & Operations*, Chapter 8
-/
open Matrix
open scoped BigOperators

namespace Matrix

section TriangularDefinitions
variable {D : ℕ} {R : Type*} [Semiring R]

/-- A matrix is strictly upper triangular when \(M_{ij}=0\) whenever \(i\ge j\). -/
def IsStrictlyUpperTriangular (M : Matrix (Fin D) (Fin D) R) : Prop :=
  ∀ (i j : Fin D), (i : ℕ) ≥ (j : ℕ) → M i j = 0
end TriangularDefinitions

section EntryLemmas
variable {D : ℕ} {R : Type*} [Semiring R] {Λ N : Matrix (Fin D) (Fin D) R}
lemma IsDiag.mul_apply (hΛ : IsDiag Λ) (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (Λ * P) i j = Λ i i * P i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hk_ne; rw [hΛ (Ne.symm hk_ne), zero_mul]
  · intro h; exfalso; exact h (Finset.mem_univ i)

lemma IsDiag.mul_apply_right (hΛ : IsDiag Λ) (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (P * Λ) i j = P i j * Λ j j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j
  · intro k _ hk_ne; rw [hΛ hk_ne, mul_zero]
  · intro h; exfalso; exact h (Finset.mem_univ j)

lemma IsStrictlyUpperTriangular.mul_apply (hN : IsStrictlyUpperTriangular N)
    (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (N * P) i j = Finset.sum
      ((Finset.univ : Finset (Fin D)).filter (fun (k : Fin D) => (i : ℕ) < (k : ℕ)))
      (fun k => N i k * P k j) := by
  rw [Matrix.mul_apply]
  apply (Finset.sum_subset
    (Finset.filter_subset (fun (k : Fin D) => (i : ℕ) < (k : ℕ)) _) ?_).symm
  intro k hk_univ hk_not_mem
  have h_not_lt : ¬ ((i : ℕ) < (k : ℕ)) := by
    intro hlt; apply hk_not_mem; simpa [Finset.mem_filter, hk_univ] using hlt
  have hge : (i : ℕ) ≥ (k : ℕ) := by omega
  simp [hN i k hge]

lemma IsStrictlyUpperTriangular.mul_apply_right (hN : IsStrictlyUpperTriangular N)
    (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (P * N) i j = Finset.sum
      ((Finset.univ : Finset (Fin D)).filter (fun (k : Fin D) => (k : ℕ) < (j : ℕ)))
      (fun k => P i k * N k j) := by
  rw [Matrix.mul_apply]
  apply (Finset.sum_subset
    (Finset.filter_subset (fun (k : Fin D) => (k : ℕ) < (j : ℕ)) _) ?_).symm
  intro k hk_univ hk_not_mem
  have h_not_lt : ¬ ((k : ℕ) < (j : ℕ)) := by
    intro hlt; apply hk_not_mem; simpa [Finset.mem_filter, hk_univ] using hlt
  have hge : (k : ℕ) ≥ (j : ℕ) := by omega
  simp [hN k j hge]
end EntryLemmas

section WordProduct
variable {D : ℕ} {R : Type*} [Semiring R]

/-- The ordered matrix product encoded by a Boolean word, with false selecting
  \(\Lambda\) and true selecting \(N\). -/
def wordProd (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool) :
    Matrix (Fin D) (Fin D) R :=
  (List.ofFn (fun i : Fin n => cond (w i) N Λ)).prod

@[simp] lemma wordProd_zero (Λ N : Matrix (Fin D) (Fin D) R) :
    wordProd Λ N (fun i => False.elim (i.elim0)) = (1 : Matrix (Fin D) (Fin D) R) := by
  simp [wordProd]

lemma wordProd_snoc (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    wordProd Λ N (Fin.snoc w b) = wordProd Λ N w * cond b N Λ := by
  dsimp [wordProd]
  let snoc_wb : Fin (n + 1) → Bool := Fin.snoc w b
  have h := List.ofFn_succ' (fun (i : Fin (n + 1)) => cond (snoc_wb i) N Λ)
  have h_castSucc : (fun (i : Fin n) => cond (snoc_wb (Fin.castSucc i)) N Λ) =
      (fun (i : Fin n) => cond (w i) N Λ) := by
    ext i; simp [snoc_wb]
  have h_last : cond (snoc_wb (Fin.last n)) N Λ = cond b N Λ := by
    simp [snoc_wb]
  calc
    (List.ofFn (fun (i : Fin (n + 1)) => cond (snoc_wb i) N Λ)).prod
        = ((List.ofFn (fun (i : Fin n) => cond (snoc_wb (Fin.castSucc i)) N Λ)).concat
            (cond (snoc_wb (Fin.last n)) N Λ)).prod := by rw [h]
    _ = ((List.ofFn (fun (i : Fin n) => cond (w i) N Λ)).concat (cond b N Λ)).prod := by
      rw [h_castSucc, h_last]
    _ = (List.ofFn (fun (i : Fin n) => cond (w i) N Λ)).prod * cond b N Λ := by simp

lemma wordProd_snoc' (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool) (b : Bool) :
    wordProd Λ N (Fin.snoc w b) = wordProd Λ N w * (if b then N else Λ) := by
  rw [wordProd_snoc, Bool.cond_eq_ite]
end WordProduct

section WordExpansion
variable {D : ℕ} {R : Type*} [Semiring R]

lemma add_pow_eq_sum_wordProd (Λ N : Matrix (Fin D) (Fin D) R) (n : ℕ) :
    (Λ + N) ^ n = ∑ w : Fin n → Bool, wordProd Λ N w := by
  induction' n with n ih
  · simp [wordProd]
  · rw [pow_succ, ih, mul_add]
    simp_rw [Finset.sum_mul]
    have h_split : ((∑ w : Fin n → Bool, (wordProd Λ N w) * Λ) +
        (∑ w : Fin n → Bool, (wordProd Λ N w) * N)) =
        ((∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true))) := by
      simp [wordProd_snoc']
    rw [h_split]
    have h_sum_eq : (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true)) =
        ∑ w' : Fin (n + 1) → Bool, wordProd Λ N w' := by
      calc
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
            (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true))
            = Finset.sum (Finset.univ : Finset (Fin n → Bool))
                (fun w => (wordProd Λ N (Fin.snoc w false) +
                  wordProd Λ N (Fin.snoc w true))) := by
          simp [Finset.sum_add_distrib]
        _ = Finset.sum (Finset.univ : Finset (Fin n → Bool))
              (fun w => Finset.sum (Finset.univ : Finset Bool)
                (fun b => wordProd Λ N (Fin.snoc w b))) := by
          refine Finset.sum_congr rfl (fun w hw => ?_)
          simp [Finset.sum_insert, Finset.sum_singleton, add_comm]
        _ = Finset.sum (Finset.univ : Finset ((Fin n → Bool) × Bool))
              (fun (p : (Fin n → Bool) × Bool) => wordProd Λ N (Fin.snoc p.1 p.2)) :=
          (Finset.sum_product (s := Finset.univ) (t := Finset.univ)
            (fun (p : (Fin n → Bool) × Bool) => wordProd Λ N (Fin.snoc p.1 p.2))).symm
        _ = ∑ w' : Fin (n + 1) → Bool, wordProd Λ N w' := by
          apply (Finset.sum_bij
            (fun (p : (Fin n → Bool) × Bool) _ => (Fin.snoc p.1 p.2 : Fin (n+1) → Bool))
            (by intro p hp; exact Finset.mem_univ _)
            (by
              intro p hp q hq h
              have h1 : p.1 = q.1 := by
                ext i
                have hcast := congr_fun h (Fin.castSucc i)
                simpa [Fin.snoc_castSucc] using hcast
              have h2 : p.2 = q.2 := by
                have hlast := congr_fun h (Fin.last n)
                simpa [Fin.snoc_last] using hlast
              exact Prod.ext h1 h2)
            (by
              intro w' hw'
              refine ⟨(Fin.init w', w' (Fin.last n)), Finset.mem_univ _, ?_⟩
              rw [Fin.snoc_init_self])
            (by intro p hp; rfl))
    rw [h_sum_eq]
end WordExpansion

section WordVanishing
variable {D : ℕ} {R : Type*} [Semiring R]

/-- The number of true entries in a Boolean word. -/
def countN {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).card

@[simp] lemma countN_zero {n : ℕ} : countN (fun _ : Fin n => false) = 0 := by simp [countN]

private lemma countN_snoc_false_aux {n : ℕ} (w : Fin n → Bool) (i : Fin (n+1)) :
    ((Fin.snoc w false : Fin (n+1) → Bool) i = true) ↔
      ∃ (j : Fin n), Fin.castSucc j = i ∧ w j = true := by
  constructor
  · intro h
    by_cases hi : i = Fin.last n
    · subst hi; simp [Fin.snoc] at h
    · have h_exists : ∃ j : Fin n, Fin.castSucc j = i := Fin.exists_castSucc_eq.mpr hi
      rcases h_exists with ⟨j, hj⟩
      refine ⟨j, hj, ?_⟩
      subst hj
      simpa [Fin.snoc] using h
  · intro ⟨j, hj, hw⟩
    subst hj
    simp [Fin.snoc, hw]

lemma countN_snoc_false {n : ℕ} (w : Fin n → Bool) :
    countN (Fin.snoc w false) = countN w := by
  dsimp [countN]
  have h_eq : (Finset.univ : Finset (Fin (n+1))).filter
      (fun i => (Fin.snoc w false : Fin (n+1) → Bool) i = true) =
      ((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).map
      ⟨Fin.castSucc, Fin.castSucc_injective (n := n)⟩ := by
    ext i
    simp [countN_snoc_false_aux w i]
    constructor
    · rintro ⟨j, hj, hw⟩; exact ⟨j, hw, hj⟩
    · rintro ⟨a, hw, ha⟩; exact ⟨a, ha, hw⟩
  rw [h_eq, Finset.card_map]

private lemma countN_snoc_true_aux {n : ℕ} (w : Fin n → Bool) (i : Fin (n+1)) :
    ((Fin.snoc w true : Fin (n+1) → Bool) i = true) ↔ (i = Fin.last n) ∨
      ∃ (j : Fin n), Fin.castSucc j = i ∧ w j = true := by
  constructor
  · intro h
    by_cases hi : i = Fin.last n
    · left; exact hi
    · right
      have h_exists : ∃ j : Fin n, Fin.castSucc j = i := Fin.exists_castSucc_eq.mpr hi
      rcases h_exists with ⟨j, hj⟩
      refine ⟨j, hj, ?_⟩
      subst hj
      simpa [Fin.snoc] using h
  · intro h
    rcases h with (rfl | ⟨j, hj, hw⟩)
    · simp [Fin.snoc]
    · subst hj; simp [Fin.snoc, hw]

lemma countN_snoc_true {n : ℕ} (w : Fin n → Bool) :
    countN (Fin.snoc w true) = countN w + 1 := by
  dsimp [countN]
  have h_eq : (Finset.univ : Finset (Fin (n+1))).filter
      (fun i => (Fin.snoc w true : Fin (n+1) → Bool) i = true) =
      (((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).map
        ⟨Fin.castSucc, Fin.castSucc_injective (n := n)⟩) ∪ {Fin.last n} := by
    ext i
    simp [countN_snoc_true_aux w i]
    constructor
    · rintro (rfl | ⟨j, hj, hw⟩)
      · left; rfl
      · right; exact ⟨j, hw, hj⟩
    · rintro (rfl | ⟨a, hw, ha⟩)
      · left; rfl
      · right; exact ⟨a, ha, hw⟩
  rw [h_eq]
  have h_disjoint : Disjoint (((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).map
      ⟨Fin.castSucc, Fin.castSucc_injective (n := n)⟩) ({Fin.last n} : Finset (Fin (n+1))) := by
    apply Finset.disjoint_singleton_right.mpr
    intro h; rw [Finset.mem_map] at h
    rcases h with ⟨j, _, h⟩
    exact Fin.castSucc_ne_last j h
  rw [Finset.card_union_of_disjoint h_disjoint, Finset.card_map, Finset.card_singleton]

lemma wordProd_apply_eq_zero_of_shift [NeZero D] (Λ N : Matrix (Fin D) (Fin D) R)
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    {n : ℕ} (w : Fin n → Bool) (i j : Fin D)
    (hshift : (j : ℕ) < (i : ℕ) + countN w) :
    (wordProd Λ N w) i j = 0 := by
  induction' n with n ih generalizing i j
  · have h_countN_zero : countN w = 0 := by
      dsimp [countN]; simp
    have h_lt_i : (j : ℕ) < (i : ℕ) := by
      simpa [h_countN_zero] using hshift
    simp [wordProd, Matrix.one_apply]
    intro h_eq
    have : (i : ℕ) = (j : ℕ) := congrArg Fin.val h_eq
    omega
  · let w' := Fin.init w
    let b := w (Fin.last n)
    have hw_eq : w = Fin.snoc w' b := (Fin.snoc_init_self w).symm
    rw [hw_eq, wordProd_snoc']
    rcases b with (rfl | rfl)
    · simp
      rw [IsDiag.mul_apply_right hΛ_diag (wordProd Λ N w') i j]
      have hshift' : (j : ℕ) < (i : ℕ) + countN w' := by
        simpa [countN_snoc_false w', hw_eq] using hshift
      rw [ih w' i j hshift', zero_mul]
    · simp
      rw [IsStrictlyUpperTriangular.mul_apply_right hN_sut (wordProd Λ N w') i j]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_filter] at hk; rcases hk with ⟨_, hk_lt⟩
      have htemp : (j : ℕ) < (i : ℕ) + countN (Fin.snoc w' true) := by
        simpa [hw_eq] using hshift
      have hk_shift : (k : ℕ) < (i : ℕ) + countN w' := by
        have : (j : ℕ) < (i : ℕ) + (countN w' + 1) := by
          simpa [countN_snoc_true w'] using htemp
        omega
      rw [ih w' i k hk_shift, zero_mul]

lemma wordProd_eq_zero_of_N_count_ge_D [NeZero D] (Λ N : Matrix (Fin D) (Fin D) R)
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    {n : ℕ} (w : Fin n → Bool)
    (hcount : D ≤ countN w) :
    wordProd Λ N w = 0 := by
  ext i j
  have hshift : (j : ℕ) < (i : ℕ) + countN w := by
    have hj_val_lt_D : (j : ℕ) < D := j.2
    have h_j_lt_cN : (j : ℕ) < countN w := lt_of_lt_of_le hj_val_lt_D hcount
    have : countN w ≤ (i : ℕ) + countN w := by
      apply Nat.le_add_left
    exact lt_of_lt_of_le h_j_lt_cN this
  exact wordProd_apply_eq_zero_of_shift Λ N hΛ_diag hN_sut w i j hshift
end WordVanishing

section CountCardinality

variable {n : ℕ}

/-- The set of indices at which a Boolean word is true. -/
private def wordToSupport (w : Fin n → Bool) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (fun i => w i = true)

@[simp] private lemma wordToSupport_card (w : Fin n → Bool) :
    (wordToSupport w).card = countN w := rfl

private lemma wordToSupport_injective :
    Function.Injective (wordToSupport : (Fin n → Bool) → Finset (Fin n)) := by
  intro w1 w2 h; ext i
  have h_mem : i ∈ wordToSupport w1 ↔ i ∈ wordToSupport w2 := by rw [h]
  simp [wordToSupport] at h_mem ⊢; exact h_mem

private lemma card_countN_eq_choose (k : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => countN w = k)).card
      = Nat.choose n k := by
  let S := ((Finset.univ : Finset (Fin n → Bool)).filter (fun w => countN w = k))
  let img := S.image wordToSupport
  have h_card_image : img.card = S.card := Finset.card_image_of_injective S wordToSupport_injective
  have h_img_eq_powerset : img = Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
    ext s; constructor
    · intro hs; rw [Finset.mem_image] at hs; rcases hs with ⟨w, hw, rfl⟩
      rw [Finset.mem_filter] at hw; rcases hw with ⟨_, hcount⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, by rw [wordToSupport_card, hcount]⟩
    · intro hs; rw [Finset.mem_powersetCard] at hs; rcases hs with ⟨hs_sub, hs_card⟩
      let w : Fin n → Bool := fun i => i ∈ s
      have h_wordToSupport : wordToSupport w = s := by
        ext i; dsimp [w, wordToSupport]; simp [hs_sub]
      have h_countN : countN w = k := by rw [← wordToSupport_card, h_wordToSupport, hs_card]
      rw [Finset.mem_image]
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h_countN⟩, h_wordToSupport⟩
  rw [← h_card_image, h_img_eq_powerset, Finset.card_powersetCard, Finset.card_fin]

end CountCardinality

section WordProdLemma

variable {D : ℕ} {R : Type*} [Semiring R]

lemma wordProd_all_false (Λ N : Matrix (Fin D) (Fin D) R) (n : ℕ) :
    wordProd Λ N (fun _ : Fin n => false) = Λ ^ n := by
  induction' n with k ih
  · simp [wordProd]
  · have h_snoc : (fun _ : Fin (k+1) => false) = Fin.snoc (fun _ : Fin k => false) false := by
      ext i; simp [Fin.snoc]
    rw [h_snoc, wordProd_snoc']; simp [ih, pow_succ]

end WordProdLemma

section SeminormHelpers

variable {D : ℕ} {R : Type*} [Ring R]

lemma map_pow_le_pow_of_ne_zero_matrix (f : Matrix (Fin D) (Fin D) R → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (a : Matrix (Fin D) (Fin D) R) {n : ℕ} (hn : n ≠ 0) : f (a ^ n) ≤ f a ^ n := by
  induction' n with k ih
  · exact (hn rfl).elim
  · rw [pow_succ, pow_succ]
    by_cases hk : k = 0
    · subst hk; simp
    · calc
        f (a ^ k * a) ≤ f (a ^ k) * f a := hf_mul _ _
        _ ≤ (f a) ^ k * f a := mul_le_mul_of_nonneg_right (ih hk) (hf_nonneg _)
        _ = f a ^ (k + 1) := by ring

end SeminormHelpers

section PowMaxAux

/-- If \(1\le k\le D-1\), then \(x^k\le\max\{x,x^{D-1}\}\) for nonnegative \(x\). -/
private lemma pow_le_max_of_one_le {k D : ℕ} {x : ℝ} (hx_nonneg : 0 ≤ x)
    (hk1 : 1 ≤ k) (hk2 : k ≤ D - 1) :
    x ^ k ≤ max x (x ^ (D - 1)) := by
  by_cases hx1 : x ≤ 1
  · have h_pow_le_one : x ^ k ≤ x := by
      calc
        x ^ k ≤ x ^ 1 := pow_le_pow_of_le_one hx_nonneg hx1 hk1
        _ = x := by simp
    have h_max : x ≤ max x (x ^ (D - 1)) := by simp
    exact h_pow_le_one.trans h_max
  · have hx1' : 1 ≤ x := by linarith
    have h_pow_le : x ^ k ≤ x ^ (D - 1) := pow_le_pow_right₀ hx1' hk2
    have h_max : x ^ (D - 1) ≤ max x (x ^ (D - 1)) := by simp
    exact h_pow_le.trans h_max

end PowMaxAux

section SeminormBound


variable {D : ℕ} {R : Type*} [Ring R]

lemma wordProd_seminorm_le (f : Matrix (Fin D) (Fin D) R → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool)
    (hpos : 1 ≤ countN w) :
    f (wordProd Λ N w) ≤ (f Λ) ^ (n - countN w) * (f N) ^ (countN w) := by
  cases' n with n
  · have h0 : countN w = 0 := by dsimp [countN]; simp
    omega
  · let w' := Fin.init w; let b := w (Fin.last n)
    have hw_eq : w = Fin.snoc w' b := (Fin.snoc_init_self w).symm
    rw [hw_eq, wordProd_snoc']
    have h_le : countN w' ≤ n := by
      dsimp [countN]
      calc
        ((Finset.univ : Finset (Fin n)).filter (fun i => w' i = true)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := Finset.card_fin n
    rcases b with (rfl | rfl)
    · have hpos_w' : 1 ≤ countN w' := by
        have h_snoc_eq : countN (Fin.snoc w' false) = countN w' := countN_snoc_false w'
        rw [hw_eq] at hpos; rw [h_snoc_eq] at hpos; exact hpos
      simp
      have h_exp : (n - countN w') + 1 = (n + 1) - countN w' := by omega
      have h_rearrange : ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f Λ
          = (f Λ) ^ ((n - countN w') + 1) * (f N) ^ (countN w') := by ring
      calc
        f (wordProd Λ N w' * Λ) ≤ f (wordProd Λ N w') * f Λ := hf_mul _ _
        _ ≤ ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f Λ :=
          mul_le_mul_of_nonneg_right
            (wordProd_seminorm_le f hf_nonneg hf_mul Λ N w' hpos_w') (hf_nonneg _)
        _ = (f Λ) ^ ((n - countN w') + 1) * (f N) ^ (countN w') := by rw [h_rearrange]
        _ = (f Λ) ^ ((n + 1) - countN w') * (f N) ^ (countN w') := by rw [h_exp]
        _ = (f Λ) ^ ((n + 1) - countN (Fin.snoc w' false))
            * (f N) ^ (countN (Fin.snoc w' false)) := by
          rw [countN_snoc_false w']
    · by_cases hzero_w' : countN w' = 0
      · have hall_false : w' = (fun _ : Fin n => false) := by
          ext i
          have hfalse : w' i = false := by
            by_cases h : w' i = true
            · have hi_mem : i ∈ ((Finset.univ : Finset (Fin n)).filter
                  (fun j => w' j = true)) := by
                simp [h]
              have hpos' : 1 ≤ countN w' := by
                dsimp [countN]; exact Finset.one_le_card.mpr ⟨i, hi_mem⟩
              omega
            · simpa using h
          exact hfalse
        have h_wordProd : wordProd Λ N w' = Λ ^ n := by
          rw [hall_false, wordProd_all_false]
        simp [h_wordProd]
        by_cases hn0 : n = 0
        · subst hn0
          simp [hzero_w', countN_snoc_true]
        · have h_pow_bound : f (Λ ^ n) ≤ (f Λ) ^ n :=
            have hn0' : n ≠ 0 := hn0
            map_pow_le_pow_of_ne_zero_matrix f hf_nonneg hf_mul Λ hn0'
          calc
            f (Λ ^ n * N) ≤ f (Λ ^ n) * f N := hf_mul _ _
            _ ≤ (f Λ) ^ n * f N := mul_le_mul_of_nonneg_right h_pow_bound (hf_nonneg _)
            _ = (f Λ) ^ ((n + 1) - (countN w' + 1)) * (f N) ^ (countN w' + 1) := by
              simp [hzero_w']
            _ = (f Λ) ^ ((n + 1) - countN (Fin.snoc w' true))
                * (f N) ^ (countN (Fin.snoc w' true)) := by
              rw [countN_snoc_true w']
      · have hpos_w' : 1 ≤ countN w' := by omega
        simp
        have h_exp : n - countN w' = (n + 1) - (countN w' + 1) := by omega
        have h_rearrange : ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f N
            = (f Λ) ^ (n - countN w') * (f N) ^ (countN w' + 1) := by ring
        calc
          f (wordProd Λ N w' * N) ≤ f (wordProd Λ N w') * f N := hf_mul _ _
          _ ≤ ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f N :=
            mul_le_mul_of_nonneg_right
              (wordProd_seminorm_le f hf_nonneg hf_mul Λ N w' hpos_w') (hf_nonneg _)
          _ = (f Λ) ^ (n - countN w') * (f N) ^ (countN w' + 1) := by rw [h_rearrange]
          _ = (f Λ) ^ ((n + 1) - countN (Fin.snoc w' true))
              * (f N) ^ (countN (Fin.snoc w' true)) := by
            rw [countN_snoc_true w', h_exp]

end SeminormBound

section WolfEq105

variable {D : ℕ} {R : Type*} [Ring R] {Λ N : Matrix (Fin D) (Fin D) R}

theorem wolf_eq_105 (f : Matrix (Fin D) (Fin D) R → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (hf_add : ∀ x y, f (x + y) ≤ f x + f y) (hf_zero : f 0 = 0)
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    (hDpos : D ≠ 0) (n : ℕ) :
    f ((Λ + N) ^ n) ≤ f (Λ ^ n) +
      (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k))) := by
  haveI : NeZero D := ⟨hDpos⟩
  have hposD : 0 < D := NeZero.pos D
  have h_expand : (Λ + N) ^ n = ∑ w : Fin n → Bool, wordProd Λ N w :=
    add_pow_eq_sum_wordProd Λ N n
  rw [h_expand]
  have h_surviving_sum : (∑ w : Fin n → Bool, wordProd Λ N w) =
      (∑ w ∈ (Finset.univ : Finset (Fin n → Bool)).filter (fun w => countN w < D),
        wordProd Λ N w) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun w hw => ?_)
    by_cases h : countN w < D
    · simp [h]
    · have h_ge : D ≤ countN w := by omega
      have h_zero : wordProd Λ N w = 0 :=
        wordProd_eq_zero_of_N_count_ge_D Λ N hΛ_diag hN_sut w h_ge
      simp [h, h_zero]
  rw [h_surviving_sum]
  have h_wordProd_zero : wordProd Λ N (fun _ : Fin n => false) = Λ ^ n :=
    wordProd_all_false Λ N n
  let allWords : Finset (Fin n → Bool) := Finset.univ
  let surWords := allWords.filter (fun w => countN w < D)
  let kZero := surWords.filter (fun w => countN w = 0)
  let kPos := surWords.filter (fun w => 1 ≤ countN w)
  have h_disjoint_union : surWords = kZero ∪ kPos := by
    ext w;
    simp [kZero, kPos, surWords]
    by_cases hc0 : countN w = 0
    · simp [hc0]
    · have hc1 : 1 ≤ countN w := by omega
      simp [hc0, hc1]
  have h_disjoint : Disjoint kZero kPos := by
    rw [Finset.disjoint_filter]; intro w _ h0 h1; omega
  have h_sum_split : (∑ w ∈ surWords, wordProd Λ N w) =
      (∑ w ∈ kZero, wordProd Λ N w) + (∑ w ∈ kPos, wordProd Λ N w) := by
    rw [h_disjoint_union, Finset.sum_union h_disjoint]
  have h_kZero_singleton : kZero = {(fun _ : Fin n => false)} := by
    ext w; constructor
    · intro hw
      rw [Finset.mem_filter] at hw; rcases hw with ⟨hw_surv, hzero⟩
      have hw_all_false : w = (fun _ : Fin n => false) := by
        ext i
        have hfalse : w i = false := by
          by_contra hnotfalse
          have htrue_val : w i = true := by
            cases hwiv : w i
            · exact (hnotfalse hwiv).elim
            · rfl
          have hi_mem : i ∈ ((Finset.univ : Finset (Fin n)).filter (fun j => w j = true)) := by
            simp [htrue_val]
          have hcard_pos : 0 < countN w := by
            dsimp [countN]; exact Finset.card_pos.mpr ⟨i, hi_mem⟩
          omega
        exact hfalse
      subst hw_all_false; simp
    · intro hw; rw [Finset.mem_singleton] at hw; subst hw
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · simp [countN, hposD]
      · simp [countN]
  have h_kZero_sum : (∑ w ∈ kZero, wordProd Λ N w) = Λ ^ n := by
    rw [h_kZero_singleton, Finset.sum_singleton, h_wordProd_zero]
  rw [h_sum_split, h_kZero_sum]
  have h_triangle : f (Λ ^ n + (∑ w ∈ kPos, wordProd Λ N w)) ≤
      f (Λ ^ n) + f (∑ w ∈ kPos, wordProd Λ N w) := hf_add _ _
  have h_zero_le : f 0 ≤ 0 := by rw [hf_zero]
  have h_rest_subadd : f (∑ w ∈ kPos, wordProd Λ N w) ≤
      (∑ w ∈ kPos, f (wordProd Λ N w)) :=
    Finset.le_sum_of_subadditive f h_zero_le hf_add kPos (fun w => wordProd Λ N w)
  have h_rest_per_word : (∑ w ∈ kPos, f (wordProd Λ N w)) ≤
      (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) := by
    refine Finset.sum_le_sum (fun w hw => ?_)
    have hw_kPos : w ∈ kPos := hw
    have hpos_countN : 1 ≤ countN w := by
      rw [Finset.mem_filter] at hw_kPos; exact hw_kPos.2
    have hbound := wordProd_seminorm_le f hf_nonneg hf_mul Λ N w hpos_countN
    rw [mul_comm]; exact hbound
  have h_fiber_regroup : (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) =
      (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k))) := by
    have h_kPos_eq : kPos = allWords.filter (fun w => 1 ≤ countN w ∧ countN w < D) := by
      ext w; simp [kPos, surWords, allWords]; omega
    rw [h_kPos_eq]
    let fibers (k : ℕ) : Finset (Fin n → Bool) := allWords.filter (fun w => countN w = k)
    let keys := Finset.Icc 1 (min n (D - 1))
    have h_filter_eq_biUnion :
        allWords.filter (fun w => 1 ≤ countN w ∧ countN w < D) = keys.biUnion fibers := by
      ext w; constructor
      · intro hw
        rw [Finset.mem_filter] at hw; rcases hw with ⟨hw_univ, ⟨hk_pos, hk_ltD⟩⟩
        have hk_val_le_n : countN w ≤ n := by
          dsimp [countN]
          calc
            ((Finset.univ : Finset (Fin n)).filter (fun i => w i = true)).card
                ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
            _ = n := Finset.card_fin n
        have hk_mem_keys : countN w ∈ keys := by
          rw [Finset.mem_Icc]
          exact ⟨hk_pos, Nat.le_min.mpr ⟨hk_val_le_n, by omega⟩⟩
        apply Finset.mem_biUnion.mpr
        exact ⟨countN w, hk_mem_keys, by simp [fibers, allWords, hw_univ]⟩
      · intro hw
        rw [Finset.mem_biUnion] at hw; rcases hw with ⟨k, hk_mem, hw_fiber⟩
        rw [Finset.mem_Icc] at hk_mem; rcases hk_mem with ⟨hk_pos, hk_le⟩
        rw [Finset.mem_filter] at hw_fiber; rcases hw_fiber with ⟨hw_univ, hcount⟩
        have hk_ltD : k < D := by
          have hk_le_Dm1 : k ≤ D - 1 := le_trans hk_le (Nat.min_le_right _ _)
          omega
        rw [Finset.mem_filter, hcount]
        exact ⟨hw_univ, hk_pos, hk_ltD⟩
    rw [h_filter_eq_biUnion]
    have h_disjoint_fibers : (keys : Set ℕ).PairwiseDisjoint fibers := by
      intro k₁ hk₁ k₂ hk₂ hne
      have h_disjoint_filt : Disjoint (fibers k₁) (fibers k₂) := by
        rw [Finset.disjoint_filter]; intro w _ h₁ h₂; rw [h₁] at h₂; exact hne h₂
      exact h_disjoint_filt
    rw [Finset.sum_biUnion h_disjoint_fibers]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [Finset.mem_Icc] at hk; rcases hk with ⟨hk_pos, hk_le⟩
    have h_card : (fibers k).card = Nat.choose n k := by
      dsimp [fibers, allWords]; exact card_countN_eq_choose k
    calc
      (∑ w ∈ fibers k, (f N) ^ (countN w) * (f Λ) ^ (n - countN w))
      = (∑ w ∈ fibers k, (f N) ^ k * (f Λ) ^ (n - k)) := by
        refine Finset.sum_congr rfl (fun w hw => ?_)
        rw [Finset.mem_filter] at hw; rcases hw with ⟨_, hw_eq⟩; rw [hw_eq]
      _ = ((fibers k).card : ℝ) * ((f N) ^ k * (f Λ) ^ (n - k)) := by simp
      _ = ((Nat.choose n k : ℕ) : ℝ) * ((f N) ^ k * (f Λ) ^ (n - k)) := by rw [h_card]
      _ = (Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k) := by ring
  calc
    f (Λ ^ n + (∑ w ∈ kPos, wordProd Λ N w)) ≤
      f (Λ ^ n) + f (∑ w ∈ kPos, wordProd Λ N w) := h_triangle
    _ ≤ f (Λ ^ n) + (∑ w ∈ kPos, f (wordProd Λ N w)) := by gcongr
    _ ≤ f (Λ ^ n) + (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) := by gcongr
    _ = f (Λ ^ n) + (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k))) := by rw [h_fiber_regroup]

end WolfEq105

section RingSeminormCorollary

variable {D : ℕ} {R : Type*} [Ring R] {Λ N : Matrix (Fin D) (Fin D) R}

open RingSeminorm

/-- **Wolf Eq. (8.105) for `RingSeminorm`**. -/
theorem wolf_eq_105_seminorm (ν : RingSeminorm (Matrix (Fin D) (Fin D) R))
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    (hDpos : D ≠ 0) (n : ℕ) :
    ν ((Λ + N) ^ n) ≤ ν (Λ ^ n) +
      (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) :=
  wolf_eq_105 ν (apply_nonneg ν) (fun x y => ν.mul_le' x y) (fun x y => ν.add_le' x y)
    (map_zero ν) hΛ_diag hN_sut hDpos n

end RingSeminormCorollary


section WolfEq103

variable {D : ℕ} {R : Type*} [Ring R] {Λ N : Matrix (Fin D) (Fin D) R} {n : ℕ}

open RingSeminorm

/-- **Wolf Eq. (8.103)** with coarse constant \((D-1)n^{D-1}\).

**Scope restriction (natural exponent):** Wolf prints the estimate for every natural \(n\),
but the source exponent \(n-D+1\) is negative when \(n<D-1\). This theorem assumes
\(D-1\le n\). See docs/paper-gaps/wolf_ch8_eq_8_103_negative_exponent.tex. -/
theorem wolf_eq_103 (ν : RingSeminorm (Matrix (Fin D) (Fin D) R))
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    (hDpos : D ≠ 0) (hn_ge : D - 1 ≤ n) (hνΛ : ν Λ ≤ 1) :
    ν ((Λ + N) ^ n) ≤ ν (Λ ^ n) +
      (((D-1 : ℕ) * n ^ (D-1 : ℕ) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1)) *
      max (ν N) ((ν N) ^ (D-1)) := by
  have h_nonneg_νΛ : 0 ≤ ν Λ := apply_nonneg ν _
  have h_nonneg_νN : 0 ≤ ν N := apply_nonneg ν _
  have h_base := wolf_eq_105_seminorm ν hΛ_diag hN_sut hDpos n
  have h_min_eq : min n (D - 1) = D - 1 := Nat.min_eq_right hn_ge
  rw [h_min_eq] at h_base
  by_cases hIcc_empty : Finset.Icc (1 : ℕ) (D - 1) = ∅
  · rw [hIcc_empty, Finset.sum_empty] at h_base
    have h_nonneg_extra : 0 ≤ (((D-1 : ℕ) * n ^ (D-1 : ℕ) : ℕ) : ℝ)
        * (ν Λ) ^ (n - (D-1)) *
      max (ν N) ((ν N) ^ (D-1)) := by positivity
    nlinarith
  · have h_Dm1_pos : 1 ≤ D - 1 := by
      contrapose! hIcc_empty
      exact Finset.Icc_eq_empty_of_lt (by omega)
    have h_card : (Finset.Icc 1 (D - 1)).card = D - 1 := by
      simp
    have h_cardℝ : ((Finset.Icc 1 (D - 1)).card : ℝ) = (D - 1 : ℝ) := by
      have hD1' : 1 ≤ D := by omega
      rw [h_card, Nat.cast_sub hD1', Nat.cast_one]
    have h_term_bound (k : ℕ) (hk : k ∈ Finset.Icc 1 (D - 1)) :
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k)) ≤
        ((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1)) * (ν Λ) ^ (n - (D-1)) := by
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
      have h_choose : (Nat.choose n k : ℝ) ≤ ((n ^ (D-1 : ℕ) : ℕ) : ℝ) := by
        have h_choose_nat : Nat.choose n k ≤ n ^ k := Nat.choose_le_pow n k
        have h_pow_mono : n ^ k ≤ n ^ (D-1) := by
          by_cases hn0 : n = 0
          · subst hn0
            have : D = 1 := by omega
            subst this
            have : Finset.Icc (1 : ℕ) 0 = ∅ := by decide
            rw [this] at hk
            simp at hk
          · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
            exact Nat.pow_le_pow_right hnpos hk2
        exact mod_cast h_choose_nat.trans h_pow_mono
      have h_nuN_pow : (ν N) ^ k ≤ max (ν N) ((ν N) ^ (D-1)) :=
        pow_le_max_of_one_le h_nonneg_νN hk1 hk2
      have h_nuΛ_pow : (ν Λ) ^ (n - k) ≤ (ν Λ) ^ (n - (D - 1)) := by
        have h_exp_le : n - (D - 1) ≤ n - k := by omega
        exact pow_le_pow_of_le_one h_nonneg_νΛ hνΛ h_exp_le
      have h_nonneg_choose : 0 ≤ (Nat.choose n k : ℝ) := by exact mod_cast Nat.zero_le _
      have h_nonneg_npow : 0 ≤ ((n ^ (D-1 : ℕ) : ℕ) : ℝ) := by exact mod_cast Nat.zero_le _
      have h_prod : ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k)) ≤
          (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1))
            * (ν Λ) ^ (n - (D-1))) := by
        calc
          ((Nat.choose n k : ℝ) * (ν N) ^ k) * (ν Λ) ^ (n - k) ≤
              (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1)))
                * (ν Λ) ^ (n - k) := by
            gcongr
          _ ≤ (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1)))
              * (ν Λ) ^ (n - (D-1)) := by
            gcongr
      exact h_prod
    have h_sum_bound : (∑ k ∈ Finset.Icc 1 (D - 1),
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) ≤
        (((D-1 : ℕ) * n ^ (D-1 : ℕ) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1)) *
        max (ν N) ((ν N) ^ (D-1)) := by
      have hD1 : 1 ≤ D := by omega
      calc
        (∑ k ∈ Finset.Icc 1 (D - 1),
            ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) ≤
            (∑ k ∈ Finset.Icc 1 (D - 1),
              (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1))
                * (ν Λ) ^ (n - (D-1)))) :=
          Finset.sum_le_sum (fun k hk => h_term_bound k hk)
        _ = ((Finset.Icc 1 (D - 1)).card : ℝ) *
            (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1))
              * (ν Λ) ^ (n - (D-1))) := by
          simp
        _ = (D - 1 : ℝ) * (((n ^ (D-1 : ℕ) : ℕ) : ℝ) * max (ν N) ((ν N) ^ (D-1))
              * (ν Λ) ^ (n - (D-1))) := by
          rw [h_cardℝ]
        _ = (((D-1 : ℕ) * n ^ (D-1 : ℕ) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1))
              * max (ν N) ((ν N) ^ (D-1)) := by
          rw [Nat.cast_mul, Nat.cast_sub hD1, Nat.cast_one, Nat.cast_pow]
          ring
    nlinarith

end WolfEq103

section WolfEq103Refined

variable {D : ℕ} {R : Type*} [Ring R] {Λ N : Matrix (Fin D) (Fin D) R} {n : ℕ}

open RingSeminorm

/-- **Wolf Eq. (8.103) with refined binomial-coefficient constant**.

Assumes \(2(D-1)\le n\), which implies \(D-1\le n/2\), monotonicity
of the binomial coefficient, and the tighter bound
\((D-1)\binom{n}{D-1}\) instead of \((D-1)n^{D-1}\). -/
theorem wolf_eq_103_refined (ν : RingSeminorm (Matrix (Fin D) (Fin D) R))
    (hΛ_diag : IsDiag Λ) (hN_sut : IsStrictlyUpperTriangular N)
    (hDpos : D ≠ 0) (hn_ge : 2 * (D - 1) ≤ n) (hνΛ : ν Λ ≤ 1) :
    ν ((Λ + N) ^ n) ≤ ν (Λ ^ n) +
      (((D-1 : ℕ) * Nat.choose n (D-1) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1)) *
      max (ν N) ((ν N) ^ (D-1)) := by
  have h_nonneg_νΛ : 0 ≤ ν Λ := apply_nonneg ν _
  have h_nonneg_νN : 0 ≤ ν N := apply_nonneg ν _
  have h_Dm1_le_n : D - 1 ≤ n := by omega
  have h_base := wolf_eq_105_seminorm ν hΛ_diag hN_sut hDpos n
  have h_min_eq : min n (D - 1) = D - 1 := Nat.min_eq_right h_Dm1_le_n
  rw [h_min_eq] at h_base
  by_cases hIcc_empty : Finset.Icc (1 : ℕ) (D - 1) = ∅
  · rw [hIcc_empty, Finset.sum_empty] at h_base
    have h_nonneg_extra : 0 ≤ (((D-1 : ℕ) * Nat.choose n (D-1) : ℕ) : ℝ)
        * (ν Λ) ^ (n - (D-1)) *
      max (ν N) ((ν N) ^ (D-1)) := by positivity
    nlinarith
  · have h_Dm1_pos : 1 ≤ D - 1 := by
      contrapose! hIcc_empty
      exact Finset.Icc_eq_empty_of_lt (by omega)
    have h_card : (Finset.Icc 1 (D - 1)).card = D - 1 := by
      simp
    have h_cardℝ : ((Finset.Icc 1 (D - 1)).card : ℝ) = (D - 1 : ℝ) := by
      have hD1' : 1 ≤ D := by omega
      rw [h_card, Nat.cast_sub hD1', Nat.cast_one]
    -- Refined bound: Nat.choose n k ≤ Nat.choose n (D-1) for k ≤ D-1
    -- The binomial coefficients increase up to the middle index.
    have h_choose_refined (k : ℕ) (hk : k ∈ Finset.Icc 1 (D - 1)) :
        Nat.choose n k ≤ Nat.choose n (D - 1) := by
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
      obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hk2
      have h_helper : ∀ d', 2 * (k + d') ≤ n → Nat.choose n k ≤ Nat.choose n (k + d') := by
        intro d'
        induction' d' with d' ih
        · intro; rfl
        · intro hbound
          have hbound' : 2 * (k + d') ≤ n := by omega
          have hk_d'_lt_half : k + d' < n / 2 := by omega
          have hstep : Nat.choose n (k + d') ≤ Nat.choose n (k + d' + 1) :=
            Nat.choose_le_succ_of_lt_half_left hk_d'_lt_half
          have h_eq : k + d' + 1 = k + (d' + 1) := by omega
          rw [← h_eq]
          exact (ih hbound').trans hstep
      have h_total_bound : 2 * (k + d) ≤ n := by
        omega
      simpa [hd] using h_helper d h_total_bound
    have h_term_bound (k : ℕ) (hk : k ∈ Finset.Icc 1 (D - 1)) :
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k)) ≤
        ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1)) * (ν Λ) ^ (n - (D-1))) := by
      rcases Finset.mem_Icc.mp hk with ⟨hk1, hk2⟩
      have h_choose : (Nat.choose n k : ℝ) ≤ (Nat.choose n (D-1) : ℝ) :=
        mod_cast h_choose_refined k hk
      have h_nuN_pow : (ν N) ^ k ≤ max (ν N) ((ν N) ^ (D-1)) :=
        pow_le_max_of_one_le h_nonneg_νN hk1 hk2
      have h_nuΛ_pow : (ν Λ) ^ (n - k) ≤ (ν Λ) ^ (n - (D - 1)) := by
        have h_exp_le : n - (D - 1) ≤ n - k := by omega
        exact pow_le_pow_of_le_one h_nonneg_νΛ hνΛ h_exp_le
      have h_prod : ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k)) ≤
          ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1)) * (ν Λ) ^ (n - (D-1))) := by
        calc
          ((Nat.choose n k : ℝ) * (ν N) ^ k) * (ν Λ) ^ (n - k) ≤
              ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1))) * (ν Λ) ^ (n - k) := by
            gcongr
          _ ≤ ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1)))
              * (ν Λ) ^ (n - (D-1)) := by
            gcongr
      exact h_prod
    have h_sum_bound : (∑ k ∈ Finset.Icc 1 (D - 1),
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) ≤
        (((D-1 : ℕ) * Nat.choose n (D-1) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1)) *
        max (ν N) ((ν N) ^ (D-1)) := by
      have hD1 : 1 ≤ D := by omega
      calc
        (∑ k ∈ Finset.Icc 1 (D - 1),
            ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) ≤
            (∑ k ∈ Finset.Icc 1 (D - 1),
              ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1)) * (ν Λ) ^ (n - (D-1)))) :=
          Finset.sum_le_sum (fun k hk => h_term_bound k hk)
        _ = ((Finset.Icc 1 (D - 1)).card : ℝ) *
            ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1)) * (ν Λ) ^ (n - (D-1))) := by
          simp
        _ = (D - 1 : ℝ) * ((Nat.choose n (D-1) : ℝ) * max (ν N) ((ν N) ^ (D-1))
              * (ν Λ) ^ (n - (D-1))) := by
          rw [h_cardℝ]
        _ = (((D-1 : ℕ) * Nat.choose n (D-1) : ℕ) : ℝ) * (ν Λ) ^ (n - (D-1))
              * max (ν N) ((ν N) ^ (D-1)) := by
          rw [Nat.cast_mul, Nat.cast_sub hD1, Nat.cast_one]
          ring
    nlinarith

end WolfEq103Refined

end Matrix
