/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
/-!
# Upper-triangular power bound -- Wolf Eqs. (8.103) and (8.105)
-/
open Matrix
open scoped BigOperators

namespace Matrix

section TriangularDefinitions
variable {D : ℕ} {R : Type*} [Semiring R]
def IsDiagonal (M : Matrix (Fin D) (Fin D) R) : Prop := ∀ i j, i ≠ j → M i j = 0
def IsStrictlyUpperTriangular (M : Matrix (Fin D) (Fin D) R) : Prop :=
  ∀ (i j : Fin D), (i : ℕ) ≥ (j : ℕ) → M i j = 0
end TriangularDefinitions

section EntryLemmas
variable {D : ℕ} {R : Type*} [Semiring R]
lemma IsDiagonal.mul_apply (hΛ : IsDiagonal Λ) (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (Λ * P) i j = Λ i i * P i j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single i
  · intro k _ hk_ne; rw [hΛ i k (Ne.symm hk_ne), zero_mul]
  · intro h; exfalso; exact h (Finset.mem_univ i)

lemma IsDiagonal.mul_apply_right (hΛ : IsDiagonal Λ) (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (P * Λ) i j = P i j * Λ j j := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_single j
  · intro k _ hk_ne; rw [hΛ k j hk_ne, mul_zero]
  · intro h; exfalso; exact h (Finset.mem_univ j)

lemma IsStrictlyUpperTriangular.mul_apply (hN : IsStrictlyUpperTriangular N)
    (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (N * P) i j = Finset.sum
      ((Finset.univ : Finset (Fin D)).filter (fun (k : Fin D) => (i : ℕ) < (k : ℕ)))
      (λ k => N i k * P k j) := by
  rw [Matrix.mul_apply]
  apply (Finset.sum_subset (Finset.filter_subset (fun (k : Fin D) => (i : ℕ) < (k : ℕ)) _) ?_).symm
  intro k hk_univ hk_not_mem
  have h_not_lt : ¬ ((i : ℕ) < (k : ℕ)) := by
    intro hlt; apply hk_not_mem; simpa [Finset.mem_filter, hk_univ] using hlt
  have hge : (i : ℕ) ≥ (k : ℕ) := by omega
  simp [hN i k hge]

lemma IsStrictlyUpperTriangular.mul_apply_right (hN : IsStrictlyUpperTriangular N)
    (P : Matrix (Fin D) (Fin D) R) (i j : Fin D) :
    (P * N) i j = Finset.sum
      ((Finset.univ : Finset (Fin D)).filter (fun (k : Fin D) => (k : ℕ) < (j : ℕ)))
      (λ k => P i k * N k j) := by
  rw [Matrix.mul_apply]
  apply (Finset.sum_subset (Finset.filter_subset (fun (k : Fin D) => (k : ℕ) < (j : ℕ)) _) ?_).symm
  intro k hk_univ hk_not_mem
  have h_not_lt : ¬ ((k : ℕ) < (j : ℕ)) := by
    intro hlt; apply hk_not_mem; simpa [Finset.mem_filter, hk_univ] using hlt
  have hge : (k : ℕ) ≥ (j : ℕ) := by omega
  simp [hN k j hge]
end EntryLemmas

section WordProduct
variable {D : ℕ} {R : Type*} [Semiring R]
def wordProd (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool) :
    Matrix (Fin D) (Fin D) R :=
  (List.ofFn (fun i : Fin n => cond (w i) N Λ)).prod

@[simp] lemma wordProd_zero (Λ N : Matrix (Fin D) (Fin D) R) :
    wordProd Λ N (λ i => False.elim (i.elim0)) = (1 : Matrix (Fin D) (Fin D) R) := by
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
    -- Now: (∑ w, wordProd w * Λ) + (∑ w, wordProd w * N) = ∑ w', wordProd w'
    -- Use wordProd_snoc' to rewrite each term
    have h_split : ((∑ w : Fin n → Bool, (wordProd Λ N w) * Λ) +
        (∑ w : Fin n → Bool, (wordProd Λ N w) * N)) =
        ((∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true))) := by
      simp [wordProd_snoc']
    rw [h_split]
    -- Now need: sum_snoc_false + sum_snoc_true = sum_all
    -- Use the bijection (Fin n → Bool) × Bool ≃ Fin (n+1) → Bool
    -- via Finset.univ for product type
    have h_sum_eq : (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true)) =
        ∑ w' : Fin (n + 1) → Bool, wordProd Λ N w' := by
      calc
        (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w false)) +
            (∑ w : Fin n → Bool, wordProd Λ N (Fin.snoc w true))
            = Finset.sum (Finset.univ : Finset (Fin n → Bool))
                (λ w => (wordProd Λ N (Fin.snoc w false) + wordProd Λ N (Fin.snoc w true))) := by
          simp [Finset.sum_add_distrib]
        _ = Finset.sum (Finset.univ : Finset (Fin n → Bool))
              (λ w => Finset.sum (Finset.univ : Finset Bool) (λ b => wordProd Λ N (Fin.snoc w b))) := by
          refine Finset.sum_congr rfl (λ w hw => ?_)
          simp [Finset.sum_insert, Finset.sum_singleton, add_comm]
        _ = Finset.sum (Finset.univ : Finset ((Fin n → Bool) × Bool))
              (λ (p : (Fin n → Bool) × Bool) => wordProd Λ N (Fin.snoc p.1 p.2)) :=
          (Finset.sum_product (s := Finset.univ) (t := Finset.univ)
            (λ (p : (Fin n → Bool) × Bool) => wordProd Λ N (Fin.snoc p.1 p.2))).symm
        _ = ∑ w' : Fin (n + 1) → Bool, wordProd Λ N w' := by
          -- Bijection: (Fin n → Bool) × Bool ≃ Fin (n+1) → Bool via Fin.snoc
          -- Both sides sum over Finset.univ; use Finset.sum_bij
          apply (Finset.sum_bij
            (λ (p : (Fin n → Bool) × Bool) _ => (Fin.snoc p.1 p.2 : Fin (n+1) → Bool))
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

def countN {n : ℕ} (w : Fin n → Bool) : ℕ :=
  ((Finset.univ : Finset (Fin n)).filter (λ i => w i = true)).card

@[simp] lemma countN_zero {n : ℕ} : countN (λ _ : Fin n => false) = 0 := by simp [countN]

lemma countN_snoc_false_aux {n : ℕ} (w : Fin n → Bool) (i : Fin (n+1)) :
    ((Fin.snoc w false : Fin (n+1) → Bool) i = true) ↔ ∃ (j : Fin n), Fin.castSucc j = i ∧ w j = true := by
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
  -- Sets are equal via the Fin.castSucc embedding
  have h_eq : (Finset.univ : Finset (Fin (n+1))).filter (λ i => (Fin.snoc w false : Fin (n+1) → Bool) i = true) =
      ((Finset.univ : Finset (Fin n)).filter (λ i => w i = true)).map
      ⟨Fin.castSucc, Fin.castSucc_injective (n := n)⟩ := by
    ext i
    simp [countN_snoc_false_aux w i]
    -- The goal reduces to (∃ j, j.castSucc = i ∧ w j = true) ↔ (∃ a, w a = true ∧ a.castSucc = i)
    -- which is true by permuting the conjunction
    constructor
    · rintro ⟨j, hj, hw⟩; exact ⟨j, hw, hj⟩
    · rintro ⟨a, hw, ha⟩; exact ⟨a, ha, hw⟩
  rw [h_eq, Finset.card_map]

lemma countN_snoc_true_aux {n : ℕ} (w : Fin n → Bool) (i : Fin (n+1)) :
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
  have h_eq : (Finset.univ : Finset (Fin (n+1))).filter (λ i => (Fin.snoc w true : Fin (n+1) → Bool) i = true) =
      (((Finset.univ : Finset (Fin n)).filter (λ i => w i = true)).map
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
  have h_disjoint : Disjoint (((Finset.univ : Finset (Fin n)).filter (λ i => w i = true)).map
      ⟨Fin.castSucc, Fin.castSucc_injective (n := n)⟩) ({Fin.last n} : Finset (Fin (n+1))) := by
    apply Finset.disjoint_singleton_right.mpr
    intro h; rw [Finset.mem_map] at h
    rcases h with ⟨j, _, h⟩
    exact Fin.castSucc_ne_last j h
  rw [Finset.card_union_of_disjoint h_disjoint, Finset.card_map, Finset.card_singleton]

lemma wordProd_apply_eq_zero_of_shift [NeZero D] (Λ N : Matrix (Fin D) (Fin D) R)
    (hΛ_diag : IsDiagonal Λ) (hN_sut : IsStrictlyUpperTriangular N)
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
    · -- b = false
      simp
      rw [IsDiagonal.mul_apply_right hΛ_diag (wordProd Λ N w') i j]
      have hshift' : (j : ℕ) < (i : ℕ) + countN w' := by
        simpa [countN_snoc_false w', hw_eq] using hshift
      rw [ih w' i j hshift', zero_mul]
    · -- b = true
      simp
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
    (hΛ_diag : IsDiagonal Λ) (hN_sut : IsStrictlyUpperTriangular N)
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

end Matrix

section CountCardinality

variable {n : ℕ}

def wordToSupport (w : Fin n → Bool) : Finset (Fin n) :=
  (Finset.univ : Finset (Fin n)).filter (λ i => w i = true)

@[simp] lemma wordToSupport_card (w : Fin n → Bool) : (wordToSupport w).card = countN w := rfl

lemma wordToSupport_injective :
    Function.Injective (wordToSupport : (Fin n → Bool) → Finset (Fin n)) := by
  intro w1 w2 h; ext i
  have h_mem : i ∈ wordToSupport w1 ↔ i ∈ wordToSupport w2 := by rw [h]
  simp [wordToSupport] at h_mem ⊢; exact h_mem

lemma card_countN_eq_choose (k : ℕ) :
    ((Finset.univ : Finset (Fin n → Bool)).filter (λ w => countN w = k)).card = Nat.choose n k := by
  let S := ((Finset.univ : Finset (Fin n → Bool)).filter (λ w => countN w = k))
  let img := S.image wordToSupport
  have h_card_image : img.card = S.card := Finset.card_image_of_injective S wordToSupport_injective
  have h_img_eq_powerset : img = Finset.powersetCard k (Finset.univ : Finset (Fin n)) := by
    ext s; constructor
    · intro hs; rw [Finset.mem_image] at hs; rcases hs with ⟨w, hw, rfl⟩
      rw [Finset.mem_filter] at hw; rcases hw with ⟨_, hcount⟩
      rw [Finset.mem_powersetCard]
      exact ⟨Finset.filter_subset _ _, by rw [wordToSupport_card, hcount]⟩
    · intro hs; rw [Finset.mem_powersetCard] at hs; rcases hs with ⟨hs_sub, hs_card⟩
      let w : Fin n → Bool := λ i => i ∈ s
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
    wordProd Λ N (λ _ : Fin n => false) = Λ ^ n := by
  induction' n with k ih
  · simp [wordProd]
  · have h_snoc : (λ _ : Fin (k+1) => false) = Fin.snoc (λ _ : Fin k => false) false := by
      ext i; simp [Fin.snoc]
    rw [h_snoc, wordProd_snoc']; simp [ih, pow_succ]

end WordProdLemma

section SeminormBound

variable {D : ℕ} {R : Type*} [Ring R]

lemma wordProd_seminorm_le (f : Matrix (Fin D) (Fin D) R → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (hf1 : f 1 ≤ 1)
    (Λ N : Matrix (Fin D) (Fin D) R) {n : ℕ} (w : Fin n → Bool) :
    f (wordProd Λ N w) ≤ (f Λ) ^ (n - countN w) * (f N) ^ (countN w) := by
  induction' n with n ih generalizing Λ N
  · have h0 : countN w = 0 := by dsimp [countN]; simp
    have h1 : wordProd Λ N w = 1 := by simp [wordProd]
    rw [h0, h1, Nat.sub_self, pow_zero, pow_zero, one_mul]; exact hf1
  · let w' := Fin.init w; let b := w (Fin.last n)
    have hw_eq : w = Fin.snoc w' b := (Fin.snoc_init_self w).symm
    rw [hw_eq, wordProd_snoc']
    have h_le : countN w' ≤ n := by
      dsimp [countN]
      calc
        ((Finset.univ : Finset (Fin n)).filter (λ i => w' i = true)).card
            ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_filter_le _ _
        _ = n := Finset.card_fin n
    rcases b with (rfl | rfl)
    · simp
      have h_exp : (n - countN w') + 1 = (n + 1) - countN w' := by omega
      have h_rearrange : ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f Λ
          = (f Λ) ^ ((n - countN w') + 1) * (f N) ^ (countN w') := by
        ring
      calc
        f (wordProd Λ N w' * Λ) ≤ f (wordProd Λ N w') * f Λ := hf_mul _ _
        _ ≤ ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f Λ :=
          mul_le_mul_of_nonneg_right (ih Λ N w') (hf_nonneg _)
        _ = (f Λ) ^ ((n - countN w') + 1) * (f N) ^ (countN w') := by rw [h_rearrange]
        _ = (f Λ) ^ ((n + 1) - countN w') * (f N) ^ (countN w') := by rw [h_exp]
        _ = (f Λ) ^ ((n + 1) - countN (Fin.snoc w' false)) * (f N) ^ (countN (Fin.snoc w' false)) := by
          rw [countN_snoc_false w']
    · simp
      have h_exp : n - countN w' = (n + 1) - (countN w' + 1) := by omega
      have h_rearrange : ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f N
          = (f Λ) ^ (n - countN w') * (f N) ^ (countN w' + 1) := by
        ring
      calc
        f (wordProd Λ N w' * N) ≤ f (wordProd Λ N w') * f N := hf_mul _ _
        _ ≤ ((f Λ) ^ (n - countN w') * (f N) ^ (countN w')) * f N :=
          mul_le_mul_of_nonneg_right (ih Λ N w') (hf_nonneg _)
        _ = (f Λ) ^ (n - countN w') * (f N) ^ (countN w' + 1) := by rw [h_rearrange]
        _ = (f Λ) ^ ((n + 1) - countN (Fin.snoc w' true)) * (f N) ^ (countN (Fin.snoc w' true)) := by
          rw [countN_snoc_true w', h_exp]

end SeminormBound

section WolfEq105

variable {D : ℕ} {R : Type*} [Ring R]

/-- **Wolf Eq. (8.105)**. -/
theorem wolf_eq_105 (f : Matrix (Fin D) (Fin D) R → ℝ)
    (hf_nonneg : ∀ x, 0 ≤ f x) (hf_mul : ∀ x y, f (x * y) ≤ f x * f y)
    (hf_add : ∀ x y, f (x + y) ≤ f x + f y) (hf_zero : f 0 = 0)
    (hf1 : f 1 ≤ 1)
    (hΛ_diag : IsDiagonal Λ) (hN_sut : IsStrictlyUpperTriangular N)
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
      (∑ w ∈ (Finset.univ : Finset (Fin n → Bool)).filter (λ w => countN w < D),
        wordProd Λ N w) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (λ w hw => ?_)
    by_cases h : countN w < D
    · simp [h]
    · have h_ge : D ≤ countN w := by omega
      have h_zero : wordProd Λ N w = 0 :=
        wordProd_eq_zero_of_N_count_ge_D Λ N hΛ_diag hN_sut w h_ge
      simp [h, h_zero]
  rw [h_surviving_sum]
  have h_wordProd_zero : wordProd Λ N (λ _ : Fin n => false) = Λ ^ n :=
    wordProd_all_false Λ N n
  let allWords : Finset (Fin n → Bool) := Finset.univ
  let surWords := allWords.filter (λ w => countN w < D)
  let kZero := surWords.filter (λ w => countN w = 0)
  let kPos := surWords.filter (λ w => 1 ≤ countN w)
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
  have h_kZero_singleton : kZero = {(λ _ : Fin n => false)} := by
    ext w; constructor
    · intro hw
      rw [Finset.mem_filter] at hw; rcases hw with ⟨hw_surv, hzero⟩
      have hw_all_false : w = (λ _ : Fin n => false) := by
        ext i
        have hfalse : w i = false := by
          by_contra hnotfalse
          have htrue_val : w i = true := by
            cases hwiv : w i
            · exact (hnotfalse hwiv).elim
            · rfl
          have hi_mem : i ∈ ((Finset.univ : Finset (Fin n)).filter (λ j => w j = true)) := by
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
    Finset.le_sum_of_subadditive f h_zero_le hf_add kPos (λ w => wordProd Λ N w)
  have h_rest_per_word : (∑ w ∈ kPos, f (wordProd Λ N w)) ≤
      (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) := by
    refine Finset.sum_le_sum (λ w hw => ?_)
    have hbound := wordProd_seminorm_le f hf_nonneg hf_mul hf1 Λ N w
    rw [mul_comm]; exact hbound
  -- fiber regrouping: group by countN value
  have h_fiber_regroup : (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) =
      (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k))) := by
    have h_kPos_eq : kPos = allWords.filter (λ w => 1 ≤ countN w ∧ countN w < D) := by
      ext w; simp [kPos, surWords, allWords]; omega
    rw [h_kPos_eq]
    let fibers (k : ℕ) : Finset (Fin n → Bool) := allWords.filter (λ w => countN w = k)
    let keys := Finset.Icc 1 (min n (D - 1))
    have h_filter_eq_biUnion :
        allWords.filter (λ w => 1 ≤ countN w ∧ countN w < D) = keys.biUnion fibers := by
      ext w; constructor
      · intro hw
        rw [Finset.mem_filter] at hw; rcases hw with ⟨hw_univ, ⟨hk_pos, hk_ltD⟩⟩
        have hk_val_le_n : countN w ≤ n := by
          dsimp [countN]
          calc
            ((Finset.univ : Finset (Fin n)).filter (λ i => w i = true)).card
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
    refine Finset.sum_congr rfl (λ k hk => ?_)
    rw [Finset.mem_Icc] at hk; rcases hk with ⟨hk_pos, hk_le⟩
    have h_card : (fibers k).card = Nat.choose n k := by
      dsimp [fibers, allWords]; exact card_countN_eq_choose k
    calc
      (∑ w ∈ fibers k, (f N) ^ (countN w) * (f Λ) ^ (n - countN w))
      = (∑ w ∈ fibers k, (f N) ^ k * (f Λ) ^ (n - k)) := by
        refine Finset.sum_congr rfl (λ w hw => ?_)
        rw [Finset.mem_filter] at hw; rcases hw with ⟨_, hw_eq⟩; rw [hw_eq]
      _ = ((fibers k).card : ℝ) * ((f N) ^ k * (f Λ) ^ (n - k)) := by simp
      _ = ((Nat.choose n k : ℕ) : ℝ) * ((f N) ^ k * (f Λ) ^ (n - k)) := by rw [h_card]
      _ = (Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k) := by ring
  -- assemble final inequality
  calc
    f (Λ ^ n + (∑ w ∈ kPos, wordProd Λ N w)) ≤ f (Λ ^ n) + f (∑ w ∈ kPos, wordProd Λ N w) := h_triangle
    _ ≤ f (Λ ^ n) + (∑ w ∈ kPos, f (wordProd Λ N w)) := by gcongr
    _ ≤ f (Λ ^ n) + (∑ w ∈ kPos, (f N) ^ (countN w) * (f Λ) ^ (n - countN w)) := by gcongr
    _ = f (Λ ^ n) + (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (f N) ^ k * (f Λ) ^ (n - k))) := by rw [h_fiber_regroup]

end WolfEq105

section RingSeminormCorollary

variable {D : ℕ} {R : Type*} [Ring R]

open RingSeminorm

/-- **Wolf Eq. (8.105) for `RingSeminorm`**. -/
theorem wolf_eq_105_seminorm (ν : RingSeminorm (Matrix (Fin D) (Fin D) R))
    (hν_one : ν 1 ≤ 1)
    (hΛ_diag : IsDiagonal Λ) (hN_sut : IsStrictlyUpperTriangular N)
    (hDpos : D ≠ 0) (n : ℕ) :
    ν ((Λ + N) ^ n) ≤ ν (Λ ^ n) +
      (∑ k ∈ Finset.Icc 1 (min n (D - 1)),
        ((Nat.choose n k : ℝ) * (ν N) ^ k * (ν Λ) ^ (n - k))) :=
  wolf_eq_105 ν (apply_nonneg ν) (λ x y => ν.mul_le' x y) (λ x y => ν.add_le' x y)
    (map_zero ν) hν_one hΛ_diag hN_sut hDpos n

end RingSeminormCorollary
