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
