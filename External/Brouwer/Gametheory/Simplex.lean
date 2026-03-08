import Mathlib

--open Classical

/-
We use S to denote a mixed stratage
-/

variable (α : Type*) [Fintype α] [DecidableEq α]

namespace stdSimplex
variable (k : Type*) [CommRing k] [LinearOrder k] [IsStrictOrderedRing k] (α : Type*) [Fintype α]

instance funlike [DecidableEq α] : FunLike (stdSimplex k α) α k where
  coe := Subtype.val
  coe_injective' := Subtype.val_injective

omit [IsStrictOrderedRing k] in
lemma funlike_eval1 (f : stdSimplex k α)  : f = f.val := rfl

omit [IsStrictOrderedRing k] in
lemma funlike_eval2 [DecidableEq α] (f : stdSimplex k α) (x : α) : f.val x = f x := rfl

variable {k α} in
abbrev pure [DecidableEq α] (i : α) : stdSimplex k α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

variable {k α} in
lemma pure_eval_eq [DecidableEq α] {i j: α} (h : i=j):  pure i j = (1:k) := by
  unfold pure;
  rw [<-funlike_eval2]
  simp [h]


variable {k α} in
lemma pure_eval_neq [DecidableEq α] {i j: α} (h : ¬ i=j):  pure i j = (0:k) := by
  unfold pure;
  rw [<-funlike_eval2]
  simp [h]


noncomputable instance SInhabited_of_Inhabited [DecidableEq α] [Inhabited α]: Inhabited (stdSimplex k α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [DecidableEq α] [Fintype α] [Inhabited α]: Nonempty (stdSimplex k α) := Nonempty.intro (default : stdSimplex k α)

variable {k α} in
lemma wsum_magic_ineq [DecidableEq α] [LinearOrder k] [IsOrderedCancelAddMonoid k] [PosMulMono k] [PosMulStrictMono k] {σ : stdSimplex k α} {f : α → k} {c : k} :
  ∑ i : α, (σ i) *  f i = c → ∃ i, 0 < σ i ∧ f i ≤ c := by
    intro H1
    by_contra H2
    push_neg at H2
    have h_exists_pos : ∃ i, 0 < σ i := by
      by_contra h_all_zero
      push_neg at h_all_zero
      have h_all_eq_zero : ∀ i, σ i = 0 := by
        intro i
        exact le_antisymm (h_all_zero i) (σ.2.1 i)
      have h_sum_zero : ∑ i, σ i = 0 := by simp [h_all_eq_zero]
      have h_sum_one : ∑ i, σ i = 1 := σ.2.2
      rw [h_sum_zero] at h_sum_one
      exact zero_ne_one h_sum_one
    obtain ⟨i₀, hi₀⟩ := h_exists_pos
    have h_ge : c < ∑ i, σ i * f i := by
      have h_sum_c : ∑ i, σ i * c = c := by
        have h_sum_eq_one : ∑ i, σ i = 1 := σ.2.2
        rw [← Finset.sum_mul, h_sum_eq_one, one_mul]
      rw [← h_sum_c]
      apply Finset.sum_lt_sum
      · intro i _
        by_cases h_pos : 0 < σ i
        · have h_fi_gt_c : c < f i := H2 i h_pos
          exact mul_le_mul_of_nonneg_left (le_of_lt h_fi_gt_c) (σ.2.1 i)
        · have h_zero : σ i = 0 := le_antisymm (le_of_not_gt h_pos) (σ.2.1 i)
          simp [h_zero]
      · use i₀, Finset.mem_univ i₀
        have h_fi₀_gt_c : c < f i₀ := H2 i₀ hi₀
        exact mul_lt_mul_of_pos_left h_fi₀_gt_c hi₀
    rw [H1] at h_ge
    exact lt_irrefl c h_ge

end stdSimplex


abbrev S:= stdSimplex ℝ α

namespace S

variable {α : Type*} [Fintype α] [DecidableEq α]

/-
@[simp]
noncomputable def pure (i : α) : S α  := ⟨fun j => if i=j then 1 else 0,
 by {
  constructor
  . {
    intro j
    by_cases H: i=j
    repeat simp [H]
  }
  . simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  }⟩

noncomputable instance SInhabited_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Inhabited (S α) where
  default := pure (default : α)


noncomputable instance SNonempty_of_Inhabited {α : Type*} [Fintype α] [Inhabited α]: Nonempty (S α) := Nonempty.intro (default : S α)

-/
