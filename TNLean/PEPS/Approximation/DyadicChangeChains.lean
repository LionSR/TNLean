/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.DyadicTreatedFrameBoundary

/-!
# Chains of changes

The protocol of Proposition 7.1 of the polynomial-PEPS manuscript passes through each
large-scale repainting by a fixed number of changes, each changing one or two sheets of the
memory (`06-geometry.tex`, lines 142–221, 328–339 and 572–583). This file collects the
bookkeeping: chains of a given number of steps of a relation, the chains of point treatments
that add the marks of a bulk operation one at a time and remove them again, and the lift of a
chain of changes of one sheet, or of the main and one auxiliary sheet, to the memory.

* `IsStepChain` : a chain of `n` steps of a relation;
* `IsStepChain.treat`, `IsStepChain.untreat` : adding and removing the marks of a list;
* `isStepChain_main`, `isStepChain_aux` : the lift of a chain of changes of one sheet;
* `hasSourceBoundedChange_of_hasPairChange` : the lift of a change of the main sheet and one
  auxiliary sheet.

## References

* Polynomial-PEPS manuscript (September 24, 2026), §7, `06-geometry.tex`: the point treatment
  (lines 328–339) and the changes of the memory (lines 572–583).
-/

noncomputable section

namespace TNLean.PEPS.Approximation

open EncodedFrame PairEffect

/-- **A chain of `n` steps.** A sequence of `n + 1` states from `a` to `b`, each related to the
next by `Rel`. -/
def IsStepChain {α : Type*} (Rel : α → α → Prop) (n : ℕ) (a b : α) : Prop :=
  ∃ seg : ℕ → α, seg 0 = a ∧ seg n = b ∧ ∀ j < n, Rel (seg j) (seg (j + 1))

namespace IsStepChain

variable {α β : Type*} {Rel : α → α → Prop} {Rel' : β → β → Prop} {a b c : α} {m n : ℕ}

/-- Every state has a chain of zero steps to itself. -/
lemma refl (a : α) : IsStepChain Rel 0 a a :=
  ⟨fun _ => a, rfl, rfl, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

/-- A related pair gives a chain of one step. -/
theorem single (h : Rel a b) : IsStepChain Rel 1 a b := by
  refine ⟨fun j => if j = 0 then a else b, rfl, rfl, fun j hj => ?_⟩
  obtain rfl : j = 0 := by omega
  simpa using h

/-- Concatenate chains with a common endpoint, adding their lengths. -/
theorem trans (h₁ : IsStepChain Rel m a b) (h₂ : IsStepChain Rel n b c) :
    IsStepChain Rel (m + n) a c := by
  obtain ⟨s₁, a₁, b₁, h₁⟩ := h₁
  obtain ⟨s₂, a₂, b₂, h₂⟩ := h₂
  refine ⟨fun j => if j ≤ m then s₁ j else s₂ (j - m), by simp [a₁], ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [b₁, ← a₂, b₂]
    · simp only [show ¬m + n ≤ m by omega, ite_false, Nat.add_sub_cancel_left, b₂]
  · rcases Nat.lt_or_ge j m with hjm | hjm
    · simp only [show j ≤ m by omega, show j + 1 ≤ m by omega, ite_true]
      exact h₁ j hjm
    · rcases Nat.eq_or_lt_of_le hjm with rfl | hjm
      · simp only [le_refl, ite_true, show ¬m + 1 ≤ m by omega, ite_false,
          Nat.add_sub_cancel_left]
        rw [b₁, ← a₂]
        exact h₂ 0 (by omega)
      · simp only [show ¬j ≤ m by omega, show ¬j + 1 ≤ m by omega, ite_false,
          show j + 1 - m = j - m + 1 by omega]
        exact h₂ _ (by omega)

/-- A relation-preserving map sends a chain to a chain of the same length. -/
theorem map (f : α → β) (hf : ∀ x y, Rel x y → Rel' (f x) (f y)) (h : IsStepChain Rel n a b) :
    IsStepChain Rel' n (f a) (f b) := by
  obtain ⟨s, h₀, h₁, h⟩ := h
  exact ⟨f ∘ s, by simp [h₀], by simp [h₁], fun j hj => hf _ _ (h j hj)⟩

/-- Replacing the length by an equal natural number preserves a chain. -/
theorem cast_length {n' : ℕ} (h : IsStepChain Rel n a b) (hn : n = n') :
    IsStepChain Rel n' a b :=
  hn ▸ h

/-- **Adding marks one at a time.** If adding one mark of the list to any set of marks is a step,
there is a chain of as many steps as marks from no mark to all of them. -/
theorem treat {ι : Type*} [DecidableEq ι] (T : Finset ι → α) (marks : List ι)
    (h : ∀ M, ∀ Q ∈ marks, Rel (T M) (T (insert Q M))) :
    IsStepChain Rel marks.length (T ∅) (T marks.toFinset) := by
  induction marks with
  | nil => exact refl _
  | cons Q l ih =>
    rw [List.toFinset_cons, List.length_cons]
    exact (ih fun M Q' hQ' => h M Q' (List.mem_cons_of_mem _ hQ')).trans
      (single (h _ Q List.mem_cons_self))

/-- **Removing marks one at a time.** If removing one mark of the list from any set of marks is
a step, there is a chain of as many steps as marks from all of them to no mark. -/
theorem untreat {ι : Type*} [DecidableEq ι] (T : Finset ι → α) (marks : List ι)
    (h : ∀ M, ∀ Q ∈ marks, Rel (T (insert Q M)) (T M)) :
    IsStepChain Rel marks.length (T marks.toFinset) (T ∅) := by
  induction marks with
  | nil => exact refl _
  | cons Q l ih =>
    rw [List.toFinset_cons, List.length_cons, add_comm]
    exact (single (h _ Q List.mem_cons_self)).trans
      (ih fun M Q' hQ' => h M Q' (List.mem_cons_of_mem _ hQ'))

/-- **A bulk operation with its point treatments.** Treat the marks one at a time, operate, and
remove the marks again: `2 m + 1` steps for `m` marks.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 328–339. -/
theorem treat_operate {ι : Type*} [DecidableEq ι] (T T' : Finset ι → α) (marks : List ι)
    (h : ∀ M, ∀ Q ∈ marks, Rel (T M) (T (insert Q M)))
    (hb : Rel (T marks.toFinset) (T' marks.toFinset))
    (h' : ∀ M, ∀ Q ∈ marks, Rel (T' (insert Q M)) (T' M)) :
    IsStepChain Rel (2 * marks.length + 1) (T ∅) (T' ∅) :=
  ((treat T marks h).trans (single hb) |>.trans (untreat T' marks h')).cast_length (by ring)

/-- Compatibility name for the chain of treatments, one operation, and reverse treatments. -/
alias treatOperate := treat_operate

end IsStepChain

/-! ### Lifting chains of changes to the memory -/

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} [NeZero q] {pos : ι → ℝ × ℝ}
  {Party : Type} {Ω : EuclideanSpace ℂ (ι → Fin q)} {S : Set Party} {r K rs : ℕ} {ε : ℝ}
  {X : Type*} [DecidableEq X]

omit [DecidableEq X] in
/-- **A chain of changes of the main sheet.** Every memory of the chain keeps the main sheet, so
no stack of the chain is empty.

Polynomial-PEPS manuscript, `06-geometry.tex`, lines 38–40 and 662–664. -/
theorem isStepChain_main {n : ℕ} {F F' : Frame pos q Party} (l : List X)
    (A : X → Frame pos q Party) (hΩ : ‖Ω‖ ≤ 1)
    (h : IsStepChain (fun F F' => HasFrameChange Ω F F' S r K rs ε) n F F') :
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ) S r K rs ε ∧
      Fs' ≠ []) n (F :: l.map A) (F' :: l.map A) :=
  h.map (fun F => F :: l.map A) fun _ _ ⟨_, hc, hs⟩ =>
    ⟨hasSourceBoundedChange_main _ hc hs hΩ (by simp), List.cons_ne_nil _ _⟩

/-- **A change of one auxiliary sheet, by its value.** -/
theorem hasSourceBoundedChange_aux_of_eq (M : Frame pos q Party) {l : List X} (hl : l.Nodup)
    {x : X} (hx : x ∈ l) {A : X → Frame pos q Party} {F F' : Frame pos q Party} (hA : A x = F)
    (hΩ : ‖Ω‖ ≤ 1) (h : HasFrameChange Ω F F' S r K rs ε) :
    HasSourceBoundedChange Ω (M :: l.map A) (M :: l.map (Function.update A x F')) (ℓ := [])
      (1 : ℂ) S r K rs ε := by
  subst hA
  obtain ⟨c, hc, hs⟩ := h
  exact hasSourceBoundedChange_aux M hl hx A hc hs hΩ (by simp)

/-- **A chain of changes of one auxiliary sheet.** Every memory of the chain keeps the main sheet
`M`, so no stack of the chain is empty. -/
theorem isStepChain_aux {n : ℕ} (M : Frame pos q Party) {l : List X} (hl : l.Nodup) {x : X}
    (hx : x ∈ l) (A : X → Frame pos q Party) {F F' : Frame pos q Party} (hΩ : ‖Ω‖ ≤ 1)
    (h : IsStepChain (fun F F' => HasFrameChange Ω F F' S r K rs ε) n F F') :
    IsStepChain (fun Fs Fs' => HasSourceBoundedChange Ω Fs Fs' (ℓ := []) (1 : ℂ) S r K rs ε ∧
      Fs' ≠ []) n (M :: l.map (Function.update A x F)) (M :: l.map (Function.update A x F')) :=
  h.map (fun F => M :: l.map (Function.update A x F)) fun G G' hG => by
    have := hasSourceBoundedChange_aux_of_eq M hl hx (A := Function.update A x G)
      (Function.update_self x G A) hΩ hG
    rw [Function.update_idem] at this
    exact ⟨this, List.cons_ne_nil _ _⟩

/-- **A change of the main sheet and one auxiliary sheet.** -/
theorem hasSourceBoundedChange_of_hasPairChange {M M' : Frame pos q Party} {l : List X}
    (hl : l.Nodup) {x : X} (hx : x ∈ l) {A : X → Frame pos q Party} {F F' : Frame pos q Party}
    (hA : A x = F) (hΩ : ‖Ω‖ ≤ 1) (h : HasPairChange Ω M F M' F' S r K rs ε) :
    HasSourceBoundedChange Ω (M :: l.map A) (M' :: l.map (Function.update A x F')) (ℓ := [])
      (1 : ℂ) S r K rs ε := by
  subst hA
  obtain ⟨c, hc, hs⟩ := h
  exact hasSourceBoundedChange_mainAux hl hx A hc hs hΩ (by simp)

end Lift

end TNLean.PEPS.Approximation
