/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.WordPermutation

/-!
# Preparation of all pair sources before the local operations

Every pair source in a word prepares fresh registers. Its preparation can therefore
precede the earlier operations, provided those operations leave the fresh registers
untouched. This gives an exact factorization into preparation of the original pair
sources followed by local operations and changes of register order.

## References

* OpenAI, *Polynomial PEPS approximation of gapped square-grid ground states*,
  September 24, 2026, Lemma 5.1, `04-compression.tex`, lines 68–70 and 125–127;
  source-gate factorization in Theorem 5.2, equation
  `eq:compression-source-gate`, lines 233–251.
  Revision `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

The proofs are independent formalizations of the manuscript; no upstream Lean
proof text is reused.
-/

/-!
Source: September 24, 2026, polynomial-PEPS manuscript, 04-compression.tex,
lem:effects and eq:compression-source-gate.
Manuscript revision: openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Independently formalized from the manuscript; no upstream Lean proof text reused.

Provenance-ID: 8768-sourcepreparation-pairsource
Downstream declaration: TNLean.PEPS.PairEffect.PairSource

Provenance-ID: 8768-sourcepreparation-pairsource.layout
Downstream declaration: TNLean.PEPS.PairEffect.PairSource.layout

Provenance-ID: 8768-sourcepreparation-sourceinventory
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory

Provenance-ID: 8768-sourcepreparation-sourceinventory.layout
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout

Provenance-ID: 8768-sourcepreparation-sourceinventory.isnormalized
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.IsNormalized

Provenance-ID: 8768-sourcepreparation-sourceinventory.prepare
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.prepare

Provenance-ID: 8768-sourcepreparation-sourceinventory.layout_nil
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout_nil

Provenance-ID: 8768-sourcepreparation-sourceinventory.layout_cons
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout_cons

Provenance-ID: 8768-sourcepreparation-sourceinventory.layout_append
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.layout_append

Provenance-ID: 8768-sourcepreparation-sourceinventory.eval_framelist_prepare
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_frameList_prepare

Provenance-ID: 8768-sourcepreparation-sourceinventory.eval_prepare_append
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepare_append

Provenance-ID: 8768-sourcepreparation-sourceinventory.isallowed_prepare_iff
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.isAllowed_prepare_iff

Provenance-ID: 8768-sourcepreparation-sourceinventory.vector
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.vector

Provenance-ID: 8768-sourcepreparation-sourceinventory.eval_prepare_eq_appendiso_symm
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_prepare_eq_appendIso_symm

Provenance-ID: 8768-sourcepreparation-sourceinventory.eval_movehead_prepare
Downstream declaration: TNLean.PEPS.PairEffect.SourceInventory.eval_moveHead_prepare

Provenance-ID: 8768-sourcepreparation-word.sources
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources

Provenance-ID: 8768-sourcepreparation-word.castinput
Downstream declaration: TNLean.PEPS.PairEffect.Word.castInput

Provenance-ID: 8768-sourcepreparation-word.sources_castinput
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_castInput

Provenance-ID: 8768-sourcepreparation-word.isallowed_castinput
Downstream declaration: TNLean.PEPS.PairEffect.Word.isAllowed_castInput

Provenance-ID: 8768-sourcepreparation-word.eval_castinput_of_heq
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_castInput_of_heq

Provenance-ID: 8768-sourcepreparation-word.sources_framelist
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_frameList

Provenance-ID: 8768-sourcepreparation-word.sources_prepare
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_prepare

Provenance-ID: 8768-sourcepreparation-word.isnormalized_sources
Downstream declaration: TNLean.PEPS.PairEffect.Word.isNormalized_sources

Provenance-ID: 8768-sourcepreparation-word.sources_movehead
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_moveHead

Provenance-ID: 8768-sourcepreparation-word.sources_exchangeblocks
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_exchangeBlocks

Provenance-ID: 8768-sourcepreparation-word.localpart
Downstream declaration: TNLean.PEPS.PairEffect.Word.localPart

Provenance-ID: 8768-sourcepreparation-word.sources_localpart
Downstream declaration: TNLean.PEPS.PairEffect.Word.sources_localPart

Provenance-ID: 8768-sourcepreparation-word.isallowed_localpart
Downstream declaration: TNLean.PEPS.PairEffect.Word.isAllowed_localPart

Provenance-ID: 8768-sourcepreparation-word.eval_localpart_prepare
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_localPart_prepare

Provenance-ID: 8768-sourcepreparation-word.eval_eq_localpart_comp_prepare
Downstream declaration: TNLean.PEPS.PairEffect.Word.eval_eq_localPart_comp_prepare
-/

noncomputable section

open scoped TensorProduct
open ContinuousLinearMap

namespace TNLean.PEPS.PairEffect

/-- One occurrence of a pair source, with its actual endpoint parties, spaces and vector.
Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 68–70. -/
structure PairSource (P : Type) : Type 1 where
  left : P
  right : P
  distinct : left ≠ right
  leftSpace : HSpace
  rightSpace : HSpace
  vector : leftSpace ⊗[ℂ] rightSpace

variable {P : Type}

/-- The two fresh registers prepared by a pair source, with their original owners. -/
def PairSource.layout (s : PairSource P) : Layout P :=
  [⟨s.left, s.leftSpace⟩, ⟨s.right, s.rightSpace⟩]

/-- A finite list of pair-source occurrences. Repeated vectors and repeated party pairs
remain distinct occurrences. -/
abbrev SourceInventory (P : Type) := List (PairSource P)

namespace SourceInventory

/-- The fresh registers of all source occurrences, in list order. -/
def layout (S : SourceInventory P) : Layout P := S.flatMap PairSource.layout

/-- Each source vector is normalized. Source: polynomial-PEPS Lemma 5.1,
`04-compression.tex`, lines 65–70. -/
def IsNormalized (S : SourceInventory P) : Prop := ∀ s ∈ S, ‖s.vector‖ = 1

/-- Preparation of the listed pair sources before the original registers. -/
def prepare : (S : SourceInventory P) → (ℓ : Layout P) → Word ℓ (S.layout ++ ℓ)
  | [], ℓ => .id ℓ
  | s :: S, ℓ => .comp (prepare S ℓ)
      (.source s.distinct s.leftSpace s.rightSpace s.vector (layout S ++ ℓ))

@[simp] theorem layout_nil : layout ([] : SourceInventory P) = [] := rfl

@[simp] theorem layout_cons (s : PairSource P) (S : SourceInventory P) :
    layout (s :: S) = s.layout ++ S.layout := rfl

@[simp] theorem layout_append (S T : SourceInventory P) :
    (S ++ T).layout = S.layout ++ T.layout := List.flatMap_append

private theorem frame_source_eval (s : PairSource P) {ℓ ℓ' : Layout P}
    (w : Word ℓ ℓ') (x : Mem ℓ) :
    (Word.frameList s.layout w).eval
      ((Word.source s.distinct s.leftSpace s.rightSpace s.vector ℓ).eval x) =
    (Word.source s.distinct s.leftSpace s.rightSpace s.vector ℓ').eval (w.eval x) := by
  change (w.eval.lTensor s.rightSpace).lTensor s.leftSpace
      (assocL s.leftSpace s.rightSpace (Mem ℓ) (s.vector ⊗ₜ x)) =
    assocL s.leftSpace s.rightSpace (Mem ℓ') (s.vector ⊗ₜ w.eval x)
  apply (TensorProduct.assocIsometry ℂ s.leftSpace s.rightSpace (Mem ℓ')).symm.injective
  simp only [lTensor_lTensor_assoc_symm, assocL, isoL_apply,
    LinearIsometryEquiv.symm_apply_apply, lTensor_tmul]

/-- Preparations of fresh sources commute with operations on the original registers.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`, lines 246–248. -/
theorem eval_frameList_prepare (S : SourceInventory P) {ℓ ℓ' : Layout P}
    (w : Word ℓ ℓ') (x : Mem ℓ) :
    (Word.frameList S.layout w).eval ((prepare S ℓ).eval x) =
      (prepare S ℓ').eval (w.eval x) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
      change (Word.frameList s.layout (Word.frameList (layout S) w)).eval
        ((Word.source s.distinct s.leftSpace s.rightSpace s.vector (layout S ++ ℓ)).eval
          ((prepare S ℓ).eval x)) =
        (Word.source s.distinct s.leftSpace s.rightSpace s.vector (layout S ++ ℓ')).eval
          ((prepare S ℓ').eval (w.eval x))
      rw [frame_source_eval, ih]

private theorem eval_source_heq (s : PairSource P) {ℓ ℓ' : Layout P} (h : ℓ = ℓ')
    {x : Mem ℓ} {y : Mem ℓ'} (hxy : HEq x y) :
    HEq ((Word.source s.distinct s.leftSpace s.rightSpace s.vector ℓ).eval x)
      ((Word.source s.distinct s.leftSpace s.rightSpace s.vector ℓ').eval y) := by
  cases h
  cases hxy
  rfl

/-- Preparation of a concatenation first prepares the second list and then the first.
The heterogeneous equality only identifies the two associations of the same register list. -/
theorem eval_prepare_append (S T : SourceInventory P) (ℓ : Layout P) (x : Mem ℓ) :
    HEq ((prepare (S ++ T) ℓ).eval x)
      ((prepare S (T.layout ++ ℓ)).eval ((prepare T ℓ).eval x)) := by
  induction S with
  | nil => rfl
  | cons s S ih =>
      exact eval_source_heq s (by simp only [layout_append, List.append_assoc]) ih

/-- A preparation word is allowed exactly when its source vectors are normalized. -/
theorem isAllowed_prepare_iff (S : SourceInventory P) (ℓ : Layout P) :
    (prepare S ℓ).IsAllowed ↔ S.IsNormalized := by
  induction S with
  | nil => simp [prepare, Word.IsAllowed, IsNormalized]
  | cons s S ih =>
      simp only [prepare, Word.IsAllowed, ih, IsNormalized, List.mem_cons,
        forall_eq_or_imp, and_comm]

/-- The tensor product of the actual source vectors, with one terminal scalar factor.
Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 125–127. -/
def vector : (S : SourceInventory P) → Mem S.layout
  | [] => (1 : ℂ)
  | s :: S => assocL s.leftSpace s.rightSpace (Mem (layout S)) (s.vector ⊗ₜ vector S)

private theorem appendIso_symm_pair (r r' : Reg P) (ℓ₀ ℓ : Layout P)
    (η : r.space ⊗[ℂ] r'.space) (s : Mem ℓ₀) (x : Mem ℓ) :
    (appendIso (r :: r' :: ℓ₀) ℓ).symm
        (assocL r.space r'.space (Mem ℓ₀) (η ⊗ₜ s) ⊗ₜ x) =
      assocL r.space r'.space (Mem (ℓ₀ ++ ℓ))
        (η ⊗ₜ (appendIso ℓ₀ ℓ).symm (s ⊗ₜ x)) := by
  induction η using TensorProduct.inductionOn with
  | tmul u v => rfl
  | add a b ha hb =>
      simp only [TensorProduct.add_tmul, map_add, ha, hb]

/-- Preparing the source list tensors its joint vector with the original input.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`, lines 233–248. -/
theorem eval_prepare_eq_appendIso_symm (S : SourceInventory P) (ℓ : Layout P)
    (x : Mem ℓ) :
    (prepare S ℓ).eval x = (appendIso S.layout ℓ).symm (vector S ⊗ₜ x) := by
  induction S with
  | nil => exact (one_smul ℂ x).symm
  | cons s S ih =>
      exact (congrArg (fun z ↦ assocL s.leftSpace s.rightSpace (Mem (layout S ++ ℓ))
        (s.vector ⊗ₜ z)) ih).trans
        (appendIso_symm_pair ⟨s.left, s.leftSpace⟩ ⟨s.right, s.rightSpace⟩
          (layout S) ℓ s.vector (vector S) x).symm

/-- A register untouched by preparation can be moved back in front of all fresh sources.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`, lines 246–251. -/
theorem eval_moveHead_prepare (S : SourceInventory P) (r : Reg P) (ℓ : Layout P)
    (x : r.space) (y : Mem ℓ) :
    (Word.moveHead r S.layout ℓ).eval ((prepare S (r :: ℓ)).eval (x ⊗ₜ y)) =
      x ⊗ₜ ((prepare S ℓ).eval y) := by
  exact (congrArg (Word.moveHead r S.layout ℓ).eval
    (eval_prepare_eq_appendIso_symm S (r :: ℓ) (x ⊗ₜ y))).trans
    ((Word.eval_moveHead_appendIso_symm r S.layout ℓ (vector S) x y).trans
      (congrArg (fun z ↦ x ⊗ₜ z) (eval_prepare_eq_appendIso_symm S ℓ y).symm))

end SourceInventory

namespace Word

/-- The actual source occurrences of a word, ordered as their fresh registers will be
prepared. Sources in the later word occur first in the list, since preparation prepends
registers. Source: polynomial-PEPS Lemma 5.1, `04-compression.tex`, lines 125–127. -/
def sources : {ℓ ℓ' : Layout P} → Word ℓ ℓ' → SourceInventory P
  | _, _, id _ => []
  | _, _, comp w w' => w'.sources ++ w.sources
  | _, _, localMap .. => []
  | _, _, @source _ p q hpq U V η _ => [⟨p, q, hpq, U, V, η⟩]
  | _, _, swap .. => []
  | _, _, frame _ w => w.sources

/-- Identify equal input layouts without adding an operation. -/
def castInput {ℓ ℓ' ℓ₁ : Layout P} (w : Word ℓ ℓ') (h : ℓ = ℓ₁) : Word ℓ₁ ℓ' :=
  h ▸ w

@[simp] theorem sources_castInput {ℓ ℓ' ℓ₁ : Layout P} (w : Word ℓ ℓ') (h : ℓ = ℓ₁) :
    (w.castInput h).sources = w.sources := by
  cases h
  rfl

@[simp] theorem isAllowed_castInput {ℓ ℓ' ℓ₁ : Layout P} (w : Word ℓ ℓ') (h : ℓ = ℓ₁) :
    (w.castInput h).IsAllowed ↔ w.IsAllowed := by
  cases h
  rfl

theorem eval_castInput_of_heq {ℓ ℓ' ℓ₁ : Layout P} (w : Word ℓ ℓ') (h : ℓ = ℓ₁)
    {x : Mem ℓ} {y : Mem ℓ₁} (hxy : HEq y x) : (w.castInput h).eval y = w.eval x := by
  cases h
  cases hxy
  rfl

@[simp] theorem sources_frameList {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (ℓ₀ : Layout P) :
    (frameList ℓ₀ w).sources = w.sources := by
  induction ℓ₀ with
  | nil => rfl
  | cons r ℓ₀ ih => exact ih

@[simp] theorem sources_prepare (S : SourceInventory P) (ℓ : Layout P) :
    (S.prepare ℓ).sources = S := by
  induction S with
  | nil => rfl
  | cons s S ih => simp only [SourceInventory.prepare, sources, ih, List.singleton_append]

/-- Every source occurring in an allowed word has unit norm. -/
theorem isNormalized_sources {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hw : w.IsAllowed) :
    w.sources.IsNormalized := by
  induction w with
  | id => simp [sources, SourceInventory.IsNormalized]
  | comp w w' ih ih' =>
      simp only [sources, SourceInventory.IsNormalized, List.mem_append, or_imp, forall_and]
      exact ⟨ih' hw.2, ih hw.1⟩
  | localMap => simp [sources, SourceInventory.IsNormalized]
  | source hpq U V η ℓ => simpa [sources, SourceInventory.IsNormalized, IsAllowed] using hw
  | swap => simp [sources, SourceInventory.IsNormalized]
  | frame r w ih => exact ih hw

@[simp] theorem sources_moveHead (r : Reg P) (ℓ₀ tail : Layout P) :
    (moveHead r ℓ₀ tail).sources = [] := by
  induction ℓ₀ with
  | nil => rfl
  | cons head ℓ₀ ih => simp only [moveHead, sources, ih, List.nil_append]

@[simp] theorem sources_exchangeBlocks (a b tail : Layout P) :
    (exchangeBlocks a b tail).sources = [] := by
  induction b with
  | nil => rfl
  | cons r b ih => simp only [exchangeBlocks, sources, sources_moveHead, ih, List.nil_append]

/-- The local operations and exchanges remaining after all actual source occurrences
have been prepared in fresh registers. Source: polynomial-PEPS Theorem 5.2,
`eq:compression-source-gate`, lines 246–251. -/
def localPart : {ℓ ℓ' : Layout P} → (w : Word ℓ ℓ') → Word (w.sources.layout ++ ℓ) ℓ'
  | _, _, id ℓ => .id ℓ
  | _, _, comp w w' =>
      (comp (frameList w'.sources.layout w.localPart) w'.localPart).castInput
        (by simp only [sources, SourceInventory.layout_append, List.append_assoc])
  | _, _, localMap p h₁ h₂ U ℓ => .localMap p h₁ h₂ U ℓ
  | _, _, source hpq U V η ℓ => .id _
  | _, _, swap r r' ℓ => .swap r r' ℓ
  | _, _, @frame _ r ℓ _ w =>
      .comp (moveHead r w.sources.layout ℓ) (.frame r w.localPart)

/-- The residual word contains no pair sources. -/
@[simp] theorem sources_localPart {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    w.localPart.sources = [] := by
  induction w with
  | id => rfl
  | comp w w' ih ih' =>
      exact (sources_castInput _ _).trans (by
        simp only [sources, sources_frameList, ih, ih', List.nil_append])
  | localMap => rfl
  | source => rfl
  | swap => rfl
  | frame r w ih => simp only [localPart, sources, ih, sources_moveHead, List.nil_append]

/-- Moving preparations to the beginning preserves the allowedness of the remaining word. -/
theorem isAllowed_localPart {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (hw : w.IsAllowed) :
    w.localPart.IsAllowed := by
  induction w with
  | id => trivial
  | comp w w' ih ih' =>
      exact (isAllowed_castInput _ _).2 ⟨isAllowed_frameList _ (ih hw.1) _, ih' hw.2⟩
  | localMap => exact hw
  | source => trivial
  | swap => trivial
  | frame r w ih => exact ⟨isAllowed_moveHead _ _ _, ih hw⟩

/-- Preparing every actual pair source first and then applying the residual word gives
exactly the original operator. No normalization or contractivity hypothesis is needed.
Source: polynomial-PEPS Theorem 5.2, `eq:compression-source-gate`, lines 246–251. -/
theorem eval_localPart_prepare : {ℓ ℓ' : Layout P} → (w : Word ℓ ℓ') → (x : Mem ℓ) →
    w.localPart.eval ((w.sources.prepare ℓ).eval x) = w.eval x
  | _, _, id _, _ => rfl
  | ℓ, _, comp w w', x => by
      refine (eval_castInput_of_heq _ _
        (SourceInventory.eval_prepare_append w'.sources w.sources ℓ x)).trans ?_
      change w'.localPart.eval ((frameList w'.sources.layout w.localPart).eval
        ((w'.sources.prepare (w.sources.layout ++ ℓ)).eval
          ((w.sources.prepare ℓ).eval x))) = w'.eval (w.eval x)
      rw [SourceInventory.eval_frameList_prepare, eval_localPart_prepare w,
        eval_localPart_prepare w']
  | _, _, localMap .., _ => rfl
  | _, _, source .., _ => rfl
  | _, _, swap .., _ => rfl
  | _, _, frame r w, x => by
      induction x using TensorProduct.inductionOn with
      | tmul u v =>
          exact (congrArg (w.localPart.eval.lTensor r.space)
            (SourceInventory.eval_moveHead_prepare w.sources r _ u v)).trans
            (congrArg (fun z ↦ u ⊗ₜ z) (eval_localPart_prepare w v))
      | add a b ha hb => simp only [map_add, ha, hb]

/-- Every word is exactly preparation of its original pair sources followed by a word
with no pair sources. Source: polynomial-PEPS Theorem 5.2,
`eq:compression-source-gate`, lines 246–251. -/
theorem eval_eq_localPart_comp_prepare {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    w.eval = w.localPart.eval ∘L (w.sources.prepare ℓ).eval := by
  ext x
  exact (eval_localPart_prepare w x).symm

end Word

end TNLean.PEPS.PairEffect
