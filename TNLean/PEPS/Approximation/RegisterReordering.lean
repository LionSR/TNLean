/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Reordering
import TNLean.PEPS.Approximation.TagRegisters

/-!
# Reordering the tag registers of holes

Words of exchanges of tensor factors used to move the tag registers of encoded frames: the
splitting and merging of the tag registers of a concatenated list of holes (`tagSplit`,
`tagMerge`), and the canonical identification of tag orderings as a word
(`exists_tagWord_of_perm`). Every such word is a reordering (`PartyCircuit.Word.IsReordering`);
each operator is computed on product vectors. The reassociations and exchanges of blocks of
registers that do not involve tags are in `TNLean.Lattice.Sheet.Reordering`.

## Main definitions

* `EncodedFrame.tagSplit`, `EncodedFrame.tagMerge`.

## Main results

* `EncodedFrame.eval_tagSplit`, `EncodedFrame.eval_tagMerge`: the operators on product vectors.
* `EncodedFrame.exists_tagWord_of_perm`: a reordering of the holes of a frame is implemented on
  its tag registers by a word of exchanges, along a relabelling of the tags that preserves the
  encoding.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 74–75 and 84–85 (the
  fixed ordering of the tags and the canonical identification of tag orderings); allowed
  monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

namespace TNLean.PEPS.EncodedFrame

open TNLean.Lattice.PartyCircuit ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Splitting and merging tag registers -/

section TagSplit

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The tag registers of `l₁ ++ l₂` as those of `l₁` followed by those of `l₂`; no register
moves. -/
def tagSplit : (l₁ l₂ : List (Hole pos q Party)) → (tail : Layout Party) →
    Word (tagRegs (l₁ ++ l₂) ++ tail) (tagRegs l₁ ++ (tagRegs l₂ ++ tail))
  | [], _, _ => .id _
  | _ :: l₁, l₂, tail => .frame _ (tagSplit l₁ l₂ tail)

/-- The inverse of `tagSplit`. -/
def tagMerge : (l₁ l₂ : List (Hole pos q Party)) → (tail : Layout Party) →
    Word (tagRegs l₁ ++ (tagRegs l₂ ++ tail)) (tagRegs (l₁ ++ l₂) ++ tail)
  | [], _, _ => .id _
  | _ :: l₁, l₂, tail => .frame _ (tagMerge l₁ l₂ tail)

/-- Splitting the tag registers of a concatenated list on basis vectors. -/
theorem eval_tagSplit (tail : Layout Party) (y : Mem tail) :
    (l₁ l₂ : List (Hole pos q Party)) → (τ : TagSpace (l₁ ++ l₂)) →
      (tagSplit l₁ l₂ tail).eval
          ((appendIso (tagRegs (l₁ ++ l₂)) tail).symm (tagVec (l₁ ++ l₂) τ ⊗ₜ y)) =
        (appendIso (tagRegs l₁) (tagRegs l₂ ++ tail)).symm
          (tagVec l₁ (tagAppendEquiv l₁ l₂ τ).1 ⊗ₜ
            (appendIso (tagRegs l₂) tail).symm (tagVec l₂ (tagAppendEquiv l₁ l₂ τ).2 ⊗ₜ y))
  | [], l₂, τ => by
      change _ = (appendIso ([] : Layout Party) (tagRegs l₂ ++ tail)).symm ((1 : ℂ) ⊗ₜ
        (appendIso (tagRegs l₂) tail).symm (tagVec l₂ τ ⊗ₜ y))
      rw [appendIso_nil_symm_tmul, one_smul]
      rfl
  | h :: l₁, l₂, ⟨t, τ⟩ =>
      congrArg (fun w => ((EuclideanSpace.single t (1 : ℂ) :
          EuclideanSpace ℂ h.patch.Tag) ⊗ₜ w : Mem (tagRegs (h :: l₁) ++ (tagRegs l₂ ++ tail))))
        (eval_tagSplit tail y l₁ l₂ τ)

/-- Merging the tag registers of two lists on basis vectors. -/
theorem eval_tagMerge (tail : Layout Party) (y : Mem tail) :
    (l₁ l₂ : List (Hole pos q Party)) → (τ₁ : TagSpace l₁) → (τ₂ : TagSpace l₂) →
      (tagMerge l₁ l₂ tail).eval
          ((appendIso (tagRegs l₁) (tagRegs l₂ ++ tail)).symm (tagVec l₁ τ₁ ⊗ₜ
            (appendIso (tagRegs l₂) tail).symm (tagVec l₂ τ₂ ⊗ₜ y))) =
        (appendIso (tagRegs (l₁ ++ l₂)) tail).symm
          (tagVec (l₁ ++ l₂) ((tagAppendEquiv l₁ l₂).symm (τ₁, τ₂)) ⊗ₜ y)
  | [], l₂, τ₁, τ₂ => by
      change (appendIso ([] : Layout Party) (tagRegs l₂ ++ tail)).symm ((1 : ℂ) ⊗ₜ
        (appendIso (tagRegs l₂) tail).symm (tagVec l₂ τ₂ ⊗ₜ y)) = _
      rw [appendIso_nil_symm_tmul, one_smul]
      rfl
  | h :: l₁, l₂, ⟨t, τ₁⟩, τ₂ =>
      congrArg (fun w => ((EuclideanSpace.single t (1 : ℂ) :
          EuclideanSpace ℂ h.patch.Tag) ⊗ₜ w : Mem (tagRegs (h :: l₁ ++ l₂) ++ tail)))
        (eval_tagMerge tail y l₁ l₂ τ₁ τ₂)

@[simp] theorem isReordering_tagSplit (tail : Layout Party) :
    (l₁ l₂ : List (Hole pos q Party)) → (tagSplit l₁ l₂ tail).IsReordering
  | [], _ => Word.isReordering_id _
  | _ :: l₁, l₂ => isReordering_tagSplit tail l₁ l₂

@[simp] theorem isReordering_tagMerge (tail : Layout Party) :
    (l₁ l₂ : List (Hole pos q Party)) → (tagMerge l₁ l₂ tail).IsReordering
  | [], _ => Word.isReordering_id _
  | _ :: l₁, l₂ => isReordering_tagMerge tail l₁ l₂

open QuantumCircuit in
/-- **The canonical identification of tag orderings as a word.** If `l'` lists the holes of `l`,
whose outer footprints are pairwise disjoint, in another order, there are a relabelling `e` of
the tag configurations that preserves the raw parts of the encoding and a word of exchanges of
tensor factors moving the tag registers of `l` to the order of `l'`, with `|τ⟩ ↦ |e τ⟩`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 74–75 and 84–85. -/
theorem exists_tagWord_of_perm [NeZero q] {l l' : List (Hole pos q Party)}
    (hd : PairwiseDisjointOuter (l.map Hole.patch)) (hp : l.Perm l') (tail : Layout Party) :
    ∃ e : TagSpace l ≃ TagSpace l', (∀ t, rawProd l' (e t) = rawProd l t) ∧
      ∃ w : Word (tagRegs l ++ tail) (tagRegs l' ++ tail),
        w.IsReordering ∧ ∀ (τ : TagSpace l) (y : Mem tail),
          w.eval ((appendIso (tagRegs l) tail).symm (tagVec l τ ⊗ₜ y)) =
            (appendIso (tagRegs l') tail).symm (tagVec l' (e τ) ⊗ₜ y) := by
  induction hp with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl, .id _, Word.isReordering_id _, fun _ _ => rfl⟩
  | @cons h l₁ l₂ _ ih =>
    obtain ⟨e, he, w, hw', hw⟩ := ih (PairwiseDisjointOuter.of_cons hd)
    refine ⟨(Equiv.refl h.patch.Tag).prodCongr e, fun t => ?_, .frame _ w, hw', fun τ y => ?_⟩
    · change h.patch.branch t.1 * rawProd _ (e t.2) = h.patch.branch t.1 * rawProd _ t.2
      rw [he]
    · obtain ⟨t, τ⟩ := τ
      exact congrArg (fun v => ((EuclideanSpace.single t (1 : ℂ) :
        EuclideanSpace ℂ h.patch.Tag) ⊗ₜ v : Mem (tagRegs (h :: l₂) ++ tail))) (hw τ y)
  | swap x y l =>
    refine ⟨⟨fun t => (t.2.1, t.1, t.2.2), fun t => (t.2.1, t.1, t.2.2), fun _ => rfl,
      fun _ => rfl⟩, fun t => ?_, .swap _ _ _, Word.isReordering_swap .., fun τ z => ?_⟩
    · change x.patch.branch t.2.1 * (y.patch.branch t.1 * rawProd l t.2.2) =
        y.patch.branch t.1 * (x.patch.branch t.2.1 * rawProd l t.2.2)
      have hyx : Disjoint (y.patch.outer : Set ι) x.patch.outer :=
        Finset.disjoint_coe.mpr (List.rel_of_pairwise_cons hd List.mem_cons_self)
      rw [← mul_assoc, ← mul_assoc, (commute_of_mem_supportedOperators hyx
        (y.patch.branch_mem_supportedOperators _) (x.patch.branch_mem_supportedOperators _)).eq]
    · obtain ⟨t, s, τ⟩ := τ
      exact leftCommL_tmul _ _ _
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨e₁, he₁, w₁, a₁, hw₁⟩ := ih₁ hd
    obtain ⟨e₂, he₂, w₂, a₂, hw₂⟩ := ih₂ (hd.perm (h₁.map _) fun h => Disjoint.symm h)
    refine ⟨e₁.trans e₂, fun t => (he₂ _).trans (he₁ t), .comp w₁ w₂, a₁.comp a₂,
      fun τ z => ?_⟩
    rw [Word.eval_comp, ContinuousLinearMap.comp_apply, hw₁, hw₂]
    rfl

end TagSplit

end TNLean.PEPS.EncodedFrame
