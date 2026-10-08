/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.SiteRegisters

/-!
# Reordering blocks of registers

Words of exchanges of tensor factors used to move whole blocks of registers of encoded frames:
reassociations of concatenated blocks (`Word.assocWord`, `Word.unassocWord`), the exchange of two
pairs of blocks around a middle pair (`Word.swapPairs`), the versions of the partition words of
`TNLean.PEPS.Approximation.SiteRegisters` in front of further registers (`partWordApp`,
`unpartWordApp`, `relabelSitesApp`), the splitting and merging of the tag registers of a
concatenated list of holes (`tagSplit`, `tagMerge`), and the canonical identification of tag
orderings as a word (`exists_tagWord_of_perm`). Every such word is allowed, uses no party and
no pair source; each operator is computed on product vectors.

## Main definitions

* `PairEffect.Word.assocWord`, `PairEffect.Word.unassocWord`, `PairEffect.Word.swapPairs`.
* `EncodedFrame.partWordApp`, `EncodedFrame.unpartWordApp`, `EncodedFrame.relabelSitesApp`.
* `EncodedFrame.tagSplit`, `EncodedFrame.tagMerge`.

## Main results

* `PairEffect.Word.eval_swapPairs`, `EncodedFrame.eval_partWordApp`,
  `EncodedFrame.eval_tagSplit`, `EncodedFrame.eval_tagMerge`: the operators on product vectors.
* `EncodedFrame.exists_tagWord_of_perm`: a reordering of the holes of a frame is implemented on
  its tag registers by a word of exchanges, along a relabelling of the tags that preserves the
  encoding.

## References

* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`, lines 74–75 and 84–85 (the
  fixed ordering of the tags and the canonical identification of tag orderings); allowed
  monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

/-! ### Reassociating blocks of registers -/

namespace TNLean.PEPS.PairEffect.Word

open ContinuousLinearMap

variable {P : Type}

/-- Reassociate `(a ++ b) ++ c` as `a ++ (b ++ c)`; no register moves. -/
def assocWord : (a b c : Layout P) → Word ((a ++ b) ++ c) (a ++ (b ++ c))
  | [], b, c => .id (b ++ c)
  | r :: a, b, c => .frame r (assocWord a b c)

/-- Reassociate `a ++ (b ++ c)` as `(a ++ b) ++ c`; no register moves. -/
def unassocWord : (a b c : Layout P) → Word (a ++ (b ++ c)) ((a ++ b) ++ c)
  | [], b, c => .id (b ++ c)
  | r :: a, b, c => .frame r (unassocWord a b c)

theorem appendIso_nil_symm_tmul (ℓ : Layout P) (a : ℂ) (y : Mem ℓ) :
    (appendIso ([] : Layout P) ℓ).symm (a ⊗ₜ y) = a • y := by
  change TensorProduct.lidIsometry ℂ (Mem ℓ) (a ⊗ₜ y) = _
  simp

theorem eval_assocWord_appendIso_symm : (a b c : Layout P) → (x : Mem a) → (y : Mem b) →
    (z : Mem c) → (assocWord a b c).eval
      ((appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ y) ⊗ₜ z)) =
        (appendIso a (b ++ c)).symm (x ⊗ₜ (appendIso b c).symm (y ⊗ₜ z))
  | [], b, c, x, y, z => by
      rw [appendIso_nil_symm_tmul, appendIso_nil_symm_tmul, ← TensorProduct.smul_tmul',
        LinearIsometryEquiv.map_smul]
      rfl
  | r :: a, b, c, x, y, z => by
      induction x using TensorProduct.inductionOn with
      | tmul u s =>
          exact congrArg (fun w => (u ⊗ₜ w : Mem (r :: (a ++ (b ++ c)))))
            (eval_assocWord_appendIso_symm a b c s y z)
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

theorem eval_unassocWord_appendIso_symm : (a b c : Layout P) → (x : Mem a) → (y : Mem b) →
    (z : Mem c) → (unassocWord a b c).eval
      ((appendIso a (b ++ c)).symm (x ⊗ₜ (appendIso b c).symm (y ⊗ₜ z))) =
        (appendIso (a ++ b) c).symm ((appendIso a b).symm (x ⊗ₜ y) ⊗ₜ z)
  | [], b, c, x, y, z => by
      rw [appendIso_nil_symm_tmul, appendIso_nil_symm_tmul, ← TensorProduct.smul_tmul',
        LinearIsometryEquiv.map_smul]
      rfl
  | r :: a, b, c, x, y, z => by
      induction x using TensorProduct.inductionOn with
      | tmul u s =>
          exact congrArg (fun w => (u ⊗ₜ w : Mem (r :: ((a ++ b) ++ c))))
            (eval_unassocWord_appendIso_symm a b c s y z)
      | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']

theorem assocWord_props (S : Set P) : (a b c : Layout P) →
    (assocWord a b c).IsAllowed ∧ (assocWord a b c).UsesOnly S ∧
      (assocWord a b c).sourceCount = 0
  | [], _, _ => ⟨trivial, trivial, rfl⟩
  | _ :: a, b, c => assocWord_props S a b c

theorem unassocWord_props (S : Set P) : (a b c : Layout P) →
    (unassocWord a b c).IsAllowed ∧ (unassocWord a b c).UsesOnly S ∧
      (unassocWord a b c).sourceCount = 0
  | [], _, _ => ⟨trivial, trivial, rfl⟩
  | _ :: a, b, c => unassocWord_props S a b c

@[simp] theorem isAllowed_frameList_iff {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).IsAllowed ↔ w.IsAllowed
  | [] => Iff.rfl
  | _ :: ℓ₀ => isAllowed_frameList_iff w ℓ₀

@[simp] theorem usesOnly_frameList_iff {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') (S : Set P) :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).UsesOnly S ↔ w.UsesOnly S
  | [] => Iff.rfl
  | _ :: ℓ₀ => usesOnly_frameList_iff w S ℓ₀

@[simp] theorem sourceCount_frameList {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).sourceCount = w.sourceCount
  | [] => rfl
  | _ :: ℓ₀ => sourceCount_frameList w ℓ₀

@[simp] theorem isAllowed_assocWord (a b c : Layout P) : (assocWord a b c).IsAllowed :=
  (assocWord_props ∅ a b c).1

@[simp] theorem usesOnly_assocWord (S : Set P) (a b c : Layout P) :
    (assocWord a b c).UsesOnly S :=
  (assocWord_props S a b c).2.1

@[simp] theorem sourceCount_assocWord (a b c : Layout P) : (assocWord a b c).sourceCount = 0 :=
  (assocWord_props ∅ a b c).2.2

@[simp] theorem isAllowed_unassocWord (a b c : Layout P) : (unassocWord a b c).IsAllowed :=
  (unassocWord_props ∅ a b c).1

@[simp] theorem usesOnly_unassocWord (S : Set P) (a b c : Layout P) :
    (unassocWord a b c).UsesOnly S :=
  (unassocWord_props S a b c).2.1

@[simp] theorem sourceCount_unassocWord (a b c : Layout P) :
    (unassocWord a b c).sourceCount = 0 :=
  (unassocWord_props ∅ a b c).2.2

attribute [simp] isAllowed_exchangeBlocks usesOnly_exchangeBlocks sourceCount_exchangeBlocks
  isAllowed_moveHead usesOnly_moveHead sourceCount_moveHead

/-- Exchange the pairs of blocks `a₁ b₁` and `a₂ b₂` around the blocks `m₁ m₂`, the order within
every block kept. -/
def swapPairs (a₁ b₁ m₁ m₂ a₂ b₂ t : Layout P) :
    Word (a₁ ++ (b₁ ++ (m₁ ++ (m₂ ++ (a₂ ++ (b₂ ++ t))))))
      (a₂ ++ (b₂ ++ (m₁ ++ (m₂ ++ (a₁ ++ (b₁ ++ t)))))) :=
  .comp (unassocWord a₁ b₁ _) <|
  .comp (frameList (a₁ ++ b₁) (unassocWord m₁ m₂ _)) <|
  .comp (frameList (a₁ ++ b₁) (frameList (m₁ ++ m₂) (unassocWord a₂ b₂ t))) <|
  .comp (frameList (a₁ ++ b₁) (unassocWord (m₁ ++ m₂) (a₂ ++ b₂) t)) <|
  .comp (exchangeBlocks (a₁ ++ b₁) ((m₁ ++ m₂) ++ (a₂ ++ b₂)) t) <|
  .comp (assocWord (m₁ ++ m₂) (a₂ ++ b₂) ((a₁ ++ b₁) ++ t)) <|
  .comp (exchangeBlocks (m₁ ++ m₂) (a₂ ++ b₂) ((a₁ ++ b₁) ++ t)) <|
  .comp (frameList (a₂ ++ b₂) (frameList (m₁ ++ m₂) (assocWord a₁ b₁ t))) <|
  .comp (frameList (a₂ ++ b₂) (assocWord m₁ m₂ (a₁ ++ (b₁ ++ t)))) <|
  assocWord a₂ b₂ (m₁ ++ (m₂ ++ (a₁ ++ (b₁ ++ t))))

theorem eval_swapPairs (a₁ b₁ m₁ m₂ a₂ b₂ t : Layout P) (x₁ : Mem a₁) (y₁ : Mem b₁)
    (u₁ : Mem m₁) (u₂ : Mem m₂) (x₂ : Mem a₂) (y₂ : Mem b₂) (z : Mem t) :
    (swapPairs a₁ b₁ m₁ m₂ a₂ b₂ t).eval
      ((appendIso a₁ (b₁ ++ (m₁ ++ (m₂ ++ (a₂ ++ (b₂ ++ t)))))).symm
        (x₁ ⊗ₜ (appendIso b₁ (m₁ ++ (m₂ ++ (a₂ ++ (b₂ ++ t))))).symm
          (y₁ ⊗ₜ (appendIso m₁ (m₂ ++ (a₂ ++ (b₂ ++ t)))).symm
            (u₁ ⊗ₜ (appendIso m₂ (a₂ ++ (b₂ ++ t))).symm
              (u₂ ⊗ₜ (appendIso a₂ (b₂ ++ t)).symm
                (x₂ ⊗ₜ (appendIso b₂ t).symm (y₂ ⊗ₜ z))))))) =
      (appendIso a₂ (b₂ ++ (m₁ ++ (m₂ ++ (a₁ ++ (b₁ ++ t)))))).symm
        (x₂ ⊗ₜ (appendIso b₂ (m₁ ++ (m₂ ++ (a₁ ++ (b₁ ++ t))))).symm
          (y₂ ⊗ₜ (appendIso m₁ (m₂ ++ (a₁ ++ (b₁ ++ t)))).symm
            (u₁ ⊗ₜ (appendIso m₂ (a₁ ++ (b₁ ++ t))).symm
              (u₂ ⊗ₜ (appendIso a₁ (b₁ ++ t)).symm
                (x₁ ⊗ₜ (appendIso b₁ t).symm (y₁ ⊗ₜ z)))))) := by
  simp only [swapPairs, eval_comp, ContinuousLinearMap.comp_apply]
  simp only [eval_unassocWord_appendIso_symm, eval_frameList_appendIso_symm,
    eval_exchangeBlocks_appendIso_symm, eval_assocWord_appendIso_symm]

theorem swapPairs_props (S : Set P) (a₁ b₁ m₁ m₂ a₂ b₂ t : Layout P) :
    (swapPairs a₁ b₁ m₁ m₂ a₂ b₂ t).IsAllowed ∧ (swapPairs a₁ b₁ m₁ m₂ a₂ b₂ t).UsesOnly S ∧
      (swapPairs a₁ b₁ m₁ m₂ a₂ b₂ t).sourceCount = 0 := by
  simp [swapPairs, IsAllowed, UsesOnly, sourceCount]

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Partitioning the sites of a list in front of further registers -/

/-- One step of `partWordApp`. -/
def partStepApp (own : ι → Party) (x : ι) (a b : List ι) (tail : Layout Party) : (c : Bool) →
    Word (⟨own x, euc (Fin q)⟩ :: (siteRegs q own a ++ (siteRegs q own b ++ tail)))
      (siteRegs q own (cond c (x :: a, b) (a, x :: b)).1 ++
        (siteRegs q own (cond c (x :: a, b) (a, x :: b)).2 ++ tail))
  | true => .id _
  | false => Word.exchangeBlocks [⟨own x, euc (Fin q)⟩] (siteRegs q own a)
      (siteRegs q own b ++ tail)

/-- The registers of the sites satisfying `p` moved to the front, in front of the registers
`tail`, which are untouched. -/
def partWordApp (own : ι → Party) (p : ι → Bool) (tail : Layout Party) :
    (S : List ι) → Word (siteRegs q own S ++ tail)
      (siteRegs q own (partSites p S).1 ++ (siteRegs q own (partSites p S).2 ++ tail))
  | [] => .id tail
  | x :: S => .comp (.frame _ (partWordApp own p tail S)) (partStepApp own x _ _ tail (p x))

/-- One step of `unpartWordApp`. -/
def unpartStepApp (own : ι → Party) (x : ι) (a b : List ι) (tail : Layout Party) :
    (c : Bool) →
    Word (siteRegs q own (cond c (x :: a, b) (a, x :: b)).1 ++
        (siteRegs q own (cond c (x :: a, b) (a, x :: b)).2 ++ tail))
      (⟨own x, euc (Fin q)⟩ :: (siteRegs q own a ++ (siteRegs q own b ++ tail)))
  | true => .id _
  | false => Word.moveHead ⟨own x, euc (Fin q)⟩ (siteRegs q own a) (siteRegs q own b ++ tail)

/-- The inverse of `partWordApp`. -/
def unpartWordApp (own : ι → Party) (p : ι → Bool) (tail : Layout Party) :
    (S : List ι) → Word
      (siteRegs q own (partSites p S).1 ++ (siteRegs q own (partSites p S).2 ++ tail))
      (siteRegs q own S ++ tail)
  | [] => .id tail
  | x :: S => .comp (unpartStepApp own x _ _ tail (p x)) (.frame _ (unpartWordApp own p tail S))

theorem eval_partStepApp (own : ι → Party) (x : ι) (a b : List ι) (tail : Layout Party)
    (c : ι → Fin q) (y : Mem tail) : (cb : Bool) → (partStepApp own x a b tail cb).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (appendIso (siteRegs q own a) (siteRegs q own b ++ tail)).symm (siteVec own a c ⊗ₜ
            (appendIso (siteRegs q own b) tail).symm (siteVec own b c ⊗ₜ y))) =
      (appendIso (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).1)
          (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).2 ++ tail)).symm
        (siteVec own (cond cb (x :: a, b) (a, x :: b)).1 c ⊗ₜ
          (appendIso (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).2) tail).symm
            (siteVec own (cond cb (x :: a, b) (a, x :: b)).2 c ⊗ₜ y))
  | true => rfl
  | false => by
      have h := Word.eval_exchangeBlocks_appendIso_symm [⟨own x, euc (Fin q)⟩]
        (siteRegs q own a) (siteRegs q own b ++ tail)
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ (1 : ℂ))
        (siteVec own a c) ((appendIso (siteRegs q own b) tail).symm (siteVec own b c ⊗ₜ y))
      rw [appendIso_one_symm_tmul, appendIso_one_symm_tmul] at h
      exact h

theorem eval_partWordApp (own : ι → Party) (p : ι → Bool) (tail : Layout Party)
    (c : ι → Fin q) (y : Mem tail) : (S : List ι) →
    (partWordApp own p tail S).eval
        ((appendIso (siteRegs q own S) tail).symm (siteVec own S c ⊗ₜ y)) =
      (appendIso (siteRegs q own (partSites p S).1)
          (siteRegs q own (partSites p S).2 ++ tail)).symm
        (siteVec own (partSites p S).1 c ⊗ₜ
          (appendIso (siteRegs q own (partSites p S).2) tail).symm
            (siteVec own (partSites p S).2 c ⊗ₜ y))
  | [] => by
      change (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y) =
        (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ
          (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y))
      rw [Word.appendIso_nil_symm_tmul (ℓ := tail), one_smul, Word.appendIso_nil_symm_tmul,
        one_smul]
  | x :: S => by
      change (partStepApp own x (partSites p S).1 (partSites p S).2 tail (p x)).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (partWordApp own p tail S).eval
            ((appendIso (siteRegs q own S) tail).symm (siteVec own S c ⊗ₜ y))) = _
      rw [eval_partWordApp own p tail c y S]
      exact eval_partStepApp own x _ _ tail c y (p x)

theorem eval_unpartStepApp (own : ι → Party) (x : ι) (a b : List ι) (tail : Layout Party)
    (c : ι → Fin q) (y : Mem tail) : (cb : Bool) → (unpartStepApp own x a b tail cb).eval
        ((appendIso (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).1)
            (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).2 ++ tail)).symm
          (siteVec own (cond cb (x :: a, b) (a, x :: b)).1 c ⊗ₜ
            (appendIso (siteRegs q own (cond cb (x :: a, b) (a, x :: b)).2) tail).symm
              (siteVec own (cond cb (x :: a, b) (a, x :: b)).2 c ⊗ₜ y))) =
      (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
        (appendIso (siteRegs q own a) (siteRegs q own b ++ tail)).symm (siteVec own a c ⊗ₜ
          (appendIso (siteRegs q own b) tail).symm (siteVec own b c ⊗ₜ y))
  | true => rfl
  | false => Word.eval_moveHead_appendIso_symm ⟨own x, euc (Fin q)⟩ (siteRegs q own a)
      (siteRegs q own b ++ tail) (siteVec own a c)
      (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q))
      ((appendIso (siteRegs q own b) tail).symm (siteVec own b c ⊗ₜ y))

theorem eval_unpartWordApp (own : ι → Party) (p : ι → Bool) (tail : Layout Party)
    (c : ι → Fin q) (y : Mem tail) : (S : List ι) →
    (unpartWordApp own p tail S).eval
        ((appendIso (siteRegs q own (partSites p S).1)
            (siteRegs q own (partSites p S).2 ++ tail)).symm
          (siteVec own (partSites p S).1 c ⊗ₜ
            (appendIso (siteRegs q own (partSites p S).2) tail).symm
              (siteVec own (partSites p S).2 c ⊗ₜ y))) =
      (appendIso (siteRegs q own S) tail).symm (siteVec own S c ⊗ₜ y)
  | [] => by
      change (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ
          (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y)) =
        (appendIso ([] : Layout Party) tail).symm ((1 : ℂ) ⊗ₜ y)
      rw [Word.appendIso_nil_symm_tmul, one_smul]
  | x :: S => by
      refine (congrArg (Word.frame _ (unpartWordApp (q := q) own p tail S)).eval
        (eval_unpartStepApp own x (partSites p S).1 (partSites p S).2 tail c y (p x))).trans ?_
      change (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
        (unpartWordApp (q := q) own p tail S).eval _ = _
      rw [eval_unpartWordApp own p tail c y S]
      rfl

theorem partWordApp_props (own : ι → Party) (p : ι → Bool) (tail : Layout Party)
    (T : Set Party) : (S : List ι) → (partWordApp (q := q) own p tail S).IsAllowed ∧
      (partWordApp (q := q) own p tail S).UsesOnly T ∧
      (partWordApp (q := q) own p tail S).sourceCount = 0
  | [] => ⟨trivial, trivial, rfl⟩
  | x :: S => by
      obtain ⟨h₁, h₂, h₃⟩ := partWordApp_props own p tail T S
      have hs : (partStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).IsAllowed ∧
          (partStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).UsesOnly T ∧
          (partStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).sourceCount = 0 := by
        cases p x
        · exact ⟨Word.isAllowed_exchangeBlocks _ _ _, Word.usesOnly_exchangeBlocks _ _ _ _,
            Word.sourceCount_exchangeBlocks _ _ _⟩
        · exact ⟨trivial, trivial, rfl⟩
      exact ⟨⟨h₁, hs.1⟩, ⟨h₂, hs.2.1⟩, congrArg₂ (· + ·) h₃ hs.2.2⟩

theorem unpartWordApp_props (own : ι → Party) (p : ι → Bool) (tail : Layout Party)
    (T : Set Party) : (S : List ι) → (unpartWordApp (q := q) own p tail S).IsAllowed ∧
      (unpartWordApp (q := q) own p tail S).UsesOnly T ∧
      (unpartWordApp (q := q) own p tail S).sourceCount = 0
  | [] => ⟨trivial, trivial, rfl⟩
  | x :: S => by
      obtain ⟨h₁, h₂, h₃⟩ := unpartWordApp_props own p tail T S
      have hs : (unpartStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).IsAllowed ∧
          (unpartStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).UsesOnly T ∧
          (unpartStepApp (q := q) own x (partSites p S).1 (partSites p S).2 tail
            (p x)).sourceCount = 0 := by
        cases p x
        · exact ⟨Word.isAllowed_moveHead _ _ _, Word.usesOnly_moveHead _ _ _ _,
            Word.sourceCount_moveHead _ _ _⟩
        · exact ⟨trivial, trivial, rfl⟩
      exact ⟨⟨hs.1, h₁⟩, ⟨hs.2.1, h₂⟩, congrArg₂ (· + ·) hs.2.2 h₃⟩

/-- The raw registers of `S` in front of `tail`, held by `own`, named with the owners `own'` that
agree on `S`. -/
def relabelSitesApp (own own' : ι → Party) (tail : Layout Party) :
    (S : List ι) → (∀ x ∈ S, own x = own' x) →
      Word (siteRegs q own S ++ tail) (siteRegs q own' S ++ tail)
  | [], _ => .id tail
  | x :: S, h => .comp
      (.frame ⟨own x, euc (Fin q)⟩
        (relabelSitesApp own own' tail S fun y hy => h y (List.mem_cons_of_mem x hy)))
      (relabelHead (h x List.mem_cons_self) (euc (Fin q)) (siteRegs q own' S ++ tail))

theorem eval_relabelSitesApp (own own' : ι → Party) (tail : Layout Party) (c : ι → Fin q)
    (y : Mem tail) : (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSitesApp own own' tail S h).eval
          ((appendIso (siteRegs q own S) tail).symm (siteVec own S c ⊗ₜ y)) =
        (appendIso (siteRegs q own' S) tail).symm (siteVec own' S c ⊗ₜ y)
  | [], _ => rfl
  | x :: S, h => by
      change (relabelHead (h x List.mem_cons_self) (euc (Fin q)) (siteRegs q own' S ++ tail)).eval
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          (relabelSitesApp own own' tail S _).eval
            ((appendIso (siteRegs q own S) tail).symm (siteVec own S c ⊗ₜ y))) = _
      rw [eval_relabelHead, eval_relabelSitesApp own own' tail c y S]
      rfl

@[simp] theorem relabelSitesApp_props (own own' : ι → Party) (tail : Layout Party)
    (T : Set Party) : (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSitesApp (q := q) own own' tail S h).IsAllowed ∧
        (relabelSitesApp (q := q) own own' tail S h).UsesOnly T ∧
        (relabelSitesApp (q := q) own own' tail S h).sourceCount = 0
  | [], _ => ⟨trivial, trivial, rfl⟩
  | x :: S, h => by
      obtain ⟨h₁, h₂, h₃⟩ := relabelSitesApp_props own own' tail T S
        fun y hy => h y (List.mem_cons_of_mem x hy)
      obtain ⟨g₁, g₂, g₃⟩ := relabelHead_props (h x List.mem_cons_self) (euc (Fin q))
        (siteRegs q own' S ++ tail) T
      exact ⟨⟨h₁, g₁⟩, ⟨h₂, g₂⟩, congrArg₂ (· + ·) h₃ g₃⟩

section Simp

variable (own own' : ι → Party) (p : ι → Bool) (tail : Layout Party) (S : List ι)
  (T : Set Party)

@[simp] theorem isAllowed_partWord : (partWord (q := q) own p S).IsAllowed :=
  (partWord_props own p ∅ S).1
@[simp] theorem usesOnly_partWord : (partWord (q := q) own p S).UsesOnly T :=
  (partWord_props own p T S).2.1
@[simp] theorem sourceCount_partWord : (partWord (q := q) own p S).sourceCount = 0 :=
  (partWord_props own p ∅ S).2.2
@[simp] theorem isAllowed_unpartWord : (unpartWord (q := q) own p S).IsAllowed :=
  (unpartWord_props own p ∅ S).1
@[simp] theorem usesOnly_unpartWord : (unpartWord (q := q) own p S).UsesOnly T :=
  (unpartWord_props own p T S).2.1
@[simp] theorem sourceCount_unpartWord : (unpartWord (q := q) own p S).sourceCount = 0 :=
  (unpartWord_props own p ∅ S).2.2
@[simp] theorem isAllowed_partWordApp : (partWordApp (q := q) own p tail S).IsAllowed :=
  (partWordApp_props own p tail ∅ S).1
@[simp] theorem usesOnly_partWordApp : (partWordApp (q := q) own p tail S).UsesOnly T :=
  (partWordApp_props own p tail T S).2.1
@[simp] theorem sourceCount_partWordApp :
    (partWordApp (q := q) own p tail S).sourceCount = 0 :=
  (partWordApp_props own p tail ∅ S).2.2
@[simp] theorem isAllowed_unpartWordApp : (unpartWordApp (q := q) own p tail S).IsAllowed :=
  (unpartWordApp_props own p tail ∅ S).1
@[simp] theorem usesOnly_unpartWordApp : (unpartWordApp (q := q) own p tail S).UsesOnly T :=
  (unpartWordApp_props own p tail T S).2.1
@[simp] theorem sourceCount_unpartWordApp :
    (unpartWordApp (q := q) own p tail S).sourceCount = 0 :=
  (unpartWordApp_props own p tail ∅ S).2.2

variable (h : ∀ x ∈ S, own x = own' x)

@[simp] theorem isAllowed_relabelSites : (relabelSites (q := q) own own' S h).IsAllowed :=
  (relabelSites_props own own' ∅ S h).1
@[simp] theorem usesOnly_relabelSites : (relabelSites (q := q) own own' S h).UsesOnly T :=
  (relabelSites_props own own' T S h).2.1
@[simp] theorem sourceCount_relabelSites :
    (relabelSites (q := q) own own' S h).sourceCount = 0 :=
  (relabelSites_props own own' ∅ S h).2.2
@[simp] theorem isAllowed_relabelSitesApp :
    (relabelSitesApp (q := q) own own' tail S h).IsAllowed :=
  (relabelSitesApp_props own own' tail ∅ S h).1
@[simp] theorem usesOnly_relabelSitesApp :
    (relabelSitesApp (q := q) own own' tail S h).UsesOnly T :=
  (relabelSitesApp_props own own' tail T S h).2.1
@[simp] theorem sourceCount_relabelSitesApp :
    (relabelSitesApp (q := q) own own' tail S h).sourceCount = 0 :=
  (relabelSitesApp_props own own' tail ∅ S h).2.2

end Simp

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
      rw [Word.appendIso_nil_symm_tmul, one_smul]
      rfl
  | h :: l₁, l₂, ⟨t, τ⟩ =>
      congrArg (fun w => ((EuclideanSpace.single t (1 : ℂ) :
          EuclideanSpace ℂ h.patch.Tag) ⊗ₜ w : Mem (tagRegs (h :: l₁) ++ (tagRegs l₂ ++ tail))))
        (eval_tagSplit tail y l₁ l₂ τ)

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
      rw [Word.appendIso_nil_symm_tmul, one_smul]
      rfl
  | h :: l₁, l₂, ⟨t, τ₁⟩, τ₂ =>
      congrArg (fun w => ((EuclideanSpace.single t (1 : ℂ) :
          EuclideanSpace ℂ h.patch.Tag) ⊗ₜ w : Mem (tagRegs (h :: l₁ ++ l₂) ++ tail)))
        (eval_tagMerge tail y l₁ l₂ τ₁ τ₂)

@[simp] theorem tagSplit_props (S : Set Party) (tail : Layout Party) :
    (l₁ l₂ : List (Hole pos q Party)) → (tagSplit l₁ l₂ tail).IsAllowed ∧
      (tagSplit l₁ l₂ tail).UsesOnly S ∧ (tagSplit l₁ l₂ tail).sourceCount = 0
  | [], _ => ⟨trivial, trivial, rfl⟩
  | _ :: l₁, l₂ => tagSplit_props S tail l₁ l₂

@[simp] theorem tagMerge_props (S : Set Party) (tail : Layout Party) :
    (l₁ l₂ : List (Hole pos q Party)) → (tagMerge l₁ l₂ tail).IsAllowed ∧
      (tagMerge l₁ l₂ tail).UsesOnly S ∧ (tagMerge l₁ l₂ tail).sourceCount = 0
  | [], _ => ⟨trivial, trivial, rfl⟩
  | _ :: l₁, l₂ => tagMerge_props S tail l₁ l₂

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
        w.IsAllowed ∧ (∀ S : Set Party, w.UsesOnly S) ∧ w.sourceCount = 0 ∧
        ∀ (τ : TagSpace l) (y : Mem tail),
          w.eval ((appendIso (tagRegs l) tail).symm (tagVec l τ ⊗ₜ y)) =
            (appendIso (tagRegs l') tail).symm (tagVec l' (e τ) ⊗ₜ y) := by
  induction hp with
  | nil => exact ⟨Equiv.refl _, fun _ => rfl, .id _, trivial, fun _ => trivial, rfl,
      fun _ _ => rfl⟩
  | @cons h l₁ l₂ _ ih =>
    obtain ⟨e, he, w, hw₁, hw₂, hw₃, hw⟩ := ih (PairwiseDisjointOuter.of_cons hd)
    refine ⟨(Equiv.refl h.patch.Tag).prodCongr e, fun t => ?_, .frame _ w, hw₁, hw₂, hw₃,
      fun τ y => ?_⟩
    · change h.patch.branch t.1 * rawProd _ (e t.2) = h.patch.branch t.1 * rawProd _ t.2
      rw [he]
    · obtain ⟨t, τ⟩ := τ
      exact congrArg (fun v => ((EuclideanSpace.single t (1 : ℂ) :
        EuclideanSpace ℂ h.patch.Tag) ⊗ₜ v : Mem (tagRegs (h :: l₂) ++ tail))) (hw τ y)
  | swap x y l =>
    refine ⟨⟨fun t => (t.2.1, t.1, t.2.2), fun t => (t.2.1, t.1, t.2.2), fun _ => rfl,
      fun _ => rfl⟩, fun t => ?_, .swap _ _ _, trivial, fun _ => trivial, rfl,
      fun τ z => ?_⟩
    · change x.patch.branch t.2.1 * (y.patch.branch t.1 * rawProd l t.2.2) =
        y.patch.branch t.1 * (x.patch.branch t.2.1 * rawProd l t.2.2)
      have hyx : Disjoint (y.patch.outer : Set ι) x.patch.outer :=
        Finset.disjoint_coe.mpr (List.rel_of_pairwise_cons hd List.mem_cons_self)
      rw [← mul_assoc, ← mul_assoc, (commute_of_mem_supportedOperators hyx
        (y.patch.branch_mem_supportedOperators _) (x.patch.branch_mem_supportedOperators _)).eq]
    · obtain ⟨t, s, τ⟩ := τ
      exact leftCommL_tmul _ _ _
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨e₁, he₁, w₁, a₁, b₁, c₁, hw₁⟩ := ih₁ hd
    obtain ⟨e₂, he₂, w₂, a₂, b₂, c₂, hw₂⟩ := ih₂ (hd.perm (h₁.map _) fun h => Disjoint.symm h)
    refine ⟨e₁.trans e₂, fun t => (he₂ _).trans (he₁ t), .comp w₁ w₂, ⟨a₁, a₂⟩,
      fun S => ⟨b₁ S, b₂ S⟩, congrArg₂ (· + ·) c₁ c₂, fun τ z => ?_⟩
    rw [Word.eval_comp, ContinuousLinearMap.comp_apply, hw₁, hw₂]
    rfl

section

variable (S : Set Party) (tail : Layout Party) (l₁ l₂ : List (Hole pos q Party))

@[simp] theorem isAllowed_tagSplit : (tagSplit l₁ l₂ tail).IsAllowed :=
  (tagSplit_props ∅ tail l₁ l₂).1
@[simp] theorem usesOnly_tagSplit : (tagSplit l₁ l₂ tail).UsesOnly S :=
  (tagSplit_props S tail l₁ l₂).2.1
@[simp] theorem sourceCount_tagSplit : (tagSplit l₁ l₂ tail).sourceCount = 0 :=
  (tagSplit_props ∅ tail l₁ l₂).2.2
@[simp] theorem isAllowed_tagMerge : (tagMerge l₁ l₂ tail).IsAllowed :=
  (tagMerge_props ∅ tail l₁ l₂).1
@[simp] theorem usesOnly_tagMerge : (tagMerge l₁ l₂ tail).UsesOnly S :=
  (tagMerge_props S tail l₁ l₂).2.1
@[simp] theorem sourceCount_tagMerge : (tagMerge l₁ l₂ tail).sourceCount = 0 :=
  (tagMerge_props ∅ tail l₁ l₂).2.2

end

end TagSplit

end TNLean.PEPS.EncodedFrame
