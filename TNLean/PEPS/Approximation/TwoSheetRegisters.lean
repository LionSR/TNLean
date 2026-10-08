/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.FrameRegisters

/-!
# The registers of two encoded frames

test
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker

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

end TagSplit

/-! ### A private contraction on the raw registers of `U` on two sheets -/

section Correction

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} {T E : Finset ι}

/-- The sites of `sites ι` in `U = (T ∪ E)ᶜ`. -/
abbrev sitesU (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (sites ι)).1

/-- The sites of `sites ι` in `T ∪ E`. -/
abbrev sitesR (T E : Finset ι) : List ι :=
  (partSites (fun x => decide (x ∈ (T ∪ E)ᶜ)) (sites ι)).2

theorem mem_sitesU_iff (x : ι) : x ∈ sitesU T E ↔ x ∈ (T ∪ E)ᶜ := by
  simp [mem_partSites_fst, mem_sites]

/-- The positions of `sitesU T E` enumerate `U = (T ∪ E)ᶜ`. -/
def equivSitesU (T E : Finset ι) : Fin (sitesU T E).length ≃ ↥(T ∪ E)ᶜ :=
  (List.Nodup.getEquiv _ (nodup_partSites_fst _ nodup_sites)).trans
    (Equiv.subtypeEquivRight mem_sitesU_iff)

/-- The raw registers of `U` on two sheets, identified with `ℂ^{(U → Fin q) × (U → Fin q)}`. -/
def pairUIso (own₁ own₂ : ι → Party) :
    Mem (siteRegs q own₁ (sitesU T E) ++ siteRegs q own₂ (sitesU T E)) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) :=
  (appendIso _ _).trans ((((groupIso own₁ _ (equivSitesU T E)).rTensor _).trans
    ((groupIso own₂ _ (equivSitesU T E)).lTensor _)).trans (pairIso _ _))

theorem pairUIso_siteVec (own₁ own₂ : ι → Party) (c₁ c₂ : ι → Fin q) :
    pairUIso (T := T) (E := E) own₁ own₂ ((appendIso _ _).symm
        (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂)) =
      EuclideanSpace.single ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x))
        (1 : ℂ) := by
  change pairIso _ _ ((groupIso own₂ _ (equivSitesU T E)).lTensor _
    ((groupIso own₁ _ (equivSitesU T E)).rTensor _ (appendIso _ _ ((appendIso _ _).symm
      (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂))))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, iso_rTensor_tmul, iso_lTensor_tmul,
    groupIso_siteVec own₁ _ _ Subtype.val (fun _ => rfl) c₁,
    groupIso_siteVec own₂ _ _ Subtype.val (fun _ => rfl) c₂]
  exact pairIso_single_tmul_single _ _

/-- **The corrections as one private contraction.** On two layouts of frames whose raw registers
of `U = (T ∪ E)ᶜ` are all held by `P`, move the raw registers of `U` of both sheets to the front
by exchanges of tensor factors, apply the matrix `W` to them as one private contraction at `P`,
and move them back.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 500–515. -/
def correctionLayoutWord (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ) :
    Word (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)
      (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) :=
  let pU : ι → Bool := fun x => decide (x ∈ (T ∪ E)ᶜ)
  let k₁ := tagRegs l₁
  let k₂ := tagRegs l₂
  let U₁ := siteRegs q own₁ (sitesU T E)
  let R₁ := siteRegs q own₁ (sitesR T E)
  let U₂ := siteRegs q own₂ (sitesU T E)
  let R₂ := siteRegs q own₂ (sitesR T E)
  let rest := k₁ ++ (R₁ ++ (k₂ ++ R₂))
  have hU : ∀ r ∈ U₁ ++ U₂, r.owner = P := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact owner_siteRegs (fun x hx => h₁ x ((mem_sitesU_iff x).mp hx)) r hr
    · exact owner_siteRegs (fun x hx => h₂ x ((mem_sitesU_iff x).mp hx)) r hr
  .comp (Word.assocWord k₁ (siteRegs q own₁ (sites ι)) (layoutRegs q l₂ own₂)) <|
  .comp (Word.frameList k₁ (partWordApp own₁ pU (layoutRegs q l₂ own₂) (sites ι))) <|
  .comp (Word.frameList k₁ (Word.frameList U₁ (Word.frameList R₁ (Word.frameList k₂
    (partWord own₂ pU (sites ι)))))) <|
  .comp (Word.exchangeBlocks k₁ U₁ (R₁ ++ (k₂ ++ (U₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.frameList R₁
    (Word.exchangeBlocks k₂ U₂ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.exchangeBlocks R₁ U₂ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.exchangeBlocks k₁ U₂ (R₁ ++ (k₂ ++ R₂)))) <|
  .comp (Word.unassocWord U₁ U₂ rest) <|
  .comp (Word.localMap P (ℓ₁ := U₁ ++ U₂) (ℓ₂ := U₁ ++ U₂) hU hU
    (isoL (pairUIso own₁ own₂).symm ∘L matL W ∘L isoL (pairUIso own₁ own₂)) rest) <|
  .comp (Word.assocWord U₁ U₂ rest) <|
  .comp (Word.frameList U₁ (Word.exchangeBlocks U₂ k₁ (R₁ ++ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.exchangeBlocks U₂ R₁ (k₂ ++ R₂)))) <|
  .comp (Word.frameList U₁ (Word.frameList k₁ (Word.frameList R₁
    (Word.exchangeBlocks U₂ k₂ R₂)))) <|
  .comp (Word.exchangeBlocks U₁ k₁ (R₁ ++ (k₂ ++ (U₂ ++ R₂)))) <|
  .comp (Word.frameList k₁ (Word.frameList U₁ (Word.frameList R₁ (Word.frameList k₂
    (unpartWord own₂ pU (sites ι)))))) <|
  .comp (Word.frameList k₁ (unpartWordApp own₁ pU (layoutRegs q l₂ own₂) (sites ι))) <|
  Word.unassocWord k₁ (siteRegs q own₁ (sites ι)) (layoutRegs q l₂ own₂)

theorem pairUIso_symm_single (h : Disjoint T E) (own₁ own₂ : ι → Party) (c₁ c₂ : ι → Fin q)
    (u : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) :
    (pairUIso (T := T) (E := E) own₁ own₂).symm (EuclideanSpace.single u (1 : ℂ)) =
      (appendIso _ _).symm (siteVec own₁ (sitesU T E) (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
        siteVec own₂ (sitesU T E) (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
  rw [LinearIsometryEquiv.symm_apply_eq, pairUIso_siteVec, merge_restrict_U, merge_restrict_U]

theorem merge_self_of_mem_union (h : Disjoint T E) (u : ↥(T ∪ E)ᶜ → Fin q) (c : ι → Fin q)
    {x : ι} (hx : x ∈ T ∪ E) : merge h ((fun y : T => c y), u) c x = c x := by
  rcases Finset.mem_union.mp hx with hT | hE
  · exact threeSplit_symm_apply_of_mem_left h _ _ _ hT
  · exact merge_of_mem_E h _ c hE

theorem mem_sitesR_iff (x : ι) : x ∈ sitesR T E ↔ x ∈ T ∪ E := by
  simp only [mem_partSites_snd, mem_sites, true_and, decide_eq_false_iff_not, Finset.mem_compl,
    not_not]

theorem eval_correctionLayoutWord (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).eval
        ((appendIso (layoutRegs q l₁ own₁) (layoutRegs q l₂ own₂)).symm
          (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂)) =
      ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (appendIso (layoutRegs q l₁ own₁) (layoutRegs q l₂ own₂)).symm
          (layoutVec l₁ own₁ τ₁ (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
            layoutVec l₂ own₂ τ₂ (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
  simp only [correctionLayoutWord, layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply]
  simp only [Word.eval_assocWord_appendIso_symm, Word.eval_frameList_appendIso_symm,
    eval_partWordApp, eval_partWord, Word.eval_exchangeBlocks_appendIso_symm,
    Word.eval_unassocWord_appendIso_symm, eval_localMap]
  have hloc : (isoL (pairUIso (T := T) (E := E) own₁ own₂).symm ∘L matL W ∘L
      isoL (pairUIso own₁ own₂)) ((appendIso _ _).symm
        (siteVec own₁ (sitesU T E) c₁ ⊗ₜ siteVec own₂ (sitesU T E) c₂)) =
      ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (appendIso _ _).symm (siteVec own₁ (sitesU T E) (merge h ((fun x : T => c₁ x), u.1) c₁) ⊗ₜ
          siteVec own₂ (sitesU T E) (merge h ((fun x : T => c₂ x), u.2) c₂)) := by
    simp only [ContinuousLinearMap.comp_apply, isoL_apply]
    rw [pairUIso_siteVec, ← (EuclideanSpace.basisFun _ ℂ).sum_repr (matL W _), map_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [LinearIsometryEquiv.map_smul, EuclideanSpace.basisFun_repr, matL_single_apply,
      EuclideanSpace.basisFun_apply, pairUIso_symm_single h]
  rw [hloc]
  set κ : (↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q) → ℂ :=
    fun u => W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x))
  simp only [TensorProduct.sum_tmul, ← TensorProduct.smul_tmul', map_sum, map_smul]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  rw [siteVec_congr own₁ (sitesR T E) (c' := merge h ((fun x : T => c₁ x), u.1) c₁)
      fun x hx => (merge_self_of_mem_union h _ c₁ ((mem_sitesR_iff x).mp hx)).symm,
    siteVec_congr own₂ (sitesR T E) (c' := merge h ((fun x : T => c₂ x), u.2) c₂)
      fun x hx => (merge_self_of_mem_union h _ c₂ ((mem_sitesR_iff x).mp hx)).symm]
  simp only [Word.eval_assocWord_appendIso_symm, Word.eval_frameList_appendIso_symm,
    Word.eval_exchangeBlocks_appendIso_symm, Word.eval_unassocWord_appendIso_symm,
    eval_unpartWord, eval_unpartWordApp]

end Correction

/-! ### The renaming of a two-sheet exchange -/

namespace TwoSheetExchange

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} (X : TwoSheetExchange pos q Party)

/-- The sites in the region `Y`, in the order of `sites ι`. -/
abbrev sitesY : List ι := (partSites (fun x => decide (x ∈ X.region)) (sites ι)).1

/-- The sites outside the region `Y`, in the order of `sites ι`. -/
abbrev sitesN : List ι := (partSites (fun x => decide (x ∈ X.region)) (sites ι)).2

theorem mem_sitesY {x : ι} (hx : x ∈ X.sitesY) : x ∈ X.region := by
  simpa using ((mem_partSites_fst _ _ x).mp hx).2

theorem notMem_sitesN {x : ι} (hx : x ∈ X.sitesN) : x ∉ X.region := by
  simpa using ((mem_partSites_snd _ _ x).mp hx).2

/-- **The renaming `ℛ` as a word of exchanges of tensor factors.** Split the tags of both frames
into those of the holes outside and inside `Y`, move the raw registers of the sites in `Y` of
each sheet next to its inside tags, exchange these blocks between the two sheets, and merge back.
Every register keeps its party: a raw register of the first sheet at a site of `Y` becomes the
register of the second new frame at that site, whose owner is the old owner on the first sheet.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–490. -/
def renameWord : Word (X.frame₁.regs ++ X.frame₂.regs) (X.newFrame₁.regs ++ X.newFrame₂.regs) :=
  let pY : ι → Bool := fun x => decide (x ∈ X.region)
  let o₁ := tagRegs X.out₁
  let i₁ := tagRegs X.in₁
  let o₂ := tagRegs X.out₂
  let i₂ := tagRegs X.in₂
  let Y₁ := siteRegs q X.owner₁ X.sitesY
  let N₁ := siteRegs q X.owner₁ X.sitesN
  let Y₂ := siteRegs q X.owner₂ X.sitesY
  let N₂ := siteRegs q X.owner₂ X.sitesN
  let Y₁' := siteRegs q X.newFrame₁.owner X.sitesY
  let N₁' := siteRegs q X.newFrame₁.owner X.sitesN
  let Y₂' := siteRegs q X.newFrame₂.owner X.sitesY
  .comp (Word.assocWord (tagRegs (X.out₁ ++ X.in₁)) (siteRegs q X.owner₁ (sites ι))
    X.frame₂.regs) <|
  .comp (tagSplit X.out₁ X.in₁ (siteRegs q X.owner₁ (sites ι) ++ X.frame₂.regs)) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (partWordApp X.owner₁ pY X.frame₂.regs
    (sites ι)))) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (Word.frameList Y₁ (Word.frameList N₁
    (tagSplit X.out₂ X.in₂ (siteRegs q X.owner₂ (sites ι))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (Word.frameList Y₁ (Word.frameList N₁
    (Word.frameList o₂ (Word.frameList i₂ (partWord X.owner₂ pY (sites ι)))))))) <|
  .comp (Word.frameList o₁ (Word.swapPairs i₁ Y₁ N₁ o₂ i₂ Y₂ N₂)) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (relabelSitesApp X.owner₂ X.newFrame₁.owner
    (N₁ ++ (o₂ ++ (i₁ ++ (Y₁ ++ N₂)))) X.sitesY fun x hx => by
      simp [X.mem_sitesY hx]))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (relabelSitesApp X.owner₁
    X.newFrame₁.owner (o₂ ++ (i₁ ++ (Y₁ ++ N₂))) X.sitesN fun x hx => by
      simp [X.notMem_sitesN hx])))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (relabelSitesApp X.owner₁ X.newFrame₂.owner N₂
      X.sitesY fun x hx => by simp [X.mem_sitesY hx]))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (Word.frameList Y₂' (relabelSites X.owner₂
      X.newFrame₂.owner X.sitesN fun x hx => by simp [X.notMem_sitesN hx])))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (unpartWord X.newFrame₂.owner pY (sites ι)))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (tagMerge X.out₂ X.in₁ (siteRegs q X.newFrame₂.owner (sites ι))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (unpartWordApp X.newFrame₁.owner pY
    X.newFrame₂.regs (sites ι)))) <|
  .comp (tagMerge X.out₁ X.in₂ (siteRegs q X.newFrame₁.owner (sites ι) ++ X.newFrame₂.regs)) <|
  Word.unassocWord (tagRegs (X.out₁ ++ X.in₂)) (siteRegs q X.newFrame₁.owner (sites ι))
    X.newFrame₂.regs

theorem eval_renameWord (τ₁ : TagSpace (X.out₁ ++ X.in₁)) (c₁ : ι → Fin q)
    (τ₂ : TagSpace (X.out₂ ++ X.in₂)) (c₂ : ι → Fin q) :
    X.renameWord.eval ((appendIso X.frame₁.regs X.frame₂.regs).symm
        (layoutVec (X.out₁ ++ X.in₁) X.owner₁ τ₁ c₁ ⊗ₜ
          layoutVec (X.out₂ ++ X.in₂) X.owner₂ τ₂ c₂)) =
      (appendIso X.newFrame₁.regs X.newFrame₂.regs).symm
        (layoutVec (X.out₁ ++ X.in₂) X.newFrame₁.owner
            ((tagAppendEquiv X.out₁ X.in₂).symm
              ((tagAppendEquiv X.out₁ X.in₁ τ₁).1, (tagAppendEquiv X.out₂ X.in₂ τ₂).2))
            (fun x => if x ∈ X.region then c₂ x else c₁ x) ⊗ₜ
          layoutVec (X.out₂ ++ X.in₁) X.newFrame₂.owner
            ((tagAppendEquiv X.out₂ X.in₁).symm
              ((tagAppendEquiv X.out₂ X.in₂ τ₂).1, (tagAppendEquiv X.out₁ X.in₁ τ₁).2))
            (fun x => if x ∈ X.region then c₁ x else c₂ x)) := by
  set c₁' : ι → Fin q := fun x => if x ∈ X.region then c₂ x else c₁ x
  set c₂' : ι → Fin q := fun x => if x ∈ X.region then c₁ x else c₂ x
  have hY₁ : siteVec X.owner₁ X.sitesY c₁ = siteVec X.owner₁ X.sitesY c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', X.mem_sitesY hx]
  have hN₁ : siteVec X.owner₁ X.sitesN c₁ = siteVec X.owner₁ X.sitesN c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', X.notMem_sitesN hx]
  have hY₂ : siteVec X.owner₂ X.sitesY c₂ = siteVec X.owner₂ X.sitesY c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', X.mem_sitesY hx]
  have hN₂ : siteVec X.owner₂ X.sitesN c₂ = siteVec X.owner₂ X.sitesN c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', X.notMem_sitesN hx]
  simp only [renameWord, layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply]
  simp only [Word.eval_assocWord_appendIso_symm, eval_tagSplit, Word.eval_frameList_appendIso_symm,
    eval_partWordApp, eval_partWord, hY₁, hN₁, hY₂, hN₂, Word.eval_swapPairs,
    eval_relabelSitesApp, eval_relabelSites, eval_unpartWord, eval_tagMerge, eval_unpartWordApp,
    Word.eval_unassocWord_appendIso_symm]
  rw [eval_tagSplit]
  simp only [Word.eval_frameList_appendIso_symm, eval_partWord, hY₂, hN₂, Word.eval_swapPairs,
    eval_relabelSitesApp, eval_relabelSites, eval_unpartWord, eval_tagMerge, eval_unpartWordApp,
    Word.eval_unassocWord_appendIso_symm]

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
