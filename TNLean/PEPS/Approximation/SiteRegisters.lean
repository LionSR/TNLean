/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.OwnershipMonomials
import TNLean.PEPS.Approximation.WordPermutation

/-!
# Raw registers of sites and tag registers of holes

The source has one raw register `ℂ^q` at every site of a sheet and one tag register for every
hole of an encoded frame, each held by a specified party (`05-frames.tex`, lines 13–20 and
Definition 6.1). This file lists such registers on a party layout
(`TNLean.PEPS.Approximation.PartyWord`) and provides the words of exchanges of tensor factors
that move them; the layout of a whole frame is `TNLean.PEPS.Approximation.FrameRegisters`.

* `siteRegs q own S` lists one register `ℂ^q` for each site of the list `S`, the register of `x`
  held by `own x`; `siteVec own S c` is the product basis vector `⊗_{x ∈ S} |c x⟩`, and
  `groupIso` identifies the registers of `S` with `ℂ^{κ → Fin q}` along an enumeration of `S`
  by `κ`, sending `siteVec` to a standard basis vector (`groupIso_siteVec`).
* `relabelSitesApp` names the registers of `S` with other owner labels that agree on `S`; it
  moves no register and uses no party.
* `partWordApp` moves the registers of the sites of `S` satisfying a predicate in front of the
  others, keeping the order within both parts, by exchanges of adjacent tensor factors, and
  `unpartWordApp` moves them back (`eval_partWordApp`, `eval_unpartWordApp`). Both act in front
  of further registers `tail`, which are untouched; `partWord`, `unpartWord` and `relabelSites`
  are the same words with no further registers, read through `Word.appendNil` and
  `Word.dropNil`.
* `tagRegs l` lists one register `ℂ^{Tag}` for each hole of `l`, held by its tag owner, with
  basis vectors `tagVec` and the identification `tagIso` with `ℂ^{TagSpace l}`.

Every word built here is a reordering (`PairEffect.Word.IsReordering`): it is allowed, uses no
party and no pair source.

## Main definitions

* `PairEffect.Word.IsReordering`: allowed, using no party and no pair source, with constructor
  lemmas for identities, exchanges, composition and framing.
* `PairEffect.Word.appendNil`, `PairEffect.Word.dropNil`: reading `ℓ` as `ℓ ++ []` and back.
* `EncodedFrame.siteRegs`, `EncodedFrame.siteVec`, `EncodedFrame.siteIsoList`,
  `EncodedFrame.groupIso`.
* `EncodedFrame.relabelHead`, `EncodedFrame.relabelSitesApp`, `EncodedFrame.relabelSites`.
* `EncodedFrame.partSites`, `EncodedFrame.partWordApp`, `EncodedFrame.unpartWordApp`,
  `EncodedFrame.partWord`, `EncodedFrame.unpartWord`.
* `EncodedFrame.tagRegs`, `EncodedFrame.tagVec`, `EncodedFrame.tagIso`.

## Main results

* `EncodedFrame.groupIso_siteVec`, `EncodedFrame.tagIso_tagVec`: the identifications on basis
  vectors.
* `EncodedFrame.eval_partWordApp`, `EncodedFrame.eval_unpartWordApp`,
  `EncodedFrame.eval_relabelSitesApp`, `EncodedFrame.eval_partWord`,
  `EncodedFrame.eval_unpartWord`, `EncodedFrame.eval_relabelSites`: the operators of the words on
  basis vectors.
* `PairEffect.Word.eval_frameList_appendIso_symm`: a word framed by untouched registers.

## References

* Polynomial-PEPS manuscript (September 24, 2026), sheets, `05-frames.tex`, lines 13–20;
  Definition 6.1 `def:frame`, lines 71–82; allowed monomials, `04-compression.tex`,
  lines 21–35.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct

/-! ### Reorderings use no party and no pair source -/

namespace TNLean.PEPS.PairEffect.Word

variable {P : Type}

/-- A word is a *reordering* when it is allowed, uses no party and has no pair source: it only
exchanges, frames and renames tensor factors, so it is an allowed monomial at any list of
parties.

Polynomial-PEPS manuscript (September 24, 2026), `04-compression.tex`, lines 32–35. -/
def IsReordering {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') : Prop :=
  w.IsAllowed ∧ (∀ S : Set P, w.UsesOnly S) ∧ w.sourceCount = 0

namespace IsReordering

variable {ℓ ℓ' : Layout P} {w : Word ℓ ℓ'}

theorem isAllowed (hw : w.IsReordering) : w.IsAllowed := hw.1

theorem usesOnly (hw : w.IsReordering) (S : Set P) : w.UsesOnly S := hw.2.1 S

theorem sourceCount_eq (hw : w.IsReordering) : w.sourceCount = 0 := hw.2.2

end IsReordering

@[simp] theorem isReordering_id (ℓ : Layout P) : (Word.id ℓ).IsReordering :=
  ⟨trivial, fun _ => trivial, rfl⟩

@[simp] theorem isReordering_swap (r r' : Reg P) (ℓ : Layout P) : (swap r r' ℓ).IsReordering :=
  ⟨trivial, fun _ => trivial, rfl⟩

@[simp] theorem isReordering_comp_iff {ℓ₁ ℓ₂ ℓ₃ : Layout P} (w : Word ℓ₁ ℓ₂)
    (w' : Word ℓ₂ ℓ₃) : (comp w w').IsReordering ↔ w.IsReordering ∧ w'.IsReordering := by
  simp only [IsReordering, IsAllowed, UsesOnly, sourceCount, forall_and, Nat.add_eq_zero_iff]
  tauto

theorem IsReordering.comp {ℓ₁ ℓ₂ ℓ₃ : Layout P} {w : Word ℓ₁ ℓ₂} {w' : Word ℓ₂ ℓ₃}
    (hw : w.IsReordering) (hw' : w'.IsReordering) : (Word.comp w w').IsReordering :=
  (isReordering_comp_iff w w').2 ⟨hw, hw'⟩

@[simp] theorem isReordering_frame_iff (r : Reg P) {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (frame r w).IsReordering ↔ w.IsReordering :=
  Iff.rfl

@[simp] theorem isReordering_frameList_iff {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (ℓ₀ : Layout P) → (frameList ℓ₀ w).IsReordering ↔ w.IsReordering
  | [] => Iff.rfl
  | _ :: ℓ₀ => isReordering_frameList_iff w ℓ₀

theorem IsReordering.frameList {ℓ ℓ' : Layout P} {w : Word ℓ ℓ'} (hw : w.IsReordering)
    (ℓ₀ : Layout P) : (Word.frameList ℓ₀ w).IsReordering :=
  (isReordering_frameList_iff w ℓ₀).2 hw

@[simp] theorem isReordering_moveHead (r : Reg P) :
    (ℓ₀ tail : Layout P) → (moveHead r ℓ₀ tail).IsReordering
  | [], _ => isReordering_id _
  | _ :: ℓ₀, tail => IsReordering.comp (isReordering_moveHead r ℓ₀ tail) (isReordering_swap ..)

@[simp] theorem isReordering_exchangeBlocks (a : Layout P) :
    (b tail : Layout P) → (exchangeBlocks a b tail).IsReordering
  | [], _ => isReordering_id _
  | r :: b, tail => IsReordering.comp (isReordering_moveHead r a (b ++ tail))
      (isReordering_exchangeBlocks a b tail)

/-- A word framed by untouched registers acts on the second factor of the concatenation. -/
theorem eval_frameList_appendIso_symm {ℓ ℓ' : Layout P} (w : Word ℓ ℓ') :
    (ℓ₀ : Layout P) → (a : Mem ℓ₀) → (b : Mem ℓ) →
      (frameList ℓ₀ w).eval ((appendIso ℓ₀ ℓ).symm (a ⊗ₜ b)) =
        (appendIso ℓ₀ ℓ').symm (a ⊗ₜ w.eval b)
  | [], a, b => by
      change w.eval (TensorProduct.lidIsometry ℂ (Mem ℓ) (a ⊗ₜ b)) =
        TensorProduct.lidIsometry ℂ (Mem ℓ') (a ⊗ₜ w.eval b)
      simp
  | r :: ℓ₀, a, b => by
      induction a using TensorProduct.inductionOn with
      | tmul x s =>
          rw [appendIso_symm_cons_tmul, appendIso_symm_cons_tmul]
          change x ⊗ₜ (frameList ℓ₀ w).eval _ = _
          rw [eval_frameList_appendIso_symm w ℓ₀ s b]
      | add x y hx hy => simp only [TensorProduct.add_tmul, map_add, hx, hy]

/-- The registers `ℓ` read as `ℓ ++ []`; no register moves. -/
def appendNil : (ℓ : Layout P) → Word ℓ (ℓ ++ [])
  | [] => .id []
  | r :: ℓ => .frame r (appendNil ℓ)

/-- The registers `ℓ ++ []` read as `ℓ`; no register moves. -/
def dropNil : (ℓ : Layout P) → Word (ℓ ++ []) ℓ
  | [] => .id []
  | r :: ℓ => .frame r (dropNil ℓ)

theorem eval_appendNil : (ℓ : Layout P) → (x : Mem ℓ) →
    (appendNil ℓ).eval x = (appendIso ℓ []).symm (x ⊗ₜ (1 : Mem ([] : Layout P)))
  | [], x => by
      rw [appendIso_nil_symm_tmul]
      exact (mul_one x).symm
  | r :: ℓ, x => by
      induction x using TensorProduct.inductionOn with
      | tmul u m =>
          rw [appendIso_symm_cons_tmul, ← eval_appendNil ℓ m]
          rfl
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

theorem eval_dropNil : (ℓ : Layout P) → (x : Mem ℓ) →
    (dropNil ℓ).eval ((appendIso ℓ []).symm (x ⊗ₜ (1 : Mem ([] : Layout P)))) = x
  | [], x => by
      rw [appendIso_nil_symm_tmul]
      exact mul_one x
  | r :: ℓ, x => by
      induction x using TensorProduct.inductionOn with
      | tmul u m =>
          rw [appendIso_symm_cons_tmul]
          exact congrArg (fun v => (u ⊗ₜ v : Mem (r :: ℓ))) (eval_dropNil ℓ m)
      | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

@[simp] theorem isReordering_appendNil : (ℓ : Layout P) → (appendNil ℓ).IsReordering
  | [] => isReordering_id _
  | _ :: ℓ => isReordering_appendNil ℓ

@[simp] theorem isReordering_dropNil : (ℓ : Layout P) → (dropNil ℓ).IsReordering
  | [] => isReordering_id _
  | _ :: ℓ => isReordering_dropNil ℓ

end TNLean.PEPS.PairEffect.Word

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### Raw registers of a list of sites -/

/-- The raw registers `ℂ^q` of a list of sites, the register of `x` held by `own x`. -/
def siteRegs (q : ℕ) (own : ι → Party) (S : List ι) : Layout Party :=
  S.map fun x => ⟨own x, euc (Fin q)⟩

/-- The product basis vector `⊗_{x ∈ S} |c x⟩` of the raw registers of `S`. -/
def siteVec (own : ι → Party) : (S : List ι) → (ι → Fin q) → Mem (siteRegs q own S)
  | [], _ => (1 : ℂ)
  | x :: S, c => (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
      siteVec own S c

/-- The raw registers of `S`, identified with `ℂ^{Fin |S| → Fin q}` by listing the sites. -/
def siteIsoList (own : ι → Party) :
    (S : List ι) → Mem (siteRegs q own S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Fin S.length → Fin q)
  | [] => emptyIso (Fin q)
  | _ :: S => ((siteIsoList own S).lTensor (EuclideanSpace ℂ (Fin q))).trans
      (consIso (Fin q) S.length)

/-- The identification of the raw registers of a list sends `⊗_x |c x⟩` to the standard basis
vector of the configuration read along the list. -/
theorem siteIsoList_siteVec (own : ι → Party) (c : ι → Fin q) :
    (S : List ι) → siteIsoList own S (siteVec own S c) =
      EuclideanSpace.single (fun k => c (S.get k)) (1 : ℂ)
  | [] => by
      change emptyIso (Fin q) (1 : ℂ) = _
      ext f
      rw [emptyIso_one (0 : EuclideanSpace ℂ (Fin q))]
      simp only [tensorPower, piTensor_apply, Finset.univ_eq_empty, Finset.prod_empty,
        PiLp.single_apply]
      have hf : f = fun k => c ([].get k) := funext fun k => k.elim0
      simp only [hf, ↓reduceIte]
  | x :: S => by
      have hc : (fun k : Fin (x :: S).length => c ((x :: S).get k)) =
          Fin.cons (c x) (fun k => c (S.get k)) := by
        funext k
        refine Fin.cases rfl (fun _ => rfl) k
      change consIso (Fin q) S.length ((siteIsoList own S).lTensor (EuclideanSpace ℂ (Fin q))
        ((EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c)) = _
      ext f
      rw [LinearIsometryEquiv.lTensor_tmul, siteIsoList_siteVec own c S, consIso_tmul_apply, hc]
      simp only [PiLp.single_apply]
      by_cases h : f = Fin.cons (c x) (fun k => c (S.get k))
      · subst h
        simp
      · simp only [h, ↓reduceIte]
        by_cases h0 : f 0 = c x
        · have ht : Fin.tail f ≠ fun k => c (S.get k) := fun ht =>
            h (by rw [← Fin.cons_self_tail f, h0, ht])
          simp only [h0, ht, ↓reduceIte, mul_zero]
        · simp only [h0, ↓reduceIte, zero_mul]

/-- The raw registers of `S` grouped into one register `ℂ^{κ → Fin q}`, along an enumeration
`e` of the positions of the list by `κ`. -/
def groupIso (own : ι → Party) (S : List ι) {κ : Type} [Fintype κ] [DecidableEq κ]
    (e : Fin S.length ≃ κ) :
    Mem (siteRegs q own S) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (κ → Fin q) :=
  (siteIsoList own S).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (e.arrowCongr (Equiv.refl (Fin q))))

/-- **Grouped raw registers on basis vectors.** If the list `S` is enumerated by `κ` through
`f`, the grouping sends `⊗_{x ∈ S} |c x⟩` to `|c ∘ f⟩`. -/
theorem groupIso_siteVec (own : ι → Party) (S : List ι) {κ : Type} [Fintype κ]
    [DecidableEq κ] (e : Fin S.length ≃ κ) (f : κ → ι) (hf : ∀ k, S.get k = f (e k))
    (c : ι → Fin q) :
    groupIso own S e (siteVec own S c) = EuclideanSpace.single (c ∘ f) (1 : ℂ) := by
  rw [groupIso, LinearIsometryEquiv.trans_apply, siteIsoList_siteVec,
    EuclideanSpace.piLpCongrLeft_single]
  congr 1
  funext j
  simp only [Equiv.arrowCongr_apply, Equiv.coe_refl, Function.comp_apply, id_eq]
  rw [hf, Equiv.apply_symm_apply]


/-! ### Relabelling owners -/

/-- The front register, held by `p`, named as a register of `p' = p`. -/
def relabelHead {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party) :
    Word (⟨p, X⟩ :: ℓ) (⟨p', X⟩ :: ℓ) :=
  h ▸ .id _

theorem eval_relabelHead {p p' : Party} (h : p = p') (X : HSpace) (ℓ : Layout Party)
    (z : Mem (⟨p, X⟩ :: ℓ)) : (relabelHead h X ℓ).eval z = z := by
  subst h
  rfl

@[simp] theorem isReordering_relabelHead {p p' : Party} (h : p = p') (X : HSpace)
    (ℓ : Layout Party) : (relabelHead h X ℓ).IsReordering := by
  subst h
  exact Word.isReordering_id _

/-! ### Partitioning a list of sites -/

/-- The sites of a list satisfying `p`, and the others, each in their order in the list.

This is `List.partition` (`partSites_eq`), written by structural recursion so that the type of
`partStepApp` at `x :: S` unfolds to a `cond` on `p x`. -/
def partSites (p : ι → Bool) : List ι → List ι × List ι
  | [] => ([], [])
  | x :: S => cond (p x) (x :: (partSites p S).1, (partSites p S).2)
      ((partSites p S).1, x :: (partSites p S).2)

theorem partSites_eq (p : ι → Bool) :
    (S : List ι) → partSites p S = (S.filter p, S.filter fun x => !p x)
  | [] => rfl
  | x :: S => by
      rw [partSites, partSites_eq p S]
      cases h : p x <;> simp [h]

theorem mem_partSites_fst (p : ι → Bool) (S : List ι) (x : ι) :
    x ∈ (partSites p S).1 ↔ x ∈ S ∧ p x = true := by
  rw [partSites_eq, List.mem_filter]

theorem mem_partSites_snd (p : ι → Bool) (S : List ι) (x : ι) :
    x ∈ (partSites p S).2 ↔ x ∈ S ∧ p x = false := by
  simp [partSites_eq]

theorem nodup_partSites_fst (p : ι → Bool) {S : List ι} (hS : S.Nodup) :
    (partSites p S).1.Nodup := by
  rw [partSites_eq]
  exact hS.filter _

theorem nodup_partSites_snd (p : ι → Bool) {S : List ι} (hS : S.Nodup) :
    (partSites p S).2.Nodup := by
  rw [partSites_eq]
  exact hS.filter _

/-! ### Moving the raw registers of a list in front of further registers -/

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

/-- `partWordApp` on product basis vectors in front of further registers. -/
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
      rw [appendIso_nil_symm_tmul (ℓ := tail), one_smul, appendIso_nil_symm_tmul, one_smul]
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

/-- `unpartWordApp` on product basis vectors in front of further registers. -/
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
      rw [appendIso_nil_symm_tmul, one_smul]
  | x :: S => by
      refine (congrArg (Word.frame _ (unpartWordApp (q := q) own p tail S)).eval
        (eval_unpartStepApp own x (partSites p S).1 (partSites p S).2 tail c y (p x))).trans ?_
      change (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
        (unpartWordApp (q := q) own p tail S).eval _ = _
      rw [eval_unpartWordApp own p tail c y S]
      rfl

@[simp] theorem isReordering_partStepApp (own : ι → Party) (x : ι) (a b : List ι)
    (tail : Layout Party) : (c : Bool) → (partStepApp (q := q) own x a b tail c).IsReordering
  | true => Word.isReordering_id _
  | false => Word.isReordering_exchangeBlocks ..

@[simp] theorem isReordering_unpartStepApp (own : ι → Party) (x : ι) (a b : List ι)
    (tail : Layout Party) : (c : Bool) → (unpartStepApp (q := q) own x a b tail c).IsReordering
  | true => Word.isReordering_id _
  | false => Word.isReordering_moveHead ..

@[simp] theorem isReordering_partWordApp (own : ι → Party) (p : ι → Bool) (tail : Layout Party) :
    (S : List ι) → (partWordApp (q := q) own p tail S).IsReordering
  | [] => Word.isReordering_id _
  | x :: S => Word.IsReordering.comp
      ((Word.isReordering_frame_iff _ _).2 (isReordering_partWordApp own p tail S))
      (isReordering_partStepApp own x _ _ tail (p x))

@[simp] theorem isReordering_unpartWordApp (own : ι → Party) (p : ι → Bool)
    (tail : Layout Party) : (S : List ι) → (unpartWordApp (q := q) own p tail S).IsReordering
  | [] => Word.isReordering_id _
  | x :: S => Word.IsReordering.comp (isReordering_unpartStepApp own x _ _ tail (p x))
      ((Word.isReordering_frame_iff _ _).2 (isReordering_unpartWordApp own p tail S))

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

/-- Renaming owners in front of further registers moves no vector. -/
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

@[simp] theorem isReordering_relabelSitesApp (own own' : ι → Party) (tail : Layout Party) :
    (S : List ι) → (h : ∀ x ∈ S, own x = own' x) →
      (relabelSitesApp (q := q) own own' tail S h).IsReordering
  | [], _ => Word.isReordering_id _
  | x :: S, h => Word.IsReordering.comp
      ((Word.isReordering_frame_iff _ _).2 (isReordering_relabelSitesApp own own' tail S
        fun y hy => h y (List.mem_cons_of_mem x hy)))
      (isReordering_relabelHead _ _ _)

/-! ### The same words without further registers -/

/-- The raw registers of `S` with owners `own`, named with owners `own'` that agree on `S`.
No register changes its party. -/
def relabelSites (own own' : ι → Party) (S : List ι) (h : ∀ x ∈ S, own x = own' x) :
    Word (siteRegs q own S) (siteRegs q own' S) :=
  .comp (Word.appendNil _) (.comp (relabelSitesApp own own' [] S h) (Word.dropNil _))

/-- The registers of the sites satisfying `p` moved to the front by exchanges of adjacent
tensor factors, the order within both parts kept. -/
def partWord (own : ι → Party) (p : ι → Bool) (S : List ι) :
    Word (siteRegs q own S)
      (siteRegs q own (partSites p S).1 ++ siteRegs q own (partSites p S).2) :=
  .comp (Word.appendNil _) (.comp (partWordApp own p [] S) (Word.frameList _ (Word.dropNil _)))

/-- The inverse of `partWord`. -/
def unpartWord (own : ι → Party) (p : ι → Bool) (S : List ι) :
    Word (siteRegs q own (partSites p S).1 ++ siteRegs q own (partSites p S).2)
      (siteRegs q own S) :=
  .comp (Word.frameList _ (Word.appendNil _)) (.comp (unpartWordApp own p [] S) (Word.dropNil _))

/-- Renaming owners moves no vector. -/
theorem eval_relabelSites (own own' : ι → Party) (c : ι → Fin q) (S : List ι)
    (h : ∀ x ∈ S, own x = own' x) :
    (relabelSites own own' S h).eval (siteVec own S c) = siteVec own' S c := by
  simp only [relabelSites, Word.eval_comp, comp_apply, Word.eval_appendNil]
  rw [eval_relabelSitesApp, Word.eval_dropNil]

/-- **Moving the registers of the sites satisfying `p` to the front.** On a product basis
vector the word gives the product vectors of the two parts. -/
theorem eval_partWord (own : ι → Party) (p : ι → Bool) (c : ι → Fin q) (S : List ι) :
    (partWord own p S).eval (siteVec own S c) =
      (appendIso _ _).symm
        (siteVec own (partSites p S).1 c ⊗ₜ siteVec own (partSites p S).2 c) := by
  simp only [partWord, Word.eval_comp, comp_apply, Word.eval_appendNil]
  rw [eval_partWordApp, Word.eval_frameList_appendIso_symm, Word.eval_dropNil]

/-- The inverse reordering on product basis vectors. -/
theorem eval_unpartWord (own : ι → Party) (p : ι → Bool) (c : ι → Fin q) (S : List ι) :
    (unpartWord own p S).eval
        ((appendIso _ _).symm (siteVec own (partSites p S).1 c ⊗ₜ
          siteVec own (partSites p S).2 c)) = siteVec own S c := by
  simp only [unpartWord, Word.eval_comp, comp_apply, Word.eval_frameList_appendIso_symm,
    Word.eval_appendNil]
  rw [eval_unpartWordApp, Word.eval_dropNil]

@[simp] theorem isReordering_relabelSites (own own' : ι → Party) (S : List ι)
    (h : ∀ x ∈ S, own x = own' x) : (relabelSites (q := q) own own' S h).IsReordering := by
  simp [relabelSites]

@[simp] theorem isReordering_partWord (own : ι → Party) (p : ι → Bool) (S : List ι) :
    (partWord (q := q) own p S).IsReordering := by
  simp [partWord]

@[simp] theorem isReordering_unpartWord (own : ι → Party) (p : ι → Bool) (S : List ι) :
    (unpartWord (q := q) own p S).IsReordering := by
  simp [unpartWord]

/-- The product vector of `S` depends only on the configuration on `S`. -/
theorem siteVec_congr (own : ι → Party) {c c' : ι → Fin q} :
    (S : List ι) → (∀ x ∈ S, c x = c' x) → siteVec own S c = siteVec own S c'
  | [], _ => rfl
  | x :: S, h => by
      change (EuclideanSpace.single (c x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c = (EuclideanSpace.single (c' x) (1 : ℂ) : EuclideanSpace ℂ (Fin q)) ⊗ₜ
          siteVec own S c'
      rw [h x List.mem_cons_self,
        siteVec_congr own S fun y hy => h y (List.mem_cons_of_mem x hy)]

/-! ### Tag registers -/

section Tags

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The tag registers of a list of holes, in the order of the list, the tag of a hole held by
its tag owner. -/
def tagRegs : List (Hole pos q Party) → Layout Party
  | [] => []
  | h :: l => ⟨h.tagOwner, euc h.patch.Tag⟩ :: tagRegs l

/-- The basis vector `⊗_a |τ_a⟩` of the tag registers. -/
def tagVec : (l : List (Hole pos q Party)) → TagSpace l → Mem (tagRegs l)
  | [], _ => (1 : ℂ)
  | h :: l, τ => (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
      tagVec l τ.2

/-- The tag registers identified with `ℂ^{TagSpace l}`. -/
def tagIso : (l : List (Hole pos q Party)) → Mem (tagRegs l) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (TagSpace l)
  | [] => (OrthonormalBasis.singleton Unit ℂ).repr
  | h :: l => ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)).trans
      (pairIso h.patch.Tag (TagSpace l))

/-- The tag registers on basis vectors: `⊗_a |τ_a⟩ ↦ |τ⟩`. -/
theorem tagIso_tagVec : (l : List (Hole pos q Party)) → (τ : TagSpace l) →
    tagIso l (tagVec l τ) = EuclideanSpace.single τ (1 : ℂ)
  | [], τ => by
      change (OrthonormalBasis.singleton Unit ℂ).repr (1 : ℂ) = _
      ext u
      rw [OrthonormalBasis.singleton_repr]
      erw [PiLp.single_apply]
      split_ifs with hu
      · rfl
      · exact absurd rfl hu
  | h :: l, τ => by
      change pairIso h.patch.Tag (TagSpace l) ((tagIso l).lTensor (EuclideanSpace ℂ h.patch.Tag)
        ((EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) ⊗ₜ
          tagVec l τ.2)) = _
      ext i
      rw [LinearIsometryEquiv.lTensor_tmul, tagIso_tagVec l τ.2, pairIso_tmul_apply]
      change (EuclideanSpace.single τ.1 (1 : ℂ) : EuclideanSpace ℂ h.patch.Tag) i.1 *
          (EuclideanSpace.single τ.2 (1 : ℂ) : EuclideanSpace ℂ (TagSpace l)) i.2 =
        (EuclideanSpace.single (τ : h.patch.Tag × TagSpace l) (1 : ℂ) :
          EuclideanSpace ℂ (h.patch.Tag × TagSpace l)) i
      simp only [PiLp.single_apply, ite_zero_mul_ite_zero, one_mul]
      erw [PiLp.single_apply]
      split_ifs with h₁ h₂ h₂
      · rfl
      · exact absurd (Prod.ext h₁.1 h₁.2) h₂
      · exact absurd ⟨congrArg Prod.fst h₂, congrArg Prod.snd h₂⟩ h₁
      · rfl

end Tags

end TNLean.PEPS.EncodedFrame
