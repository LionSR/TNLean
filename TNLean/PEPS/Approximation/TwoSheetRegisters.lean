/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.FrontChanges
import TNLean.PEPS.Approximation.FrameRegisters
import TNLean.PEPS.Approximation.RegisterReordering

/-!
# The registers of two encoded frames and the two-sheet exchange

The two-sheet exchange of Lemma 6.6 acts on the registers of two frames, those of the first
frame followed by those of the second (`twoLayoutIso` identifies them with the product of the
canonical coordinates of the two frames). Its proof implements the exchange by a register
renaming `ℛ` and private corrections at `P∘` (`05-frames.tex`, lines 485–515). This file writes
both on the registers of the frames:

* `TwoSheetExchange.renameWord` is the renaming as a word of exchanges of tensor factors: the
  tags of each frame are split into those of the holes outside and inside `Y`, the raw registers
  of the sites in `Y` of each sheet are moved next to its inside tags, these blocks are exchanged
  between the sheets, and everything is merged back. No register changes its party. Its operator
  in canonical coordinates is `ℛ` (`twoLayoutIso_renameWord`). Between the splitting and the
  merging of the tags it is the word `blockRenameWord` of `TNLean.Lattice.Sheet.FrontChanges`,
  stated there for any blocks of front registers outside and inside `Y`.
* `correctionLayoutWord` moves the raw registers of `U` of both sheets to the front, applies a
  matrix `W` to them as one private contraction at `P∘`, and moves them back; its operator is
  `1_tags ⊗ (1_{T E} ⊗ W)` (`twoLayoutIso_correctionLayoutWord`). It is the word
  `frontCorrectionWord` of `TNLean.Lattice.Sheet.TwoRegisters`, stated there for any blocks of
  front registers, read with the tag registers of the two frames in front.

## Main definitions

* `EncodedFrame.twoLayoutIso`: the registers of two frames in canonical coordinates.
* `EncodedFrame.correctionLayoutWord`.
* `EncodedFrame.TwoSheetExchange.renameWord`.

## Main results

* `EncodedFrame.twoLayoutIso_eq_act_of_basis`: operators on two frames are determined by their
  values on basis vectors.
* `EncodedFrame.twoLayoutIso_correctionLayoutWord`, `EncodedFrame.correctionLayoutWord_props`.
* `EncodedFrame.TwoSheetExchange.twoLayoutIso_renameWord`,
  `EncodedFrame.TwoSheetExchange.isReordering_renameWord`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.
-/

noncomputable section

open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame

open PairEffect ContinuousLinearMap EuclideanSpace

variable {ι : Type} {q : ℕ} {Party : Type}

/-! ### The registers of two frames in canonical coordinates -/

section TwoLayout

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ}

/-- The registers of two frames, those of the first followed by those of the second, identified
with the product `ℂ^{L₁ × L₂}` of their canonical coordinates. -/
def twoLayoutIso (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party) :
    Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) ≃ₗᵢ[ℂ]
      EuclideanSpace ℂ ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) :=
  (appendIso _ _).trans ((((layoutIso l₁ own₁).rTensor _).trans
    ((layoutIso l₂ own₂).lTensor _)).trans (pairIso _ _))

theorem twoLayoutIso_symm_single (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    (twoLayoutIso l₁ l₂ own₁ own₂).symm (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) =
      (appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂) := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  change _ = pairIso _ _ ((layoutIso l₂ own₂).lTensor _ ((layoutIso l₁ own₁).rTensor _
    (appendIso _ _ ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ
      layoutVec l₂ own₂ τ₂ c₂)))))
  rw [LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.rTensor_tmul,
    LinearIsometryEquiv.lTensor_tmul,
    layoutIso_layoutVec, layoutIso_layoutVec, pairIso_single_tmul_single]

theorem twoLayoutIso_basis (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    twoLayoutIso l₁ l₂ own₁ own₂
        ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂)) =
      EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ) := by
  rw [← twoLayoutIso_symm_single, LinearIsometryEquiv.apply_symm_apply]

/-- Two operators on the registers of two frames agree in canonical coordinates as soon as they
agree on the basis vectors. -/
theorem twoLayoutIso_eq_act_of_basis (l₁ l₂ : List (Hole pos q Party)) (own₁ own₂ : ι → Party)
    (l₁' l₂' : List (Hole pos q Party)) (own₁' own₂' : ι → Party)
    (f : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂) →L[ℂ]
      Mem (layoutRegs q l₁' own₁' ++ layoutRegs q l₂' own₂'))
    (A : Matrix ((TagSpace l₁' × (ι → Fin q)) × (TagSpace l₂' × (ι → Fin q)))
      ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q))) ℂ)
    (hf : ∀ τ₁ c₁ τ₂ c₂, twoLayoutIso l₁' l₂' own₁' own₂'
      (f ((appendIso _ _).symm (layoutVec l₁ own₁ τ₁ c₁ ⊗ₜ layoutVec l₂ own₂ τ₂ c₂))) =
        act A (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)))
    (z : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)) :
    twoLayoutIso l₁' l₂' own₁' own₂' (f z) = act A (twoLayoutIso l₁ l₂ own₁ own₂ z) := by
  obtain ⟨y, rfl⟩ : ∃ y, z = (twoLayoutIso l₁ l₂ own₁ own₂).symm y :=
    ⟨twoLayoutIso l₁ l₂ own₁ own₂ z, by simp⟩
  rw [LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  conv_rhs => rw [← (EuclideanSpace.basisFun _ ℂ).sum_repr y]
  simp only [map_sum, map_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨⟨τ₁, c₁⟩, ⟨τ₂, c₂⟩⟩ := i
  rw [EuclideanSpace.basisFun_apply, twoLayoutIso_symm_single, hf]

end TwoLayout

/-! ### A private contraction on the raw registers of `U` on two sheets -/

section Correction

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} {T E : Finset ι}

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
  frontCorrectionWord (tagRegs l₁) (tagRegs l₂) own₁ own₂ h₁ h₂ W

/-- **The corrections on basis vectors.** The configurations of the two sheets on `U` are
mixed by `W`; those on `T ∪ E` and the tags are untouched. -/
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
            layoutVec l₂ own₂ τ₂ (merge h ((fun x : T => c₂ x), u.2) c₂)) :=
  eval_frontCorrectionWord h (tagRegs l₁) (tagRegs l₂) own₁ own₂ h₁ h₂ W (tagVec l₁ τ₁) c₁
    (tagVec l₂ τ₂) c₂

theorem sum_single_merge₂ (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (τ₁ : TagSpace l₁) (c₁ : ι → Fin q) (τ₂ : TagSpace l₂) (c₂ : ι → Fin q) :
    ∑ u, W u ((fun x : ↥(T ∪ E)ᶜ => c₁ x), (fun x : ↥(T ∪ E)ᶜ => c₂ x)) •
        (EuclideanSpace.single ((τ₁, merge h ((fun x : T => c₁ x), u.1) c₁),
          (τ₂, merge h ((fun x : T => c₂ x), u.2) c₂)) (1 : ℂ) :
          EuclideanSpace ℂ ((TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)))) =
      act (liftTags (l₁ := l₁) (l₂ := l₂) (twoSheetPlace h W))
        (EuclideanSpace.single ((τ₁, c₁), (τ₂, c₂)) (1 : ℂ)) :=
  sum_single_merge₂_liftFront h W τ₁ c₁ τ₂ c₂

/-- **The corrections in canonical coordinates.** The correction word acts on the registers of
the two frames as `1_tags ⊗ (1_{T E} ⊗ W)`. -/
theorem twoLayoutIso_correctionLayoutWord (h : Disjoint T E) (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    (W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ)
    (z : Mem (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)) :
    twoLayoutIso l₁ l₂ own₁ own₂ ((correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).eval z) =
      act (liftTags (l₁ := l₁) (l₂ := l₂) (twoSheetPlace h W)) (twoLayoutIso l₁ l₂ own₁ own₂ z) :=
  twoFrontLayoutIso_frontCorrectionWord h (tagRegs l₁) (tagIso l₁) (tagRegs l₂) (tagIso l₂) own₁
    own₂ h₁ h₂ W z

/-- The corrections form an allowed word using only `P`, without pair sources. -/
theorem correctionLayoutWord_props (l₁ l₂ : List (Hole pos q Party))
    (own₁ own₂ : ι → Party) {P : Party}
    (h₁ : ∀ x ∈ (T ∪ E)ᶜ, own₁ x = P) (h₂ : ∀ x ∈ (T ∪ E)ᶜ, own₂ x = P)
    {W : Matrix ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q))
      ((↥(T ∪ E)ᶜ → Fin q) × (↥(T ∪ E)ᶜ → Fin q)) ℂ} (hW : ‖W‖ ≤ 1) :
    (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).IsAllowed ∧
      (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).UsesOnly {P} ∧
      (correctionLayoutWord l₁ l₂ own₁ own₂ h₁ h₂ W).sourceCount = 0 :=
  frontCorrectionWord_props (tagRegs l₁) (tagRegs l₂) own₁ own₂ h₁ h₂ hW

end Correction

/-! ### The renaming of a two-sheet exchange -/

namespace TwoSheetExchange

variable [Fintype ι] [DecidableEq ι] {pos : ι → ℝ × ℝ} (X : TwoSheetExchange pos q Party)

/-- The sites in the region `Y`, in the order of `sites ι`. -/
abbrev sitesY : List ι := listT (sites ι) X.region

/-- The sites outside the region `Y`, in the order of `sites ι`. -/
abbrev sitesN : List ι := listR (sites ι) X.region

/-- **The renaming `ℛ` as a word of exchanges of tensor factors.** Split the tags of both frames
into those of the holes outside and inside `Y`, move the raw registers of the sites in `Y` of
each sheet next to its inside tags, exchange these blocks between the two sheets, and merge back.
Every register keeps its party: a raw register of the first sheet at a site of `Y` becomes the
register of the second new frame at that site, whose owner is the old owner on the first sheet.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–490. -/
def renameWord : Word (X.frame₁.regs ++ X.frame₂.regs) (X.newFrame₁.regs ++ X.newFrame₂.regs) :=
  .comp (Word.assocWord (tagRegs (X.out₁ ++ X.in₁)) (siteRegs q X.owner₁ (sites ι))
    X.frame₂.regs) <|
  .comp (tagSplit X.out₁ X.in₁ (siteRegs q X.owner₁ (sites ι) ++ X.frame₂.regs)) <|
  .comp (Word.frameList (tagRegs X.out₁) (Word.frameList (tagRegs X.in₁)
    (Word.frameList (siteRegs q X.owner₁ (sites ι))
      (tagSplit X.out₂ X.in₂ (siteRegs q X.owner₂ (sites ι)))))) <|
  .comp (blockRenameWord (tagRegs X.out₁) (tagRegs X.in₁) (tagRegs X.out₂) (tagRegs X.in₂)
    X.owner₁ X.owner₂ X.region) <|
  .comp (Word.frameList (tagRegs X.out₁) (Word.frameList (tagRegs X.in₂)
    (Word.frameList (siteRegs q X.newFrame₁.owner (sites ι))
      (tagMerge X.out₂ X.in₁ (siteRegs q X.newFrame₂.owner (sites ι)))))) <|
  .comp (tagMerge X.out₁ X.in₂ (siteRegs q X.newFrame₁.owner (sites ι) ++ X.newFrame₂.regs)) <|
  Word.unassocWord (tagRegs (X.out₁ ++ X.in₂)) (siteRegs q X.newFrame₁.owner (sites ι))
    X.newFrame₂.regs

/-- **The renaming on basis vectors.** Inside `Y` the configurations and the inside tags of the
two sheets change places. -/
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
  simp only [renameWord, layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply,
    Word.eval_assocWord_appendIso_symm, eval_tagSplit]
  erw [Word.eval_frameList_appendIso_symm, Word.eval_frameList_appendIso_symm,
    Word.eval_frameList_appendIso_symm, eval_tagSplit, eval_blockRenameWord]
  simp only [Word.eval_frameList_appendIso_symm, eval_tagMerge,
    Word.eval_unassocWord_appendIso_symm]

/-- **The renaming in canonical coordinates** is the renaming `ℛ` of `TwoSheetExchange.rename`. -/
theorem twoLayoutIso_renameWord
    (z : Mem (X.frame₁.regs ++ X.frame₂.regs)) :
    twoLayoutIso (X.out₁ ++ X.in₂) (X.out₂ ++ X.in₁) X.newFrame₁.owner X.newFrame₂.owner
        (X.renameWord.eval z) =
      act X.rename (twoLayoutIso (X.out₁ ++ X.in₁) (X.out₂ ++ X.in₂) X.owner₁ X.owner₂ z) :=
  twoLayoutIso_eq_act_of_basis _ _ _ _ _ _ _ _ _ _ (fun τ₁ c₁ τ₂ c₂ => by
    rw [eval_renameWord, twoLayoutIso_basis, rename, act_toMatrix_symm_single]
    rfl) z

/-- The renaming is a reordering: an allowed word using no party and no pair source. -/
@[simp] theorem isReordering_renameWord : X.renameWord.IsReordering := by
  simp [renameWord]

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
