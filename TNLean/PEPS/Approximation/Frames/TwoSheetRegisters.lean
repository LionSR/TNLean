/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.TaggedExchange
import TNLean.PEPS.Approximation.Frames.SheetStack
import TNLean.PEPS.Approximation.Frames.TwoSheetExchange

/-!
# The registers of two encoded frames and the two-sheet exchange

The two-sheet exchange of Lemma 6.6 acts on the registers of two frames: at every party, its
registers on the first frame and on the second (`twoFrameEquiv` identifies their configurations
with the product of the canonical coordinates of the two frames). Its proof implements the
exchange by a register renaming `ℛ` and private corrections at `P∘` (`05-frames.tex`,
lines 485–515). This file writes both on the registers of the frames:

* `TwoSheetExchange.renameWord` is the renaming as a relabelling of the bases of every party:
  the tags of each frame at a party are split into those of the holes outside and inside `Y`,
  the inside tags and the raw configurations of the sites in `Y` are exchanged between the
  sheets (`QuantumCircuit.Party.Sheet.swapInsideTags`, `QuantumCircuit.Party.Sheet.swapInEquiv`),
  and the tags are merged back. No register changes its party. Its operator in canonical
  coordinates is `ℛ` (`TwoSheetExchange.op_renameWord`).
* `TwoSheetExchange.correctionWord` applies, at `P∘` alone, the corrections of the exchange of
  the raw configurations of the two sheets (`QuantumCircuit.Party.Sheet.correctionAt`), beside
  the tags; its operator in canonical coordinates is `1_tags ⊗ D_U F_A`
  (`TwoSheetExchange.op_correctionWord`).

## Main definitions

* `EncodedFrame.twoFrameEquiv`: the registers of two frames in canonical coordinates.
* `EncodedFrame.TwoSheetExchange.renameWord`, `EncodedFrame.TwoSheetExchange.correctionWord`.

## Main results

* `EncodedFrame.pairRef_eq_twoFrameEquiv_symm`: the reference vector of two frames is
  `Ω_{F₁} ⊗ Ω_{F₂}` in canonical coordinates.
* `EncodedFrame.TwoSheetExchange.op_renameWord`, `EncodedFrame.TwoSheetExchange.op_correctionWord`,
  `EncodedFrame.TwoSheetExchange.op_comp_renameWord_correctionWord`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), proof of Lemma 6.6 `lem:exchange`,
  `05-frames.tex`, lines 481–561.
-/

noncomputable section

namespace TNLean.PEPS.EncodedFrame

open ManyBody QuantumCircuit.Party Matrix
open scoped Kronecker

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  [DecidableEq Party]

/-! ### The registers of two frames in canonical coordinates -/

/-- The registers of two lists of holes and two ownership assignments, identified with the
product of their canonical coordinates. -/
def twoLayoutEquiv (l₁ : List (Hole pos q Party)) (own₁ : ι → Party)
    (l₂ : List (Hole pos q Party)) (own₂ : ι → Party) :
    Config (fun p ↦ layoutSystem q l₁ own₁ p × layoutSystem q l₂ own₂ p) ≃
      (TagSpace l₁ × (ι → Fin q)) × (TagSpace l₂ × (ι → Fin q)) :=
  (Equiv.arrowProdEquivProdArrow Party _ _).trans
    ((layoutConfigEquiv l₁ own₁).prodCongr (layoutConfigEquiv l₂ own₂))

/-- The registers of two frames identified with the product of their canonical coordinates. -/
abbrev twoFrameEquiv (F₁ F₂ : Frame pos q Party) :
    Config (fun p ↦ F₁.system p × F₂.system p) ≃ F₁.Layout × F₂.Layout :=
  twoLayoutEquiv F₁.holes F₁.owner F₂.holes F₂.owner

/-- **The reference vector of two sheets in canonical coordinates.** The reference vector of two
frames on the product of their registers is `Ω_{F₁} ⊗ Ω_{F₂}` read through the coordinates of
the two frames. -/
theorem pairRef_eq_twoFrameEquiv_symm [Fintype Party] [NeZero q] (F₁ F₂ : Frame pos q Party)
    (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    pairRef F₁ F₂ Ω = LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (twoFrameEquiv F₁ F₂).symm
      (EuclideanSpace.vecKron (F₁.refVec Ω) (F₂.refVec Ω)) := by
  ext z
  simp [pairRef, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft'_apply,
    EuclideanSpace.vecKron, twoLayoutEquiv]

/-- A tag configuration of a concatenation assembled from the tags of its two parts at every
party is the concatenation of the two tag configurations. -/
theorem tagConfigEquiv_append_symm (l₁ l₂ : List (Hole pos q Party))
    (a : Config (tagSystem l₁)) (b : Config (tagSystem l₂)) :
    tagConfigEquiv (l₁ ++ l₂) (fun p ↦ (tagSystemAppendEquiv l₁ l₂ p).symm (a p, b p)) =
      (tagAppendEquiv l₁ l₂).symm (tagConfigEquiv l₁ a, tagConfigEquiv l₂ b) := by
  rw [Equiv.eq_symm_apply, tagAppendEquiv_tagConfigEquiv]
  simp

/-- The splitting of the tags of a concatenation at every party, read in canonical
coordinates. -/
theorem tagAppendEquiv_tagConfigEquiv_fst (l₁ l₂ : List (Hole pos q Party))
    (z : Config (tagSystem (l₁ ++ l₂))) :
    (tagAppendEquiv l₁ l₂ (tagConfigEquiv (l₁ ++ l₂) z)).1 =
      tagConfigEquiv l₁ fun p ↦ (tagSystemAppendEquiv l₁ l₂ p (z p)).1 := by
  rw [tagAppendEquiv_tagConfigEquiv]

theorem tagAppendEquiv_tagConfigEquiv_snd (l₁ l₂ : List (Hole pos q Party))
    (z : Config (tagSystem (l₁ ++ l₂))) :
    (tagAppendEquiv l₁ l₂ (tagConfigEquiv (l₁ ++ l₂) z)).2 =
      tagConfigEquiv l₂ fun p ↦ (tagSystemAppendEquiv l₁ l₂ p (z p)).2 := by
  rw [tagAppendEquiv_tagConfigEquiv]

/-! ### The exchange on the registers of two frames -/

namespace TwoSheetExchange

variable (X : TwoSheetExchange pos q Party)

omit [DecidableEq Party] in
/-- The sheet of the first frame after the exchange: inside `Y` the owners of the second. -/
theorem newFrame₁_sheet :
    X.newFrame₁.sheet = Sheet.swapIn X.frame₁.sheet X.frame₂.sheet X.region := rfl

omit [DecidableEq Party] in
/-- The sheet of the second frame after the exchange. -/
theorem newFrame₂_sheet :
    X.newFrame₂.sheet = Sheet.swapIn X.frame₂.sheet X.frame₁.sheet X.region := rfl

/-- The registers of the two frames at a party, grouped as the tags of the holes outside and
inside `Y` on both sheets, followed by the raw configurations on both sheets. -/
def inEquiv (p : Party) :
    X.frame₁.system p × X.frame₂.system p ≃
      ((tagSystem X.out₁ p × tagSystem X.in₁ p) × (tagSystem X.out₂ p × tagSystem X.in₂ p)) ×
        (X.frame₁.sheet.system q p × X.frame₂.sheet.system q p) :=
  (((tagSystemAppendEquiv X.out₁ X.in₁ p).prodCongr (Equiv.refl _)).prodCongr
    ((tagSystemAppendEquiv X.out₂ X.in₂ p).prodCongr (Equiv.refl _))).trans
      (Equiv.prodProdProdComm _ _ _ _)

/-- The registers of the two frames after the exchange at a party, grouped in the same way. -/
def outEquiv (p : Party) :
    X.newFrame₁.system p × X.newFrame₂.system p ≃
      ((tagSystem X.out₁ p × tagSystem X.in₂ p) × (tagSystem X.out₂ p × tagSystem X.in₁ p)) ×
        ((Sheet.swapIn X.frame₁.sheet X.frame₂.sheet X.region).system q p ×
          (Sheet.swapIn X.frame₂.sheet X.frame₁.sheet X.region).system q p) :=
  (((tagSystemAppendEquiv X.out₁ X.in₂ p).prodCongr (Equiv.refl _)).prodCongr
    ((tagSystemAppendEquiv X.out₂ X.in₁ p).prodCongr (Equiv.refl _))).trans
      (Equiv.prodProdProdComm _ _ _ _)

/-- **The renaming at one party.** The registers of a party after the exchange are those before
it: the inside tags and the raw configurations of the sites in `Y` change sheet. -/
def renameEquivAt (p : Party) :
    X.newFrame₁.system p × X.newFrame₂.system p ≃ X.frame₁.system p × X.frame₂.system p :=
  (X.outEquiv p).trans
    (((Sheet.swapInsideTags _ _ _ _).prodCongr
      (Sheet.swapInEquiv X.frame₁.sheet X.frame₂.sheet X.region p)).trans (X.inEquiv p).symm)

/-- **The renaming `ℛ` on the registers of the frames**: the relabelling of the bases of every
party along `renameEquivAt`. Every register keeps its party.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–490. -/
def renameWord : Word (fun p ↦ X.frame₁.system p × X.frame₂.system p)
    (fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p) :=
  PartyCircuit.relabel X.renameEquivAt

theorem isAllowed_renameWord : X.renameWord.IsAllowed :=
  Word.isAllowed_relabel _

theorem sourceCount_renameWord : X.renameWord.sourceCount = 0 :=
  rfl

/-- The swap `F_Y` read on the raw configurations of the two sheets before and after the
exchange is the renaming of `QuantumCircuit.Party.Sheet.swapInEquiv` (the same computation as
the operator of `QuantumCircuit.Party.Sheet.renameWord`). -/
private theorem twoConfigEquiv_symm_permCongr_pairSwap (S₁ S₂ : Sheet ι Party) (Y : Finset ι)
    (y : Config fun p ↦ (Sheet.swapIn S₁ S₂ Y).system q p × (Sheet.swapIn S₂ S₁ Y).system q p) :
    (Sheet.twoConfigEquiv q S₁ S₂).symm ((Equiv.arrowProdEquivProdArrow ι _ _).permCongr
        (pairSwap (X := fun _ : ι ↦ Fin q) Y) (Sheet.twoConfigEquiv q _ _ y)) =
      Equiv.piCongrRight (Sheet.swapInEquiv S₁ S₂ Y) y := by
  rw [permCongr_pairSwap_apply]
  funext p
  refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
  · have hv := (mem_blockPreimage_singleton _).mp v.2
    by_cases hY : (v : ι) ∈ Y
    · exact (ite_eq_left hY).trans ((Sheet.twoConfigEquiv_snd_eq _ _ y
        (show (Sheet.swapIn S₂ S₁ Y).owner v = p from
          (ite_eq_left hY).trans hv)).trans (by simp [Sheet.swapInEquiv, hY]))
    · exact (ite_eq_right hY).trans ((Sheet.twoConfigEquiv_fst_eq _ _ y
        (show (Sheet.swapIn S₁ S₂ Y).owner v = p from
          (ite_eq_right hY).trans hv)).trans (by simp [Sheet.swapInEquiv, hY]))
  · have hv := (mem_blockPreimage_singleton _).mp v.2
    by_cases hY : (v : ι) ∈ Y
    · exact (ite_eq_left hY).trans ((Sheet.twoConfigEquiv_fst_eq _ _ y
        (show (Sheet.swapIn S₁ S₂ Y).owner v = p from
          (ite_eq_left hY).trans hv)).trans (by simp [Sheet.swapInEquiv, hY]))
    · exact (ite_eq_right hY).trans ((Sheet.twoConfigEquiv_snd_eq _ _ y
        (show (Sheet.swapIn S₂ S₁ Y).owner v = p from
          (ite_eq_right hY).trans hv)).trans (by simp [Sheet.swapInEquiv, hY]))

/-- The renaming at every party, read in canonical coordinates, is the renaming `ℛ` of
`TwoSheetExchange.renameEquiv`. -/
theorem twoFrameEquiv_renameEquivAt
    (y : Config fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p) :
    twoFrameEquiv X.frame₁ X.frame₂ (Equiv.piCongrRight X.renameEquivAt y) =
      X.renameEquiv.symm (twoFrameEquiv X.newFrame₁ X.newFrame₂ y) := by
  have hraw : Sheet.twoConfigEquiv q X.frame₁.sheet X.frame₂.sheet
      (Equiv.piCongrRight (Sheet.swapInEquiv X.frame₁.sheet X.frame₂.sheet X.region)
        fun p ↦ ((y p).1.2, (y p).2.2)) =
      (Equiv.arrowProdEquivProdArrow ι _ _).permCongr (pairSwap (X := fun _ : ι ↦ Fin q) X.region)
        (Sheet.twoConfigEquiv q _ _ fun p ↦ ((y p).1.2, (y p).2.2)) := by
    rw [← twoConfigEquiv_symm_permCongr_pairSwap, Equiv.apply_symm_apply]
    rfl
  refine Prod.ext (Prod.ext ?h11 ?h12) (Prod.ext ?h21 ?h22)
  case h11 =>
    refine (tagConfigEquiv_append_symm _ _
      (fun p ↦ (tagSystemAppendEquiv X.out₁ X.in₂ p (y p).1.1).1)
      (fun p ↦ (tagSystemAppendEquiv X.out₂ X.in₁ p (y p).2.1).2)).trans ?_
    rw [← tagAppendEquiv_tagConfigEquiv_fst, ← tagAppendEquiv_tagConfigEquiv_snd]
    rfl
  case h12 => exact congrArg Prod.fst hraw
  case h21 =>
    refine (tagConfigEquiv_append_symm _ _
      (fun p ↦ (tagSystemAppendEquiv X.out₂ X.in₁ p (y p).2.1).1)
      (fun p ↦ (tagSystemAppendEquiv X.out₁ X.in₂ p (y p).1.1).2)).trans ?_
    rw [← tagAppendEquiv_tagConfigEquiv_fst, ← tagAppendEquiv_tagConfigEquiv_snd]
    rfl
  case h22 => exact congrArg (fun z ↦ z.2) hraw

variable [Fintype Party]

/-- **The renaming in canonical coordinates** is the renaming `ℛ` of
`TwoSheetExchange.rename`. -/
theorem op_renameWord :
    X.renameWord.op = reindex (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm
      (twoFrameEquiv X.frame₁ X.frame₂).symm X.rename := by
  ext y x
  rw [renameWord, Word.op, PartyCircuit.op_relabel, reindex_apply, submatrix_apply,
    Equiv.symm_symm, Equiv.symm_symm, rename]
  simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  refine if_congr ?_ rfl rfl
  rw [← twoFrameEquiv_renameEquivAt, (twoFrameEquiv X.frame₁ X.frame₂).apply_eq_iff_eq]

variable (P : Party)

/-- The corrections of the exchange beside the tags, at one party: at `P∘` the corrections
`QuantumCircuit.Party.Sheet.correctionAt` of the raw configurations of the two sheets, the
identity elsewhere. -/
def correctionAt (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P))
    (p : Party) :
    Matrix (X.newFrame₁.system p × X.newFrame₂.system p)
      (X.newFrame₁.system p × X.newFrame₂.system p) ℂ :=
  reindex (X.outEquiv p).symm (X.outEquiv p).symm
    ((1 : Matrix _ _ ℂ) ⊗ₖ Function.update (fun p ↦ (1 : Matrix
        ((Sheet.swapIn X.frame₁.sheet X.frame₂.sheet X.region).system q p ×
          (Sheet.swapIn X.frame₂.sheet X.frame₁.sheet X.region).system q p)
        ((Sheet.swapIn X.frame₁.sheet X.frame₂.sheet X.region).system q p ×
          (Sheet.swapIn X.frame₂.sheet X.frame₁.sheet X.region).system q p) ℂ)) P
      (Sheet.correctionAt X.frame₁.sheet X.frame₂.sheet X.region P (X.exchangeEnv P)
        (fun _ hx ↦ X.owner_eq_of_notMem_exchangeEnv P hx) σ) p)

/-- **The corrections `D_U F_A` as one private contraction at `P∘`.**

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 500–515. -/
def correctionWord (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    Word (fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p)
      (fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p) :=
  PartyCircuit.localOps (X.correctionAt P σ)

omit [Fintype Party] in
/-- The corrections are allowed. -/
theorem isAllowed_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    (X.correctionWord P σ).IsAllowed := by
  intro r
  refine (l2_opNorm_reindex_le _ _ _).trans ((l2_opNorm_one_kronecker_le _).trans ?_)
  by_cases hr : r = P
  · subst hr
    rw [Function.update_self]
    exact Sheet.norm_correctionAt_le_one _ _ _ _ _ _ σ
  · rw [Function.update_of_ne hr, ← PEquiv.toMatrix_refl, ← Equiv.toPEquiv_refl]
    exact l2_opNorm_toMatrix_toPEquiv_le _

omit [Fintype Party] in
/-- The corrections use only `P∘`. -/
theorem usesOnly_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    (X.correctionWord P σ).UsesOnly {P} := fun r hr ↦
  ⟨rfl, fun y x ↦ by
    rw [correctionAt, Function.update_of_ne hr, one_kronecker_one, reindex_apply, submatrix_apply,
      Equiv.symm_symm, one_apply, cast_eq]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    split_ifs <;> rfl⟩

omit [Fintype Party] in
/-- The corrections have no pair source. -/
theorem sourceCount_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    (X.correctionWord P σ).sourceCount = 0 :=
  rfl

/-- **The corrections in canonical coordinates** are `1_tags ⊗ D_U F_A`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 504–515. -/
theorem op_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    (X.correctionWord P σ).op =
      reindex (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm
        (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm
        (liftTags (l₁ := X.out₁ ++ X.in₂) (l₂ := X.out₂ ++ X.in₁)
          (configBufferCorrection Finset.subset_union_left σ * Matrix.reindex
            (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
            (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
            (ManyBody.pairSwapOp (X.aSet P)))) := by
  have hc := Sheet.op_correctionWord X.frame₁.sheet X.frame₂.sheet X.region P (X.exchangeEnv P)
    (fun _ hx ↦ X.owner_eq_of_notMem_exchangeEnv P hx) σ
  simp only [Sheet.correctionWord, Word.op, PartyCircuit.op_localOps] at hc
  ext y x
  have hcyx := congrFun (congrFun hc (fun p ↦ (X.outEquiv p (y p)).2))
    (fun p ↦ (X.outEquiv p (x p)).2)
  rw [correctionWord, Word.op, PartyCircuit.op_localOps, piKronecker_apply]
  simp only [correctionAt, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    one_apply, ite_mul, one_mul, zero_mul]
  rw [piKronecker_apply] at hcyx
  rw [Fintype.prod_ite_zero, hcyx]
  simp only [liftTags, reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply,
    one_apply, Equiv.prodProdProdComm_apply, ite_mul, one_mul, zero_mul]
  refine if_congr ?_ rfl rfl
  constructor
  · intro h
    have h₁ : (fun p ↦ (y p).1.1) = fun p ↦ (x p).1.1 := funext fun p ↦
      (tagSystemAppendEquiv X.out₁ X.in₂ p).injective
        (Prod.ext (congrArg (fun t ↦ t.1.1) (h p))
          (congrArg (fun t ↦ t.1.2) (h p)))
    have h₂ : (fun p ↦ (y p).2.1) = fun p ↦ (x p).2.1 := funext fun p ↦
      (tagSystemAppendEquiv X.out₂ X.in₁ p).injective
        (Prod.ext (congrArg (fun t ↦ t.2.1) (h p))
          (congrArg (fun t ↦ t.2.2) (h p)))
    simp only [twoLayoutEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
      layoutConfigEquiv_apply, Equiv.arrowProdEquivProdArrow_apply]
    rw [h₁, h₂]
  · intro h p
    simp only [twoLayoutEquiv, Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map,
      layoutConfigEquiv_apply, Equiv.arrowProdEquivProdArrow_apply, Prod.mk.injEq] at h
    have h₁ := congrFun ((tagConfigEquiv _).injective h.1) p
    have h₂ := congrFun ((tagConfigEquiv _).injective h.2) p
    change (tagSystemAppendEquiv X.out₁ X.in₂ p (y p).1.1,
        tagSystemAppendEquiv X.out₂ X.in₁ p (y p).2.1) =
      (tagSystemAppendEquiv X.out₁ X.in₂ p (x p).1.1, tagSystemAppendEquiv X.out₂ X.in₁ p (x p).2.1)
    rw [h₁, h₂]

/-- **The exchange in canonical coordinates**: the renaming followed by the corrections is
`C = D_U F_A ℛ`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–527. -/
theorem op_comp_renameWord_correctionWord
    (σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P)) :
    Word.op (PartyCircuit.comp X.renameWord (X.correctionWord P σ)) =
      reindex (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm (twoFrameEquiv X.frame₁ X.frame₂).symm
        (X.exchangeOp P σ) := by
  rw [Word.op_comp, op_correctionWord, op_renameWord, exchangeOp, reindex_apply, reindex_apply,
    reindex_apply, submatrix_mul_equiv]
  rfl

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
