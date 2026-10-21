/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Approximation.TwoSheetRegisters

/-!
# Births, deaths and exchanges as bounded changes

Lemmas 6.5 and 6.6 of the polynomial-PEPS manuscript assert that a homogeneous birth or death,
and a two-sheet exchange, are bounded changes: monomials allowed by Theorem 5.2 on a fixed list
of parties, with small reference-vector error. This file proves these assertions on the
registers of the frames, one register per site and per tag, each held by its owner
(`TNLean.PEPS.Approximation.FrameRegisters`), in their canonical coordinates.

* `Frame.birth_bounded`: the birth is an allowed word using only `P∘` and `Q∘`, with at most one
  normalized pair source, whose operator is `1_tags ⊗ B` for the canonical map `B` of
  `eq:birth-map`; the reference-vector error is at most `L^{-30}`. The word groups the raw
  registers of `T` and `U` at `P∘` (`groupWord`), applies the birth monomial of
  `TNLean.PEPS.Approximation.OwnershipMonomials`, and ungroups at `Q∘` and `P∘`.
* `Frame.death_bounded`: the death is the same with one normalized pair effect instead.
* `TwoSheetExchange.exchange_bounded`: the exchange is the renaming `ℛ`, a word of exchanges of
  tensor factors, followed by one private contraction at `P∘`; it uses only `P∘`, and its
  operator is `C = D_U F_A ℛ` with reference-vector error at most `4 L^{-30}`.
* `TwoSheetExchange.exchange_ofFrames_bounded`: the same for two frames whose holes are listed in
  any order, after the canonical identification of tag orderings, itself a word of exchanges.

The words of the birth and the death do not act on the tag registers. They are
`exists_frontBirthWord` and `exists_frontDeathChain` of `TNLean.Lattice.Sheet.FrontChanges`,
stated for any block of registers in front of the raw registers and read here with the tag
registers of the holes in front; read with the empty front block they give the bounds for
sheets without holes, `Lattice.Sheet.birth_bounded` and `Lattice.Sheet.death_bounded`, which
are stated for any exponent: `I_Ω(T:E) ≤ L^{-2p}` gives error `L^{-p}`; the frame bounds here are
the manuscript's case `p = 30`. The
reference error of the exchange is bounded on the sheets by
`norm_act_sheetBufferCorrection_mul_sheetSwapOp_sub_le`, shared with
`Lattice.Sheet.exchange_bounded`.

## Main results

* `EncodedFrame.Frame.birth_bounded`, `EncodedFrame.Frame.death_bounded`: Lemma 6.5 `lem:birth`.
* `EncodedFrame.TwoSheetExchange.exchange_bounded`,
  `EncodedFrame.TwoSheetExchange.exchange_ofFrames_bounded`: Lemma 6.6 `lem:exchange`.
* `EncodedFrame.exists_tagReorderWord`: the canonical identification of tag orderings of two
  frames as a word.

## References

* Polynomial-PEPS manuscript (September 24, 2026), bounded changes, `05-frames.tex`,
  lines 99–105; Lemma 6.5 `lem:birth`, lines 396–447; Lemma 6.6 `lem:exchange`, lines 460–561;
  allowed monomials, `04-compression.tex`, lines 32–35.
-/

open TNLean.Lattice (sheetSwapOp)

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker

namespace TNLean.PEPS.EncodedFrame

open PairEffect

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

namespace Frame

variable (F : Frame pos q Party)

variable {T : Finset ι} {P Q : Party}

/-- **Lemma 6.5 (homogeneous birth): the birth is a bounded change involving only `P∘` and
`Q∘`.** In an encoded frame `F`, let `T` be a set of raw sites owned by `P∘` and disjoint from
every outer hole footprint, and let `E` and `U = Λ ∖ (T ∪ E)` be as in `eq:birth-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data and an allowed monomial `w`
from the registers of `F` (one per site and per tag, each held by its owner) to the registers
of the frame `F'` in which `T` is owned by `Q∘`, such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source; the statement records
  these counts, which are what a bounded change asks for (`05-frames.tex`, lines 99–105). The
  monomial constructed in the proof groups the registers of `T` and of `U` at `P∘`, applies, for
  `Q∘ ≠ P∘`, the private contraction `⟨s| (1_T ⊗ V)` at `P∘`, prepares the pair state `s` on `T`
  held by `Q∘` and `B_T` held by `P∘` and applies `Vᴴ` at `P∘`, and ungroups `T` at `Q∘` and `U`
  at `P∘`, with exchanges of tensor factors in between;
* in canonical coordinates the operator of `w` is `1_tags ⊗ B` for the canonical map `B` of
  `eq:birth-map`, and `(1 ⊗ B) K_F = K_{F'} B`;
* the reference-vector error is at most `L^{-30}`: `‖w Ω_F - Ω_{F'}‖ ≤ L^{-30}`, with the
  reference vectors read on the registers of the two frames.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437 and 445–446; bounded changes, lines 99–105; allowed monomials, `04-compression.tex`,
lines 32–35. -/
theorem birth_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ∃ w : Word F.regs (F.changeOwner T Q).regs,
        w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
        (∀ z, (F.changeOwner T Q).regIso (w.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.regIso z)) ∧
        ‖w.eval (F.regIso.symm (F.refVec Ω)) -
          (F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)‖ ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.birth (Q := Q) hTP hTH hΩ hI
  obtain ⟨hB, hA', hB', hE'⟩ := F.changeOwner_birth_owners (Q := Q) hTP hTH
  obtain ⟨w, hwA, hwU, hwS, hw⟩ := exists_frontBirthWord (tagRegs F.holes) (tagIso F.holes)
    F.owner (F.changeOwner T Q).owner (F.disjoint_birthEnv hTP hTH) hTP hB hA' hB'
    (fun x hx => (hE' x hx).symm) σ
  have heval : ∀ z, (F.changeOwner T Q).regIso (w.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
        sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.regIso z) := hw
  refine ⟨σ, hσ, hK, w, hwA, hwU, hwS, heval, ?_⟩
  rw [← (F.changeOwner T Q).regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply,
    heval, LinearIsometryEquiv.apply_symm_apply]
  exact herr

/-- **Lemma 6.5 (homogeneous death): the death is a bounded change involving only `P∘` and
`Q∘`.** Let `F` be the frame *after* the death, in which `T` is owned by `P∘` and avoids every
outer hole footprint, and let the frame before the death be `F'`, in which `T` is owned by
`Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in `F`, there are splitting data and an allowed
monomial from the registers of `F'` to those of `F`, using only `P∘` and `Q∘`, without pair
sources and with at most one normalized pair effect, whose operator in canonical coordinates is
`1_tags ⊗ B` for the canonical map `B` of `eq:birth-map`, with `(1 ⊗ B) K_{F'} = K_F B` and
reference-vector error `‖M Ω_{F'} - Ω_F‖ ≤ L^{-30}`. The statement records the parties and the
pair-resource counts; the monomial constructed in the proof groups the registers of `T` at `Q∘`
and of `U` at `P∘`, then, for `Q∘ ≠ P∘`, applies `V` at `P∘`, contracts `T` and `B_T` with the
pair effect `⟨s|` held by `Q∘` and `P∘`, reinserts `s` and applies `Vᴴ` at `P∘`, and ungroups at
`P∘`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem death_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ∃ M : PartyChain (F.changeOwner T Q).regs F.regs,
        M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
        (∀ z, F.regIso (M.toEffectChain.eval z) =
          act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).regIso z)) ∧
        ‖M.toEffectChain.eval ((F.changeOwner T Q).regIso.symm ((F.changeOwner T Q).refVec Ω)) -
          F.regIso.symm (F.refVec Ω)‖ ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.death (Q := Q) hTP hTH hΩ hI
  obtain ⟨hB', hA, hB, hE⟩ := F.changeOwner_birth_owners (Q := Q) hTP hTH
  obtain ⟨M, hMA, hMU, hMS, hMe, hM⟩ := exists_frontDeathChain (tagRegs F.holes)
    (tagIso F.holes) (F.changeOwner T Q).owner F.owner (F.disjoint_birthEnv hTP hTH) hA hB hTP
    hB' hE σ
  have heval : ∀ z, F.regIso (M.toEffectChain.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
        sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).regIso z) := hM
  refine ⟨σ, hσ, hK, M, hMA, hMU, hMS, hMe, heval, ?_⟩
  rw [← F.regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply, heval,
    LinearIsometryEquiv.apply_symm_apply]
  exact herr

end Frame

/-- **The canonical identification of tag orderings on two frames, as a word.** If `l₁'`, `l₂'`
list the holes of `l₁`, `l₂` in other orders, there are relabellings `e₁`, `e₂` of the tag
configurations preserving the raw parts of the encodings and a word of exchanges of tensor
factors, using no party, whose operator in canonical coordinates is the relabelling
`tagReorder e₁ e₂`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 74–75 and 84–85. -/
theorem exists_tagReorderWord [NeZero q] {l₁ l₁' l₂ l₂' : List (Hole pos q Party)}
    (hd₁ : PairwiseDisjointOuter (l₁.map Hole.patch))
    (hd₂ : PairwiseDisjointOuter (l₂.map Hole.patch)) (hp₁ : l₁.Perm l₁') (hp₂ : l₂.Perm l₂')
    (own₁ own₂ : ι → Party) :
    ∃ (e₁ : TagSpace l₁ ≃ TagSpace l₁') (e₂ : TagSpace l₂ ≃ TagSpace l₂'),
      (∀ t, rawProd l₁' (e₁ t) = rawProd l₁ t) ∧ (∀ t, rawProd l₂' (e₂ t) = rawProd l₂ t) ∧
      ∃ w : Word (layoutRegs q l₁ own₁ ++ layoutRegs q l₂ own₂)
          (layoutRegs q l₁' own₁ ++ layoutRegs q l₂' own₂),
        w.IsReordering ∧ ∀ z, twoLayoutIso l₁' l₂' own₁ own₂ (w.eval z) =
          act (TwoSheetExchange.tagReorder e₁ e₂) (twoLayoutIso l₁ l₂ own₁ own₂ z) := by
  obtain ⟨e₁, he₁, w₁, a₁, hw₁⟩ := exists_tagWord_of_perm hd₁ hp₁
    (siteRegs q own₁ (sites ι) ++ layoutRegs q l₂ own₂)
  obtain ⟨e₂, he₂, w₂, a₂, hw₂⟩ := exists_tagWord_of_perm hd₂ hp₂
    (siteRegs q own₂ (sites ι))
  refine ⟨e₁, e₂, he₁, he₂,
    (Word.assocWord (tagRegs l₁) (siteRegs q own₁ (sites ι)) (layoutRegs q l₂ own₂)).comp
      (w₁.comp ((Word.unassocWord (tagRegs l₁') (siteRegs q own₁ (sites ι))
        (layoutRegs q l₂ own₂)).comp (Word.frameList (layoutRegs q l₁' own₁) w₂))),
    by simp [a₁, a₂], ?_⟩
  · refine twoLayoutIso_eq_act_of_basis _ _ _ _ _ _ _ _ _ _ fun τ₁ c₁ τ₂ c₂ => ?_
    simp only [layoutVec, Word.eval_comp, ContinuousLinearMap.comp_apply,
      Word.eval_assocWord_appendIso_symm, hw₁, Word.eval_unassocWord_appendIso_symm,
      Word.eval_frameList_appendIso_symm, hw₂]
    rw [← layoutVec, ← layoutVec, twoLayoutIso_basis, TwoSheetExchange.tagReorder,
      act_toMatrix_symm_single]
    rfl

namespace TwoSheetExchange

open EuclideanSpace (vecKron)

variable (X : TwoSheetExchange pos q Party) (P : Party)

/-- **Lemma 6.6 (two-sheet exchange): the exchange is implemented by private contractions and a
register renaming.** Consider two encoded frames and a region `Y` such that every hole's outer
square lies on one side of `∂Y`, with the holes of each frame listed as those outside `Y`
followed by those inside. Let `P∘` be a party and `Z`, `T`, `E`, `U` as in `eq:exchange-Z` and
`eq:exchange-partition`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data
and an allowed monomial `w` from the registers of the two frames (one per site and per tag on
each sheet, each held by its owner) to the registers of the two frames after the exchange, such
that:

* `w` uses only `P∘` and no pair resource; the monomial constructed in the proof is the renaming
  `ℛ`, a word of exchanges of tensor factors that keeps every register at its party, followed by
  one private contraction at `P∘` on the raw registers of `U` of both sheets (the corrections
  `D_U F_A`);
* in canonical coordinates its operator is the map `C = D_U F_A ℛ`, with
  `C (K_{F₁} ⊗ K_{F₂}) = K_out D_U F_T`;
* the reference-vector error is at most `4 L^{-30}`:
  `‖w (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`, read on the registers of the frames.

Hence the exchange is a bounded change in the sense of Theorem 5.2.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479; proof
lines 481–561; bounded changes, lines 99–105. -/
theorem exchange_bounded [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω (X.tSet P) (X.eSet P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q (X.tSet P) (X.eSet P),
      σ.error (X.disjoint_tSet_eSet P) Ω ≤ L ^ (-30 : ℤ) ∧
      X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
        (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
          (sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.tSet P)) ∧
      ∃ w : Word (X.frame₁.regs ++ X.frame₂.regs) (X.newFrame₁.regs ++ X.newFrame₂.regs),
        w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
        (∀ z, twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner (w.eval z) =
          act (X.exchangeOp P σ) (twoLayoutIso _ _ X.owner₁ X.owner₂ z)) ∧
        ‖w.eval ((twoLayoutIso _ _ X.owner₁ X.owner₂).symm
            (vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω))) -
          (twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner).symm
            (vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω))‖ ≤ 4 * L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, hK, herr⟩ := X.exchange P hΩ hI
  set h := X.disjoint_tSet_eSet P
  have hU : ∀ x ∈ (X.tSet P ∪ X.eSet P)ᶜ,
      X.newFrame₁.owner x = P ∧ X.newFrame₂.owner x = P := fun x hx =>
    X.newOwner_eq_of_notMem_exchangeEnv P (by
      rw [← X.tSet_union_eSet P]
      exact Finset.mem_compl.mp hx)
  have heval : ∀ z, twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner
      ((X.renameWord.comp (correctionLayoutWord (X.out₁ ++ X.in₂) (X.out₂ ++ X.in₁)
        X.newFrame₁.owner X.newFrame₂.owner (fun x hx => (hU x hx).1) (fun x hx => (hU x hx).2)
        (correctionMatrix σ (X.aSet P)))).eval z) =
      act (X.exchangeOp P σ) (twoLayoutIso _ _ X.owner₁ X.owner₂ z) := by
    intro z
    rw [Word.eval_comp, ContinuousLinearMap.comp_apply, twoLayoutIso_correctionLayoutWord h,
      twoLayoutIso_renameWord, ← act_mul, exchangeOp,
      sheetBufferCorrection_mul_sheetSwapOp_eq h σ (X.aSet_subset_compl P)]
  have r := X.isReordering_renameWord
  obtain ⟨c₁, c₂, c₃⟩ := correctionLayoutWord_props (q := q) (X.out₁ ++ X.in₂) (X.out₂ ++ X.in₁)
    X.newFrame₁.owner X.newFrame₂.owner (fun x hx => (hU x hx).1) (fun x hx => (hU x hx).2)
    (norm_correctionMatrix_le_one σ (X.aSet P))
  refine ⟨σ, hσ, hK, X.renameWord.comp (correctionLayoutWord (X.out₁ ++ X.in₂)
    (X.out₂ ++ X.in₁) X.newFrame₁.owner X.newFrame₂.owner (fun x hx => (hU x hx).1)
    (fun x hx => (hU x hx).2) (correctionMatrix σ (X.aSet P))), ⟨r.isAllowed, c₁⟩,
    ⟨r.usesOnly _, c₂⟩, congrArg₂ (· + ·) r.sourceCount_eq c₃, heval, ?_⟩
  rw [← (twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner).norm_map, map_sub,
    LinearIsometryEquiv.apply_symm_apply, heval, LinearIsometryEquiv.apply_symm_apply]
  exact herr

/-- **Lemma 6.6 (two-sheet exchange) for frames with holes in any order: the exchange is a bounded
change.** Let `F₁`, `F₂` be encoded frames and `Y` the physical sample of a region, with the
holes of both frames classified as outside or inside the region as in `ofFrames`. With `Z`, `T`,
`E`, `U` computed from the two frames (`mem_ofFrames_exchangeEnv`), if `I_Ω(T:E) ≤ L^{-60}` for a
unit vector `Ω`, there are relabellings `e₁`, `e₂` of the tag configurations identifying the
encodings of each frame with those of its holes listed outside first (the canonical
identification of tag orderings), splitting data with error at most `L^{-30}`, and an allowed
monomial `w` from the registers of `F₁` and `F₂` to the registers of the two frames after the
exchange, such that `w` uses only `P∘` and no pair resource (the monomial constructed in the
proof consists of exchanges of tensor factors and one private contraction at `P∘`), acts in
canonical coordinates as
`C G = D_U F_A ℛ G` with `G = tagReorder e₁ e₂`, satisfies `C G (K_{F₁} ⊗ K_{F₂}) = K_out D_U F_T`,
and has reference-vector error `‖w (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`.

The statement constrains `e₁` and `e₂` only by preserving the raw parts of the encodings. The
relabellings constructed in the proof (`exists_tagWord_of_perm`) are the ones implemented by the
exchanges of tag registers, which move the tag of each hole to that hole's position in the new
list; the operator, the intertwining relation and the error bound are stated for these.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479, with the
canonical identification of tag orderings of lines 75–76 and 84–85; proof lines 481–561;
bounded changes, lines 99–105. -/
theorem exchange_ofFrames_bounded [NeZero q] (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true → Disjoint (h.patch.outer : Set ι) Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false → (h.patch.outer : Set ι) ⊆ Y) (P : Party)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω
      ((ofFrames F₁ F₂ Y out hout hin).tSet P) ((ofFrames F₁ F₂ Y out hout hin).eSet P) ≤
        L ^ (-60 : ℤ)) :
    ∃ (e₁ : TagSpace F₁.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₁.holes)
      (e₂ : TagSpace F₂.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₂.holes),
      (∀ t, rawProd _ (e₁ t) = rawProd F₁.holes t) ∧ (∀ t, rawProd _ (e₂ t) = rawProd F₂.holes t) ∧
      ∃ σ : SplittingData q ((ofFrames F₁ F₂ Y out hout hin).tSet P)
          ((ofFrames F₁ F₂ Y out hout hin).eSet P),
        σ.error ((ofFrames F₁ F₂ Y out hout hin).disjoint_tSet_eSet P) Ω ≤ L ^ (-30 : ℤ) ∧
        (ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂ *
            (F₁.encoder ⊗ₖ F₂.encoder) =
          ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.encoder ⊗ₖ
              (ofFrames F₁ F₂ Y out hout hin).newFrame₂.encoder) *
            (sheetBufferCorrection ((ofFrames F₁ F₂ Y out hout hin).disjoint_tSet_eSet P) σ *
              sheetSwapOp q ((ofFrames F₁ F₂ Y out hout hin).tSet P)) ∧
        ∃ w : Word (F₁.regs ++ F₂.regs) ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.regs ++
            (ofFrames F₁ F₂ Y out hout hin).newFrame₂.regs),
          w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
          (∀ z, twoLayoutIso _ _ (ofFrames F₁ F₂ Y out hout hin).newFrame₁.owner
              (ofFrames F₁ F₂ Y out hout hin).newFrame₂.owner (w.eval z) =
            act ((ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂)
              (twoLayoutIso _ _ F₁.owner F₂.owner z)) ∧
          ‖w.eval ((twoLayoutIso _ _ F₁.owner F₂.owner).symm
              (vecKron (F₁.refVec Ω) (F₂.refVec Ω))) -
            (twoLayoutIso _ _ (ofFrames F₁ F₂ Y out hout hin).newFrame₁.owner
                (ofFrames F₁ F₂ Y out hout hin).newFrame₂.owner).symm
              (vecKron ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.refVec Ω)
                ((ofFrames F₁ F₂ Y out hout hin).newFrame₂.refVec Ω))‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set X := ofFrames F₁ F₂ Y out hout hin
  obtain ⟨e₁, e₂, he₁, he₂, g, hgR, hg⟩ := exists_tagReorderWord (q := q) F₁.disjoint
    F₂.disjoint (List.filter_append_perm out F₁.holes).symm
    (List.filter_append_perm out F₂.holes).symm F₁.owner F₂.owner
  obtain ⟨σ, hσ, hK, w, w₁, w₂, w₃, hw, herr⟩ := X.exchange_bounded P hΩ hI
  have hG : tagReorder e₁ e₂ * (F₁.encoder ⊗ₖ F₂.encoder) =
      X.frame₁.encoder ⊗ₖ X.frame₂.encoder :=
    tagReorder_mul_kronecker he₁ he₂
  have heval : ∀ z, twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner ((g.comp w).eval z) =
      act (X.exchangeOp P σ * (tagReorder e₁ e₂ :
        Matrix (X.frame₁.Layout × X.frame₂.Layout) (F₁.Layout × F₂.Layout) ℂ))
        (twoLayoutIso _ _ F₁.owner F₂.owner z) := by
    intro z
    calc _ = act (X.exchangeOp P σ)
          (twoLayoutIso _ _ X.owner₁ X.owner₂ (g.eval z)) := hw (g.eval z)
      _ = act (X.exchangeOp P σ) (act (tagReorder e₁ e₂ :
          Matrix (X.frame₁.Layout × X.frame₂.Layout) (F₁.Layout × F₂.Layout) ℂ)
            (twoLayoutIso _ _ F₁.owner F₂.owner z)) := congrArg (act (X.exchangeOp P σ)) (hg z)
      _ = _ := (act_mul _ _ _).symm
  refine ⟨e₁, e₂, he₁, he₂, σ, hσ, ?_, g.comp w, ⟨hgR.isAllowed, w₁⟩, ⟨hgR.usesOnly {P}, w₂⟩,
    congrArg₂ (· + ·) hgR.sourceCount_eq w₃, heval, ?_⟩
  · rw [Matrix.mul_assoc]
    exact (congrArg _ hG).trans hK
  · have hv : act (tagReorder e₁ e₂ :
          Matrix (X.frame₁.Layout × X.frame₂.Layout) (F₁.Layout × F₂.Layout) ℂ)
          (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) =
        vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) := by
      rw [Frame.refVec, Frame.refVec, Frame.refVec, Frame.refVec, ← act_kronecker_vecKron,
        ← act_kronecker_vecKron, ← act_mul]
      exact congrArg (fun M => act M (vecKron Ω Ω)) hG
    have hgv : g.eval ((twoLayoutIso _ _ F₁.owner F₂.owner).symm
        (vecKron (F₁.refVec Ω) (F₂.refVec Ω))) = (twoLayoutIso _ _ X.owner₁ X.owner₂).symm
          (vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω)) := by
      apply (twoLayoutIso _ _ X.owner₁ X.owner₂).injective
      refine (hg _).trans ?_
      rw [LinearIsometryEquiv.apply_symm_apply]
      exact hv.trans ((twoLayoutIso _ _ X.owner₁ X.owner₂).apply_symm_apply _).symm
    calc _ = ‖w.eval ((twoLayoutIso _ _ X.owner₁ X.owner₂).symm
          (vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω))) -
        (twoLayoutIso _ _ X.newFrame₁.owner X.newFrame₂.owner).symm
          (vecKron (X.newFrame₁.refVec Ω) (X.newFrame₂.refVec Ω))‖ := by
          rw [← hgv]
          rfl
      _ ≤ _ := herr

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
