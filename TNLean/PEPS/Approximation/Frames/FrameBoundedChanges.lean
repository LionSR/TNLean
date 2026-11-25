/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.TaggedBirthDeath
import QICLean.Spectral.Eigenvalue.MatrixReindexEuclidean
import TNLean.PEPS.Approximation.Frames.TwoSheetRegisters

/-!
# Births, deaths and exchanges as bounded changes

Lemmas 6.5 and 6.6 of the polynomial-PEPS manuscript assert that a homogeneous birth or death,
and a two-sheet exchange, are bounded changes: monomials allowed by Theorem 5.2 on a fixed list
of parties, with small reference-vector error. This file proves these assertions on the
registers of the frames, at every party the tags it holds and the raw configurations of the
sites it owns (`TNLean.PEPS.Approximation.Frames.FrameRegisters`), in their canonical
coordinates.

* `Frame.birth_bounded`: the birth is an allowed word using only `P∘` and `Q∘`, with at most one
  normalized pair source, whose operator is `1_tags ⊗ B` for the canonical map `B` of
  `eq:birth-map`; the reference-vector error is at most `L^{-30}`. The word is the birth of the
  raw configurations of the sheet beside the untouched tags
  (`QuantumCircuit.Party.Sheet.exists_taggedBirthWord_of_environment`).
* `Frame.death_bounded`: the death is the same with one normalized pair effect instead.
* `TwoSheetExchange.exchange_bounded`: the exchange is the renaming `ℛ`, a relabelling of the
  bases of the parties, followed by one private contraction at `P∘`; the contraction uses only
  `P∘`, and the operator is `C = D_U F_A ℛ` with reference-vector error at most `4 L^{-30}`.
* `TwoSheetExchange.exchange_ofFrames_bounded`: the same for two frames whose holes are listed in
  any order, after the canonical identification of tag orderings, itself a relabelling.

The frame bounds here are the manuscript's case of the exponent `30`; the bounds for sheets
without holes, stated for any exponent, are `QuantumCircuit.Party.Sheet.birth_bounded` and its
companions in `TNLean.Network.Party.SheetBoundedChanges`.

## Main results

* `EncodedFrame.Frame.birth_bounded`, `EncodedFrame.Frame.death_bounded`: Lemma 6.5 `lem:birth`.
* `EncodedFrame.TwoSheetExchange.exchange_bounded`,
  `EncodedFrame.TwoSheetExchange.exchange_ofFrames_bounded`: Lemma 6.6 `lem:exchange`.
* `EncodedFrame.exists_tagReorderWord`: the canonical identification of tag orderings of two
  frames as a relabelling.

## References

* Polynomial-PEPS manuscript (September 24, 2026), bounded changes, `05-frames.tex`,
  lines 99–105; Lemma 6.5 `lem:birth`, lines 396–447; Lemma 6.6 `lem:exchange`, lines 460–561;
  allowed monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open Matrix ManyBody QuantumCircuit.Party
open EuclideanSpace (vecKron)
open scoped Kronecker

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  [Fintype Party] [DecidableEq Party]

/-- An operator `1_W ⊗ M` of the tags beside the raw configurations of a sheet, read in the
canonical coordinates of a frame. -/
private theorem reindex_one_kronecker_tags (l : List (Hole pos q Party)) (own own' : ι → Party)
    (M : Matrix (ι → Fin q) (ι → Fin q) ℂ) :
    reindex
        ((Equiv.arrowProdEquivProdArrow Party (tagSystem l) (Sheet.system q ⟨own'⟩)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv own' fun _ ↦ Fin q))).symm
        ((Equiv.arrowProdEquivProdArrow Party (tagSystem l) (Sheet.system q ⟨own⟩)).trans
          ((Equiv.refl _).prodCongr (blockConfigEquiv own fun _ ↦ Fin q))).symm
        ((1 : Matrix (Config (tagSystem l)) (Config (tagSystem l)) ℂ) ⊗ₖ M) =
      reindex (layoutConfigEquiv l own').symm (layoutConfigEquiv l own).symm
        ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ M) := by
  ext y x
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, kroneckerMap_apply, one_apply,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    layoutConfigEquiv_apply, Equiv.arrowProdEquivProdArrow_apply,
    (tagConfigEquiv l).apply_eq_iff_eq]
  rfl

namespace Frame

variable (F : Frame pos q Party) {T : Finset ι} {P Q : Party}

/-- **Lemma 6.5 (homogeneous birth): the birth is a bounded change involving only `P∘` and
`Q∘`.** In an encoded frame `F`, let `T` be a set of raw sites owned by `P∘` and disjoint from
every outer hole footprint, and let `E` and `U = Λ ∖ (T ∪ E)` be as in `eq:birth-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data and an allowed monomial `w`
from the registers of `F` (at every party, the tags it holds and the raw configurations of the
sites it owns) to the registers of the frame `F'` in which `T` is owned by `Q∘`, such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source; the statement records
  these counts, which are what a bounded change asks for (`05-frames.tex`, lines 99–105). The
  monomial constructed in the proof prepares, for `Q∘ ≠ P∘`, the pair state `s` on a fresh copy
  of `T` held by `Q∘` and a fresh `B_T` held by `P∘`, and applies at `P∘` the contraction
  `Vᴴ (1_{B_T} ⊗ K)` with `K = ⟨s| (1_T ⊗ V)`, beside the tags;
* in canonical coordinates the operator of `w` is `1_tags ⊗ B` for the canonical map `B` of
  `eq:birth-map`, and `(1 ⊗ B) K_F = K_{F'} B`;
* the reference-vector error is at most `L^{-30}`: `‖w Ω_F - Ω_{F'}‖ ≤ L^{-30}`, with the
  reference vectors read on the registers of the two frames.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437 and 445–446; bounded changes, lines 99–105; allowed monomials, `04-compression.tex`,
lines 32–35. -/
theorem birth_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint T F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : ManyBody.regionMutualInformation Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ F.birthEnv P),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          configBirthOp Finset.subset_union_left σ) * F.encoder =
        (F.changeOwner T Q).encoder * configBirthOp Finset.subset_union_left σ ∧
      ∃ w : Word F.system (F.changeOwner T Q).system,
        w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
        w.op = reindex (F.changeOwner T Q).configEquiv.symm F.configEquiv.symm
          ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            configBirthOp Finset.subset_union_left σ) ∧
        ‖toEuclideanLin w.op (F.regRef Ω) - (F.changeOwner T Q).regRef Ω‖ ≤ L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.birth (Q := Q) hTP hTH hΩ hI
  obtain ⟨hB, -, -, -⟩ := F.changeOwner_birth_owners (Q := Q) hTP hTH
  obtain ⟨w, hA, hR, hn, hop'⟩ : ∃ w : Word F.system (F.changeOwner T Q).system,
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      w.op = reindex (F.changeOwner T Q).configEquiv.symm F.configEquiv.symm
        ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          configBirthOp Finset.subset_union_left σ) := by
    obtain ⟨w, hA, hR, hn, hop⟩ := Sheet.exists_taggedBirthWord_of_environment (Q := Q) F.sheet
      (tagSystem F.holes) (F.disjoint_birthEnv hTP hTH) hTP
      (fun x hx ↦ hB x (Finset.mem_compl.mpr hx)) σ
    exact ⟨w, hA, hR, hn,
      hop.trans (reindex_one_kronecker_tags F.holes F.owner (F.changeOwner T Q).owner _)⟩
  refine ⟨σ, hσ, hK, w, hA, hR, hn, hop', ?_⟩
  rw [hop', Frame.regRef, toEuclideanLin_reindex_piLpCongrLeft₂, Frame.regRef, ← map_sub,
    LinearIsometryEquiv.norm_map]
  exact herr

/-- **Lemma 6.5 (homogeneous death): the death is a bounded change involving only `P∘` and
`Q∘`.** Let `F` be the frame *after* the death, in which `T` is owned by `P∘` and avoids every
outer hole footprint, and let the frame before the death be `F'`, in which `T` is owned by
`Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in `F`, there are splitting data and an allowed
monomial from the registers of `F'` to those of `F`, using only `P∘` and `Q∘`, whose gates are
normalized pair effects, at most one of them, whose operator in canonical coordinates is
`1_tags ⊗ B` for the canonical map `B` of `eq:birth-map`, with `(1 ⊗ B) K_{F'} = K_F B` and
reference-vector error `‖M Ω_{F'} - Ω_F‖ ≤ L^{-30}`. For `Q∘ ≠ P∘` the monomial constructed in
the proof applies at `Q∘` and `P∘` the local maps reversing those of the birth and ends with the
normalized pair effect `⟨s|` held by `Q∘` and `P∘`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem death_bounded [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint T F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : ManyBody.regionMutualInformation Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ F.birthEnv P),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-30 : ℤ) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          configBirthOp Finset.subset_union_left σ) * (F.changeOwner T Q).encoder =
        F.encoder * configBirthOp Finset.subset_union_left σ ∧
      ∃ M : PartyCircuit (ChainGate (P := Party)) (F.changeOwner T Q).system F.system,
        M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P, Q} ∧
        M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
        M.op chainEv = reindex F.configEquiv.symm (F.changeOwner T Q).configEquiv.symm
          ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            configBirthOp Finset.subset_union_left σ) ∧
        ‖toEuclideanLin (M.op chainEv) ((F.changeOwner T Q).regRef Ω) - F.regRef Ω‖ ≤
          L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.death (Q := Q) hTP hTH hΩ hI
  obtain ⟨hB, -, -, -⟩ := F.changeOwner_birth_owners (Q := Q) hTP hTH
  obtain ⟨M, hA, hR, hG, hn, hop'⟩ :
      ∃ M : PartyCircuit (ChainGate (P := Party)) (F.changeOwner T Q).system F.system,
        M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P, Q} ∧
        M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
        M.op chainEv = reindex F.configEquiv.symm (F.changeOwner T Q).configEquiv.symm
          ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
            configBirthOp Finset.subset_union_left σ) := by
    obtain ⟨M, hA, hR, hG, hn, hop⟩ := Sheet.exists_taggedDeathChain_of_environment (Q := Q)
      F.sheet (tagSystem F.holes) (F.disjoint_birthEnv hTP hTH) hTP
      (fun x hx ↦ hB x (Finset.mem_compl.mpr hx)) σ
    exact ⟨M, hA, hR, hG, hn,
      hop.trans (reindex_one_kronecker_tags F.holes (F.changeOwner T Q).owner F.owner _)⟩
  refine ⟨σ, hσ, hK, M, hA, hR, hG, hn, hop', ?_⟩
  rw [hop', Frame.regRef, toEuclideanLin_reindex_piLpCongrLeft₂, Frame.regRef, ← map_sub,
    LinearIsometryEquiv.norm_map]
  exact herr

end Frame

/-! ### The canonical identification of tag orderings -/

omit [Fintype Party] in
/-- **Reordering the tags of the holes at every party.** If `l'` lists the holes of `l`, whose
outer footprints are pairwise disjoint, in another order, the tag registers of `l'` are those of
`l` at every party, the tag of every hole moved to the hole's new position, and the raw parts of
the encodings agree along this identification. -/
theorem exists_tagSystemEquiv_of_perm [NeZero q] {l l' : List (Hole pos q Party)}
    (hd : PairwiseDisjointOuter (l.map Hole.patch)) (hp : l.Perm l') :
    ∃ f : ∀ p, tagSystem l' p ≃ tagSystem l p, ∀ z : Config (tagSystem l'),
      rawProd l (tagConfigEquiv l (Equiv.piCongrRight f z)) = rawProd l' (tagConfigEquiv l' z) := by
  induction hp with
  | nil => exact ⟨fun _ ↦ Equiv.refl _, fun _ ↦ rfl⟩
  | cons h _ ih =>
    obtain ⟨f, hf⟩ := ih (PairwiseDisjointOuter.of_cons hd)
    refine ⟨fun p ↦ (Equiv.refl _).prodCongr (f p), fun z ↦ ?_⟩
    change h.patch.branch _ * rawProd _ (tagConfigEquiv _ (Equiv.piCongrRight f fun p ↦ (z p).2)) =
      h.patch.branch _ * rawProd _ (tagConfigEquiv _ fun p ↦ (z p).2)
    rw [hf]
    rfl
  | swap x y l =>
    refine ⟨fun p ↦ ⟨fun t ↦ (t.2.1, t.1, t.2.2), fun t ↦ (t.2.1, t.1, t.2.2), fun _ ↦ rfl,
      fun _ ↦ rfl⟩, fun z ↦ ?_⟩
    change y.patch.branch _ * (x.patch.branch _ * rawProd l _) =
      x.patch.branch _ * (y.patch.branch _ * rawProd l _)
    have hyx : Disjoint y.patch.outer x.patch.outer :=
      List.rel_of_pairwise_cons hd List.mem_cons_self
    rw [← mul_assoc, ← mul_assoc,
      (ManyBody.commute_of_mem_supportedOperators_of_disjoint
        (y.patch.branch_mem_supportedOperators _) (x.patch.branch_mem_supportedOperators _) hyx).eq]
    rfl
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨f₁, hf₁⟩ := ih₁ hd
    obtain ⟨f₂, hf₂⟩ := ih₂ (hd.perm (h₁.map _) fun h ↦ Disjoint.symm h)
    exact ⟨fun p ↦ (f₂ p).trans (f₁ p), fun z ↦ (hf₁ _).trans (hf₂ z)⟩

/-- **The canonical identification of tag orderings on two frames, as a relabelling.** If `l₁'`,
`l₂'` list the holes of `l₁`, `l₂` in other orders, there are relabellings `e₁`, `e₂` of the tag
configurations preserving the raw parts of the encodings and an allowed word without pair
sources, a relabelling of the bases of the parties, whose operator in canonical coordinates is
the relabelling `tagReorder e₁ e₂`.

Polynomial-PEPS manuscript, `05-frames.tex`, lines 74–75 and 84–85. -/
theorem exists_tagReorderWord [NeZero q] {l₁ l₁' l₂ l₂' : List (Hole pos q Party)}
    (hd₁ : PairwiseDisjointOuter (l₁.map Hole.patch))
    (hd₂ : PairwiseDisjointOuter (l₂.map Hole.patch)) (hp₁ : l₁.Perm l₁') (hp₂ : l₂.Perm l₂')
    (own₁ own₂ : ι → Party) :
    ∃ (e₁ : TagSpace l₁ ≃ TagSpace l₁') (e₂ : TagSpace l₂ ≃ TagSpace l₂'),
      (∀ t, rawProd l₁' (e₁ t) = rawProd l₁ t) ∧ (∀ t, rawProd l₂' (e₂ t) = rawProd l₂ t) ∧
      ∃ w : Word (fun p ↦ layoutSystem q l₁ own₁ p × layoutSystem q l₂ own₂ p)
          (fun p ↦ layoutSystem q l₁' own₁ p × layoutSystem q l₂' own₂ p),
        w.IsAllowed ∧ w.sourceCount = 0 ∧
        w.op = reindex (twoLayoutEquiv l₁' own₁ l₂' own₂).symm
          (twoLayoutEquiv l₁ own₁ l₂ own₂).symm (TwoSheetExchange.tagReorder e₁ e₂) := by
  obtain ⟨f₁, hf₁⟩ := exists_tagSystemEquiv_of_perm hd₁ hp₁
  obtain ⟨f₂, hf₂⟩ := exists_tagSystemEquiv_of_perm hd₂ hp₂
  set e₁ : TagSpace l₁ ≃ TagSpace l₁' := (tagConfigEquiv l₁).symm.trans
    ((Equiv.piCongrRight f₁).symm.trans (tagConfigEquiv l₁'))
  set e₂ : TagSpace l₂ ≃ TagSpace l₂' := (tagConfigEquiv l₂).symm.trans
    ((Equiv.piCongrRight f₂).symm.trans (tagConfigEquiv l₂'))
  refine ⟨e₁, e₂, fun t ↦ ?_, fun t ↦ ?_,
    PartyCircuit.relabel fun p ↦ ((f₁ p).prodCongr (Equiv.refl _)).prodCongr
      ((f₂ p).prodCongr (Equiv.refl _)), Word.isAllowed_relabel _, rfl, ?_⟩
  · change rawProd l₁' (tagConfigEquiv l₁' ((Equiv.piCongrRight f₁).symm
      ((tagConfigEquiv l₁).symm t))) = _
    rw [← hf₁, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · change rawProd l₂' (tagConfigEquiv l₂' ((Equiv.piCongrRight f₂).symm
      ((tagConfigEquiv l₂).symm t))) = _
    rw [← hf₂, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · ext y x
    rw [Word.op, PartyCircuit.op_relabel, reindex_apply, submatrix_apply, Equiv.symm_symm,
      Equiv.symm_symm, TwoSheetExchange.tagReorder]
    simp only [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
    refine if_congr ?_ rfl rfl
    have key : ((e₁.prodCongr (Equiv.refl _)).prodCongr (e₂.prodCongr (Equiv.refl _))).symm
        (twoLayoutEquiv l₁' own₁ l₂' own₂ y) =
        twoLayoutEquiv l₁ own₁ l₂ own₂ (Equiv.piCongrRight (fun p ↦
          ((f₁ p).prodCongr (Equiv.refl _)).prodCongr ((f₂ p).prodCongr (Equiv.refl _))) y) := by
      simp only [Equiv.prodCongr_symm, Equiv.symm_trans, Equiv.symm_symm, Equiv.refl_symm,
        twoLayoutEquiv, Equiv.trans_apply, Equiv.arrowProdEquivProdArrow_apply,
        Equiv.prodCongr_apply, Prod.map_apply, layoutConfigEquiv_apply, Equiv.coe_trans,
        Equiv.coe_refl, Function.comp_apply, Equiv.symm_apply_apply, id_eq,
        Equiv.piCongrRight_apply, Pi.map_apply, Prod.map_fst, Prod.map_snd, Prod.mk.injEq,
        EmbeddingLike.apply_eq_iff_eq, and_true, e₁, e₂]
      exact ⟨rfl, rfl⟩
    rw [key, (twoLayoutEquiv l₁ own₁ l₂ own₂).apply_eq_iff_eq]

namespace TwoSheetExchange

variable (X : TwoSheetExchange pos q Party) (P : Party)

/-- **Lemma 6.6 (two-sheet exchange): the exchange is implemented by private contractions and a
register renaming.** Consider two encoded frames and a region `Y` such that every hole's outer
square lies on one side of `∂Y`, with the holes of each frame listed as those outside `Y`
followed by those inside. Let `P∘` be a party and `Z`, `T`, `E`, `U` as in `eq:exchange-Z` and
`eq:exchange-partition`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data
and an allowed word `c` on the registers of the two frames after the exchange (at every party,
its tags and raw configurations on both sheets) such that:

* `c` uses only `P∘` and no pair resource; it is one private contraction at `P∘` on the raw
  configurations of `U` of both sheets (the corrections `D_U F_A`), beside the tags;
* the renaming `ℛ` (`renameWord`, a relabelling of the bases of the parties that keeps every
  register at its party) followed by `c` has, in canonical coordinates, the operator
  `C = D_U F_A ℛ`, with `C (K_{F₁} ⊗ K_{F₂}) = K_out D_U F_T`;
* the reference-vector error is at most `4 L^{-30}`:
  `‖C (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`, read on the registers of the frames.

Hence the exchange is a bounded change in the sense of Theorem 5.2.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479; proof
lines 481–561; bounded changes, lines 99–105. -/
theorem exchange_bounded [NeZero q] {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : ManyBody.regionMutualInformation Ω (X.tSet P) (X.eSet P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) (X.tSet P) (X.tSet P ∪ X.eSet P),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-30 : ℤ) ∧
      X.exchangeOp P σ * (X.frame₁.encoder ⊗ₖ X.frame₂.encoder) =
        (X.newFrame₁.encoder ⊗ₖ X.newFrame₂.encoder) *
          (configBufferCorrection Finset.subset_union_left σ * Matrix.reindex
              (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
              (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
              (ManyBody.pairSwapOp (X.tSet P))) ∧
      ∃ c : Word (fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p)
          (fun p ↦ X.newFrame₁.system p × X.newFrame₂.system p),
        c.IsAllowed ∧ c.UsesOnly {P} ∧ c.sourceCount = 0 ∧
        Word.op (PartyCircuit.comp X.renameWord c) =
          reindex (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm
            (twoFrameEquiv X.frame₁ X.frame₂).symm (X.exchangeOp P σ) ∧
        ‖toEuclideanLin (Word.op (PartyCircuit.comp X.renameWord c))
            (pairRef X.frame₁ X.frame₂ Ω) - pairRef X.newFrame₁ X.newFrame₂ Ω‖ ≤
          4 * L ^ (-30 : ℤ) := by
  obtain ⟨σ, hσ, -, hK, herr⟩ := X.exchange P hΩ hI
  refine ⟨σ, hσ, hK, X.correctionWord P σ, X.isAllowed_correctionWord P σ,
    X.usesOnly_correctionWord P σ, X.sourceCount_correctionWord P σ,
    X.op_comp_renameWord_correctionWord P σ, ?_⟩
  rw [X.op_comp_renameWord_correctionWord P σ, pairRef_eq_twoFrameEquiv_symm,
    pairRef_eq_twoFrameEquiv_symm, toEuclideanLin_reindex_piLpCongrLeft₂, ← map_sub,
    LinearIsometryEquiv.norm_map]
  exact herr

/-- **Lemma 6.6 (two-sheet exchange) for frames with holes in any order: the exchange is a bounded
change.** Let `F₁`, `F₂` be encoded frames and `Y` the physical sample of a region, with the
holes of both frames classified as outside or inside the region as in `ofFrames`. With `Z`, `T`,
`E`, `U` computed from the two frames (`mem_ofFrames_exchangeEnv`), if `I_Ω(T:E) ≤ L^{-60}` for a
unit vector `Ω`, there are relabellings `e₁`, `e₂` of the tag configurations identifying the
encodings of each frame with those of its holes listed outside first (the canonical
identification of tag orderings), splitting data with error at most `L^{-30}`, a relabelling
`g` of the bases of the parties implementing `e₁` and `e₂`, and an allowed word `c` using only
`P∘` and no pair resource (one private contraction at `P∘`), such that `g`, then the renaming
`ℛ`, then `c` acts in canonical coordinates as `C G = D_U F_A ℛ G` with
`G = tagReorder e₁ e₂`, satisfies `C G (K_{F₁} ⊗ K_{F₂}) = K_out D_U F_T`, and has
reference-vector error `‖C G (Ω_{F₁} ⊗ Ω_{F₂}) - Ω_{F₁'} ⊗ Ω_{F₂'}‖ ≤ 4 L^{-30}`.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 460–479, with the
canonical identification of tag orderings of lines 75–76 and 84–85; proof lines 481–561;
bounded changes, lines 99–105. -/
theorem exchange_ofFrames_bounded [NeZero q] (F₁ F₂ : Frame pos q Party) (Y : Finset ι)
    (out : Hole pos q Party → Bool)
    (hout : ∀ h ∈ F₁.holes ++ F₂.holes, out h = true → Disjoint h.patch.outer Y)
    (hin : ∀ h ∈ F₁.holes ++ F₂.holes, out h = false → h.patch.outer ⊆ Y) (P : Party)
    {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : ManyBody.regionMutualInformation Ω
      ((ofFrames F₁ F₂ Y out hout hin).tSet P) ((ofFrames F₁ F₂ Y out hout hin).eSet P) ≤
        L ^ (-60 : ℤ)) :
    ∃ (e₁ : TagSpace F₁.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₁.holes)
      (e₂ : TagSpace F₂.holes ≃ TagSpace (ofFrames F₁ F₂ Y out hout hin).frame₂.holes),
      (∀ t, rawProd _ (e₁ t) = rawProd F₁.holes t) ∧ (∀ t, rawProd _ (e₂ t) = rawProd F₂.holes t) ∧
      ∃ σ : SplittingData (fun _ : ι ↦ Fin q) ((ofFrames F₁ F₂ Y out hout hin).tSet P)
          ((ofFrames F₁ F₂ Y out hout hin).tSet P ∪ (ofFrames F₁ F₂ Y out hout hin).eSet P),
        σ.error Finset.subset_union_left Ω ≤ L ^ (-30 : ℤ) ∧
        (ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂ *
            (F₁.encoder ⊗ₖ F₂.encoder) =
          ((ofFrames F₁ F₂ Y out hout hin).newFrame₁.encoder ⊗ₖ
              (ofFrames F₁ F₂ Y out hout hin).newFrame₂.encoder) *
            (configBufferCorrection Finset.subset_union_left σ *
              Matrix.reindex (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
                  (Equiv.arrowProdEquivProdArrow ι (fun _ ↦ Fin q) fun _ ↦ Fin q)
                  (ManyBody.pairSwapOp ((ofFrames F₁ F₂ Y out hout hin).tSet P))) ∧
        ∃ g : Word (fun p ↦ F₁.system p × F₂.system p)
            (fun p ↦ (ofFrames F₁ F₂ Y out hout hin).frame₁.system p ×
              (ofFrames F₁ F₂ Y out hout hin).frame₂.system p),
          g.IsAllowed ∧ g.sourceCount = 0 ∧
          ∃ c : Word (fun p ↦ (ofFrames F₁ F₂ Y out hout hin).newFrame₁.system p ×
                (ofFrames F₁ F₂ Y out hout hin).newFrame₂.system p)
              (fun p ↦ (ofFrames F₁ F₂ Y out hout hin).newFrame₁.system p ×
                (ofFrames F₁ F₂ Y out hout hin).newFrame₂.system p),
            c.IsAllowed ∧ c.UsesOnly {P} ∧ c.sourceCount = 0 ∧
            Word.op ((g.comp (ofFrames F₁ F₂ Y out hout hin).renameWord).comp c) =
              reindex (twoFrameEquiv (ofFrames F₁ F₂ Y out hout hin).newFrame₁
                  (ofFrames F₁ F₂ Y out hout hin).newFrame₂).symm
                (twoFrameEquiv F₁ F₂).symm
                ((ofFrames F₁ F₂ Y out hout hin).exchangeOp P σ * tagReorder e₁ e₂) ∧
            ‖toEuclideanLin (Word.op ((g.comp (ofFrames F₁ F₂ Y out hout hin).renameWord).comp c))
                (pairRef F₁ F₂ Ω) -
              pairRef (ofFrames F₁ F₂ Y out hout hin).newFrame₁
                (ofFrames F₁ F₂ Y out hout hin).newFrame₂ Ω‖ ≤ 4 * L ^ (-30 : ℤ) := by
  set X := ofFrames F₁ F₂ Y out hout hin
  obtain ⟨e₁, e₂, he₁, he₂, g, hgA, hgS, hg⟩ :
      ∃ (e₁ : TagSpace F₁.holes ≃ TagSpace X.frame₁.holes)
        (e₂ : TagSpace F₂.holes ≃ TagSpace X.frame₂.holes),
        (∀ t, rawProd _ (e₁ t) = rawProd F₁.holes t) ∧
        (∀ t, rawProd _ (e₂ t) = rawProd F₂.holes t) ∧
        ∃ g : Word (fun p ↦ F₁.system p × F₂.system p)
            (fun p ↦ X.frame₁.system p × X.frame₂.system p),
          g.IsAllowed ∧ g.sourceCount = 0 ∧
          g.op = reindex (twoFrameEquiv X.frame₁ X.frame₂).symm (twoFrameEquiv F₁ F₂).symm
            (tagReorder e₁ e₂) := exists_tagReorderWord (q := q)
    (l₁' := X.frame₁.holes) (l₂' := X.frame₂.holes) F₁.disjoint
    F₂.disjoint (List.filter_append_perm out F₁.holes).symm
    (List.filter_append_perm out F₂.holes).symm F₁.owner F₂.owner
  obtain ⟨σ, hσ, hK, c, hcA, hcU, hcS, hop, herr⟩ := X.exchange_bounded P hΩ hI
  have hG : tagReorder e₁ e₂ * (F₁.encoder ⊗ₖ F₂.encoder) =
      X.frame₁.encoder ⊗ₖ X.frame₂.encoder :=
    tagReorder_mul_kronecker he₁ he₂
  have hop' : Word.op ((g.comp X.renameWord).comp c) =
      reindex (twoFrameEquiv X.newFrame₁ X.newFrame₂).symm (twoFrameEquiv F₁ F₂).symm
        (X.exchangeOp P σ * tagReorder e₁ e₂) := by
    simp only [Word.op_comp]
    rw [← Matrix.mul_assoc, show c.op * X.renameWord.op =
        Word.op (PartyCircuit.comp X.renameWord c) from (Word.op_comp X.renameWord c).symm, hop,
      hg, reindex_apply, reindex_apply, reindex_apply, submatrix_mul_equiv]
  refine ⟨e₁, e₂, he₁, he₂, σ, hσ, ?_, g, hgA, hgS, c, hcA, hcU, hcS, hop', ?_⟩
  · rw [Matrix.mul_assoc]
    exact (congrArg _ hG).trans hK
  · have hv : toEuclideanLin (tagReorder e₁ e₂ :
          Matrix (X.frame₁.Layout × X.frame₂.Layout) (F₁.Layout × F₂.Layout) ℂ)
          (vecKron (F₁.refVec Ω) (F₂.refVec Ω)) =
        vecKron (X.frame₁.refVec Ω) (X.frame₂.refVec Ω) := by
      rw [Frame.refVec, Frame.refVec, Frame.refVec, Frame.refVec,
        ← toEuclideanLin_kronecker_vecKron, ← toEuclideanLin_kronecker_vecKron,
        ← toEuclideanLin_mul_apply]
      exact congrArg (fun M ↦ toEuclideanLin M (vecKron Ω Ω)) hG
    have hgv : toEuclideanLin g.op (pairRef F₁ F₂ Ω) = pairRef X.frame₁ X.frame₂ Ω := by
      rw [hg, pairRef_eq_twoFrameEquiv_symm, pairRef_eq_twoFrameEquiv_symm,
        toEuclideanLin_reindex_piLpCongrLeft₂, hv]
    simp only [Word.op_comp]
    rw [← Matrix.mul_assoc, show c.op * X.renameWord.op =
        Word.op (PartyCircuit.comp X.renameWord c) from (Word.op_comp X.renameWord c).symm,
      toEuclideanLin_mul_apply, hgv]
    exact herr

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
