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

## Main definitions

* `PairEffect.PartyChain.precomp`, `PairEffect.PartyChain.postcomp`: a monomial composed with
  words.

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

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker

/-! ### Composing a monomial with words -/

namespace TNLean.PEPS.PairEffect.PartyChain

variable {P : Type}

/-- A monomial preceded by a word. -/
def precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) : PartyChain ℓX ℓY → PartyChain ℓ₀ ℓY
  | final w' => final (.comp w w')
  | effect hpq α β ℓS w' η rest => effect hpq α β ℓS (.comp w w') η rest

/-- A monomial followed by a word. -/
def postcomp {ℓX ℓY ℓZ : Layout P} : PartyChain ℓX ℓY → Word ℓY ℓZ → PartyChain ℓX ℓZ
  | final w', w => final (.comp w' w)
  | effect hpq α β ℓS w' η rest, w => effect hpq α β ℓS w' η (rest.postcomp w)

theorem eval_precomp {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) :
    (M : PartyChain ℓX ℓY) → (M.precomp w).toEffectChain.eval = M.toEffectChain.eval ∘L w.eval
  | final _ => rfl
  | effect .. => rfl

theorem eval_postcomp {ℓX ℓY ℓZ : Layout P} :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) →
      (M.postcomp w).toEffectChain.eval = w.eval ∘L M.toEffectChain.eval
  | final _, _ => rfl
  | effect _ _ _ _ _ _ rest, w => by
      change (rest.postcomp w).toEffectChain.eval ∘L _ ∘L _ = _
      rw [eval_postcomp rest w]
      rfl

theorem precomp_props {ℓ₀ ℓX ℓY : Layout P} (w : Word ℓ₀ ℓX) (S : Set P) (hw : w.IsAllowed)
    (hS : w.UsesOnly S) : (M : PartyChain ℓX ℓY) → M.IsAllowed → M.UsesOnly S →
      (M.precomp w).IsAllowed ∧ (M.precomp w).UsesOnly S ∧
        (M.precomp w).sourceCount = w.sourceCount + M.sourceCount ∧
        (M.precomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, hM, hMS => ⟨⟨hw, hM⟩, ⟨hS, hMS⟩, rfl, rfl⟩
  | effect .. , hM, hMS => ⟨⟨⟨hw, hM.1⟩, hM.2⟩, ⟨hMS.1, hMS.2.1, ⟨hS, hMS.2.2.1⟩, hMS.2.2.2⟩,
      by simp only [precomp, sourceCount, Word.sourceCount, Nat.add_assoc], rfl⟩

theorem postcomp_props {ℓX ℓY ℓZ : Layout P} (S : Set P) :
    (M : PartyChain ℓX ℓY) → (w : Word ℓY ℓZ) → w.IsAllowed → w.UsesOnly S → M.IsAllowed →
      M.UsesOnly S → (M.postcomp w).IsAllowed ∧ (M.postcomp w).UsesOnly S ∧
        (M.postcomp w).sourceCount = M.sourceCount + w.sourceCount ∧
        (M.postcomp w).toEffectChain.effectCount = M.toEffectChain.effectCount
  | final _, _, hw, hS, hM, hMS => ⟨⟨hM, hw⟩, ⟨hMS, hS⟩, rfl, rfl⟩
  | effect _ _ _ _ _ _ rest, w, hw, hS, hM, hMS => by
      obtain ⟨h₁, h₂, h₃, h₄⟩ := postcomp_props S rest w hw hS hM.2.2 hMS.2.2.2
      refine ⟨⟨hM.1, hM.2.1, h₁⟩, ⟨hMS.1, hMS.2.1, hMS.2.2.1, h₂⟩, ?_, ?_⟩
      · simp only [postcomp, sourceCount, h₃, Nat.add_assoc]
      · change (rest.postcomp w).toEffectChain.effectCount + 1 = _
        rw [h₄]

end TNLean.PEPS.PairEffect.PartyChain

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
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨wm, hwA, hwU, hwS, hwE⟩ := exists_birthWord P Q σ
    (tagRegs F.holes ++ siteRegs q F.owner (listE (sites ι) T (F.birthEnv P)))
  have hB : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P := fun x hx =>
    F.owner_eq_of_notMem_birthEnv fun h => Finset.mem_compl.mp hx (Finset.mem_union_right _ h)
  have hA' : ∀ x ∈ T, (F.changeOwner T Q).owner x = Q := fun x hx => by
    simp only [hx, ↓reduceIte]
  have hB' : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, (F.changeOwner T Q).owner x = P := fun x hx => by
    have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa only [hxT, ↓reduceIte] using hB x hx
  have hE : ∀ x ∈ F.birthEnv P, F.owner x = (F.changeOwner T Q).owner x := fun x hx => by
    have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp hTE hT hx
    simp only [hxT, ↓reduceIte]
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) F.owner nodup_sites mem_sites (tagRegs F.holes)
    hTP hB (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  have r := isReordering_relabelRest (q := q) F.owner (F.changeOwner T Q).owner mem_sites
    hTE hE (tagRegs F.holes) ⟨Q, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) (F.changeOwner T Q).owner nodup_sites
    mem_sites (tagRegs F.holes) hA' hB' (V := {P, Q}) (Set.mem_insert_of_mem P rfl)
    (Set.mem_insert P _)
  let W : Word F.regs (F.changeOwner T Q).regs :=
    (groupWord F.owner nodup_sites mem_sites (tagRegs F.holes) hTP hB).comp <|
      wm.comp <| (relabelRest F.owner (F.changeOwner T Q).owner mem_sites hTE hE
        (tagRegs F.holes) _ _).comp <|
        ungroupWord (F.changeOwner T Q).owner nodup_sites mem_sites (tagRegs F.holes) hA' hB'
  have heval : ∀ z, (F.changeOwner T Q).regIso (W.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ sheetBirthOp hTE σ)
        (F.regIso z) := by
    intro z
    rw [sheetBirthOp_eq_submatrix]
    exact layoutIso_place F.holes F.owner (F.changeOwner T Q).owner hTE hTP hB hA' hB' hE
      wm.eval _ hwE z
  refine ⟨σ, hσ, hK, W, ⟨g₁, hwA, r.isAllowed, u₁⟩, ⟨g₂, hwU, r.usesOnly _, u₂⟩, ?_, heval, ?_⟩
  · change Word.sourceCount _ + (Word.sourceCount _ + (Word.sourceCount _ +
      Word.sourceCount _)) ≤ 1
    rw [g₃, r.sourceCount_eq, u₃]
    omega
  · rw [← (F.changeOwner T Q).regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply,
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
  set hTE := F.disjoint_birthEnv hTP hTH
  obtain ⟨Mm, hMA, hMU, hMS, hMe, hME⟩ := exists_deathChain P Q σ
    (tagRegs F.holes ++ siteRegs q (F.changeOwner T Q).owner (listE (sites ι) T (F.birthEnv P)))
  have hB' : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, F.owner x = P := fun x hx =>
    F.owner_eq_of_notMem_birthEnv fun h => Finset.mem_compl.mp hx (Finset.mem_union_right _ h)
  have hA : ∀ x ∈ T, (F.changeOwner T Q).owner x = Q := fun x hx => by
    simp only [hx, ↓reduceIte]
  have hB : ∀ x ∈ (T ∪ F.birthEnv P)ᶜ, (F.changeOwner T Q).owner x = P := fun x hx => by
    have hxT : x ∉ T := fun h => Finset.mem_compl.mp hx (Finset.mem_union_left _ h)
    simpa only [hxT, ↓reduceIte] using hB' x hx
  have hE : ∀ x ∈ F.birthEnv P, (F.changeOwner T Q).owner x = F.owner x := fun x hx => by
    have hxT : x ∉ T := fun hT => Finset.disjoint_left.mp hTE hT hx
    simp only [hxT, ↓reduceIte]
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) (F.changeOwner T Q).owner nodup_sites
    mem_sites (tagRegs F.holes) hA hB (V := {P, Q}) (Set.mem_insert_of_mem P rfl)
    (Set.mem_insert P _)
  have r := isReordering_relabelRest (q := q) (F.changeOwner T Q).owner F.owner mem_sites
    hTE hE (tagRegs F.holes) ⟨P, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) F.owner nodup_sites mem_sites
    (tagRegs F.holes) hTP hB' (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  let tail := (relabelRest (F.changeOwner T Q).owner F.owner mem_sites hTE hE
    (tagRegs F.holes) ⟨P, euc (T → Fin q)⟩ ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩).comp
      (ungroupWord F.owner nodup_sites mem_sites (tagRegs F.holes) hTP hB')
  obtain ⟨p₁, p₂, p₃, p₄⟩ := PartyChain.postcomp_props {P, Q} Mm tail ⟨r.isAllowed, u₁⟩
    ⟨r.usesOnly _, u₂⟩ hMA hMU
  let G := groupWord (q := q) (F.changeOwner T Q).owner nodup_sites mem_sites (tagRegs F.holes)
    hA hB
  obtain ⟨q₁, q₂, q₃, q₄⟩ := PartyChain.precomp_props G {P, Q} g₁ g₂ (Mm.postcomp tail) p₁ p₂
  have heval : ∀ z, F.regIso (((Mm.postcomp tail).precomp G).toEffectChain.eval z) =
      act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ sheetBirthOp hTE σ)
        ((F.changeOwner T Q).regIso z) := by
    intro z
    rw [PartyChain.eval_precomp, PartyChain.eval_postcomp, sheetBirthOp_eq_submatrix]
    exact layoutIso_place F.holes (F.changeOwner T Q).owner F.owner hTE hA hB hTP hB' hE
      Mm.toEffectChain.eval _ hME z
  refine ⟨σ, hσ, hK, (Mm.postcomp tail).precomp G, q₁, q₂, ?_, ?_, heval, ?_⟩
  · rw [q₃, p₃, g₃, hMS]
    change 0 + (0 + (Word.sourceCount _ + Word.sourceCount _)) = 0
    rw [r.sourceCount_eq, u₃]
  · rw [q₄, p₄]
    exact hMe
  · rw [← F.regIso.norm_map, map_sub, LinearIsometryEquiv.apply_symm_apply, heval,
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
