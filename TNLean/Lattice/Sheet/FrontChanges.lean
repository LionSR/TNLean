/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Composition
import TNLean.Lattice.Sheet.TwoRegisters

/-!
# Births, deaths and exchanges behind blocks of front registers

Lemmas 6.5 and 6.6 of the polynomial-PEPS manuscript implement a change of ownership of a sheet
by an allowed monomial on its registers. Apart from the raw registers of the sites, one register
`ℂ^q` per site held by its owner, the registers of an encoded frame contain the tags of its
holes; the monomials of the two lemmas never act on them. This file states the monomials for
any block of registers in front of the raw registers, identified with some `ℂ^κ`, so that the
same words serve the encoded frames, whose front block is the tag registers of the holes, and
the sheets without holes, whose front block is empty.

* `exists_frontBirthWord`: the birth of Lemma 6.5. If `T` and `U = (T ∪ E)ᶜ` are held by `P∘`
  and, after the change, `T` is held by `Q∘` and `U` by `P∘`, with the owners on `E` unchanged,
  there is an allowed word using only `P∘` and `Q∘`, with at most one normalized pair source,
  whose operator in canonical coordinates is `1_κ ⊗ B` for the canonical map `B` of
  `eq:birth-map`. It groups the raw registers of `T` and `U`, applies the birth monomial of
  `TNLean.Lattice.Sheet.Monomials`, and ungroups.
* `exists_frontDeathChain`: the death, with one normalized pair effect instead.
* `blockRenameWord`: the renaming `ℛ` of Lemma 6.6 on two sheets, each with two front blocks
  (the registers outside and inside the region `Y`) followed by the raw registers: inside `Y`,
  the raw registers and the inside front blocks of the two sheets exchange their sheet names, by
  exchanges of tensor factors only (`eval_blockRenameWord`, `isReordering_blockRenameWord`).
* `norm_act_sheetBufferCorrection_mul_sheetSwapOp_sub_le`: the net map `D_U F_T` of the
  exchange moves the product `Ω ⊗ Ω` of two copies of a unit vector by at most four times the
  splitting error.

These are original proofs; no OpenAI Lean code is copied or adapted.

## Main results

* `Sheet.exists_frontBirthWord`, `Sheet.exists_frontDeathChain`.
* `Sheet.blockRenameWord`, `Sheet.eval_blockRenameWord`.
* `Sheet.norm_act_sheetBufferCorrection_mul_sheetSwapOp_sub_le`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth`, `05-frames.tex`,
  lines 396–456; Lemma 6.6 `lem:exchange`, lines 460–561; bounded changes, lines 99–105;
  allowed monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.Lattice.Sheet

open PartyCircuit

/-! ### The reference error of the net map of an exchange -/

section NetMap

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ} {T E : Finset ι}

-- Two copies of the configurations `((t, e), u)` of three regions form a fourfold product of
-- function types; synthesizing their decidable equality exceeds the default instance size.
set_option synthInstance.maxSize 512 in
/-- **The net map of an exchange on two copies of the reference vector.** For splitting data
`σ` of a unit vector `Ω`, the net map `D_U F_T = (𝒱^{⊗2})ᴴ F_{T B_T} 𝒱^{⊗2}` of the exchange
moves `Ω ⊗ Ω` by at most `4 ‖𝒱 Ω - s ⊗ s'‖`.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 516–561. -/
theorem norm_act_sheetBufferCorrection_mul_sheetSwapOp_sub_le (h : Disjoint T E)
    (σ : SplittingData q T E) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) :
    ‖act (sheetBufferCorrection h σ * TNLean.Lattice.sheetSwapOp q T) (vecKron Ω Ω) -
      vecKron Ω Ω‖ ≤ 4 * σ.error h Ω := by
  rw [sheetSwapOp_eq_submatrix h, sheetBufferCorrection, submatrix_mul_equiv,
    norm_act_submatrix_sub]
  set ω : EuclideanSpace ℂ _ := WithLp.toLp 2 (splitVec h Ω)
  have hω : (WithLp.toLp 2 (⇑(vecKron Ω Ω) ∘ (threeSplit₂ h).symm) : EuclideanSpace ℂ _) =
      vecKron ω ω := rfl
  have hω1 : ‖ω‖ = 1 :=
    norm_toLp_eq_one_of_star_dotProduct (star_splitVec_dotProduct_splitVec h hΩ)
  rw [hω]
  exact norm_act_bufferCorrection_mul_tSwap_sub_le σ.isIsometry σ.star_s σ.star_s' hω1

end NetMap

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {Party : Type}

/-! ### Birth and death behind a front block -/

section BirthDeath

variable {κ : Type} [Fintype κ] [DecidableEq κ] {T E : Finset ι}

/-- **The birth behind a front block (Lemma 6.5).** Let `T` and `U = (T ∪ E)ᶜ` be held by `P∘`
under the owners `own`, and let the owners `own'` after the change hold `T` at `Q∘` and `U` at
`P∘`, agreeing with `own` on `E`. For splitting data `σ` there is an allowed word from a block `k`
of front registers followed by the raw registers with owners `own` to the same block followed
by the raw registers with owners `own'`, using only `P∘` and `Q∘` and at most one normalized
pair source, whose operator in canonical coordinates is `1_κ ⊗ B` for the canonical map `B`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437. -/
theorem exists_frontBirthWord (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (own own' : ι → Party) (h : Disjoint T E) {P Q : Party} (hTP : ∀ x ∈ T, own x = P)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = P) (hA' : ∀ x ∈ T, own' x = Q)
    (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = P) (hE : ∀ x ∈ E, own x = own' x)
    (σ : SplittingData q T E) :
    ∃ w : Word (k ++ siteRegs q own (sites ι)) (k ++ siteRegs q own' (sites ι)),
      w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
      ∀ z, frontLayoutIso k i own' (w.eval z) =
        act ((1 : Matrix κ κ ℂ) ⊗ₖ sheetBirthOp h σ) (frontLayoutIso k i own z) := by
  obtain ⟨wm, hwA, hwU, hwS, hwE⟩ := Frame.exists_birthWord P Q σ
    (k ++ siteRegs q own (listE (sites ι) T E))
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) own nodup_sites mem_sites k hTP hB
    (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  have r := isReordering_relabelRest (q := q) own own' mem_sites h hE k ⟨Q, euc (T → Fin q)⟩
    ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) own' nodup_sites mem_sites k hA' hB'
    (V := {P, Q}) (Set.mem_insert_of_mem P rfl) (Set.mem_insert P _)
  refine ⟨(groupWord own nodup_sites mem_sites k hTP hB).comp <| wm.comp <|
      (relabelRest own own' mem_sites h hE k _ _).comp <|
        ungroupWord own' nodup_sites mem_sites k hA' hB',
    ⟨g₁, hwA, r.isAllowed, u₁⟩, ⟨g₂, hwU, r.usesOnly _, u₂⟩, ?_, fun z => ?_⟩
  · change Word.sourceCount _ + (Word.sourceCount _ + (Word.sourceCount _ +
      Word.sourceCount _)) ≤ 1
    rw [g₃, r.sourceCount_eq, u₃]
    omega
  · rw [sheetBirthOp_eq_submatrix]
    exact frontLayoutIso_place k i own own' h hTP hB hA' hB' hE wm.eval _ hwE z

/-- **The death behind a front block (Lemma 6.5).** Let `T` be held by `Q∘` and
`U = (T ∪ E)ᶜ` by `P∘` under the owners `own` before the death, and let the owners `own'` after
the death hold `T` and `U` at `P∘`, agreeing with `own` on `E`. For splitting data `σ` there is
an allowed monomial from a block `k` of front registers followed by the raw registers with owners
`own` to the same block followed by the raw registers with owners `own'`, using only `P∘` and
`Q∘`, without pair sources and with at most one normalized pair effect, whose operator in
canonical coordinates is `1_κ ⊗ B` for the canonical map `B`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–446. -/
theorem exists_frontDeathChain (k : Layout Party) (i : Mem k ≃ₗᵢ[ℂ] EuclideanSpace ℂ κ)
    (own own' : ι → Party) (h : Disjoint T E) {P Q : Party} (hA : ∀ x ∈ T, own x = Q)
    (hB : ∀ x ∈ (T ∪ E)ᶜ, own x = P) (hTP : ∀ x ∈ T, own' x = P)
    (hB' : ∀ x ∈ (T ∪ E)ᶜ, own' x = P) (hE : ∀ x ∈ E, own x = own' x)
    (σ : SplittingData q T E) :
    ∃ M : PartyChain (k ++ siteRegs q own (sites ι)) (k ++ siteRegs q own' (sites ι)),
      M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
      ∀ z, frontLayoutIso k i own' (M.toEffectChain.eval z) =
        act ((1 : Matrix κ κ ℂ) ⊗ₖ sheetBirthOp h σ) (frontLayoutIso k i own z) := by
  obtain ⟨Mm, hMA, hMU, hMS, hMe, hME⟩ := Frame.exists_deathChain P Q σ
    (k ++ siteRegs q own (listE (sites ι) T E))
  obtain ⟨g₁, g₂, g₃⟩ := groupWord_props (q := q) own nodup_sites mem_sites k hA hB
    (V := {P, Q}) (Set.mem_insert_of_mem P rfl) (Set.mem_insert P _)
  have r := isReordering_relabelRest (q := q) own own' mem_sites h hE k ⟨P, euc (T → Fin q)⟩
    ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩
  obtain ⟨u₁, u₂, u₃⟩ := ungroupWord_props (q := q) own' nodup_sites mem_sites k hTP hB'
    (V := {P, Q}) (Set.mem_insert P _) (Set.mem_insert P _)
  let tail := (relabelRest own own' mem_sites h hE k ⟨P, euc (T → Fin q)⟩
    ⟨P, euc (↥(T ∪ E)ᶜ → Fin q)⟩).comp (ungroupWord own' nodup_sites mem_sites k hTP hB')
  obtain ⟨p₁, p₂, p₃, p₄⟩ := PartyChain.postcomp_props {P, Q} Mm tail ⟨r.isAllowed, u₁⟩
    ⟨r.usesOnly _, u₂⟩ hMA hMU
  let G := groupWord (q := q) own nodup_sites mem_sites k hA hB
  obtain ⟨q₁, q₂, q₃, q₄⟩ := PartyChain.precomp_props G {P, Q} g₁ g₂ (Mm.postcomp tail) p₁ p₂
  refine ⟨(Mm.postcomp tail).precomp G, q₁, q₂, ?_, ?_, fun z => ?_⟩
  · rw [q₃, p₃, g₃, hMS]
    change 0 + (0 + (Word.sourceCount _ + Word.sourceCount _)) = 0
    rw [r.sourceCount_eq, u₃]
  · rw [q₄, p₄]
    exact hMe
  · rw [PartyChain.eval_precomp, PartyChain.eval_postcomp, sheetBirthOp_eq_submatrix]
    exact frontLayoutIso_place k i own own' h hA hB hTP hB' hE Mm.toEffectChain.eval _ hME z

end BirthDeath

/-! ### The renaming of a two-sheet exchange -/

section Rename

/-- **The renaming `ℛ` behind front blocks, as a word of exchanges of tensor factors.** Each of
two sheets carries a block `oₐ` of front registers outside the region `Y`, a block `iₐ` inside
it, and its raw registers. Move the raw registers of the sites in `Y` of each sheet next to its
inside block, exchange these pairs of blocks between the two sheets, and merge back. Every
register keeps its party: a raw register of the first sheet at a site of `Y` becomes the
register of the second new sheet at that site, whose owner is the old owner on the first sheet.

Polynomial-PEPS manuscript, proof of Lemma 6.6, `05-frames.tex`, lines 485–490. -/
def blockRenameWord (o₁ i₁ o₂ i₂ : Layout Party) (own₁ own₂ : ι → Party) (Y : Finset ι) :
    Word (o₁ ++ (i₁ ++ (siteRegs q own₁ (sites ι) ++ (o₂ ++ (i₂ ++ siteRegs q own₂ (sites ι))))))
      (o₁ ++ (i₂ ++ (siteRegs q (fun x => if x ∈ Y then own₂ x else own₁ x) (sites ι) ++
        (o₂ ++ (i₁ ++ siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι)))))) :=
  let pY : ι → Bool := fun x => decide (x ∈ Y)
  let new₁ : ι → Party := fun x => if x ∈ Y then own₂ x else own₁ x
  let new₂ : ι → Party := fun x => if x ∈ Y then own₁ x else own₂ x
  let Y₁ := siteRegs q own₁ (listT (sites ι) Y)
  let N₁ := siteRegs q own₁ (listR (sites ι) Y)
  let Y₂ := siteRegs q own₂ (listT (sites ι) Y)
  let N₂ := siteRegs q own₂ (listR (sites ι) Y)
  let Y₁' := siteRegs q new₁ (listT (sites ι) Y)
  let N₁' := siteRegs q new₁ (listR (sites ι) Y)
  let Y₂' := siteRegs q new₂ (listT (sites ι) Y)
  .comp (Word.frameList o₁ (Word.frameList i₁ (partWordApp own₁ pY
    (o₂ ++ (i₂ ++ siteRegs q own₂ (sites ι))) (sites ι)))) <|
  .comp (Word.frameList o₁ (Word.frameList i₁ (Word.frameList Y₁ (Word.frameList N₁
    (Word.frameList o₂ (Word.frameList i₂ (partWord own₂ pY (sites ι)))))))) <|
  .comp (Word.frameList o₁ (Word.swapPairs i₁ Y₁ N₁ o₂ i₂ Y₂ N₂)) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (relabelSitesApp own₂ new₁
    (N₁ ++ (o₂ ++ (i₁ ++ (Y₁ ++ N₂)))) (listT (sites ι) Y) fun x hx => by
      simp [new₁, (mem_listT mem_sites x).mp hx]))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (relabelSitesApp own₁
    new₁ (o₂ ++ (i₁ ++ (Y₁ ++ N₂))) (listR (sites ι) Y) fun x hx => by
      simp [new₁, (mem_listR mem_sites x).mp hx])))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (relabelSitesApp own₁ new₂ N₂
      (listT (sites ι) Y) fun x hx => by simp [new₂, (mem_listT mem_sites x).mp hx]))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (Word.frameList Y₂' (relabelSites own₂
      new₂ (listR (sites ι) Y) fun x hx => by
        simp [new₂, (mem_listR mem_sites x).mp hx])))))))) <|
  .comp (Word.frameList o₁ (Word.frameList i₂ (Word.frameList Y₁' (Word.frameList N₁'
    (Word.frameList o₂ (Word.frameList i₁ (unpartWord new₂ pY (sites ι)))))))) <|
  Word.frameList o₁ (Word.frameList i₂ (unpartWordApp new₁ pY
    (o₂ ++ (i₁ ++ siteRegs q new₂ (sites ι))) (sites ι)))

/-- **The renaming on basis vectors.** Inside `Y` the configurations and the inside front
vectors of the two sheets change places. -/
theorem eval_blockRenameWord (o₁ i₁ o₂ i₂ : Layout Party) (own₁ own₂ : ι → Party) (Y : Finset ι)
    (x₁ : Mem o₁) (y₁ : Mem i₁) (x₂ : Mem o₂) (y₂ : Mem i₂) (c₁ c₂ : ι → Fin q) :
    (blockRenameWord (q := q) o₁ i₁ o₂ i₂ own₁ own₂ Y).eval
        ((appendIso o₁ _).symm (x₁ ⊗ₜ (appendIso i₁ _).symm (y₁ ⊗ₜ
          (appendIso (siteRegs q own₁ (sites ι)) _).symm (siteVec own₁ (sites ι) c₁ ⊗ₜ
            (appendIso o₂ _).symm (x₂ ⊗ₜ (appendIso i₂ _).symm
              (y₂ ⊗ₜ siteVec own₂ (sites ι) c₂)))))) =
      (appendIso o₁ (i₂ ++ (siteRegs q (fun x => if x ∈ Y then own₂ x else own₁ x) (sites ι) ++
          (o₂ ++ (i₁ ++ siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι)))))).symm
        (x₁ ⊗ₜ (appendIso i₂ (siteRegs q (fun x => if x ∈ Y then own₂ x else own₁ x) (sites ι) ++
          (o₂ ++ (i₁ ++ siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι))))).symm
        (y₂ ⊗ₜ (appendIso (siteRegs q (fun x => if x ∈ Y then own₂ x else own₁ x) (sites ι))
          (o₂ ++ (i₁ ++ siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι)))).symm
          (siteVec (fun x => if x ∈ Y then own₂ x else own₁ x) (sites ι)
              (fun x => if x ∈ Y then c₂ x else c₁ x) ⊗ₜ
            (appendIso o₂ (i₁ ++ siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x)
              (sites ι))).symm (x₂ ⊗ₜ (appendIso i₁
                (siteRegs q (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι))).symm (y₁ ⊗ₜ
              siteVec (fun x => if x ∈ Y then own₁ x else own₂ x) (sites ι)
                (fun x => if x ∈ Y then c₁ x else c₂ x)))))) := by
  set c₁' : ι → Fin q := fun x => if x ∈ Y then c₂ x else c₁ x
  set c₂' : ι → Fin q := fun x => if x ∈ Y then c₁ x else c₂ x
  have hY₁ : siteVec own₁ (listT (sites ι) Y) c₁ = siteVec own₁ (listT (sites ι) Y) c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', (mem_listT mem_sites x).mp hx]
  have hN₁ : siteVec own₁ (listR (sites ι) Y) c₁ = siteVec own₁ (listR (sites ι) Y) c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', (mem_listR mem_sites x).mp hx]
  have hY₂ : siteVec own₂ (listT (sites ι) Y) c₂ = siteVec own₂ (listT (sites ι) Y) c₁' :=
    siteVec_congr _ _ fun x hx => by simp [c₁', (mem_listT mem_sites x).mp hx]
  have hN₂ : siteVec own₂ (listR (sites ι) Y) c₂ = siteVec own₂ (listR (sites ι) Y) c₂' :=
    siteVec_congr _ _ fun x hx => by simp [c₂', (mem_listR mem_sites x).mp hx]
  simp only [blockRenameWord, Word.eval_comp, ContinuousLinearMap.comp_apply]
  simp only [Word.eval_frameList_appendIso_symm, eval_partWordApp, hY₁, hN₁]
  simp only [Word.eval_frameList_appendIso_symm, eval_partWord, hY₂, hN₂, Word.eval_swapPairs,
    eval_relabelSitesApp, eval_relabelSites, eval_unpartWord, eval_unpartWordApp]

/-- The renaming is a reordering: an allowed word using no party and no pair source. -/
@[simp] theorem isReordering_blockRenameWord (o₁ i₁ o₂ i₂ : Layout Party) (own₁ own₂ : ι → Party)
    (Y : Finset ι) : (blockRenameWord (q := q) o₁ i₁ o₂ i₂ own₁ own₂ Y).IsReordering := by
  simp [blockRenameWord]

end Rename

end TNLean.Lattice.Sheet
