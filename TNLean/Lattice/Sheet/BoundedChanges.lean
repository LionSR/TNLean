/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Defs

/-!
# Births, deaths and exchanges of sheets as bounded changes

Lemmas `lem:birth` and `lem:exchange` of the one-dimensional note assert that a birth or a death
of a set `T` of sites of a sheet, and an exchange of two sheets inside a region `Y`, are bounded
changes: allowed monomials on a bounded number of parties, with small reference-vector error.
These are Lemmas 6.5 and 6.6 of the polynomial-PEPS manuscript read on sheets without encoded
holes; in one dimension no holes are needed (remark following `lem:exchange` in the note).

* `Sheet.birth_bounded`: if `T` is owned by `P∘` and `I_Ω(T:E) ≤ L^{-60}`, handing `T` to `Q∘`
  is an allowed word using only `P∘` and `Q∘`, with at most one normalized pair source, whose
  operator in canonical coordinates is the canonical map `B` of the splitting data, with
  reference-vector error at most `L^{-30}`.
* `Sheet.death_bounded`: the reverse change, with one normalized pair effect instead.
* `Sheet.exchange_bounded`: the exchange is an allowed word using only `P∘` and no pair
  resource, whose operator is `C = D_U F_A F_Y = D_U F_T`, with reference-vector error at most
  `4 L^{-30}` between the products of the old and new reference vectors.

The words are those of `TNLean.Lattice.Sheet.FrontChanges` behind the empty front block; the
same words, behind the tag registers of the holes, give the bounds for encoded frames.

These are original proofs; no OpenAI Lean code is copied or adapted.

## References

* One-dimensional note, `docs/notes/one_dimensional_note/part2b_mps_protocol.tex`: bounded
  changes, lines 47–64; Lemma `lem:birth`, lines 70–94; Lemma `lem:exchange`, lines 112–158;
  the remark of lines 165–171.
* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`: bounded changes,
  lines 99–105; Lemma 6.5 `lem:birth`, lines 396–456; Lemma 6.6 `lem:exchange`, lines 460–561;
  allowed monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator
open TNLean.PEPS.EncodedFrame TNLean.PEPS.PairEffect

namespace TNLean.Lattice

namespace Sheet

variable {ι Party : Type} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### Birth and death -/

section Birth

variable (S : Sheet ι Party) {T : Finset ι} {P Q : Party}

/-- **Lemma `lem:birth` (birth): the birth is a bounded change involving only `P∘` and `Q∘`.**
In a sheet `S`, let `T` be a set of sites owned by `P∘`, `E` the set of sites not owned by
`P∘`, and `U = Λ ∖ (T ∪ E)`. If `I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting
data and an allowed monomial `w` from the registers of `S` to those of the sheet in which `T` is
owned by `Q∘`, such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source;
* in canonical coordinates the operator of `w` is the canonical map `B` of the splitting data;
* the reference-vector error is at most `L^{-30}`.

The monomial constructed in the proof groups the registers of `T` and of `U` at `P∘`, applies,
for `Q∘ ≠ P∘`, the private contraction `⟨s| (1_T ⊗ V)` at `P∘`, prepares the pair state `s` on
`T` held by `Q∘` and `B_T` held by `P∘`, applies `Vᴴ` at `P∘`, and ungroups.

One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 70–79; proof
lines 80–94. Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 396–437. -/
theorem birth_bounded (hTP : ∀ x ∈ T, S.owner x = P) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (S.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (S.birthEnv P),
      σ.error (S.disjoint_birthEnv hTP) Ω ≤ L ^ (-30 : ℤ) ∧
      ∃ w : Word (S.regs q) ((S.changeOwner T Q).regs q),
        w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
        (∀ z, (S.changeOwner T Q).regIso q (w.eval z) =
          act (sheetBirthOp (S.disjoint_birthEnv hTP) σ) (S.regIso q z)) ∧
        ‖w.eval (S.regRef Ω) - (S.changeOwner T Q).regRef Ω‖ ≤ L ^ (-30 : ℤ) := by
  set h := S.disjoint_birthEnv hTP
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow h hΩ hI
  obtain ⟨hB, hA', hB', hE⟩ := S.changeOwner_birth_owners (Q := Q) hTP
  obtain ⟨w, hwA, hwU, hwS, hw⟩ := exists_frontBirthWord [] nilFrontIso S.owner
    (S.changeOwner T Q).owner h hTP hB hA' hB' hE σ
  have heval : ∀ z, (S.changeOwner T Q).regIso q (w.eval z) =
      act (sheetBirthOp h σ) (S.regIso q z) := fun z => by
    rw [regIso_eq_frontLayoutIso, regIso_eq_frontLayoutIso]
    exact (congrArg (unitProdIso _) (hw z)).trans (unitProdIso_act_one_kronecker _ _)
  refine ⟨σ, hσ, w, hwA, hwU, hwS, heval, ?_⟩
  rw [← ((S.changeOwner T Q).regIso q).norm_map, map_sub, regRef, regRef, heval,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact (norm_act_sheetBirthOp_sub_le h σ Ω).trans hσ

/-- **Lemma `lem:birth` (death): the death is a bounded change involving only `P∘` and `Q∘`.**
Let `S` be the sheet *after* the death, in which `T` is owned by `P∘`, and let the sheet before
the death be the one in which `T` is owned by `Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E` computed in
`S`, there are splitting data and an allowed monomial from the registers of the sheet before
the death to those of `S`, using only `P∘` and `Q∘`, without pair sources and with at most one
normalized pair effect, whose operator in canonical coordinates is the canonical map `B`, with
reference-vector error at most `L^{-30}`. The monomial constructed in the proof groups the
registers of `T` at `Q∘` and of `U` at `P∘`, then, for `Q∘ ≠ P∘`, applies `V` at `P∘`, contracts
`T` and `B_T` with the pair effect `⟨s|` held by `Q∘` and `P∘`, reinserts `s` and applies `Vᴴ` at
`P∘`, and ungroups at `P∘`.

One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 75–79; proof
lines 91–93. Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 407–410 and
439–446. -/
theorem death_bounded (hTP : ∀ x ∈ T, S.owner x = P) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (S.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (S.birthEnv P),
      σ.error (S.disjoint_birthEnv hTP) Ω ≤ L ^ (-30 : ℤ) ∧
      ∃ M : PartyChain ((S.changeOwner T Q).regs q) (S.regs q),
        M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧ M.toEffectChain.effectCount ≤ 1 ∧
        (∀ z, S.regIso q (M.toEffectChain.eval z) =
          act (sheetBirthOp (S.disjoint_birthEnv hTP) σ) ((S.changeOwner T Q).regIso q z)) ∧
        ‖M.toEffectChain.eval ((S.changeOwner T Q).regRef Ω) - S.regRef Ω‖ ≤
          L ^ (-30 : ℤ) := by
  set h := S.disjoint_birthEnv hTP
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow h hΩ hI
  obtain ⟨hB', hA, hB, hE⟩ := S.changeOwner_birth_owners (Q := Q) hTP
  obtain ⟨M, hMA, hMU, hMS, hMe, hM⟩ := exists_frontDeathChain [] nilFrontIso
    (S.changeOwner T Q).owner S.owner h hA hB hTP hB' (fun x hx => (hE x hx).symm) σ
  have heval : ∀ z, S.regIso q (M.toEffectChain.eval z) =
      act (sheetBirthOp h σ) ((S.changeOwner T Q).regIso q z) := fun z => by
    rw [regIso_eq_frontLayoutIso, regIso_eq_frontLayoutIso]
    exact (congrArg (unitProdIso _) (hM z)).trans (unitProdIso_act_one_kronecker _ _)
  refine ⟨σ, hσ, M, hMA, hMU, hMS, hMe, heval, ?_⟩
  rw [← (S.regIso q).norm_map, map_sub, regRef, regRef, heval,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.apply_symm_apply]
  exact (norm_act_sheetBirthOp_sub_le h σ Ω).trans hσ

end Birth

/-! ### Two-sheet exchange -/

section Exchange

variable (S₁ S₂ : Sheet ι Party) (Y : Finset ι) (P : Party)

/-- **The renaming `ℛ` of an exchange of two sheets**, a word of exchanges of tensor factors that
keeps every register at its party: a raw register of the first sheet at a site of `Y` becomes
the register of the second sheet after the exchange at that site.

One-dimensional note, proof of Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 126–129. -/
def renameWord :
    Word (S₁.regs q ++ S₂.regs q) ((swapIn S₁ S₂ Y).regs q ++ (swapIn S₂ S₁ Y).regs q) :=
  blockRenameWord [] [] [] [] S₁.owner S₂.owner Y

/-- **The renaming on basis vectors.** Inside `Y` the configurations of the two sheets change
places. -/
theorem eval_renameWord (c₁ c₂ : ι → Fin q) :
    (renameWord S₁ S₂ Y).eval ((appendIso _ _).symm
        (siteVec S₁.owner (sites ι) c₁ ⊗ₜ siteVec S₂.owner (sites ι) c₂)) =
      (appendIso _ _).symm (siteVec (swapIn S₁ S₂ Y).owner (sites ι)
          (fun x => if x ∈ Y then c₂ x else c₁ x) ⊗ₜ
        siteVec (swapIn S₂ S₁ Y).owner (sites ι) (fun x => if x ∈ Y then c₁ x else c₂ x)) := by
  have h := eval_blockRenameWord (q := q) [] [] [] [] S₁.owner S₂.owner Y (1 : ℂ) (1 : ℂ)
    (1 : ℂ) (1 : ℂ) c₁ c₂
  repeat rw [appendIso_nil_symm_tmul, one_smul] at h
  exact h

/-- **The renaming in canonical coordinates** is the swap `F_Y` of the two sheets on `Y`. -/
theorem twoRegIso_renameWord (z : Mem (S₁.regs q ++ S₂.regs q)) :
    twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y) ((renameWord S₁ S₂ Y).eval z) =
      act (sheetSwapOp q Y) (twoRegIso q S₁ S₂ z) :=
  twoRegIso_eq_act_of_basis q S₁ S₂ _ _ _ _ (fun c₁ c₂ => by
    rw [eval_renameWord, twoRegIso_appendIso_symm, regIso_siteVec, regIso_siteVec, sheetSwapOp,
      ← sheetSwap_symm, act_toMatrix_symm_single]
    ext ⟨a, b⟩
    simp only [vecKron, sheetSwap, Equiv.coe_fn_mk, PiLp.single_apply, Prod.mk.injEq]
    split_ifs <;> simp_all) z

@[simp] theorem isReordering_renameWord : (renameWord (q := q) S₁ S₂ Y).IsReordering :=
  isReordering_blockRenameWord _ _ _ _ _ _ _

/-- **Lemma `lem:exchange` (two-sheet exchange): the exchange is a bounded change involving only
`P∘`.** Consider two sheets and a region `Y`. Inside `Y`, exchange the two ownership
assignments; outside `Y`, keep both. Let `P∘` be a party, `Z` the set of sites whose two owners
are not both `P∘`, `T = Z ∩ Y`, `E = Z ∖ Y` and `U = Λ ∖ Z`. If `I_Ω(T:E) ≤ L^{-60}` for a unit
vector `Ω`, there are splitting data and an allowed monomial `w` from the registers of the two
sheets to the registers of the two sheets after the exchange, such that:

* `w` uses only `P∘` and no pair resource; the monomial constructed in the proof is the renaming
  `ℛ`, a word of exchanges of tensor factors that keeps every register at its party, followed by
  one private contraction at `P∘` on the raw registers of `U` of both sheets (the corrections
  `D_U F_A`);
* in canonical coordinates its operator is the map `C = D_U F_A F_Y`, and `C = D_U F_T`;
* the reference-vector error is at most `4 L^{-30}`: `‖w (Ω ⊗ Ω) - Ω ⊗ Ω‖ ≤ 4 L^{-30}`, read on
  the registers of the sheets before and after the exchange.

One-dimensional note, Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 112–124; proof
lines 125–158. Polynomial-PEPS manuscript, Lemma 6.6, `05-frames.tex`, lines 460–561. -/
theorem exchange_bounded {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω (tSet S₁ S₂ Y P)
      (eSet S₁ S₂ Y P) ≤ L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q (tSet S₁ S₂ Y P) (eSet S₁ S₂ Y P),
      σ.error (disjoint_tSet_eSet S₁ S₂ Y P) Ω ≤ L ^ (-30 : ℤ) ∧
      exchangeOp S₁ S₂ Y P σ =
        sheetBufferCorrection (disjoint_tSet_eSet S₁ S₂ Y P) σ * sheetSwapOp q (tSet S₁ S₂ Y P) ∧
      ∃ w : Word (S₁.regs q ++ S₂.regs q) ((swapIn S₁ S₂ Y).regs q ++ (swapIn S₂ S₁ Y).regs q),
        w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
        (∀ z, twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y) (w.eval z) =
          act (exchangeOp S₁ S₂ Y P σ) (twoRegIso q S₁ S₂ z)) ∧
        ‖w.eval ((twoRegIso q S₁ S₂).symm (vecKron Ω Ω)) -
          (twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm (vecKron Ω Ω)‖ ≤
            4 * L ^ (-30 : ℤ) := by
  set h := disjoint_tSet_eSet S₁ S₂ Y P
  obtain ⟨σ, hσ⟩ := exists_sheetSplitting_zpow h hΩ hI
  have hU : ∀ x ∈ (tSet S₁ S₂ Y P ∪ eSet S₁ S₂ Y P)ᶜ,
      (swapIn S₁ S₂ Y).owner x = P ∧ (swapIn S₂ S₁ Y).owner x = P := fun x hx =>
    swapIn_owner_eq_of_mem_compl S₁ S₂ Y P hx
  let c := frontCorrectionWord (q := q) [] [] (swapIn S₁ S₂ Y).owner (swapIn S₂ S₁ Y).owner
    (fun x hx => (hU x hx).1) (fun x hx => (hU x hx).2) (correctionMatrix σ (aSet S₁ S₂ Y P))
  have hc : ∀ z, twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y) (c.eval z) =
      act (sheetBufferCorrection h σ * sheetSwapOp q (aSet S₁ S₂ Y P))
        (twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y) z) := fun z => by
    rw [twoRegIso_eq_twoFrontLayoutIso, twoRegIso_eq_twoFrontLayoutIso,
      twoFrontLayoutIso_frontCorrectionWord h, liftFront, unitProdIso₂_act_liftFront,
      sheetBufferCorrection_mul_sheetSwapOp_eq h σ (aSet_subset_compl S₁ S₂ Y P)]
  have heval : ∀ z, twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)
      (((renameWord S₁ S₂ Y).comp c).eval z) =
        act (exchangeOp S₁ S₂ Y P σ) (twoRegIso q S₁ S₂ z) := fun z => by
    rw [Word.eval_comp, ContinuousLinearMap.comp_apply, hc, twoRegIso_renameWord, ← act_mul,
      exchangeOp]
  have r := isReordering_renameWord (q := q) S₁ S₂ Y
  obtain ⟨c₁, c₂, c₃⟩ := frontCorrectionWord_props (q := q) [] [] (swapIn S₁ S₂ Y).owner
    (swapIn S₂ S₁ Y).owner (fun x hx => (hU x hx).1) (fun x hx => (hU x hx).2)
    (norm_correctionMatrix_le_one σ (aSet S₁ S₂ Y P))
  refine ⟨σ, hσ, exchangeOp_eq S₁ S₂ Y P σ, (renameWord S₁ S₂ Y).comp c, ⟨r.isAllowed, c₁⟩,
    ⟨r.usesOnly _, c₂⟩, congrArg₂ (· + ·) r.sourceCount_eq c₃, heval, ?_⟩
  rw [← (twoRegIso q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).norm_map, map_sub,
    LinearIsometryEquiv.apply_symm_apply, heval, LinearIsometryEquiv.apply_symm_apply,
    exchangeOp_eq]
  exact (norm_act_sheetBufferCorrection_mul_sheetSwapOp_sub_le h σ hΩ).trans (by linarith)

end Exchange

end Sheet

end TNLean.Lattice
