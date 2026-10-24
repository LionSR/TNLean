/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Monomials
import TNLean.PEPS.Approximation.TwoSheetExchange

/-!
# Births, deaths and exchange corrections as allowed monomials

Lemma 6.5 of the polynomial-PEPS manuscript asserts that a homogeneous birth is a bounded change
involving only `P∘` and `Q∘`: at `P∘` apply `V` on `U` and contract `T B_T` with `⟨s|`, supply
the normalized pair state `s` on `T B_T` with `T` now held by `Q∘` and `B_T` still held by `P∘`,
and apply `Vᴴ` to `B_T B_E` at `P∘`.  The death uses one normalized pair effect `⟨s|` on `T B_T`
held by `Q∘` and `P∘` instead.  Lemma 6.6 asserts that the corrections of a two-sheet exchange
are private contractions at `P∘`.

The monomials themselves, written on a party layout in which the raw registers of `T`, and
those of `U`, are grouped into one register each, and the forms `1_E ⊗ Kᴴ K` and `1 ⊗ W` of the
canonical maps in the coordinates of a sheet, do not depend on the holes and are stated in
`TNLean.Lattice.Sheet.Monomials`.  This file reads them in encoded frames and in a two-sheet
exchange.  The grouped monomials are the middle steps of the bounded changes on the registers of
the frames, one register per site and per tag (`TNLean.PEPS.Approximation.FrameBoundedChanges`),
which group and ungroup the raw registers by private unitaries and exchanges of tensor factors.

## Main results

* `EncodedFrame.Frame.birth_monomial`, `EncodedFrame.Frame.death_monomial` : the birth and the
  death of Lemma 6.5 `lem:birth` on grouped registers.
* `EncodedFrame.TwoSheetExchange.exchange_correction_monomial` : the corrections `D_U F_A` of
  Lemma 6.6 form one private contraction at `P∘` on grouped registers.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.5 `lem:birth` and Lemma 6.6
  `lem:exchange`, `05-frames.tex`, lines 396–570; allowed monomials, `04-compression.tex`,
  lines 32–35.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open TNLean.Lattice (sheetSwap sheetSwapOp)

noncomputable section

open Matrix ContinuousLinearMap EuclideanSpace
open scoped InnerProductSpace TensorProduct Kronecker Matrix.Norms.L2Operator

namespace TNLean.PEPS.EncodedFrame
open TNLean.Lattice.Sheet

open TNLean.Lattice.PartyCircuit

/-! ### Birth and death in an encoded frame -/

section FrameMonomial

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}

namespace Frame
open TNLean.Lattice.Sheet.Frame

variable (F : Frame pos q Party) {T : Finset ι} {P Q : Party}

/-- **The homogeneous birth of Lemma 6.5 on grouped registers.** In
an encoded frame `F`, let `T` be a set of raw sites owned by `P∘` and disjoint from every outer
hole footprint, and let `E` and `U = Λ ∖ (T ∪ E)` be as in `eq:birth-partition`. If
`I_Ω(T:E) ≤ L^{-60}` for a unit vector `Ω`, there are splitting data such that:

* the canonical map `B` is `1_E ⊗ Kᴴ K` with `K = ⟨s| (1_T ⊗ V)` on the registers of `T ∪ U`,
  satisfies `(1 ⊗ B) K_F = K_{F'} B` for the frame `F'` in which `T` is owned by `Q∘`, and
  `‖(1 ⊗ B) Ω_F - Ω_{F'}‖ ≤ L^{-30}`;
* the registers of `U` are owned by `P∘` before and after the birth, and those of `T` by `P∘`
  before and by `Q∘` after;
* on a layout grouping the raw registers of `T`, and those of `U`, into one register each,
  followed by any layout `ℓ` of other registers, `Kᴴ K ⊗ 1` is the operator of an allowed word
  using only `P∘` and `Q∘` with at most one normalized pair source, from `T` and `U` held by
  `P∘` to `T` held by `Q∘`; for `Q∘ ≠ P∘` it is a private contraction at `P∘`, one pair source
  between `Q∘` and `P∘`, and a private contraction at `P∘` (`birthWord`).  On the registers of
  the frame, one per site and per tag, this is `Frame.birth_bounded`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 396–407; proof lines
413–437 and 447–449. -/
theorem birth_monomial [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ =
        sheetPlace (F.disjoint_birthEnv hTP hTH) ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * F.encoder =
        (F.changeOwner T Q).encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) (F.refVec Ω) -
        (F.changeOwner T Q).refVec Ω‖ ≤ L ^ (-30 : ℤ) ∧
      (∀ x ∉ T ∪ F.birthEnv P, F.owner x = P ∧ (F.changeOwner T Q).owner x = P) ∧
      (∀ x ∈ T, (F.changeOwner T Q).owner x = Q) ∧
      ∀ ℓ : Lattice.PartyCircuit.Layout Party,
        ∃ w : Word (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ),
          w.IsAllowed ∧ w.UsesOnly {P, Q} ∧ w.sourceCount ≤ 1 ∧
          ∀ z, pairHeadIso ℓ (w.eval z) =
            (act ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
              (pairHeadIso ℓ z) := by
  obtain ⟨σ, hσ, -, -, hK, herr⟩ := F.birth (Q := Q) hTP hTH hΩ hI
  obtain ⟨hB, hT, hB', -⟩ := F.changeOwner_birth_owners (Q := Q) hTP hTH
  exact ⟨σ, hσ, sheetBirthOp_eq_submatrix _ σ, hK, herr,
    fun x hx => ⟨hB x (Finset.mem_compl.mpr hx), hB' x (Finset.mem_compl.mpr hx)⟩, hT,
    fun ℓ => exists_birthWord P Q σ ℓ⟩

/-- **The homogeneous death of Lemma 6.5 on grouped registers.** Let `F`
be the frame *after* the death, in which `T` is owned by `P∘` and avoids every outer hole footprint,
and let the frame before the death be `F` with `T` owned by `Q∘`. If `I_Ω(T:E) ≤ L^{-60}` for `E`
computed in `F`, there are splitting data such that the canonical map `B = 1_E ⊗ Kᴴ K`, with the
reverse input and output ownership, satisfies `(1 ⊗ B) K_{F_before} = K_F B` and `‖(1 ⊗ B)
Ω_{F_before} - Ω_F‖ ≤ L^{-30}`. On a layout grouping the raw registers of `T`, and those of `U`,
into one register each, followed by any layout `ℓ` of other registers, `Kᴴ K ⊗ 1` is the operator of
an allowed monomial using only `P∘` and `Q∘`, without pair sources and with at most one normalized
pair effect, from `T` held by `Q∘` and `U` by `P∘` to both held by `P∘`; for `Q∘ ≠ P∘` it is a
private contraction at `P∘`, one pair effect between `Q∘` and `P∘`, and a private contraction at
`P∘` (`deathChain`). On the registers of the frame, one per site and per tag, this is
`Frame.death_bounded`.

Polynomial-PEPS manuscript, Lemma 6.5 `lem:birth`, `05-frames.tex`, lines 407–410; proof lines
439–449. -/
theorem death_monomial [NeZero q] (hTP : ∀ x ∈ T, F.owner x = P)
    (hTH : Disjoint (T : Set ι) F.outerHoles) {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L : ℝ}
    (hI : FiniteProduct.mutualInformation (fun _ : ι => Fin q) Ω T (F.birthEnv P) ≤
      L ^ (-60 : ℤ)) :
    ∃ σ : SplittingData q T (F.birthEnv P),
      σ.error (F.disjoint_birthEnv hTP hTH) Ω ≤ L ^ (-30 : ℤ) ∧
      sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ =
        sheetPlace (F.disjoint_birthEnv hTP hTH) ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s) ∧
      ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) * (F.changeOwner T Q).encoder =
        F.encoder * sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ ∧
      ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ
          sheetBirthOp (F.disjoint_birthEnv hTP hTH) σ) ((F.changeOwner T Q).refVec Ω) -
        F.refVec Ω‖ ≤ L ^ (-30 : ℤ) ∧
      (∀ x ∉ T ∪ F.birthEnv P, F.owner x = P ∧ (F.changeOwner T Q).owner x = P) ∧
      (∀ x ∈ T, (F.changeOwner T Q).owner x = Q) ∧
      ∀ ℓ : Lattice.PartyCircuit.Layout Party,
        ∃ M : PartyChain (⟨Q, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨P, euc (T → Fin q)⟩ :: ⟨P, euc (↥(T ∪ F.birthEnv P)ᶜ → Fin q)⟩ :: ℓ),
          M.IsAllowed ∧ M.UsesOnly {P, Q} ∧ M.sourceCount = 0 ∧
          M.toEffectChain.effectCount ≤ 1 ∧
          ∀ z, pairHeadIso ℓ (M.toEffectChain.eval z) =
            (act ((birthKernel σ.V σ.s)ᴴ * birthKernel σ.V σ.s)).rTensor (Mem ℓ)
              (pairHeadIso ℓ z) := by
  obtain ⟨σ, hσ, hB, hK, herr, hown, hT, -⟩ := F.birth_monomial (Q := Q) hTP hTH hΩ hI
  exact ⟨σ, hσ, hB, hK, herr, hown, hT, fun ℓ => exists_deathChain P Q σ ℓ⟩

end Frame

end FrameMonomial

namespace TwoSheetExchange

variable {ι : Type} [Fintype ι] [DecidableEq ι] {q : ℕ} {pos : ι → ℝ × ℝ} {Party : Type}
  (X : TwoSheetExchange pos q Party) (P : Party)

-- Same fourfold product of function types as in `correctionMatrix`.
set_option synthInstance.maxSize 512 in
/-- **Lemma 6.6 (two-sheet exchange): the corrections are a private contraction at `P∘`.** For
splitting data of the exchange partition, the corrections `D_U F_A` of the implemented map
`C = D_U F_A ℛ` are `1 ⊗ W` with `W = correctionMatrix σ A` acting on the two copies of `U`, the
registers of `U` are held by `P∘` on both sheets before and after the exchange, and for every
layout `ℓ` of the other registers `W ⊗ 1` is the operator of one allowed private contraction at
`P∘` on two registers `ℂ^U` of `P∘` grouping the raw registers of `U` on each sheet.  The
renaming `ℛ` is the identification of tensor factors `renameEquiv`, which keeps every register at
its party.  On the registers of the frames, one per site and per tag, the exchange is
`exchange_bounded`.

Polynomial-PEPS manuscript, Lemma 6.6 `lem:exchange`, `05-frames.tex`, lines 474–479; proof
lines 485–515 and 556–561. -/
theorem exchange_correction_monomial (σ : SplittingData q (X.tSet P) (X.eSet P)) :
    sheetBufferCorrection (X.disjoint_tSet_eSet P) σ * sheetSwapOp q (X.aSet P) =
      (((1 : Matrix (((X.tSet P → Fin q) × (X.eSet P → Fin q)) ×
            ((X.tSet P → Fin q) × (X.eSet P → Fin q)))
          (((X.tSet P → Fin q) × (X.eSet P → Fin q)) ×
            ((X.tSet P → Fin q) × (X.eSet P → Fin q))) ℂ) ⊗ₖ
        correctionMatrix σ (X.aSet P)).submatrix
          (Equiv.prodProdProdComm _ _ _ _) (Equiv.prodProdProdComm _ _ _ _)).submatrix
        (threeSplit₂ (X.disjoint_tSet_eSet P)) (threeSplit₂ (X.disjoint_tSet_eSet P)) ∧
      (∀ x ∉ X.tSet P ∪ X.eSet P, (X.owner₁ x = P ∧ X.owner₂ x = P) ∧
        (X.newFrame₁.owner x = P ∧ X.newFrame₂.owner x = P)) ∧
      ∀ ℓ : Lattice.PartyCircuit.Layout Party,
        ∃ w : Word (⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ ::
              ⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ :: ℓ)
            (⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ ::
              ⟨P, euc (↥(X.tSet P ∪ X.eSet P)ᶜ → Fin q)⟩ :: ℓ),
          w.IsAllowed ∧ w.UsesOnly {P} ∧ w.sourceCount = 0 ∧
          ∀ z, pairHeadIso ℓ (w.eval z) =
            (act (correctionMatrix σ (X.aSet P))).rTensor (Mem ℓ) (pairHeadIso ℓ z) := by
  refine ⟨sheetBufferCorrection_mul_sheetSwapOp_eq _ σ (X.aSet_subset_compl P), fun x hx => ?_,
    fun ℓ => ⟨correctionWord P (correctionMatrix σ (X.aSet P)) ℓ,
      (norm_matLocal₂₂_le _ _).trans (norm_correctionMatrix_le_one σ _), Set.mem_singleton P, rfl,
      pairHeadIso_eval_localMap₂₂ P _ ℓ _ _⟩⟩
  rw [tSet_union_eSet] at hx
  exact ⟨X.owner_eq_of_notMem_exchangeEnv P hx, X.newOwner_eq_of_notMem_exchangeEnv P hx⟩

end TwoSheetExchange

end TNLean.PEPS.EncodedFrame
