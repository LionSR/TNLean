/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Circuit.Party.Sheet.BoundedChanges
import QICLean.ManyBody.Entropy.RegionPurificationSplitting

/-!
# Births, deaths and exchanges of sheets as bounded changes

Lemmas `lem:birth` and `lem:exchange` of the one-dimensional note assert that a birth or a death
of a set `T` of sites of a sheet, and an exchange of two sheets inside a region `Y`, are bounded
changes: allowed monomials on a bounded number of parties, with small reference-vector error,
provided a regional mutual information is small. These are Lemmas 6.5 and 6.6 of the
polynomial-PEPS manuscript read on sheets without encoded holes; in one dimension no holes are
needed (remark following `lem:exchange` in the note).

The circuits and their operators are constructed for given splitting data of the cut
(`QuantumCircuit.Party.Sheet.exists_birthWord_of_splittingData`,
`exists_deathChain_of_splittingData`, `exists_exchangeWord_of_splittingData`); the splitting
data with error at most `L^{-p}` come from the information bound
(`ManyBody.SplittingData.exists_error_le_rpow`). The statements below compose the two, with the
hypotheses of the source.

* `QuantumCircuit.Party.Sheet.birth_bounded`: if `T` is owned by `P∘` and `I_Ω(T:E) ≤ L^{-2p}`,
  handing `T` to `Q∘` is an allowed word using only `P∘` and `Q∘`, with at most one normalized
  pair source, whose operator in canonical coordinates is the canonical map `B` of the splitting
  data, with reference-vector error at most `L^{-p}`.
* `QuantumCircuit.Party.Sheet.death_bounded`: the reverse change, a monomial whose only gate is at
  most one normalized pair effect.
* `QuantumCircuit.Party.Sheet.exchange_bounded`: the exchange is the renaming of the bases of the
  parties whose sites change sheet, followed by an allowed word using only `P∘` and no pair
  resource; its operator is `C = D_U F_A F_Y = D_U F_T`, with reference-vector error at most
  `4 L^{-p}` between the products of the old and new reference vectors.

As in the note, the exponent is a free real parameter `p` (the information hypothesis is
`I_Ω(T:E) ≤ L^{-2p}`, the error `L^{-p}`, for `0 ≤ L`); the polynomial-PEPS manuscript takes
`p = 30`, and the chain protocol of the note uses `2p = 24`.

## References

* One-dimensional note, `docs/notes/one_dimensional_note/part2b_mps_protocol.tex`: bounded
  changes, lines 47–64; Lemma `lem:birth`, lines 70–94; Lemma `lem:exchange`, lines 112–158;
  the remark of lines 165–171.
* Polynomial-PEPS manuscript (September 24, 2026), `05-frames.tex`: bounded changes,
  lines 99–105; Lemma 6.5 `lem:birth`, lines 396–456; Lemma 6.6 `lem:exchange`, lines 460–561;
  allowed monomials, `04-compression.tex`, lines 32–35.
-/

noncomputable section

open Matrix ManyBody
open scoped Matrix.Norms.L2Operator

namespace QuantumCircuit.Party

namespace Sheet

variable {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P] [DecidableEq P] {q : ℕ}

/-! ### Birth and death -/

section Birth

variable (S : Sheet ι P) {T : Finset ι} {P₀ Q : P}

/-- **Lemma `lem:birth` (birth): the birth is a bounded change involving only `P∘` and `Q∘`.**
In a sheet `S`, let `T` be a set of sites owned by `P∘`, `E` the set of sites not owned by
`P∘`, and `U = Λ ∖ (T ∪ E)`. Let `0 ≤ L` and let `p` be real. If `I_Ω(T:E) ≤ L^{-2p}` for a
unit vector `Ω`, there are splitting data of the cut `T`, `E` with error at most `L^{-p}` and an
allowed word `w` from the system of `S` to the system of the sheet in which `T` is owned by `Q∘`,
such that:

* `w` uses only `P∘` and `Q∘` and at most one normalized pair source;
* in canonical coordinates the operator of `w` is the canonical map `B` of the splitting data;
* the reference-vector error is at most `L^{-p}`.

One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 70–79; proof
lines 80–94. Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 396–437, there with
`p = 30`. -/
theorem birth_bounded (hTP : ∀ x ∈ T, S.owner x = P₀) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {L p : ℝ} (hL : 0 ≤ L)
    (hI : regionMutualInformation Ω T (S.birthEnv P₀) ≤ L ^ (-(2 * p))) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-p) ∧
      ∃ w : Word (S.system q) ((S.changeOwner T Q).system q),
        w.IsAllowed ∧ w.UsesOnly {P₀, Q} ∧ w.sourceCount ≤ 1 ∧
        w.op = reindex (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
          (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
          (configBirthOp Finset.subset_union_left σ) ∧
        ‖toEuclideanLin w.op (S.refVec Ω) - (S.changeOwner T Q).refVec Ω‖ ≤ L ^ (-p) := by
  have hI' : regionMutualInformation Ω T ((T ∪ S.birthEnv P₀) \ T) ≤ L ^ (-(2 * p)) := by
    rwa [Finset.union_sdiff_cancel_left (S.disjoint_birthEnv hTP)]
  obtain ⟨σ, hσ⟩ := SplittingData.exists_error_le_rpow Finset.subset_union_left hΩ hL hI'
  obtain ⟨w, hwA, hwU, hwS, hop, herr⟩ :=
    exists_birthWord_of_splittingData (Q := Q) S hTP σ Ω
  exact ⟨σ, hσ, w, hwA, hwU, hwS, hop, herr.trans hσ⟩

/-- **Lemma `lem:birth` (death): the death is a bounded change involving only `P∘` and `Q∘`.**
Let `S` be the sheet *after* the death, in which `T` is owned by `P∘`, and let the sheet before
the death be the one in which `T` is owned by `Q∘`. Let `0 ≤ L` and let `p` be real. If
`I_Ω(T:E) ≤ L^{-2p}` for `E` computed in `S`, there are splitting data with error at most
`L^{-p}` and an allowed monomial from the system of the sheet before the death to that of `S`,
using only `P∘` and `Q∘`, whose gates are pair effects, at most one of them, whose operator in
canonical coordinates is the canonical map `B`, with reference-vector error at most `L^{-p}`.

One-dimensional note, Lemma `lem:birth`, `part2b_mps_protocol.tex`, lines 75–79; proof
lines 91–93. Polynomial-PEPS manuscript, Lemma 6.5, `05-frames.tex`, lines 407–410 and
439–446. -/
theorem death_bounded (hTP : ∀ x ∈ T, S.owner x = P₀) {Ω : EuclideanSpace ℂ (ι → Fin q)}
    (hΩ : ‖Ω‖ = 1) {L p : ℝ} (hL : 0 ≤ L)
    (hI : regionMutualInformation Ω T (S.birthEnv P₀) ≤ L ^ (-(2 * p))) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) T (T ∪ S.birthEnv P₀),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-p) ∧
      ∃ M : PartyCircuit (ChainGate (P := P)) ((S.changeOwner T Q).system q) (S.system q),
        M.IsAllowed chainEv ChainGate.IsAllowed ∧ M.UsesOnly {P₀, Q} ∧
        M.ForallGate (fun _ _ _ g ↦ Sum.isRight g) ∧ M.numGates ≤ 1 ∧
        M.op chainEv = reindex (blockConfigEquiv S.owner fun _ ↦ Fin q).symm
          (blockConfigEquiv (S.changeOwner T Q).owner fun _ ↦ Fin q).symm
          (configBirthOp Finset.subset_union_left σ) ∧
        ‖toEuclideanLin (M.op chainEv) ((S.changeOwner T Q).refVec Ω) - S.refVec Ω‖ ≤
          L ^ (-p) := by
  have hI' : regionMutualInformation Ω T ((T ∪ S.birthEnv P₀) \ T) ≤ L ^ (-(2 * p)) := by
    rwa [Finset.union_sdiff_cancel_left (S.disjoint_birthEnv hTP)]
  obtain ⟨σ, hσ⟩ := SplittingData.exists_error_le_rpow Finset.subset_union_left hΩ hL hI'
  obtain ⟨M, hMA, hMU, hMg, hMn, hop, herr⟩ :=
    exists_deathChain_of_splittingData (Q := Q) S hTP σ Ω
  exact ⟨σ, hσ, M, hMA, hMU, hMg, hMn, hop, herr.trans hσ⟩

end Birth

/-! ### Two-sheet exchange -/

section Exchange

variable (S₁ S₂ : Sheet ι P) (Y : Finset ι) (P₀ : P)

/-- **Lemma `lem:exchange` (two-sheet exchange): the exchange is a bounded change involving only
`P∘`.** Consider two sheets and a region `Y`. Inside `Y`, exchange the two ownership
assignments; outside `Y`, keep both. Let `P∘` be a party, `Z` the set of sites whose two owners
are not both `P∘` (`exchangeEnv S₁ S₂ P∘`), `T = Z ∩ Y`, `E = Z ∖ Y` and `U = Λ ∖ Z`. Let
`0 ≤ L` and let `p` be real. If `I_Ω(T:E) ≤ L^{-2p}` for a unit vector `Ω`, there are splitting
data of the cut `T`, `E` with error at most `L^{-p}` and an allowed word `c` using only `P∘` and
no pair resource such that the renaming `ℛ` (`renameWord`, a relabelling of the bases of the
parties whose sites change sheet) followed by `c`:

* has, in canonical coordinates, the operator `C = D_U F_A F_Y`, and `C = D_U F_T`;
* moves `Ω ⊗ Ω` on the two sheets by at most `4 L^{-p}`.

One-dimensional note, Lemma `lem:exchange`, `part2b_mps_protocol.tex`, lines 112–124; proof
lines 125–158. Polynomial-PEPS manuscript, Lemma 6.6, `05-frames.tex`, lines 460–561, there
with `p = 30`. -/
theorem exchange_bounded {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L p : ℝ}
    (hL : 0 ≤ L)
    (hI : regionMutualInformation Ω (exchangeEnv S₁ S₂ P₀ ∩ Y) (exchangeEnv S₁ S₂ P₀ \ Y) ≤
      L ^ (-(2 * p))) :
    ∃ σ : SplittingData (fun _ : ι ↦ Fin q) (exchangeEnv S₁ S₂ P₀ ∩ Y)
        (exchangeEnv S₁ S₂ P₀ ∩ Y ∪ exchangeEnv S₁ S₂ P₀ \ Y),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-p) ∧
      exchangeOp Y (exchangeEnv S₁ S₂ P₀) σ =
        configBufferCorrection Finset.subset_union_left σ *
          reindex (Equiv.arrowProdEquivProdArrow ι _ _) (Equiv.arrowProdEquivProdArrow ι _ _)
            (pairSwapOp (X := fun _ : ι ↦ Fin q) (exchangeEnv S₁ S₂ P₀ ∩ Y)) ∧
      ∃ c : Word (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p)
          (fun p ↦ (swapIn S₁ S₂ Y).system q p × (swapIn S₂ S₁ Y).system q p),
        c.IsAllowed ∧ c.UsesOnly {P₀} ∧ c.sourceCount = 0 ∧
        Word.op (PartyCircuit.comp (renameWord S₁ S₂ Y) c) =
          reindex (twoConfigEquiv q (swapIn S₁ S₂ Y) (swapIn S₂ S₁ Y)).symm
            (twoConfigEquiv q S₁ S₂).symm (exchangeOp Y (exchangeEnv S₁ S₂ P₀) σ) ∧
        ‖toEuclideanLin (Word.op (PartyCircuit.comp (renameWord S₁ S₂ Y) c))
            (prodVec (S₁.refVec Ω) (S₂.refVec Ω)) -
          prodVec ((swapIn S₁ S₂ Y).refVec Ω) ((swapIn S₂ S₁ Y).refVec Ω)‖ ≤
            4 * L ^ (-p) := by
  set Z := exchangeEnv S₁ S₂ P₀
  have hI' : regionMutualInformation Ω (Z ∩ Y) ((Z ∩ Y ∪ Z \ Y) \ (Z ∩ Y)) ≤
      L ^ (-(2 * p)) := by
    rwa [Finset.union_sdiff_cancel_left (Finset.disjoint_sdiff_inter Z Y).symm]
  obtain ⟨σ, hσ⟩ := SplittingData.exists_error_le_rpow Finset.subset_union_left hΩ hL hI'
  obtain ⟨hK, c, hcA, hcU, hcS, hop, herr⟩ :=
    exists_exchangeWord_of_splittingData S₁ S₂ Y P₀ Z
      (fun _ hx ↦ owner_eq_of_notMem_exchangeEnv S₁ S₂ P₀ hx) hΩ σ
  exact ⟨σ, hσ, hK, c, hcA, hcU, hcS, hop, herr.trans (by linarith)⟩

end Exchange

end Sheet

end QuantumCircuit.Party
