/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Entropy.RegionPurificationSplitting
import TNLean.PEPS.Approximation.PatchRewrite

/-!
# Splitting a sheet, and operators passing through the encoding of a frame

The splitting consequence of Lemma 6.4 of the polynomial-PEPS manuscript is stated in QICLean for
two regions `A ⊆ B`, with second region `B \ A`, in the three-region coordinates
`ManyBody.threeCutEquiv` (`ManyBody.SplittingData.exists_error_le`). This file reads it for two
disjoint sets of sites `T`, `E` of a sheet, as the manuscript states it: `A = T`, `B = T ∪ E`, and
`(T ∪ E) \ T = E`. It then adds the two facts that involve the holes of an encoded frame: an
operator `1 ⊗ B`, acting as `B` on the raw registers and as the identity on the tags, passes
through the encoding `K_F` whenever `B` commutes with its raw part on every tag configuration, and
then `‖(1 ⊗ B) Ω_F - Ω_F‖ ≤ ‖B Ω - Ω‖`.

## Main results

* `EncodedFrame.exists_sheetSplitting`, `EncodedFrame.exists_sheetSplitting_zpow`,
  `EncodedFrame.exists_sheetSplitting_rpow`: Lemma 6.4 for disjoint `T`, `E`.
* `EncodedFrame.one_kronecker_mul_frameEncoder`: `(1 ⊗ B) K_F = K_F B`.
* `EncodedFrame.norm_toEuclideanLin_one_kronecker_refVec_sub_le`: the defect of `1 ⊗ B` on the
  reference vector is at most the defect of `B` on `Ω`.

## References

* Polynomial-PEPS manuscript (September 24, 2026), Lemma 6.4 `lem:splitting`,
  `05-frames.tex`, lines 352–394.

Source text: `openai/math` at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, file
`preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/`
`build/sections/05-frames.tex`. The statements and proofs here are formalized independently from
the manuscript; no upstream Lean proof text was reused.
-/

open Matrix
open scoped Kronecker Matrix.Norms.L2Operator

noncomputable section

namespace TNLean.PEPS.EncodedFrame

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {q : ℕ}

/-! ### The splitting consequence for two disjoint sets of sites -/

section Splitting

variable {T E : Finset ι} (h : Disjoint T E)

include h in
/-- The mutual information between `T` and the middle region `(T ∪ E) \ T` of the three-region
coordinates is the mutual information between `T` and `E`. -/
private theorem regionMutualInformation_union_sdiff (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ManyBody.regionMutualInformation Ω T ((T ∪ E) \ T) =
      ManyBody.regionMutualInformation Ω T E := by
  rw [Finset.union_sdiff_cancel_left h]

include h in
/-- **Splitting consequence on a sheet** (Lemma 6.4 `lem:splitting`). Let `T`, `E` be disjoint
sets of sites, `U = (T ∪ E)ᶜ`, and `b = I_Ω(T:E)` for a unit vector `Ω` on the sheet. There are
splitting data, in the three-region coordinates of `T ⊆ T ∪ E` (whose middle region
`(T ∪ E) \ T` is `E`), with `‖(1_{TE} ⊗ V) Ω - s ⊗ s'‖ ≤ √(2(1 - e^{-b/2})) ≤ √b`. No bound on
the dimensions is imposed.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 352–368. -/
theorem exists_sheetSplitting {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) :
    ∃ σ : ManyBody.SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E),
      σ.error Finset.subset_union_left Ω ≤
        √(2 * (1 - Real.exp (-(ManyBody.regionMutualInformation Ω T E
          / 2)))) ∧
      √(2 * (1 - Real.exp (-(ManyBody.regionMutualInformation Ω T E
          / 2)))) ≤ √(ManyBody.regionMutualInformation Ω T E) := by
  rw [← regionMutualInformation_union_sdiff h Ω]
  exact ManyBody.SplittingData.exists_error_le Finset.subset_union_left hΩ

include h in
/-- **Splitting at a polynomially small mutual information** (Lemma 6.4 `lem:splitting`, last
sentence). If `I_Ω(T:E) ≤ L^{-60}`, the splitting error is at most `L^{-30}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367. -/
theorem exists_sheetSplitting_zpow {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1) {L : ℝ}
    (hI : ManyBody.regionMutualInformation Ω T E ≤ L ^ (-60 : ℤ)) :
    ∃ σ : ManyBody.SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-30 : ℤ) := by
  rw [← regionMutualInformation_union_sdiff h Ω] at hI
  exact ManyBody.SplittingData.exists_error_le_zpow Finset.subset_union_left hΩ hI

include h in
/-- **Splitting at a polynomially small mutual information, any exponent** (Lemma 6.4
`lem:splitting`, last sentence, and the splitting step of Lemmas `lem:birth` and `lem:exchange` of
the one-dimensional note, `part2b_mps_protocol.tex`, lines 70–158). For `0 ≤ L` and any real
exponent `p`, if `I_Ω(T:E) ≤ L^{-2p}`, the splitting error is at most `L^{-p}`.

Polynomial-PEPS manuscript, Lemma 6.4 `lem:splitting`, `05-frames.tex`, lines 366–367, there
with `p = 30`. -/
theorem exists_sheetSplitting_rpow {Ω : EuclideanSpace ℂ (ι → Fin q)} (hΩ : ‖Ω‖ = 1)
    {L p : ℝ} (hL : 0 ≤ L)
    (hI : ManyBody.regionMutualInformation Ω T E ≤ L ^ (-(2 * p))) :
    ∃ σ : ManyBody.SplittingData (fun _ : ι ↦ Fin q) T (T ∪ E),
      σ.error Finset.subset_union_left Ω ≤ L ^ (-p) := by
  rw [← regionMutualInformation_union_sdiff h Ω] at hI
  exact ManyBody.SplittingData.exists_error_le_rpow Finset.subset_union_left hΩ hL hI

end Splitting

/-! ### Operators passing through the encoding -/

/-- The operator `1 ⊗ B` on the layout of a list of holes, acting as `B` on the raw registers and
as the identity on the tags, passes through the encoding of the list whenever `B` commutes with
the raw part of the encoding on every tag configuration. -/
theorem one_kronecker_mul_frameEncoder [NeZero q] {pos : ι → ℝ × ℝ} {Party : Type*}
    {l : List (Hole pos q Party)} {B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hB : ∀ t, Commute B (rawProd l t)) :
    ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ B) * frameEncoder l = frameEncoder l * B :=
  one_kronecker_mul_stack hB

/-- If `B` passes through the encoding, `‖(1 ⊗ B) Ω_F - Ω_F‖ ≤ ‖B Ω - Ω‖`. -/
theorem norm_toEuclideanLin_one_kronecker_refVec_sub_le [NeZero q] {pos : ι → ℝ × ℝ}
    {Party : Type*} (F : Frame pos q Party) {B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hB : ∀ t, Commute B (rawProd F.holes t)) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖toEuclideanLin ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ B) (F.refVec Ω) -
        F.refVec Ω‖ ≤ ‖toEuclideanLin B Ω - Ω‖ := by
  have h : toEuclideanLin ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ B)
      (F.refVec Ω) - F.refVec Ω = toEuclideanLin F.encoder (toEuclideanLin B Ω - Ω) := by
    rw [Frame.refVec, ← toEuclideanLin_mul_apply, Frame.encoder,
      one_kronecker_mul_frameEncoder hB, toEuclideanLin_mul_apply, map_sub]
  rw [h]
  exact norm_toEuclideanLin_apply_le_of_norm_le_one F.norm_encoder_le_one _

end TNLean.PEPS.EncodedFrame
