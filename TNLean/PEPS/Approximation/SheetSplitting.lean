/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Lattice.Sheet.Splitting
import TNLean.PEPS.Approximation.PatchRewrite

/-!
# Operators passing through the encoding of a frame

The splitting consequence of Lemma 6.4 of the polynomial-PEPS manuscript and the three-region
coordinates of a sheet are stated on any finite set of sites in `TNLean.Lattice.Sheet.Splitting`.
This file adds the two facts that involve the holes of an encoded frame: an operator `1 ⊗ B`,
acting as `B` on the raw registers and as the identity on the tags, passes through the encoding
`K_F` whenever `B` commutes with its raw part on every tag configuration, and then
`‖(1 ⊗ B) Ω_F - Ω_F‖ ≤ ‖B Ω - Ω‖`.

## Main results

* `EncodedFrame.one_kronecker_mul_frameEncoder`: `(1 ⊗ B) K_F = K_F B`.
* `EncodedFrame.norm_act_one_kronecker_refVec_sub_le`: the defect of `1 ⊗ B` on the reference
  vector is at most the defect of `B` on `Ω`.

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

/-- The operator `1 ⊗ B` on the layout of a list of holes, acting as `B` on the raw registers and
as the identity on the tags, passes through the encoding of the list whenever `B` commutes with
the raw part of the encoding on every tag configuration. -/
theorem one_kronecker_mul_frameEncoder [NeZero q] {pos : ι → ℝ × ℝ} {Party : Type*}
    {l : List (Hole pos q Party)} {B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hB : ∀ t, Commute B (rawProd l t)) :
    ((1 : Matrix (TagSpace l) (TagSpace l) ℂ) ⊗ₖ B) * frameEncoder l = frameEncoder l * B :=
  one_kronecker_mul_stack hB

/-- If `B` passes through the encoding, `‖(1 ⊗ B) Ω_F - Ω_F‖ ≤ ‖B Ω - Ω‖`. -/
theorem norm_act_one_kronecker_refVec_sub_le [NeZero q] {pos : ι → ℝ × ℝ} {Party : Type*}
    (F : Frame pos q Party) {B : Matrix (ι → Fin q) (ι → Fin q) ℂ}
    (hB : ∀ t, Commute B (rawProd F.holes t)) (Ω : EuclideanSpace ℂ (ι → Fin q)) :
    ‖act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ B) (F.refVec Ω) - F.refVec Ω‖ ≤
      ‖act B Ω - Ω‖ := by
  have h : act ((1 : Matrix (TagSpace F.holes) (TagSpace F.holes) ℂ) ⊗ₖ B) (F.refVec Ω) -
      F.refVec Ω = act F.encoder (act B Ω - Ω) := by
    rw [Frame.refVec, ← act_mul, Frame.encoder, one_kronecker_mul_frameEncoder hB, act_mul,
      act_sub_right]
  rw [h]
  exact norm_act_le_of_norm_le_one F.norm_encoder_le_one _

end TNLean.PEPS.EncodedFrame
