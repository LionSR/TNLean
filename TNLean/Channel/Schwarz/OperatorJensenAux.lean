/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Finite-POVM compression lemmas for operator Jensen

This file records algebraic lemmas for the finite-POVM / compression route to
operator Jensen inequalities. The main target is the concave real-power case in
Wolf Corollary 5.2, but the final Löwner-integral packaging is still absent.

## Main statements

- `inverse_compression_le`: inverse of a compression is bounded by the
  compression of the inverse.
- `povmIsometry`: the isometric dilation attached to a finite PSD family and its
  defect block.
- `povmIsometry_star_mul`: the dilation is an isometry.
- `povmIsometry_compress_diagonal`: compressing a scalar block-diagonal matrix
  yields the expected weighted POVM sum.
- `povm_sum_add_defect`: the POVM family plus defect block sums to the identity.
- `povmDiagonal_posDef`: positivity of the scalar block-diagonal matrix used in
  the resolvent step.

## Status

These lemmas formalize the compression / finite-POVM half of the direct proof
route for the concave real-power Jensen inequality. The remaining unfinished
step is the explicit diagonal-inverse rewrite together with the final algebraic
rearrangement to the resolvent inequality.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {Y : Matrix n n ℂ} {W : Matrix n m ℂ}

lemma inverse_compression_le
    (hY : Y.PosDef) (hW : Wᴴ * W = (1 : Matrix m m ℂ)) :
    (Wᴴ * Y * W)⁻¹ ≤ Wᴴ * Y⁻¹ * W := by
  have hWinj : Function.Injective W.mulVec := by
    intro x y hxy
    have hxy' := congrArg (fun z : n → ℂ => Wᴴ *ᵥ z) hxy
    simpa [Matrix.mulVec_mulVec, hW] using hxy'
  have hD : (Wᴴ * Y * W).PosDef :=
    hY.conjTranspose_mul_mul_same hWinj
  letI : Invertible Y := hY.isUnit.invertible
  letI : Invertible (Wᴴ * Y * W) := hD.isUnit.invertible
  have hBlock : (Matrix.fromBlocks Y⁻¹ W Wᴴ (Wᴴ * Y * W)).PosSemidef := by
    have hZero : ((Wᴴ * Y * W) - Wᴴ * (Y⁻¹)⁻¹ * W).PosSemidef := by
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix m m ℂ).PosSemidef)
    exact (Matrix.PosDef.fromBlocks₁₁ (B := W) (D := Wᴴ * Y * W) hY.inv).2 hZero
  have hSchur : (Y⁻¹ - W * (Wᴴ * Y * W)⁻¹ * Wᴴ).PosSemidef := by
    exact (Matrix.PosDef.fromBlocks₂₂ (A := Y⁻¹) (B := W) hD).1 hBlock
  rw [Matrix.le_iff]
  have hConj : (Wᴴ * (Y⁻¹ - W * (Wᴴ * Y * W)⁻¹ * Wᴴ) * W).PosSemidef :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hSchur W
  have hEq :
      Wᴴ * (Y⁻¹ - W * (Wᴴ * Y * W)⁻¹ * Wᴴ) * W =
        Wᴴ * Y⁻¹ * W - (Wᴴ * Y * W)⁻¹ := by
    calc
      Wᴴ * (Y⁻¹ - W * (Wᴴ * Y * W)⁻¹ * Wᴴ) * W
          = Wᴴ * Y⁻¹ * W - Wᴴ * W * (Wᴴ * Y * W)⁻¹ * (Wᴴ * W) := by
              simp [sub_eq_add_neg, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = Wᴴ * Y⁻¹ * W - (Wᴴ * Y * W)⁻¹ := by
            simp [Matrix.mul_assoc, hW]
  simpa [hEq] using hConj

end

section POVM

variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ
local notation "AuxIx" => ((ι × Fin D) ⊕ Fin D)
local notation "IsoMat" => Matrix AuxIx (Fin D) ℂ
local notation "AuxMat" => Matrix AuxIx AuxIx ℂ

noncomputable def povmIsometry (C : ι → MatD) (S : MatD) : IsoMat
  | Sum.inl ⟨i, p⟩, q => star (C i q p)
  | Sum.inr p, q => star (S q p)

noncomputable def povmDiagonal (w : ι → ℝ) (t : ℝ) : AuxMat :=
  Matrix.diagonal fun
    | Sum.inl ⟨i, _⟩ => ((w i : ℝ) : ℂ)
    | Sum.inr _ => (t : ℂ)

omit [DecidableEq ι] in
lemma povmIsometry_star_mul
    {C : ι → MatD} {S : MatD}
    (hdef : S * Sᴴ = 1 - ∑ i, C i * (C i)ᴴ) :
    (povmIsometry C S)ᴴ * povmIsometry C S = (1 : MatD) := by
  ext r s
  rw [Matrix.mul_apply, Fintype.sum_sum_type]
  calc
    (∑ x : ι × Fin D,
        (povmIsometry C S)ᴴ r (Sum.inl x) * povmIsometry C S (Sum.inl x) s) +
        ∑ x : Fin D, (povmIsometry C S)ᴴ r (Sum.inr x) * povmIsometry C S (Sum.inr x) s
      = (∑ i, (C i * (C i)ᴴ) r s) + (S * Sᴴ) r s := by
          simp [povmIsometry, Matrix.mul_apply, Matrix.conjTranspose_apply,
            Fintype.sum_prod_type]
    _ = (1 : MatD) r s := by
      have hdef' : (S * Sᴴ) r s = (1 : MatD) r s - ∑ i, (C i * (C i)ᴴ) r s := by
        simpa [Matrix.sub_apply, Matrix.sum_apply] using congrArg (fun M : MatD => M r s) hdef
      have hsum :
          (∑ i, (C i * (C i)ᴴ) r s) + (S * Sᴴ) r s =
            (∑ i, (C i * (C i)ᴴ) r s) +
              ((1 : MatD) r s - ∑ i, (C i * (C i)ᴴ) r s) :=
        congrArg (fun z : ℂ => (∑ i, (C i * (C i)ᴴ) r s) + z) hdef'
      rw [hsum]
      ring

lemma povmIsometry_compress_diagonal
    {C : ι → MatD} {S : MatD} (w : ι → ℝ) (t : ℝ) :
    (povmIsometry C S)ᴴ * povmDiagonal w t * povmIsometry C S =
      (∑ i, w i • (C i * (C i)ᴴ)) + t • (S * Sᴴ) := by
  ext r s
  simp [povmIsometry, povmDiagonal, Matrix.mul_apply, Matrix.diagonal_apply,
    Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    mul_comm, mul_left_comm, mul_assoc]
  rw [Matrix.sum_apply]
  simp [Matrix.smul_apply, Matrix.mul_apply]
  have hMain :
      ∑ x, ∑ x_1, C x r x_1 * (↑(w x) * (starRingEnd ℂ) (C x s x_1)) =
        ∑ x, ↑(w x) * ∑ x_1, C x r x_1 * (starRingEnd ℂ) (C x s x_1) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hterm :
        ∀ x_1 : Fin D,
          C x r x_1 * (↑(w x) * (starRingEnd ℂ) (C x s x_1)) =
            ↑(w x) * (C x r x_1 * (starRingEnd ℂ) (C x s x_1)) := by
      intro x_1
      ring
    simp_rw [hterm]
    rw [Finset.mul_sum]
  have hDefect :
      ∑ x, S r x * (↑t * (starRingEnd ℂ) (S s x)) =
        ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) := by
    have hterm :
        ∀ x : Fin D,
          S r x * (↑t * (starRingEnd ℂ) (S s x)) =
            ↑t * (S r x * (starRingEnd ℂ) (S s x)) := by
      intro x
      ring
    simp_rw [hterm]
    rw [Finset.mul_sum]
  rw [hMain, hDefect]

omit [DecidableEq ι] in
lemma povm_sum_add_defect
    {C : ι → MatD} {S : MatD}
    (hdef : S * Sᴴ = 1 - ∑ i, C i * (C i)ᴴ) :
    (∑ i, C i * (C i)ᴴ) + S * Sᴴ = (1 : MatD) := by
  ext r s
  have hdef' : (S * Sᴴ) r s = (1 : MatD) r s - ∑ i, (C i * (C i)ᴴ) r s := by
    simpa [Matrix.sub_apply, Matrix.sum_apply] using congrArg (fun M : MatD => M r s) hdef
  calc
    ((∑ i, C i * (C i)ᴴ) + S * Sᴴ) r s
        = (∑ i, (C i * (C i)ᴴ) r s) + (S * Sᴴ) r s := by
            simp [Matrix.add_apply, Matrix.sum_apply]
    _ = (∑ i, (C i * (C i)ᴴ) r s) + ((1 : MatD) r s - ∑ i, (C i * (C i)ᴴ) r s) := by
          rw [hdef']
    _ = (1 : MatD) r s := by ring

omit [Fintype ι] in
lemma povmDiagonal_posDef (w : ι → ℝ) {t : ℝ}
    (ht : 0 < t) (hw : ∀ i, 0 < w i) :
    Matrix.PosDef (povmDiagonal (D := D) w t) := by
  let d : AuxIx → ℂ := fun a =>
    match a with
    | Sum.inl ip => ((w ip.1 : ℝ) : ℂ)
    | Sum.inr _ => (t : ℂ)
  have hdiag : (Matrix.diagonal d).PosDef := by
    refine Matrix.PosDef.diagonal ?_
    intro a
    cases a with
    | inl ip =>
        rcases ip with ⟨i, p⟩
        simpa [d, Complex.lt_def] using hw i
    | inr p =>
        simpa [d, Complex.lt_def] using ht
  simpa [povmDiagonal, d] using hdiag

end POVM
