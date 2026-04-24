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
- `povmDiagonal_inv`: the inverse of the scalar block-diagonal matrix is again
  block-diagonal with pointwise-inverted entries.
- `povm_resolvent_compression_le`: the resolvent Hansen-compression bound
  combining the dilation isometry with `inverse_compression_le`.

## Status

These lemmas formalize the compression / finite-POVM half of the direct proof
route for the concave real-power Jensen inequality, up to the resolvent
Hansen-compression endpoint. The remaining unfinished step is the Löwner
integral representation of `rpow` (blocked on Mathlib
`CFC.Rpow.IntegralRepresentation`), which is required to lift the resolvent
bound to the concave real-power Jensen inequality.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

noncomputable section

attribute [local instance] Matrix.instL2OpNormedAddCommGroup
attribute [local instance] Matrix.instL2OpNormedRing
attribute [local instance] Matrix.instL2OpNormedAlgebra

namespace Matrix.PosDef

section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
variable {Y : Matrix n n ℂ} {W : Matrix n m ℂ}

/-- The Schur-complement compression bound used in the Hansen--Pedersen route to
operator Jensen: compressing a positive-definite matrix by an isometry makes the
inverse larger in the Loewner order than the compression of the inverse. -/
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
    exact (Matrix.PosDef.fromBlocks₁₁ (B := W) (D := Wᴴ * Y * W) hY.inv).2 <| by
      simpa using (Matrix.PosSemidef.zero : (0 : Matrix m m ℂ).PosSemidef)
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

end Matrix.PosDef

namespace TNLean.OperatorJensen

section POVM

variable {D : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

local notation "MatD" => Matrix (Fin D) (Fin D) ℂ
local notation "AuxIx" => ((ι × Fin D) ⊕ Fin D)
local notation "IsoMat" => Matrix AuxIx (Fin D) ℂ
local notation "AuxMat" => Matrix AuxIx AuxIx ℂ

/-- The block matrix whose rows are the adjoints of a finite family `C i`
together with a defect block `S`; this is the standard isometric dilation used
to encode a finite POVM. -/
def povmIsometry (C : ι → MatD) (S : MatD) : IsoMat
  | Sum.inl ⟨i, p⟩, q => star (C i q p)
  | Sum.inr p, q => star (S q p)

/-- The scalar block-diagonal matrix whose `ι`-blocks carry the weights `w i`
and whose defect block carries the scalar `t`. -/
def povmDiagonal (w : ι → ℝ) (t : ℝ) : AuxMat :=
  Matrix.diagonal fun
    | Sum.inl ⟨i, _⟩ => ((w i : ℝ) : ℂ)
    | Sum.inr _ => (t : ℂ)

omit [DecidableEq ι] in
/-- If the defect block closes the finite POVM relation
`∑ i, C i * (C i)ᴴ + S * Sᴴ = 1`, then the dilation matrix `povmIsometry C S`
is an isometry. -/
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

/-- Compressing the scalar block-diagonal matrix `povmDiagonal w t` by the POVM
dilation produces the weighted sum of the POVM blocks and the defect block. -/
lemma povmIsometry_compress_diagonal
    {C : ι → MatD} {S : MatD} (w : ι → ℝ) (t : ℝ) :
    (povmIsometry C S)ᴴ * povmDiagonal w t * povmIsometry C S =
      (∑ i, w i • (C i * (C i)ᴴ)) + t • (S * Sᴴ) := by
  ext r s
  have hMain :
      ∑ x, ∑ x_1, C x r x_1 * ↑(w x) * (starRingEnd ℂ) (C x s x_1) =
        ∑ x, ↑(w x) * ∑ x_1, C x r x_1 * (starRingEnd ℂ) (C x s x_1) := by
    refine Finset.sum_congr rfl ?_
    intro x _
    calc
      ∑ x_1, C x r x_1 * ↑(w x) * (starRingEnd ℂ) (C x s x_1)
          = ∑ x_1, ↑(w x) * (C x r x_1 * (starRingEnd ℂ) (C x s x_1)) := by
              refine Finset.sum_congr rfl ?_
              intro x_1 _
              ring
      _ = ↑(w x) * ∑ x_1, C x r x_1 * (starRingEnd ℂ) (C x s x_1) := by
            simpa using
              (Finset.mul_sum
                (s := Finset.univ)
                (f := fun x_1 : Fin D => C x r x_1 * (starRingEnd ℂ) (C x s x_1))
                (a := (↑(w x) : ℂ))).symm
  have hDefect :
      ∑ x, S r x * ↑t * (starRingEnd ℂ) (S s x) =
        ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) := by
    calc
      ∑ x, S r x * ↑t * (starRingEnd ℂ) (S s x)
          = ∑ x, ↑t * (S r x * (starRingEnd ℂ) (S s x)) := by
              refine Finset.sum_congr rfl ?_
              intro x _
              ring
      _ = ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) := by
            simpa using
              (Finset.mul_sum
                (s := Finset.univ)
                (f := fun x : Fin D => S r x * (starRingEnd ℂ) (S s x))
                (a := (↑t : ℂ))).symm
  suffices
      ∑ x, ∑ x_1, C x r x_1 * ↑(w x) * (starRingEnd ℂ) (C x s x_1) +
          ∑ x, S r x * ↑t * (starRingEnd ℂ) (S s x) =
        ∑ x, w x • ∑ j, C x r j * (C x)ᴴ j s + ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) by
    simpa [povmIsometry, povmDiagonal, Matrix.mul_apply, Matrix.diagonal_apply,
      Fintype.sum_sum_type, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
      Matrix.sum_apply, Matrix.smul_apply] using this
  calc
    ∑ x, ∑ x_1, C x r x_1 * ↑(w x) * (starRingEnd ℂ) (C x s x_1) +
        ∑ x, S r x * ↑t * (starRingEnd ℂ) (S s x)
      = (∑ x, ↑(w x) * ∑ x_1, C x r x_1 * (starRingEnd ℂ) (C x s x_1)) +
          ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) := by
            rw [hMain, hDefect]
    _ = ∑ x, w x • ∑ j, C x r j * (C x)ᴴ j s + ↑t * ∑ x, S r x * (starRingEnd ℂ) (S s x) := by
          simp [Matrix.conjTranspose_apply]

omit [DecidableEq ι] in
/-- Rewriting the defect relation gives the more symmetric identity
`∑ i, C i * (C i)ᴴ + S * Sᴴ = 1`. -/
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
/-- If every weight on the diagonal blocks is strictly positive, then the scalar
block-diagonal matrix `povmDiagonal w t` is positive definite. -/
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

/-- Under strict positivity of every weight, the inverse of the scalar
block-diagonal matrix `povmDiagonal w t` is obtained by inverting each scalar
entry pointwise. -/
lemma povmDiagonal_inv (w : ι → ℝ) {t : ℝ}
    (ht : 0 < t) (hw : ∀ i, 0 < w i) :
    (povmDiagonal (D := D) w t)⁻¹ =
      povmDiagonal (D := D) (fun i => (w i)⁻¹) t⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [povmDiagonal, povmDiagonal, Matrix.diagonal_mul_diagonal,
      show (1 : AuxMat) = Matrix.diagonal (fun _ : AuxIx => (1 : ℂ)) from
        Matrix.diagonal_one.symm]
  congr 1
  funext a
  cases a with
  | inl ip =>
      change ((w ip.1 : ℝ) : ℂ) * (((w ip.1)⁻¹ : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt (hw ip.1)),
          Complex.ofReal_one]
  | inr _ =>
      change ((t : ℝ) : ℂ) * ((t⁻¹ : ℝ) : ℂ) = 1
      rw [← Complex.ofReal_mul, mul_inv_cancel₀ (ne_of_gt ht),
          Complex.ofReal_one]

omit [DecidableEq ι] in
/-- **Resolvent Hansen-compression bound.** For a finite PSD family
`C i * (C i)ᴴ` that, together with the defect block `S * Sᴴ`, sums to the
identity, any choice of strictly positive weights `w i` and `t` yields the
Loewner inequality

  `(∑ i, w i • (C i * (C i)ᴴ) + t • (S * Sᴴ))⁻¹ ≤`
  `  ∑ i, (w i)⁻¹ • (C i * (C i)ᴴ) + t⁻¹ • (S * Sᴴ)`.

This is the explicit resolvent form of the POVM compression inequality used as
an intermediate step toward the Hansen--Pedersen operator Jensen inequality.

It combines four ingredients:

* `povmIsometry_star_mul` — the POVM dilation is an isometry;
* `povmIsometry_compress_diagonal` — compression of `povmDiagonal w t` by the
  dilation recovers the weighted POVM sum on both sides;
* `povmDiagonal_inv` — the inverse of `povmDiagonal w t` is
  `povmDiagonal w⁻¹ t⁻¹`;
* `Matrix.PosDef.inverse_compression_le` — inverse-of-compression is
  pointwise below compression-of-inverse. -/
lemma povm_resolvent_compression_le
    {C : ι → MatD} {S : MatD}
    (hdef : S * Sᴴ = 1 - ∑ i, C i * (C i)ᴴ)
    {w : ι → ℝ} {t : ℝ} (ht : 0 < t) (hw : ∀ i, 0 < w i) :
    ((∑ i, w i • (C i * (C i)ᴴ)) + t • (S * Sᴴ))⁻¹ ≤
      (∑ i, (w i)⁻¹ • (C i * (C i)ᴴ)) + t⁻¹ • (S * Sᴴ) := by
  classical
  set W : IsoMat := povmIsometry C S with hW
  have hWiso : Wᴴ * W = (1 : MatD) := povmIsometry_star_mul (C := C) (S := S) hdef
  have hYpd : Matrix.PosDef (povmDiagonal (D := D) w t) :=
    povmDiagonal_posDef (ι := ι) (D := D) w ht hw
  have hcompress :
      Wᴴ * povmDiagonal (D := D) w t * W =
        (∑ i, w i • (C i * (C i)ᴴ)) + t • (S * Sᴴ) := by
    simpa [hW] using povmIsometry_compress_diagonal (C := C) (S := S) w t
  have hcompress_inv :
      Wᴴ * povmDiagonal (D := D) (fun i => (w i)⁻¹) t⁻¹ * W =
        (∑ i, (w i)⁻¹ • (C i * (C i)ᴴ)) + t⁻¹ • (S * Sᴴ) := by
    simpa [hW] using
      povmIsometry_compress_diagonal (C := C) (S := S) (fun i => (w i)⁻¹) t⁻¹
  have hbound :
      (Wᴴ * povmDiagonal (D := D) w t * W)⁻¹ ≤
        Wᴴ * (povmDiagonal (D := D) w t)⁻¹ * W :=
    Matrix.PosDef.inverse_compression_le hYpd hWiso
  rw [povmDiagonal_inv (ι := ι) (D := D) w ht hw] at hbound
  rw [hcompress, hcompress_inv] at hbound
  exact hbound

end POVM

end TNLean.OperatorJensen
