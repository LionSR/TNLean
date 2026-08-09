/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.SimpleBlocking

/-!
# Simple contractions with supplied fixed witnesses

This file transports the existential witnesses of an MPU-simple tensor to the
separately supplied rank-one projector from a normalized transfer power.

The result follows the insertion argument of arXiv:1703.09188: the
existential simple witnesses first show that every pair of double-layer letters
is unchanged by inserting a positive power of the normalized diagonal.  Only
then is that power replaced by the supplied rank-one matrix.
-/

open scoped Matrix BigOperators
open Matrix

namespace MPOTensor

variable {d D : ℕ}

private theorem normalizedDiagonal_eq_smul_sum_diagonal
    (W : MPOTensor d D) :
    normalizedDiagonal W = ((d : ℂ)⁻¹) • ∑ q : Fin d, W q q := by
  classical
  simp only [normalizedDiagonal, contractPhysical, Matrix.one_apply, ite_smul,
    one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem simple_letter_mul_normalizedDiagonal_mul_letter
    [NeZero d] {W : MPOTensor d D} (hW : IsMPUSimple W)
    (i j k l : Fin d) :
    doubleLayerTensor W i j * normalizedDiagonal (doubleLayerTensor W) *
        doubleLayerTensor W k l =
      doubleLayerTensor W i j * doubleLayerTensor W k l := by
  classical
  obtain ⟨a, b, h₁, h₂⟩ := hW
  let R := Matrix.vecMulVec b a
  have hsandwich (q : Fin d) :
      R * doubleLayerTensor W q q * R = R := by
    have h := Matrix.vecMulVec_mul_mul_vecMulVec_eq_trace_smul
      b a (doubleLayerTensor W q q)
    have htrace : Matrix.trace (doubleLayerTensor W q q * R) = 1 := by
      change Matrix.trace (doubleLayerTensor W q q * Matrix.vecMulVec b a) = 1
      rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]
      simpa using h₁ q q
    simpa only [R, htrace, one_smul] using h
  rw [normalizedDiagonal_eq_smul_sum_diagonal]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Finset.mul_sum, Finset.sum_mul]
  have hterm (q : Fin d) :
      doubleLayerTensor W i j * doubleLayerTensor W q q *
          doubleLayerTensor W k l =
        doubleLayerTensor W i j * R * doubleLayerTensor W k l := by
    calc
      _ = (doubleLayerTensor W i j * R * doubleLayerTensor W q q) *
          doubleLayerTensor W k l := by rw [← h₂ i j q q]
      _ = doubleLayerTensor W i j * R *
          (doubleLayerTensor W q q * R * doubleLayerTensor W k l) := by
            rw [← h₂ q q k l]; simp [Matrix.mul_assoc]
      _ = doubleLayerTensor W i j * (R * doubleLayerTensor W q q * R) *
          doubleLayerTensor W k l := by simp [Matrix.mul_assoc]
      _ = doubleLayerTensor W i j * R * doubleLayerTensor W k l := by rw [hsandwich]
  simp_rw [hterm]
  have hd : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne d)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ext x y
  simp only [Matrix.smul_apply]
  change (d : ℂ)⁻¹ * ((d : ℕ) •
    (doubleLayerTensor W i j * R * doubleLayerTensor W k l) x y) = _
  rw [nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  exact congrArg (fun M ↦ M x y) (h₂ i j k l).symm

/-- If a simple tensor has a positive normalized-diagonal power equal to a
supplied rank-one matrix, then `simple2` holds with exactly those supplied
witnesses.

The proof inserts the normalized diagonal between two letters using the
existing existential `simple1` and `simple2` witnesses, iterates that insertion,
and only then substitutes the supplied transfer power.  No uniqueness of
rank-one witnesses is used.

Source: arXiv:1703.09188, equations `simple1`, `simple2`, and `Erightleft`,
lines 274--280, 356--374, and 429--438. -/
theorem IsMPUSimple.simple2_of_normalizedDiagonal_pow_eq_vecMulVec
    [NeZero d] {W : MPOTensor d D} (hW : IsMPUSimple W)
    (ρ Φ : Fin (D * D) → ℂ) (J : ℕ) (hJ : 0 < J)
    (hpower : normalizedDiagonal (doubleLayerTensor W) ^ J =
      Matrix.vecMulVec ρ Φ) :
    ∀ i j k l : Fin d,
      doubleLayerTensor W i j * doubleLayerTensor W k l =
        doubleLayerTensor W i j * Matrix.vecMulVec ρ Φ *
          doubleLayerTensor W k l := by
  intro i j k l
  let E := normalizedDiagonal (doubleLayerTensor W)
  have hinsert : doubleLayerTensor W i j * E * doubleLayerTensor W k l =
      doubleLayerTensor W i j * doubleLayerTensor W k l :=
    simple_letter_mul_normalizedDiagonal_mul_letter hW i j k l
  have hE : E = ((d : ℂ)⁻¹) • ∑ q : Fin d, doubleLayerTensor W q q :=
    normalizedDiagonal_eq_smul_sum_diagonal (doubleLayerTensor W)
  have hleftIdem : doubleLayerTensor W i j * E * E =
      doubleLayerTensor W i j * E := by
    calc
      doubleLayerTensor W i j * E * E =
          doubleLayerTensor W i j * E *
            (((d : ℂ)⁻¹) • ∑ q : Fin d, doubleLayerTensor W q q) := by rw [hE]
      _ = ((d : ℂ)⁻¹) • ∑ q : Fin d,
            doubleLayerTensor W i j * E * doubleLayerTensor W q q := by
              rw [Matrix.mul_smul, Finset.mul_sum]
      _ = ((d : ℂ)⁻¹) • ∑ q : Fin d,
            doubleLayerTensor W i j * doubleLayerTensor W q q := by
              congr 1
              apply Finset.sum_congr rfl
              intro q _
              exact simple_letter_mul_normalizedDiagonal_mul_letter hW i j q q
      _ = doubleLayerTensor W i j * E := by
              rw [hE, Matrix.mul_smul, Finset.mul_sum]
  have hleftPow : ∀ N : ℕ, 0 < N →
      doubleLayerTensor W i j * E ^ N = doubleLayerTensor W i j * E := by
    intro N hN
    obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    clear hN
    induction N with
    | zero => simp
    | succ N ih =>
        rw [pow_succ, ← Matrix.mul_assoc, ih, hleftIdem]
  calc
    doubleLayerTensor W i j * doubleLayerTensor W k l =
        doubleLayerTensor W i j * E ^ J * doubleLayerTensor W k l := by
          rw [hleftPow J hJ, hinsert]
    _ = doubleLayerTensor W i j * Matrix.vecMulVec ρ Φ *
        doubleLayerTensor W k l := by rw [hpower]

end MPOTensor
