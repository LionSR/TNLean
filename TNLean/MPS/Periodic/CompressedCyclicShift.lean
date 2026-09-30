/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Channel.KrausCornerCompression

/-!
# Cyclic projections under compression

A cyclic projection supported on a reducing orbit sector retains its
adjoint-transfer shift after isometric compression. This is the local
calculation used to recover the exact period of the compressed orbit tensor.

Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806.
-/

open scoped Matrix

namespace MPSTensor

/-- An ambient adjoint-transfer shift between matrices supported on one
reducing sector descends to the compressed tensor. Source:
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 765--806. -/
theorem compressed_adjointTransferMap_shift
    {d D n : ℕ} (B : MPSTensor d D) (C : MPSTensor d n)
    (Q X Y : MatrixAlg D) (V : Matrix (Fin D) (Fin n) ℂ)
    (hVrange : V * Vᴴ = Q)
    (hC : ∀ i, C i = Vᴴ * B i * V)
    (hX : Q * X * Q = X)
    (hshift : Kraus.map (fun i => (B i)ᴴ) X = Y) :
    Kraus.map (fun i => (C i)ᴴ) (Vᴴ * X * V) = Vᴴ * Y * V := by
  have hCadj : ∀ i, (C i)ᴴ =
      Vᴴ * (B i)ᴴ * V := by
    intro i
    rw [hC i]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  rw [Kraus.map_compressed_eq_conj (fun i => (B i)ᴴ)
    (fun i => (C i)ᴴ) V hCadj]
  have hVX : V * (Vᴴ * X * V) * Vᴴ = X := by
    calc
      V * (Vᴴ * X * V) * Vᴴ = (V * Vᴴ) * X * (V * Vᴴ) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hVrange, hX]
  rw [hVX, hshift]

end MPSTensor
