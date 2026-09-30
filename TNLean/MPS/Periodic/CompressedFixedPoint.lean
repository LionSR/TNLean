/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Defs
import QICLean.Channel.KrausCornerCompression
import Mathlib.Analysis.Matrix.PosDef

/-!
# Faithful fixed points on reducing tensor sectors

An isometric compression to a reducing sector preserves a faithful stationary
matrix. This applies to the orbit sectors of a blocked periodic tensor in
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 432–459.
-/

open scoped Matrix ComplexOrder

namespace MPSTensor

/-- A reducing isometric compression of a tensor inherits its faithful fixed
point. The compressed matrix need not have trace one.
Source: arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 432–459. -/
theorem compressed_posDef_fixedPoint {d D n : ℕ}
    (A : MPSTensor d D) (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (A i))
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρ : ρ.PosDef)
    (hfix : Kraus.map A ρ = ρ) :
    (Vᴴ * ρ * V).PosDef ∧
      Kraus.map (fun i => Vᴴ * A i * V) (Vᴴ * ρ * V) = Vᴴ * ρ * V := by
  constructor
  · apply hρ.conjTranspose_mul_mul_same
    intro x y hxy
    have h := congrArg (fun z => Vᴴ *ᵥ z) hxy
    simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using h
  · rw [Kraus.map_compressed_eq_conj A _ V (fun _ => rfl)]
    have hstar (i : Fin d) : (A i)ᴴ * (V * Vᴴ) = (V * Vᴴ) * (A i)ᴴ := by
      simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using
        congrArg Matrix.conjTranspose (hcomm i).eq
    have hmap : Kraus.map A ((V * Vᴴ) * ρ * (V * Vᴴ)) =
        (V * Vᴴ) * Kraus.map A ρ * (V * Vᴴ) := by
      simp only [Kraus.map_apply, Matrix.mul_sum, Matrix.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      calc
        A i * ((V * Vᴴ) * ρ * (V * Vᴴ)) * (A i)ᴴ =
            (A i * (V * Vᴴ)) * ρ * ((V * Vᴴ) * (A i)ᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = ((V * Vᴴ) * A i) * ρ * ((A i)ᴴ * (V * Vᴴ)) := by
          rw [← (hcomm i).eq, ← hstar i]
        _ = _ := by simp only [Matrix.mul_assoc]
    rw [show V * (Vᴴ * ρ * V) * Vᴴ = (V * Vᴴ) * ρ * (V * Vᴴ) by
      simp only [Matrix.mul_assoc], hmap, hfix]
    simp only [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV,
      Matrix.one_mul, Matrix.mul_one]

end MPSTensor
