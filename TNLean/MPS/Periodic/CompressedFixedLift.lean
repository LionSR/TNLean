/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.KrausCornerCompression
import TNLean.MPS.Defs

/-!
# Lifting a compressed Kraus map to a reducing corner

If the range projection of an isometry commutes with every Kraus letter,
the ambient Kraus map preserves its matrix corner and agrees there with
the map of the compressed letters. This is the support-corner calculation
used for cyclic-sector fixed points in arXiv:1708.00029, Section 4.1.
-/

open scoped Matrix BigOperators

namespace MPSTensor

/-- A Kraus letter commutes with a support projection exactly as needed
to intertwine its compression with the ambient action. Source:
arXiv:1708.00029, Section 4.1. -/
theorem compressedLetter_lift_of_commute {d D n : ℕ}
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i)) (i : Fin d) :
    B i * V = V * (Vᴴ * B i * V) := by
  have hQV : (V * Vᴴ) * V = V := by
    rw [Matrix.mul_assoc, hV, Matrix.mul_one]
  calc
    B i * V = B i * ((V * Vᴴ) * V) := by rw [hQV]
    _ = ((V * Vᴴ) * B i) * V := by
      rw [← Matrix.mul_assoc, (hcomm i).eq, Matrix.mul_assoc]
    _ = V * (Vᴴ * B i * V) := by simp only [Matrix.mul_assoc]

/-- The ambient Kraus map of a supported matrix is the isometric lift of
the compressed Kraus map whenever the range projection reduces every
letter. Source: arXiv:1708.00029, Section 4.1. -/
theorem compressedKrausMap_lift_of_commute {d D n : ℕ}
    (B : Fin d → Matrix (Fin D) (Fin D) ℂ)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i))
    (σ : Matrix (Fin n) (Fin n) ℂ) :
    Kraus.map B (V * σ * Vᴴ) =
      V * Kraus.map (fun i => Vᴴ * B i * V) σ * Vᴴ := by
  classical
  simp only [Kraus.map_apply, Matrix.mul_sum, Matrix.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have hletter := compressedLetter_lift_of_commute B V hV hcomm i
  have hstar : Vᴴ * (B i)ᴴ = (Vᴴ * B i * V)ᴴ * Vᴴ := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.mul_assoc] using congrArg Matrix.conjTranspose hletter
  calc
    B i * (V * σ * Vᴴ) * (B i)ᴴ =
        (B i * V) * σ * (Vᴴ * (B i)ᴴ) := by
          simp only [Matrix.mul_assoc]
    _ = V * (Vᴴ * B i * V * σ * (Vᴴ * B i * V)ᴴ) * Vᴴ := by
          rw [hletter, hstar]
          simp only [Matrix.mul_assoc]

/-- Tensor-family form of the reducing-corner Kraus-map identity. The
compressed letters may be supplied independently once their conjugation
formula is known. Source: arXiv:1708.00029, Section 4.1. -/
theorem compressedTensorMap_lift_of_commute {d D n : ℕ}
    (B : MPSTensor d D) (C : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i))
    (hC : ∀ i, C i = Vᴴ * B i * V)
    (σ : Matrix (Fin n) (Fin n) ℂ) :
    Kraus.map B (V * σ * Vᴴ) = V * Kraus.map C σ * Vᴴ := by
  have hCeq : C = fun i => Vᴴ * B i * V := funext hC
  rw [hCeq]
  exact compressedKrausMap_lift_of_commute B V hV hcomm σ

/-- A fixed point of the compressed tensor map lifts to a fixed point of
the ambient map on the reducing corner. Source: arXiv:1708.00029,
Section 4.1. -/
theorem compressedTensorFixedPoint_lift_of_commute {d D n : ℕ}
    (B : MPSTensor d D) (C : MPSTensor d n)
    (V : Matrix (Fin D) (Fin n) ℂ)
    (hV : Vᴴ * V = 1)
    (hcomm : ∀ i, Commute (V * Vᴴ) (B i))
    (hC : ∀ i, C i = Vᴴ * B i * V)
    (σ : Matrix (Fin n) (Fin n) ℂ)
    (hfix : Kraus.map C σ = σ) :
    Kraus.map B (V * σ * Vᴴ) = V * σ * Vᴴ := by
  rw [compressedTensorMap_lift_of_commute B C V hV hcomm hC σ, hfix]

end MPSTensor
