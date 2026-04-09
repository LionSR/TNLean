import TNLean.MPS.Core.Transfer
import TNLean.Channel.Irreducible.Basic

/-!
# Orthogonal-projection invariance for transfer maps

This module provides a lightweight bridge from the Kraus-operator condition
`(1 - P) * A i * P = 0` to invariance of the compressed algebra under the
transfer map of an MPS tensor.
-/

open scoped Matrix ComplexOrder BigOperators
open Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If each Kraus operator `A i` is block-upper-triangular with respect to an
orthogonal projection `P`, then the transfer map preserves the compression
`P M_D P`. -/
lemma lowerZero_implies_invariance
    (A : MPSTensor d D) (P : Matrix (Fin D) (Fin D) ℂ)
    (hProj : IsOrthogonalProjection P)
    (hLower : ∀ i : Fin d, (1 - P) * A i * P = 0) :
    ∀ X, P * transferMap (d := d) (D := D) A (P * X * P) * P =
      transferMap (d := d) (D := D) A (P * X * P) := by
  intro X
  have hPH : Pᴴ = P := hProj.1.eq
  have hAP : ∀ i : Fin d, A i * P = P * A i * P := by
    intro i
    have hkey : A i * P - P * A i * P = 0 := by
      have h : (1 - P) * A i * P = A i * P - P * A i * P := by
        noncomm_ring
      rw [← h]
      exact hLower i
    exact eq_of_sub_eq_zero hkey
  have hPAd : ∀ i : Fin d, P * (A i)ᴴ = P * (A i)ᴴ * P := by
    intro i
    have hct : P * (A i)ᴴ * (1 - P) = 0 := by
      have h := congrArg Matrix.conjTranspose (hLower i)
      simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
        Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH] at h
      simpa [Matrix.mul_assoc] using h
    have hkey : P * (A i)ᴴ - P * (A i)ᴴ * P = 0 := by
      have h : P * (A i)ᴴ * (1 - P) = P * (A i)ᴴ - P * (A i)ᴴ * P := by
        noncomm_ring
      rwa [← h]
    exact eq_of_sub_eq_zero hkey
  simp only [transferMap_apply]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  have h1 : A i * (P * X * P) * (A i)ᴴ =
      (A i * P) * X * (P * (A i)ᴴ) := by
    noncomm_ring
  have h2 : (A i * P) * X * (P * (A i)ᴴ) =
      (P * A i * P) * X * (P * (A i)ᴴ * P) := by
    conv_lhs => rw [hAP i, hPAd i]
  have h3 : (P * A i * P) * X * (P * (A i)ᴴ * P) =
      P * (A i * (P * X * P) * (A i)ᴴ) * P := by
    noncomm_ring
  exact ((h1.trans h2).trans h3).symm

end MPSTensor
