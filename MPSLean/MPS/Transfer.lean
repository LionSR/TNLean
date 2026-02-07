import MPSLean.MPS.Defs

import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef

open scoped Matrix ComplexOrder

namespace MPSTensor

open scoped BigOperators

variable {d D : ℕ}

/-- The transfer operator / channel associated to an MPS tensor `A`:

$$E_A(X) = \sum_i A_i X A_i^{\dagger}.$$ -/
noncomputable def transferMap (A : MPSTensor d D) :
    Matrix (Fin D) (Fin D) ℂ →ₗ[ℂ] Matrix (Fin D) (Fin D) ℂ :=
  ∑ i : Fin d,
    (LinearMap.mulLeft ℂ (A i)).comp (LinearMap.mulRight ℂ (A i)ᴴ)

@[simp]
lemma transferMap_apply (A : MPSTensor d D) (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (d := d) (D := D) A X = ∑ i : Fin d, A i * X * (A i)ᴴ := by
  classical
  simp [transferMap, Matrix.mul_assoc]

/-- Gauge covariance of the transfer map. For `B i = X * A i * X⁻¹` we have

$$E_B(Y) = X\, E_A(X^{-1} Y (X^{-1})^{\dagger})\, X^{\dagger}.$$ -/
lemma transferMap_gauge_conj (A : MPSTensor d D) (X : GL (Fin D) ℂ)
    (Y : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (d := d) (D := D)
        (fun i : Fin d => (X : Matrix (Fin D) (Fin D) ℂ) * A i * (X⁻¹ : Matrix (Fin D) (Fin D) ℂ)) Y
      = (X : Matrix (Fin D) (Fin D) ℂ)
          * transferMap (d := d) (D := D) A
              ((X⁻¹ : Matrix (Fin D) (Fin D) ℂ) * Y * ((X⁻¹ : Matrix (Fin D) (Fin D) ℂ)ᴴ))
          * (X : Matrix (Fin D) (Fin D) ℂ)ᴴ := by
  classical
  -- Expand both sides into `Finset.univ.sum` and simplify term-by-term.
  simp [transferMap_apply, Finset.mul_sum, Finset.sum_mul, Matrix.mul_assoc]

/-- Positivity of the transfer map: it maps positive semidefinite matrices to positive
semidefinite matrices. -/
lemma transferMap_pos (A : MPSTensor d D) {X : Matrix (Fin D) (Fin D) ℂ}
    (hX : X.PosSemidef) : (transferMap (d := d) (D := D) A X).PosSemidef := by
  classical
  -- Each summand `A i * X * (A i)ᴴ` is positive semidefinite, and PSD is closed under finite sums.
  simpa [transferMap_apply] using
    (Matrix.posSemidef_sum (n := Fin D) (R := ℂ) (s := (Finset.univ : Finset (Fin d)))
      (x := fun i : Fin d => A i * X * (A i)ᴴ) (by
        intro i hi
        simpa [Matrix.mul_assoc] using
          (Matrix.PosSemidef.mul_mul_conjTranspose_same (hA := hX) (B := A i))))

end MPSTensor
