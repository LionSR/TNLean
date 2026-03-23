import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Projective representations and concrete `U(1)`-valued 2-cocycles

This file introduces a concrete notion of projective representation for matrix-valued
virtual symmetries:

* `ScalarCocycle G` is a function `G × G → ℂˣ` (implemented as `Units ℂ`).
* `ProjectiveRepresentation ω` is a map `X : G → GL(D, ℂ)` satisfying
  `X g * X h = ω g h • X (g * h)` at the matrix level.
* `ProjectiveRepresentation.cocycle_of_assoc` derives the standard 2-cocycle identity
  from associativity of matrix multiplication.

This is the concrete multiplicative cocycle used in MPS/SPT arguments.
-/

open scoped Matrix

namespace TNLean
namespace Algebra

/-- A concrete multiplicative scalar 2-cochain on a group. -/
abbrev ScalarCocycle (G : Type*) := G → G → Units ℂ

section Group

variable {G : Type*} [Group G]
variable {D : ℕ}

/-- A matrix-valued projective representation with factor system `ω`. -/
structure ProjectiveRepresentation (ω : ScalarCocycle G) where
  /-- Virtual action on the bond space. -/
  X : G → GL (Fin D) ℂ
  /-- Multiplication law up to the scalar cocycle. -/
  map_mul' :
    ∀ g h : G,
      ((X g : Matrix (Fin D) (Fin D) ℂ) * (X h : Matrix (Fin D) (Fin D) ℂ)) =
        (ω g h : ℂ) • (X (g * h) : Matrix (Fin D) (Fin D) ℂ)

namespace ProjectiveRepresentation

variable {ω : ScalarCocycle G} (ρ : ProjectiveRepresentation (D := D) ω)

/-- The projective multiplication law, restated as a lemma. -/
lemma map_mul (g h : G) :
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) =
      (ω g h : ℂ) • (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) :=
  ρ.map_mul' g h

/-- Left-associated triple product in terms of the cocycle. -/
lemma mul_assoc_left_scalar (g h k : G) :
    (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
        (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) =
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
        (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by
  calc
    (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
        (ρ.X k : Matrix (Fin D) (Fin D) ℂ))
        = ((ω g h : ℂ) • (ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ)) *
            (ρ.X k : Matrix (Fin D) (Fin D) ℂ) := by rw [map_mul]
    _ = (ω g h : ℂ) •
          (((ρ.X (g * h) : Matrix (Fin D) (Fin D) ℂ) *
            (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) := by
            simp
    _ = (ω g h : ℂ) • ((ω (g * h) k : ℂ) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by simp [mul_smul]

/-- Right-associated triple product in terms of the cocycle. -/
lemma mul_assoc_right_scalar (g h k : G) :
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
        ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) =
      ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
        (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
  calc
    ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
        ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ)))
        = (ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((ω h k : ℂ) • (ρ.X (h * k) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = (ω h k : ℂ) •
          ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            (ρ.X (h * k) : Matrix (Fin D) (Fin D) ℂ)) := by
            simp
    _ = (ω h k : ℂ) • ((ω g (h * k) : ℂ) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ)) := by rw [map_mul]
    _ = ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
          simp [smul_smul, mul_comm]

/-- Scalar cancellation on an invertible matrix (requires a nonempty index set). -/
lemma smul_eq_smul_cancel {a b : ℂ} {M : Matrix (Fin D) (Fin D) ℂ}
    (hD : 0 < D) (hM : IsUnit M) (h : a • M = b • M) : a = b := by
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hD) with ⟨n, rfl⟩
  rcases hM with ⟨U, rfl⟩
  have h' : a • (1 : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ n)) ℂ) =
      b • (1 : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ n)) ℂ) := by
    simpa [smul_mul_assoc, Matrix.mul_smul, Matrix.mul_assoc] using
      congrArg (fun T => T * ((↑U⁻¹ : Matrix (Fin (Nat.succ n)) (Fin (Nat.succ n)) ℂ))) h
  have h00 := congrArg (fun T => T 0 0) h'
  simpa using h00

/-- Associativity forces the cocycle condition (for `D > 0`). -/
theorem cocycle_of_assoc (ρ : ProjectiveRepresentation (D := D) ω) (hD : 0 < D) (g h k : G) :
    (ω g h : ℂ) * (ω (g * h) k : ℂ) = (ω g (h * k) : ℂ) * (ω h k : ℂ) := by
  have hAssoc :
      (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
          (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) =
        ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
          ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) := by
    simp [Matrix.mul_assoc]
  have hLeft := ρ.mul_assoc_left_scalar g h k
  have hRight := ρ.mul_assoc_right_scalar g h k
  have hScalars :
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) =
        ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := by
    calc
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ)
          = (((ρ.X g : Matrix (Fin D) (Fin D) ℂ) * (ρ.X h : Matrix (Fin D) (Fin D) ℂ)) *
              (ρ.X k : Matrix (Fin D) (Fin D) ℂ)) := hLeft.symm
      _ = ((ρ.X g : Matrix (Fin D) (Fin D) ℂ) *
            ((ρ.X h : Matrix (Fin D) (Fin D) ℂ) * (ρ.X k : Matrix (Fin D) (Fin D) ℂ))) :=
            hAssoc
      _ = ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
            (ρ.X (g * (h * k)) : Matrix (Fin D) (Fin D) ℂ) := hRight
  have hScalars' :
      ((ω g h : ℂ) * (ω (g * h) k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) =
        ((ω g (h * k) : ℂ) * (ω h k : ℂ)) •
          (ρ.X ((g * h) * k) : Matrix (Fin D) (Fin D) ℂ) := by
    simpa [mul_assoc] using hScalars
  exact smul_eq_smul_cancel (D := D) hD (hM := by
      refine ⟨ρ.X ((g * h) * k), rfl⟩) hScalars'

end ProjectiveRepresentation

end Group

end Algebra
end TNLean
