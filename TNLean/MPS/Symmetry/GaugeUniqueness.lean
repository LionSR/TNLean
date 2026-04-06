import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Chain.OneSidedInverse
import TNLean.Algebra.ScalarCommutant

/-!
# Gauge uniqueness for injective MPS tensors

If two invertible gauges `X` and `Y` both map an injective tensor `A` to the same
`B`, then `Y` is a nonzero scalar multiple of `X`.

This is the scalar-commutant input needed to make the symmetry gauge
well-defined up to phase.
-/

open scoped Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- If two gauges send the same injective tensor `A` to the same tensor `B`,
then they differ by a nonzero scalar. -/
theorem gauge_unique_up_to_scalar {A B : MPSTensor d D} (hA : IsInjective A)
    {X Y : GL (Fin D) ℂ}
    (hX : ∀ i, B i = X * A i * X⁻¹)
    (hY : ∀ i, B i = Y * A i * Y⁻¹) :
    ∃ u : Units ℂ,
      (Y : Matrix (Fin D) (Fin D) ℂ) = (u : ℂ) • (X : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  cases D with
  | zero =>
      refine ⟨1, ?_⟩
      exact Subsingleton.elim _ _
  | succ D' =>
      let Z : GL (Fin (Nat.succ D')) ℂ := X⁻¹ * Y
      have hcommA : ∀ i : Fin d,
          (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A i
            = A i * (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
        intro i
        have hXY :
            (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A i *
              ((X⁻¹ : GL (Fin (Nat.succ D')) ℂ) : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
              =
            (Y : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * A i *
              ((Y⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
          rw [← hX i, hY i]
        have hXY' := congrArg
          (fun M : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ =>
            ((X⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) * M *
              (Y : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) hXY
        simpa [Z, Matrix.mul_assoc] using hXY'.symm
      have hscalar := Matrix.isScalar_of_commute_span_eq_top
        (Z := (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ))
        hA.span_eq_top (fun M hM => by
          rcases hM with ⟨i, rfl⟩
          exact hcommA i)
      rcases hscalar with ⟨c, hc⟩
      have hc_ne : c ≠ 0 := by
        intro hc0
        have hZ0 : (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) = 0 := by
          calc
            (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
                = Matrix.scalar (Fin (Nat.succ D')) c := hc
            _ = 0 := by
                ext i j
                simp [hc0]
        have hmul :
            (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
                (((Z⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                  Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) = 1 := by
          simp
        rw [hZ0, zero_mul] at hmul
        exact
          (one_ne_zero :
            (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) ≠ 0) hmul.symm
      refine ⟨Units.mk0 c hc_ne, ?_⟩
      calc
        (Y : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
            = (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
                (Z : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              simp [Z]
        _ = (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
              Matrix.scalar (Fin (Nat.succ D')) c := by
              simp [hc]
        _ = (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) *
              (c • (1 : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)) := by
              rw [Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
        _ = c • (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              ext i j
              simp [Matrix.mul_apply, Matrix.one_apply, mul_comm]
        _ = ((Units.mk0 c hc_ne : Units ℂ) : ℂ) •
              (X : Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ) := by
              simp

/-- A Same-MPV corollary: after obtaining any two gauges from the single-block FT,
they are unique up to a nonzero scalar. -/
theorem gauge_unique_up_to_scalar_of_sameMPV {A B : MPSTensor d D}
    (hA : IsInjective A) (_hAB : SameMPV A B)
    {X Y : GL (Fin D) ℂ}
    (hX : ∀ i, B i = X * A i * X⁻¹)
    (hY : ∀ i, B i = Y * A i * Y⁻¹) :
    ∃ u : Units ℂ, (Y : Matrix (Fin D) (Fin D) ℂ) = (u : ℂ) • (X : Matrix (Fin D) (Fin D) ℂ) :=
  gauge_unique_up_to_scalar hA hX hY

end MPSTensor
