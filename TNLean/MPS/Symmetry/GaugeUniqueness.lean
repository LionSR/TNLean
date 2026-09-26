/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.Basic
import TNLean.MPS.Chain.OneSidedInverse
import QICLean.Algebra.ScalarCommutant

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
theorem gauge_unique_up_to_scalar {A B : MPSTensor d D} (hA : Kraus.IsInjective A)
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
              ((X⁻¹ : GL (Fin (Nat.succ D')) ℂ) :
                Matrix (Fin (Nat.succ D')) (Fin (Nat.succ D')) ℂ)
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
          rw [hc]; ext i j; simp [hc0]
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

/-- Gauge uniqueness for tensors with identical matrix product vector families: after
obtaining any two gauges from the single-block fundamental theorem, they are unique up
to a nonzero scalar.

Although the hypothesis that $A$ and $B$ generate the same matrix product vector
family is not needed for the conclusion — gauge uniqueness follows from
injectivity alone, together with the two gauge equations $B_i = X A_i X^{-1}$
and $B_i = Y A_i Y^{-1}$ — it is retained to match the blueprint statement
faithfully. -/
theorem gauge_unique_up_to_scalar_of_sameMPV {A B : MPSTensor d D}
    (hA : Kraus.IsInjective A) (_hAB : SameMPV A B)
    {X Y : GL (Fin D) ℂ}
    (hX : ∀ i, B i = X * A i * X⁻¹)
    (hY : ∀ i, B i = Y * A i * Y⁻¹) :
    ∃ u : Units ℂ,
      (Y : Matrix (Fin D) (Fin D) ℂ) = (u : ℂ) • (X : Matrix (Fin D) (Fin D) ℂ) :=
  gauge_unique_up_to_scalar hA hX hY

/-- **Gauge-phase uniqueness for injective tensors.**
Source: arXiv:2011.12127, §III.A, eq. `eq:XAX=B`
(`Papers/2011.12127/TN-Review-main.tex` lines 1085–1087): for a normal tensor,
`X⁻¹ Aⁱ X = e^{iχ} Y⁻¹ Aⁱ Y` for all `i` forces `e^{iχ} = 1` and `X ∝ Y`.

The source writes the proportionality constant as a phase `e^{iφ}`, which it is
when `X` and `Y` are unitary; for general invertible gauges the constant is a
nonzero scalar.  The proof: `Z = Y X⁻¹` satisfies `Z Aⁱ = c Aⁱ Z`, which extends
by linearity to every matrix; the identity matrix gives `c = 1`, and then `Z`
commutes with the whole matrix algebra, so it is a scalar. -/
theorem gauge_phase_unique [NeZero D] {A : MPSTensor d D} (hA : Kraus.IsInjective A)
    {X Y : GL (Fin D) ℂ} {c : ℂ}
    (h : ∀ i, ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * X =
      c • (((Y⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) * A i * Y)) :
    c = 1 ∧ ∃ u : Units ℂ,
      (X : Matrix (Fin D) (Fin D) ℂ) = (u : ℂ) • (Y : Matrix (Fin D) (Fin D) ℂ) := by
  classical
  let Z : GL (Fin D) ℂ := Y * X⁻¹
  have hZA : ∀ i, (Z : Matrix (Fin D) (Fin D) ℂ) * A i =
      c • (A i * (Z : Matrix (Fin D) (Fin D) ℂ)) := by
    intro i
    have hi := congrArg (fun M : Matrix (Fin D) (Fin D) ℂ =>
      (Y : Matrix (Fin D) (Fin D) ℂ) * M * ((X⁻¹ : GL (Fin D) ℂ) : Matrix _ _ ℂ)) (h i)
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc] at hi
    simpa [Z, Matrix.mul_assoc, Units.mul_inv_cancel_left] using hi
  -- The twisted commutation relation extends to the span of the letters.
  have hall : ∀ M : Matrix (Fin D) (Fin D) ℂ,
      (Z : Matrix (Fin D) (Fin D) ℂ) * M = c • (M * (Z : Matrix (Fin D) (Fin D) ℂ)) := by
    intro M
    have hM : M ∈ Submodule.span ℂ (Set.range A) := hA.span_eq_top ▸ Submodule.mem_top
    induction hM using Submodule.span_induction with
    | mem x hx => obtain ⟨i, rfl⟩ := hx; exact hZA i
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mul_add, hx, hy, Matrix.add_mul, smul_add]
    | smul r x _ hx => rw [Matrix.mul_smul, hx, Matrix.smul_mul, smul_comm]
  have hc : c = 1 := by
    have h1 := hall 1
    rw [Matrix.mul_one, Matrix.one_mul] at h1
    have h2 : ((1 - c) • (Z : Matrix (Fin D) (Fin D) ℂ)) = 0 := by
      rw [sub_smul, one_smul, ← h1, sub_self]
    have h3 := congrArg (· * ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) h2
    simp only [Matrix.smul_mul, Units.mul_inv, Matrix.zero_mul] at h3
    have h4 : (1 - c) = 0 := by
      by_contra hne
      exact one_ne_zero ((smul_eq_zero.mp h3).resolve_left hne)
    exact (sub_eq_zero.mp h4).symm
  subst hc
  obtain ⟨a, ha⟩ := Matrix.isScalar_of_commute_span_eq_top
    (Z : Matrix (Fin D) (Fin D) ℂ) hA.span_eq_top (fun M _ => by simpa using hall M)
  have ha0 : a ≠ 0 := by
    rintro rfl
    have h3 := congrArg (· * ((Z⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ)) ha
    simp only [Units.mul_inv, map_zero, Matrix.zero_mul] at h3
    exact one_ne_zero h3
  refine ⟨rfl, (Units.mk0 a ha0)⁻¹, ?_⟩
  have hY : (Y : Matrix (Fin D) (Fin D) ℂ) = a • (X : Matrix (Fin D) (Fin D) ℂ) := by
    calc (Y : Matrix (Fin D) (Fin D) ℂ)
        = (Z : Matrix (Fin D) (Fin D) ℂ) * X := by simp [Z, Matrix.mul_assoc]
      _ = a • (X : Matrix (Fin D) (Fin D) ℂ) := by
        rw [ha, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.smul_mul,
          Matrix.one_mul]
  rw [hY, smul_smul]
  simp [ha0]

end MPSTensor
