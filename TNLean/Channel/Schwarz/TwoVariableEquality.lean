/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Channel.Schwarz.TwoVariableUnconditional
import TNLean.Channel.Schwarz.AbstractMultiplicativeDomain

/-!
# Equality in the two-variable operator Schwarz inequality

This file proves Wolf's equality criterion for the two-variable operator
Schwarz inequality (Eq. (5.4)): for a fixed `B` such that the inequality
holds for every `A`, and for `A` at which equality is attained, the
pseudoinverse sandwich `E(A†B) · pinv(E(B†B)) · E(B†X)` agrees with
`E(A†X)` for *every* `X`, not only `X = A`.

The proof is Wolf's `t A + X` quadratic-in-`t` completing-the-square
argument: expanding the (matrix-valued) nonnegative quadratic form of the
Schwarz inequality at `A + t X` for real `t`, the `t²`-coefficient vanishes
at the equality point `A`, so the remaining linear-in-`t` term must vanish
identically; applying this at `X` and at `i X` and combining isolates the
one-sided identity Eq. (5.5).

## Main definitions

* `HasSchwarzInequalityFor`: Wolf's per-`B` hypothesis, Eq. (5.4) held for a
  given `B` and every `A`.
* `equalityAttaining`: the equality-attaining set `𝒜_B`.

## Main results

* `hasSchwarzInequalityFor_of_is2PositiveMap`: a 2-positive map satisfies
  the per-`B` hypothesis for every `B` (Theorem 5.3).
* `schwarz_equality_criterion`: Wolf's Eq. (5.5), the equality criterion.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Chapter 5,
  Theorem "Equality in the operator Schwarz inequality"][Wolf2012QChannels]
* Local source: `Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`,
  line 198.
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix

namespace SchwarzTwoVariable

variable {D : ℕ}

local notation "Mat" => Matrix (Fin D) (Fin D) ℂ

/-- Wolf's per-`B` hypothesis for the equality theorem: the two-variable
Schwarz inequality Eq. (5.4) holds for the given `B`, for every `A`.

Source: Wolf, *Quantum Channels & Operations*, Chapter 5, Theorem "Equality
in the operator Schwarz inequality", local source
`Notes/WolfNoteTexSource/ch05_schwarz_inequalities.tex`, line 198. -/
def HasSchwarzInequalityFor (E : Mat →ₗ[ℂ] Mat) (B : Mat) : Prop :=
  ∀ A, E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A) ≤ E (Aᴴ * A)

/-- The equality-attaining set `𝒜_B` for a given `B`: the `A`'s for which
equality is attained in Eq. (5.4).

Source: Wolf, Ch5, line 198. -/
def equalityAttaining (E : Mat →ₗ[ℂ] Mat) (B : Mat) : Set Mat :=
  {A | E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * A) = E (Aᴴ * A)}

/-- A 2-positive map satisfies Wolf's per-`B` hypothesis for every `B`
(Theorem 5.3, Eq. (5.4) unconditionally). -/
theorem hasSchwarzInequalityFor_of_is2PositiveMap
    {E : Mat →ₗ[ℂ] Mat} (h2pos : Is2PositiveMap E) (B : Mat) :
    HasSchwarzInequalityFor E B :=
  fun A => schwarz_two_variable_unconditional E h2pos A B

/-- The quadratic form of the two-variable Schwarz inequality:
`QQ E B U V = E(U†V) - E(U†B) · pinv(E(B†B)) · E(B†V)`, the difference whose
nonnegativity is Eq. (5.4) and whose vanishing at `U = V = A` is membership
in the equality-attaining set.

`E` and `B` are explicit (rather than section variables) throughout this
file: unfolding `QQ` via `simp only [QQ]` against a `QQ` built from
section-variable `E`, `B` was observed to desynchronize the unfolded
occurrences from the ambient `E`, `B` in the goal. -/
private noncomputable def QQ (E : Mat →ₗ[ℂ] Mat) (B U V : Mat) : Mat :=
  E (Uᴴ * V) - E (Uᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * V)

/-- `QQ E B U` is `ℂ`-linear in its second argument. -/
private theorem QQ_add_right (E : Mat →ₗ[ℂ] Mat) (B U V1 V2 : Mat) (c : ℂ) :
    QQ E B U (V1 + c • V2) = QQ E B U V1 + c • QQ E B U V2 := by
  simp only [QQ, Matrix.mul_add, Matrix.mul_smul, map_add, map_smul]
  module

/-- `QQ E B` is conjugate-linear in its first argument. -/
private theorem QQ_add_left (E : Mat →ₗ[ℂ] Mat) (B U1 U2 V : Mat) (c : ℂ) :
    QQ E B (U1 + c • U2) V = QQ E B U1 V + (star c) • QQ E B U2 V := by
  simp only [QQ, Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.add_mul,
    Matrix.smul_mul, map_add, map_smul]
  module

/-- `QQ E B U U` is positive semidefinite whenever Wolf's per-`B` hypothesis
holds: this is exactly Eq. (5.4) rearranged as a difference. -/
private theorem QQ_posSemidef {E : Mat →ₗ[ℂ] Mat} {B : Mat}
    (hSchwarz : HasSchwarzInequalityFor E B) (U : Mat) :
    (QQ E B U U).PosSemidef :=
  Matrix.le_iff.mp (hSchwarz U)

/-- The quadratic-in-`c` expansion of `QQ E B` at `A + c • X`, using
bilinearity and the equality hypothesis `QQ E B A A = 0`. -/
private theorem QQ_expand (E : Mat →ₗ[ℂ] Mat) (B : Mat) {A X : Mat}
    (hAA : QQ E B A A = 0) (c : ℂ) :
    QQ E B (A + c • X) (A + c • X) =
      c • QQ E B A X + (star c) • QQ E B X A + (star c * c) • QQ E B X X := by
  rw [QQ_add_left, QQ_add_right, QQ_add_right, hAA]
  module

/-- **Equality in the two-variable operator Schwarz inequality**
(Wolf, Theorem "Equality in the operator Schwarz inequality", Eq. (5.5)).

Let `E` be a positive linear map such that for a given `B` the two-variable
Schwarz inequality holds for all `A` (`hSchwarz`). Then for every `A` in
the equality-attaining set `equalityAttaining E B` and every `X`:

`E(A†B) · pinv(E(B†B)) · E(B†X) = E(A†X)`.

The `IsPositiveMap E` hypothesis matches Wolf's theorem statement; it is not
needed by this proof, which only uses `hSchwarz` and the equality
hypothesis `hA`. -/
theorem schwarz_equality_criterion (E : Mat →ₗ[ℂ] Mat) (B : Mat) (_hE : IsPositiveMap E)
    (hSchwarz : HasSchwarzInequalityFor E B) {A : Mat} (hA : A ∈ equalityAttaining E B)
    (X : Mat) :
    E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * X) = E (Aᴴ * X) := by
  have hAA : QQ E B A A = 0 := sub_eq_zero.mpr hA.symm
  set L : Mat := QQ E B A X with hL_def
  set R : Mat := QQ E B X A with hR_def
  set Q : Mat := QQ E B X X with hQ_def
  have hQt (c : ℂ) : QQ E B (A + c • X) (A + c • X) =
      c • L + (star c) • R + (star c * c) • Q :=
    QQ_expand E B hAA c
  have hreal (t : ℝ) :
      (((t : ℂ) • (L + R)) + ((t ^ 2 : ℝ) : ℂ) • Q).PosSemidef := by
    have h := QQ_posSemidef hSchwarz (A + (t : ℂ) • X)
    rw [hQt (t : ℂ)] at h
    have e1 : star (t : ℂ) = (t : ℂ) := by simp
    have e2 : (t : ℂ) • L + (t : ℂ) • R + ((t : ℂ) * (t : ℂ)) • Q =
        (t : ℂ) • (L + R) + ((t ^ 2 : ℝ) : ℂ) • Q := by push_cast; module
    rw [e1, e2] at h
    exact h
  have hsum : L + R = 0 := SchwarzMap.eq_zero_of_forall_quadratic_posSemidef hreal
  have himag (t : ℝ) :
      (((t : ℂ) • ((Complex.I : ℂ) • L - (Complex.I : ℂ) • R)) +
        ((t ^ 2 : ℝ) : ℂ) • Q).PosSemidef := by
    have h := QQ_posSemidef hSchwarz (A + ((t : ℂ) * Complex.I) • X)
    rw [hQt ((t : ℂ) * Complex.I)] at h
    have e1 : star ((t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by simp
    have hcoef : (-((t : ℂ) * Complex.I)) * ((t : ℂ) * Complex.I) = ((t ^ 2 : ℝ) : ℂ) := by
      have hI2 : Complex.I * Complex.I = -1 := Complex.I_mul_I
      calc (-((t : ℂ) * Complex.I)) * ((t : ℂ) * Complex.I)
          = -((t : ℂ) * (t : ℂ)) * (Complex.I * Complex.I) := by ring
        _ = -((t : ℂ) * (t : ℂ)) * (-1) := by rw [hI2]
        _ = (t : ℂ) * (t : ℂ) := by ring
        _ = ((t ^ 2 : ℝ) : ℂ) := by push_cast; ring
    have e2 : ((t : ℂ) * Complex.I) • L + (-((t : ℂ) * Complex.I)) • R +
        ((-((t : ℂ) * Complex.I)) * ((t : ℂ) * Complex.I)) • Q =
        (t : ℂ) • ((Complex.I : ℂ) • L - (Complex.I : ℂ) • R) + ((t ^ 2 : ℝ) : ℂ) • Q := by
      rw [hcoef]; module
    rw [e1, e2] at h
    exact h
  have hdiff : (Complex.I : ℂ) • L - (Complex.I : ℂ) • R = 0 :=
    SchwarzMap.eq_zero_of_forall_quadratic_posSemidef himag
  have hR_eq : R = -L := eq_neg_of_add_eq_zero_right hsum
  have hL : L = 0 := by
    rw [hR_eq, smul_neg, sub_neg_eq_add, ← add_smul] at hdiff
    exact (smul_eq_zero.mp hdiff).resolve_left (by norm_num)
  have hLzero : QQ E B A X = 0 := hL_def ▸ hL
  have hLzero' : E (Aᴴ * X) - E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * X) = 0 := by
    simpa [QQ] using hLzero
  exact (sub_eq_zero.mp hLzero').symm

/-- **Converse of the equality criterion.** If the Eq. (5.5) identity
`E(A†B) · pinv(E(B†B)) · E(B†X) = E(A†X)` holds for every `X`, then in
particular (at `X = A`) `A` is in the equality-attaining set
`equalityAttaining E B`. The source states only the forward direction
(`schwarz_equality_criterion`); this converse is immediate from it by
specializing at `X = A`. -/
theorem mem_equalityAttaining_of_forall_eq (E : Mat →ₗ[ℂ] Mat) (B A : Mat)
    (hid : ∀ X, E (Aᴴ * B) * Douglas.pinv (E (Bᴴ * B)) * E (Bᴴ * X) = E (Aᴴ * X)) :
    A ∈ equalityAttaining E B :=
  hid A

end SchwarzTwoVariable
