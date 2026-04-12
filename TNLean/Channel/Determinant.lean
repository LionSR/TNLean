/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.DeterminantAux

/-!
# Determinants of quantum channels — main theorems

This file provides the user-facing results on channel determinants (Wolf §6.1.1):

* `channelDet_unitary_eq_one` : unitary channels have determinant `1`
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` : **Wolf Thm 6.1(2)** for CPTP maps

Definitions, basic properties, and the private helper lemmas live in `DeterminantAux.lean`.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}

section WolfStatements

variable {T : MatrixEnd d}

/-- The determinant of a unitary channel equals `1`. -/
theorem channelDet_unitary_eq_one (U : Matrix.unitaryGroup (Fin d) ℂ) :
    channelDet (unitaryChannel U) = 1 := by
  let e : MatrixAlg d ≃ₗ[ℂ] (Fin d × Fin d → ℂ) := matrixVecLinearEquiv d
  let M : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
    ((U : MatrixAlg d).map star) ⊗ₖ (U : MatrixAlg d)
  have hvec : ∀ X : MatrixAlg d,
      e (unitaryChannel U X) = Matrix.toLin' M (e X) := by
    intro X
    change Matrix.vec (((U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ) : MatrixAlg d) =
      M.mulVec (Matrix.vec X)
    symm
    simpa [M, unitaryChannel, Matrix.conjTranspose] using
      (Matrix.kronecker_mulVec_vec (A := (U : MatrixAlg d)) (X := X)
        (B := (U : MatrixAlg d).map star))
  have hconj :
      ((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
          ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
            (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d)) =
        Matrix.toLin' M := by
    apply LinearMap.ext
    intro w
    ext ij
    simpa [e] using congrFun (hvec (e.symm w)) ij
  have hdet_map_star :
      ((U : MatrixAlg d).map star).det = star (Matrix.det (U : MatrixAlg d)) := by
    simpa using (RingEquiv.map_det (starRingAut : ℂ ≃+* ℂ) (U : MatrixAlg d)).symm
  have hdet_unitary :
      star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d) = 1 := by
    have hU : ((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
    have h := congrArg Matrix.det hU
    simpa [Matrix.det_mul, Matrix.det_conjTranspose] using h
  calc
    channelDet (unitaryChannel U) = LinearMap.det (unitaryChannel U) :=
      channelDet_eq_linearMap_det (T := unitaryChannel U)
    _ = LinearMap.det
          (((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
            ((e.symm : (Fin d × Fin d → ℂ) ≃ₗ[ℂ] MatrixAlg d) :
              (Fin d × Fin d → ℂ) →ₗ[ℂ] MatrixAlg d))) :=
        (LinearMap.det_conj (f := unitaryChannel U) (e := e)).symm
    _ = LinearMap.det (Matrix.toLin' M) := by rw [hconj]
    _ = Matrix.det M := by rw [LinearMap.det_toLin']
    _ = ((U : MatrixAlg d).map star).det ^ d * Matrix.det (U : MatrixAlg d) ^ d := by
          simpa [M] using
            (Matrix.det_kronecker (A := (U : MatrixAlg d).map star)
              (B := (U : MatrixAlg d)))
    _ = (star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d)) ^ d := by
          rw [hdet_map_star, mul_pow]
    _ = 1 := by rw [hdet_unitary, one_pow]

/-- Every unitary channel has determinant of modulus `1`. -/
theorem channelDet_norm_eq_one_of_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet (unitaryChannel U)‖ = 1 := by
  simp [channelDet_unitary_eq_one]

/-- Wolf Thm 6.1(2) restricted to CPTP maps: `‖det T‖ = 1 ↔ ∃ U, T = unitaryChannel U`.

The transposition branch from Wolf's general Thm 6.1(2) for positive TP maps does not
appear for CPTP maps since the transpose map is not completely positive. -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  constructor
  · intro h
    by_cases hd : d = 0
    · subst hd; exact ⟨1, Subsingleton.elim _ _⟩
    · haveI : NeZero d := ⟨hd⟩
      exact forward_det_one_implies_unitaryChannel hT h
  · rintro ⟨U, rfl⟩
    exact channelDet_norm_eq_one_of_unitaryChannel U

/-- CPTP specialization of the unitary characterization (alias of
`channelDet_norm_eq_one_iff_exists_unitaryChannel`). -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U :=
  channelDet_norm_eq_one_iff_exists_unitaryChannel hT

end WolfStatements
