/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Determinants of quantum channels

This file provides a minimal formal interface for the determinant of a quantum
channel viewed as a linear endomorphism of the $d^2$-dimensional complex vector
space `Matrix (Fin d) (Fin d) ℂ`, following Wolf §6.1.1.

## Main definitions

* `channelMatrix` : the matrix of a channel with respect to the standard matrix basis
* `channelDet` : the determinant of that matrix representation
* `unitaryChannel` : conjugation by a unitary matrix

## Main results

* `channelDet_eq_linearMap_det` : the chosen matrix determinant agrees with `LinearMap.det`
* `channelDet_eq_zero_iff_not_bijective` : determinant zero iff the underlying linear map is
  not invertible
* `channelDet_norm_le_one_of_positive_tracePreserving` : Wolf's determinant bound (statement)
* `channelDet_norm_eq_one_iff_exists_unitaryChannel` : Wolf's unitary characterization
  (statement)

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder BigOperators
open Matrix

variable {d : ℕ}

/-- The ambient matrix algebra `M_d(ℂ)`. -/
abbrev MatrixAlg (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Endomorphisms of `M_d(ℂ)`. -/
abbrev MatrixEnd (d : ℕ) := MatrixAlg d →ₗ[ℂ] MatrixAlg d

/-- Index type for the standard basis of `M_d(ℂ)`.

We use `Fin d × Fin d × Unit`, which has cardinality $d^2$. -/
abbrev MatrixBasisIndex (d : ℕ) := Fin d × Fin d × Unit

/-- The standard basis of `M_d(ℂ)` coming from matrix units. -/
noncomputable def matrixSpaceBasis (d : ℕ) :
    Module.Basis (MatrixBasisIndex d) ℂ (MatrixAlg d) :=
  Module.Basis.matrix (Fin d) (Fin d) (Module.Basis.singleton Unit ℂ)

section Determinant

/-- The matrix representation of a channel with respect to `matrixSpaceBasis d`. -/
noncomputable def channelMatrix (T : MatrixEnd d) :
    Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ :=
  (LinearMap.toMatrix (matrixSpaceBasis d) (matrixSpaceBasis d)) T

/-- The determinant of a channel, defined as the determinant of its matrix
representation on the $d^2$-dimensional space of matrices. -/
noncomputable def channelDet (T : MatrixEnd d) : ℂ :=
  Matrix.det (n := MatrixBasisIndex d) (channelMatrix T)

/-- The chosen matrix determinant agrees with the basis-independent determinant
`LinearMap.det`. -/
theorem channelDet_eq_linearMap_det (T : MatrixEnd d) :
    channelDet T = LinearMap.det T := by
  unfold channelDet channelMatrix
  exact (LinearMap.det_toMatrix (matrixSpaceBasis d) T)

/-- A channel determinant is nonzero exactly when the underlying linear map is invertible in
`Module.End`. -/
theorem channelDet_ne_zero_iff_isUnit (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ IsUnit T := by
  rw [channelDet_eq_linearMap_det]
  constructor
  · intro hdet
    exact (LinearMap.isUnit_iff_isUnit_det (f := T)).2 (isUnit_iff_ne_zero.mpr hdet)
  · intro hT
    exact isUnit_iff_ne_zero.mp ((LinearMap.isUnit_iff_isUnit_det (f := T)).1 hT)

/-- A channel determinant is nonzero exactly when the underlying linear map is injective. -/
theorem channelDet_ne_zero_iff_injective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Injective T := by
  constructor
  · intro hdet
    have hT : IsUnit T := (channelDet_ne_zero_iff_isUnit T).1 hdet
    exact (LinearMap.ker_eq_bot).1 ((LinearMap.isUnit_iff_ker_eq_bot T).1 hT)
  · intro hT
    have hker : T.ker = ⊥ := (LinearMap.ker_eq_bot).2 hT
    exact (channelDet_ne_zero_iff_isUnit T).2 ((LinearMap.isUnit_iff_ker_eq_bot T).2 hker)

/-- A channel determinant is nonzero exactly when the underlying linear map is bijective. -/
theorem channelDet_ne_zero_iff_bijective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Bijective T := by
  constructor
  · intro hdet
    have hT : Function.Injective T := (channelDet_ne_zero_iff_injective T).1 hdet
    exact ⟨hT, (LinearMap.injective_iff_surjective (f := T)).1 hT⟩
  · intro hT
    exact (channelDet_ne_zero_iff_injective T).2 hT.1

/-- Wolf Thm 6.1: `det T = 0` iff `T` is not invertible as a linear map on `M_d(ℂ)`. -/
theorem channelDet_eq_zero_iff_not_bijective (T : MatrixEnd d) :
    channelDet T = 0 ↔ ¬ Function.Bijective T := by
  simpa using not_congr (channelDet_ne_zero_iff_bijective (d := d) T)

@[simp] theorem channelDet_id :
    channelDet (1 : MatrixEnd d) = 1 := by
  rw [channelDet_eq_linearMap_det]
  exact
    (LinearMap.det_id : LinearMap.det (LinearMap.id : MatrixAlg d →ₗ[ℂ] MatrixAlg d) = 1)

end Determinant

section Unitary

/-- The unitary channel `X ↦ U X U†`. -/
noncomputable def unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) : MatrixEnd d where
  toFun X := (U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ
  map_add' X Y := by
    simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  map_smul' a X := by
    simp [Matrix.mul_assoc]

/-- Unitary conjugation is positive. -/
theorem unitaryChannel_isPositiveMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsPositiveMap (unitaryChannel U) := by
  intro X hX
  simpa [unitaryChannel, Matrix.mul_assoc] using
    hX.mul_mul_conjTranspose_same (B := (U : MatrixAlg d))

/-- Unitary conjugation is completely positive, with a single Kraus operator. -/
theorem unitaryChannel_isCPMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsCPMap (unitaryChannel U) := by
  refine ⟨1, fun _ => (U : MatrixAlg d), ?_⟩
  intro X
  simp [unitaryChannel]

/-- Unitary conjugation is trace-preserving. -/
theorem unitaryChannel_isTracePreserving (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsTracePreservingMap (unitaryChannel U) := by
  intro X
  have hU : ((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  calc
    trace (unitaryChannel U X)
        = trace (((U : MatrixAlg d) * X) * (U : MatrixAlg d)ᴴ) := by
            rfl
    _ = trace (((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) * X) := by
          simpa [Matrix.mul_assoc] using
            (Matrix.trace_mul_cycle (U : MatrixAlg d) X ((U : MatrixAlg d)ᴴ))
    _ = trace X := by
          simp [hU]

/-- Unitary conjugation is a quantum channel. -/
theorem unitaryChannel_isChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsChannel (unitaryChannel U) :=
  ⟨unitaryChannel_isCPMap U, unitaryChannel_isTracePreserving U⟩

end Unitary

section WolfStatements

variable {T : MatrixEnd d}

/-- Wolf Thm 6.1: for a positive trace-preserving map on `M_d(ℂ)`, the channel determinant
satisfies `|det T| ≤ 1`. -/
theorem channelDet_norm_le_one_of_positive_tracePreserving
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ‖channelDet T‖ ≤ 1 := by
  sorry

/-- CPTP specialization of Wolf's determinant bound. -/
theorem channelDet_norm_le_one_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ ≤ 1 := by
  exact channelDet_norm_le_one_of_positive_tracePreserving (T := T) hT.pos hT.tp

/-- Wolf Thm 6.1: for positive trace-preserving maps, `|det T| = 1` iff `T` is unitary
conjugation. -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel
    (hPos : IsPositiveMap T) (hTP : IsTracePreservingMap T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  sorry

/-- CPTP specialization of the unitary characterization. -/
theorem channelDet_norm_eq_one_iff_exists_unitaryChannel_of_channel
    (hT : IsChannel T) :
    ‖channelDet T‖ = 1 ↔ ∃ U : Matrix.unitaryGroup (Fin d) ℂ, T = unitaryChannel U := by
  exact channelDet_norm_eq_one_iff_exists_unitaryChannel (T := T) hT.pos hT.tp

/-- Wolf Cor. 6.2: the determinant of a unitary channel is the phase
`(det U / |det U|)^(2d)`. -/
theorem channelDet_unitary_eq_phase_pow (U : Matrix.unitaryGroup (Fin d) ℂ) :
    channelDet (unitaryChannel U) =
      ((Matrix.det (U : MatrixAlg d) / (↑‖Matrix.det (U : MatrixAlg d)‖ : ℂ)) ^ (2 * d)) := by
  sorry

/-- Every unitary channel has determinant of modulus `1`. -/
theorem channelDet_norm_eq_one_of_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet (unitaryChannel U)‖ = 1 := by
  have hPos : IsPositiveMap (unitaryChannel U) := unitaryChannel_isPositiveMap U
  have hTP : IsTracePreservingMap (unitaryChannel U) := unitaryChannel_isTracePreserving U
  exact (channelDet_norm_eq_one_iff_exists_unitaryChannel (T := unitaryChannel U) hPos hTP).2
    ⟨U, rfl⟩

end WolfStatements
