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
# Determinant API and unitary channels

This file contains the foundational definitions for the determinant of a quantum
channel acting on $M_d(\mathbb{C})$, together with the basic unitary-channel
API used in Wolf's determinant-rigidity argument.

## Main definitions

* `MatrixAlg`, `MatrixEnd` — the ambient matrix algebra and its endomorphisms.
* `MatrixBasisIndex`, `matrixSpaceBasis` — linear-algebra models for the
  standard matrix basis.
* `channelMatrix`, `channelDet` — the matrix representation of a channel and its
  determinant.
* `unitaryChannel` — conjugation by a unitary matrix.

## Main statements

* `channelDet_eq_linearMap_det` — `channelDet` agrees with `LinearMap.det`.
* `channelDet_ne_zero_iff_injective`, `channelDet_ne_zero_iff_bijective` —
  determinant nonvanishing is equivalent to invertibility.
* `channelDet_eq_zero_iff_not_bijective` — determinant zero iff the channel is
  not bijective as a linear map.
* `unitaryChannel_isPositiveMap`, `unitaryChannel_isCPMap`,
  `unitaryChannel_isTracePreserving`, `unitaryChannel_isChannel` — the basic
  positivity and trace-preservation facts for unitary conjugation.

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, §6.1.1][Wolf2012QChannels]

## Tags

quantum channel, determinant, unitary channel, matrix algebra
-/
open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker Matrix.Norms.Frobenius
open Matrix

variable {d : ℕ}
/-- The ambient matrix algebra `M_d(ℂ)`. -/
private abbrev MatrixAlg (d : ℕ) := Matrix (Fin d) (Fin d) ℂ

/-- Endomorphisms of `M_d(ℂ)`. -/
private abbrev MatrixEnd (d : ℕ) := MatrixAlg d →ₗ[ℂ] MatrixAlg d

/-- Index type for the standard basis of `M_d(ℂ)`.

We use `Fin d × Fin d × Unit`, which has cardinality $d^2$. -/
private abbrev MatrixBasisIndex (d : ℕ) := Fin d × Fin d × Unit

/-- The standard basis of `M_d(ℂ)` coming from matrix units. -/
private noncomputable def matrixSpaceBasis (d : ℕ) :
    Module.Basis (MatrixBasisIndex d) ℂ (MatrixAlg d) :=
  Module.Basis.matrix (Fin d) (Fin d) (Module.Basis.singleton Unit ℂ)

section Determinant

/-- The matrix representation of a channel with respect to `matrixSpaceBasis d`. -/
noncomputable def channelMatrix (T : MatrixEnd d) :
    Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ :=
  (LinearMap.toMatrix (matrixSpaceBasis d) (matrixSpaceBasis d)) T

/-- The determinant of a channel's matrix representation on `M_d(ℂ)`. -/
noncomputable def channelDet (T : MatrixEnd d) : ℂ :=
  Matrix.det (n := MatrixBasisIndex d) (channelMatrix T)

/-- `channelDet` agrees with the basis-independent `LinearMap.det`. -/
theorem channelDet_eq_linearMap_det (T : MatrixEnd d) :
    channelDet T = LinearMap.det T := by
  rw [channelDet, channelMatrix]
  exact LinearMap.det_toMatrix (matrixSpaceBasis d) T

/-- Nonzero channel determinant iff the map is a unit in `Module.End`. -/
theorem channelDet_ne_zero_iff_isUnit (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ IsUnit T := by
  simpa only [channelDet_eq_linearMap_det, ne_eq] using
    ((isUnit_iff_ne_zero : IsUnit (LinearMap.det T) ↔ LinearMap.det T ≠ 0).symm.trans
      (LinearMap.isUnit_iff_isUnit_det (f := T)).symm)

/-- A channel determinant is nonzero exactly when the underlying linear map is injective. -/
theorem channelDet_ne_zero_iff_injective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Injective T := by
  simpa only [ne_eq, LinearMap.ker_eq_bot] using
    (channelDet_ne_zero_iff_isUnit (T := T)).trans (LinearMap.isUnit_iff_ker_eq_bot T)

/-- A channel determinant is nonzero exactly when the underlying linear map is bijective. -/
theorem channelDet_ne_zero_iff_bijective (T : MatrixEnd d) :
    channelDet T ≠ 0 ↔ Function.Bijective T := by
  have hbij : Function.Injective T ↔ Function.Bijective T :=
    ⟨fun hT => ⟨hT, (LinearMap.injective_iff_surjective (f := T)).1 hT⟩, (·.1)⟩
  exact (channelDet_ne_zero_iff_injective (T := T)).trans hbij

/-- Wolf Thm 6.1: `det T = 0` iff `T` is not invertible as a linear map on `M_d(ℂ)`. -/
theorem channelDet_eq_zero_iff_not_bijective (T : MatrixEnd d) :
    channelDet T = 0 ↔ ¬ Function.Bijective T := by
  simpa only [ne_eq, Decidable.not_not] using
    not_congr (channelDet_ne_zero_iff_bijective (d := d) T)

/-- The determinant of the identity channel is `1`. -/
@[simp]
theorem channelDet_id :
    channelDet (1 : MatrixEnd d) = 1 := by
  simp only [channelDet_eq_linearMap_det, map_one]

end Determinant

section Unitary

/-- The unitary channel `X ↦ U X U†`. -/
noncomputable def unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) : MatrixEnd d where
  toFun X := (U : MatrixAlg d) * X * (U : MatrixAlg d)ᴴ
  map_add' X Y := by simp only [mul_add, add_mul]
  map_smul' a X := by simp only [mul_smul_comm, smul_mul_assoc, RingHom.id_apply]

/-- Unitary conjugation is positive. -/
theorem unitaryChannel_isPositiveMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsPositiveMap (unitaryChannel U) := by
  intro X hX
  simpa only [unitaryChannel, Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk] using
    hX.mul_mul_conjTranspose_same (B := (U : MatrixAlg d))

/-- Unitary conjugation is completely positive, with a single Kraus operator. -/
theorem unitaryChannel_isCPMap (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsCPMap (unitaryChannel U) := by
  refine ⟨1, fun _ => (U : MatrixAlg d), ?_⟩
  intro X
  simp only [unitaryChannel, Fin.sum_univ_one, LinearMap.coe_mk, AddHom.coe_mk]

/-- Unitary conjugation is trace-preserving. -/
theorem unitaryChannel_isTracePreserving (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsTracePreservingMap (unitaryChannel U) := by
  intro X
  have hU : (U : MatrixAlg d)ᴴ * (U : MatrixAlg d) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
  simpa only [unitaryChannel, Matrix.mul_assoc, LinearMap.coe_mk, AddHom.coe_mk, hU, one_mul] using
    (Matrix.trace_mul_cycle (U : MatrixAlg d) X ((U : MatrixAlg d)ᴴ))

/-- Unitary conjugation is a quantum channel. -/
theorem unitaryChannel_isChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    IsChannel (unitaryChannel U) :=
  ⟨unitaryChannel_isCPMap U, unitaryChannel_isTracePreserving U⟩

end Unitary
