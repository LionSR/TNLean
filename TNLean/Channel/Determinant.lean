/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.Basic
import TNLean.Channel.Peripheral.IrreducibleChannel
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec
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

open scoped Matrix ComplexOrder MatrixOrder BigOperators Kronecker
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

/-- Column-stacking vectorization as a linear equivalence. -/
noncomputable def matrixVecLinearEquiv (d : ℕ) :
    MatrixAlg d ≃ₗ[ℂ] (Fin d × Fin d → ℂ) where
  toFun := Matrix.vec
  invFun v i j := v (j, i)
  left_inv X := by
    ext i j
    rfl
  right_inv v := by
    ext ij
    cases ij
    rfl
  map_add' X Y := by
    ext ij
    rfl
  map_smul' a X := by
    ext ij
    rfl

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
  classical
  by_cases hd : d = 0
  · subst hd
    rw [channelDet_eq_linearMap_det]
    simpa using (show ‖LinearMap.det T‖ ≤ 1 by
      rw [LinearMap.det_eq_one_of_subsingleton]
      simp)
  · haveI : NeZero d := ⟨hd⟩
    let A : Matrix (MatrixBasisIndex d) (MatrixBasisIndex d) ℂ := channelMatrix T
    have hspectrum : spectrum ℂ A = spectrum ℂ T := by
      change spectrum ℂ (channelMatrix T) = spectrum ℂ T
      exact AlgEquiv.spectrum_eq (LinearMap.toMatrixAlgEquiv (matrixSpaceBasis d)) T
    have hroot_le : ∀ μ ∈ A.charpoly.roots, ‖μ‖ ≤ 1 := by
      intro μ hμ
      have hμ_root : Polynomial.IsRoot A.charpoly μ :=
        (Polynomial.mem_roots A.charpoly_monic.ne_zero).1 hμ
      have hμ_specA : μ ∈ spectrum ℂ A :=
        Matrix.mem_spectrum_of_isRoot_charpoly hμ_root
      have hμ_specT : μ ∈ spectrum ℂ T := by
        simpa [hspectrum] using hμ_specA
      have hμ_eig : Module.End.HasEigenvalue T μ :=
        (Module.End.hasEigenvalue_iff_mem_spectrum).2 hμ_specT
      exact IsChannel.eigenvalue_norm_le_one hT μ hμ_eig
    have hprod_le_aux :
        ∀ s : Multiset ℂ, (∀ μ ∈ s, ‖μ‖ ≤ 1) → ‖s.prod‖ ≤ 1 := by
      intro s
      refine Multiset.induction_on s ?_ ?_
      · intro _
        simp
      · intro a s ih hs
        have ha : ‖a‖ ≤ 1 := hs a (by simp)
        have hs' : ∀ μ ∈ s, ‖μ‖ ≤ 1 := by
          intro μ hμ
          exact hs μ (by simp [hμ])
        calc
          ‖(a ::ₘ s).prod‖ = ‖a * s.prod‖ := by simp
          _ = ‖a‖ * ‖s.prod‖ := by rw [norm_mul]
          _ ≤ 1 * 1 := by gcongr; exact ih hs'
          _ = 1 := by norm_num
    have hprod_le : ‖A.charpoly.roots.prod‖ ≤ 1 :=
      hprod_le_aux A.charpoly.roots hroot_le
    calc
      ‖channelDet T‖ = ‖A.det‖ := by simp [A, channelDet]
      _ = ‖A.charpoly.roots.prod‖ := by rw [Matrix.det_eq_prod_roots_charpoly]
      _ ≤ 1 := hprod_le

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

/-- Wolf Thm. 6.1(3): the determinant of a unitary channel is `1`. With the matrix-unit
basis, the representing matrix is `U ⊗ conj U`, whose determinant is
`(det U)^d * conj(det U)^d = 1`. -/
theorem channelDet_unitary_eq_phase_pow (U : Matrix.unitaryGroup (Fin d) ℂ) :
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
  have hdet_map_star : ((U : MatrixAlg d).map star).det = star (Matrix.det (U : MatrixAlg d)) := by
    simpa using (RingEquiv.map_det (starRingAut : ℂ ≃+* ℂ) (U : MatrixAlg d)).symm
  have hdet_unitary : star (Matrix.det (U : MatrixAlg d)) * Matrix.det (U : MatrixAlg d) = 1 := by
    have hU : ((U : MatrixAlg d)ᴴ) * (U : MatrixAlg d) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self U
    have h := congrArg Matrix.det hU
    simpa [Matrix.det_mul, Matrix.det_conjTranspose] using h
  calc
    channelDet (unitaryChannel U) = LinearMap.det (unitaryChannel U) :=
      channelDet_eq_linearMap_det (T := unitaryChannel U)
    _ = LinearMap.det (((e : MatrixAlg d →ₗ[ℂ] (Fin d × Fin d → ℂ)) ∘ₗ unitaryChannel U ∘ₗ
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
    _ = 1 := by
          rw [hdet_unitary, one_pow]

/-- Every unitary channel has determinant of modulus `1`. -/
theorem channelDet_norm_eq_one_of_unitaryChannel (U : Matrix.unitaryGroup (Fin d) ℂ) :
    ‖channelDet (unitaryChannel U)‖ = 1 := by
  rw [channelDet_unitary_eq_phase_pow]
  simp

end WolfStatements
