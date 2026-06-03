/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.MPS.Symmetry.Defs
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# On-site rotational symmetry of the AKLT state

This module formalizes the on-site rotational symmetry of the AKLT matrix
product state in its Cartesian (Pauli) form `A^i = σ^i`, `i ∈ {x, y, z}`
(arXiv:2011.12127, around line 1159).

The physical site carries the spin-`1` (defining) representation of the
rotations, while the virtual/bond index transforms in the projective
spin-`½` representation: for every `U ∈ SU(2)`, conjugation of the Pauli
vector by `U` is a rotation `R(U)` of the three physical components, and the
AKLT tensor twisted by `R(U)` is gauge equivalent to the original through the
gauge `U⁻¹`.  This is the projective-representation content of the
symmetry-protected topological phase.  The symmetry is first stated over the
cover `SU(2)`; the `SO(3)` version then follows from the surjectivity of the
cover, both proved here.

## Main definitions

* `MPSTensor.pauli` : the three Pauli matrices indexed by `Fin 3`
* `MPSTensor.pauliConjAd` : the rotation matrix `R(U)ᵢⱼ = ½ tr(σᵢ U σⱼ U⁻¹)`
* `MPSTensor.spinHalfCover` : `R` packaged as a `MonoidHom` on `GL (Fin 2) ℂ`
* `MPSTensor.akltCartesian` : the AKLT tensor `A^i = σ^i`
* `MPSTensor.so3DefiningRep` : the spin-`1` defining representation of `SO(3)`

## Main results

* `MPSTensor.pauli_expansion` : every `2×2` matrix expands in `{1, σx, σy, σz}`
* `MPSTensor.pauli_conj_eq` : the covariance `U σⱼ U⁻¹ = ∑ᵢ R(U)ᵢⱼ σᵢ`
* `MPSTensor.transpose_mul_pauliConjAd` : the rotations `R(U)` are orthogonal,
  `R(U)ᵀ R(U) = 1`
* `MPSTensor.aklt_isOnSiteSymmetric_spinHalfCover` : the AKLT tensor is on-site
  symmetric under the `SU(2)`-parametrized rotations
* `MPSTensor.spinHalfCover_surjective_onto_SO3` : every `SO(3)` rotation is a
  Pauli conjugation by some `SU(2)` element
* `MPSTensor.aklt_isOnSiteSymmetric_SO3` : the AKLT tensor is on-site symmetric
  under the spin-`1` representation of `SO(3)`

## References

* RMP review (arXiv:2011.12127) line 1159 (`A^i = σ^i`, on-site `SO(3)`)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace MPSTensor

/-! ### The Pauli matrices -/

/-- The three Pauli matrices `σx, σy, σz`, indexed by `Fin 3`. -/
def pauli : Fin 3 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => !![0, 1; 1, 0]
  | 1 => !![0, -Complex.I; Complex.I, 0]
  | 2 => !![1, 0; 0, -1]

@[simp] lemma pauli_zero : pauli 0 = !![0, 1; 1, 0] := rfl
@[simp] lemma pauli_one : pauli 1 = !![0, -Complex.I; Complex.I, 0] := rfl
@[simp] lemma pauli_two : pauli 2 = !![1, 0; 0, -1] := rfl

/-- Each Pauli matrix is traceless. -/
@[simp] lemma trace_pauli (k : Fin 3) : (pauli k).trace = 0 := by
  fin_cases k <;> simp [pauli, Matrix.trace, Fin.sum_univ_two]

/-! ### Expansion in the Pauli basis

Every `2×2` complex matrix is a linear combination of the identity and the
three Pauli matrices, with coefficients read off by the trace pairing. -/

/-- The Pauli basis expansion: `M = ½(tr M)·1 + ∑ₖ ½ tr(σₖ M)·σₖ`. -/
lemma pauli_expansion (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M = (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ) +
      ∑ k : Fin 3, ((pauli k * M).trace / 2) • pauli k := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    refine Complex.ext ?_ ?_ <;>
    simp [pauli, Matrix.trace, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.mul_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.add_re, Complex.add_im] <;>
    ring

/-- The trace pairing of two Pauli matrices: `tr(σᵢ σⱼ) = 2 δᵢⱼ`. -/
lemma pauli_mul_pauli_trace (i j : Fin 3) :
    (pauli i * pauli j).trace = if i = j then 2 else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [pauli, Matrix.trace, Fin.sum_univ_two, Complex.ext_iff] <;> norm_num

/-! ### The spin-`½` rotation `R(U)` -/

/-- The rotation matrix `R(U)ᵢⱼ = ½ tr(σᵢ U σⱼ U⁻¹)` obtained by conjugating the
Pauli vector by `U`.  It is the spin-`1` (adjoint) action that accompanies the
virtual spin-`½` action of `U` on the AKLT bond index (arXiv:2011.12127,
around line 1159). -/
def pauliConjAd (U : GL (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => ((pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
    ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).trace) / 2

/-- Conjugating a single Pauli matrix is traceless: `tr(U σⱼ U⁻¹) = tr σⱼ = 0`. -/
lemma trace_conj_pauli_zero (U : GL (Fin 2) ℂ) (j : Fin 3) :
    ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
      ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).trace = 0 := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.GeneralLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, Matrix.one_mul, trace_pauli]

/-- Covariance of the Pauli vector under conjugation: `U σⱼ U⁻¹ = ∑ᵢ R(U)ᵢⱼ σᵢ`.
The conjugate is traceless, so it carries no identity component and expands purely
in the Pauli basis with the rotation coefficients `R(U)`. -/
lemma pauli_conj_eq (U : GL (Fin 2) ℂ) (j : Fin 3) :
    (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
      ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      ∑ i, pauliConjAd U i j • pauli i := by
  have hM := pauli_expansion ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
    ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))
  rw [trace_conj_pauli_zero] at hM
  simp only [zero_div, zero_smul, zero_add] at hM
  rw [hM]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [pauliConjAd, Matrix.mul_assoc]

/-- The rotation by the identity is the identity matrix: `R(1) = 1`. -/
lemma pauliConjAd_one : pauliConjAd 1 = (1 : Matrix (Fin 3) (Fin 3) ℂ) := by
  ext i j
  simp only [pauliConjAd, inv_one, Matrix.GeneralLinearGroup.coe_one, Matrix.mul_one,
    Matrix.one_apply]
  rw [pauli_mul_pauli_trace]
  split <;> norm_num

/-- Pull a finite Pauli expansion out of the conjugated trace. -/
private lemma trace_conj_sum (U : GL (Fin 2) ℂ) (X : Matrix (Fin 2) (Fin 2) ℂ)
    (c : Fin 3 → ℂ) :
    (X * (∑ k, c k • pauli k) *
      ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).trace =
      ∑ k, c k * (X * pauli k *
        ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)).trace := by
  rw [Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

/-- The rotations compose: `R(U V) = R(U) R(V)`.  Conjugation by `U V` is
conjugation by `V` followed by conjugation by `U`, and covariance turns the inner
conjugation into a Pauli expansion whose coefficients are exactly the product. -/
lemma pauliConjAd_mul (U V : GL (Fin 2) ℂ) :
    pauliConjAd (U * V) = pauliConjAd U * pauliConjAd V := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [pauliConjAd]
  rw [_root_.mul_inv_rev, Matrix.GeneralLinearGroup.coe_mul,
    Matrix.GeneralLinearGroup.coe_mul]
  rw [show pauli i * ((U : Matrix (Fin 2) (Fin 2) ℂ) * (V : Matrix (Fin 2) (Fin 2) ℂ)) *
      pauli j * (((V⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
        ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
      (pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((V : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
          ((V⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) by
    simp only [Matrix.mul_assoc]]
  rw [pauli_conj_eq, trace_conj_sum, Finset.sum_div]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [pauliConjAd, Matrix.mul_assoc]
  ring

/-- The spin-`½` cover `U ↦ R(U)`, packaged as a monoid homomorphism from
`GL (Fin 2) ℂ` into the multiplicative monoid of `3×3` matrices. -/
def spinHalfCover : GL (Fin 2) ℂ →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun := pauliConjAd
  map_one' := pauliConjAd_one
  map_mul' := pauliConjAd_mul

@[simp] lemma spinHalfCover_apply (U : GL (Fin 2) ℂ) :
    spinHalfCover U = pauliConjAd U := rfl

/-! ### The AKLT tensor and its on-site symmetry -/

/-- The AKLT tensor in Cartesian (Pauli) form `A^i = σ^i`, `i ∈ {x, y, z}`
(arXiv:2011.12127, around line 1159). -/
def akltCartesian : MPSTensor 3 2 := pauli

@[simp] lemma akltCartesian_apply (i : Fin 3) : akltCartesian i = pauli i := rfl

/-- Trace cyclicity exchanges `U` and `U⁻¹` while transposing the rotation:
`R(U)ᵢⱼ = R(U⁻¹)ⱼᵢ`. -/
lemma pauliConjAd_swap (U : GL (Fin 2) ℂ) (i j : Fin 3) :
    pauliConjAd U i j = pauliConjAd U⁻¹ j i := by
  simp only [pauliConjAd, inv_inv]
  congr 1
  rw [show pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
      ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ)) *
        (pauli j * ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-- For every `U ∈ GL (Fin 2) ℂ` the AKLT tensor twisted on the physical index by
the rotation `R(U)` is gauge equivalent to the original through the virtual gauge
`U⁻¹`: this is the projective spin-`½` representation acting on the bond index
(arXiv:2011.12127, around line 1159). -/
theorem aklt_gaugeEquiv_spinHalfCover (U : GL (Fin 2) ℂ) :
    GaugeEquiv akltCartesian (twistedTensor akltCartesian spinHalfCover U) := by
  refine ⟨U⁻¹, fun i => ?_⟩
  -- The gauge `X = U⁻¹` sends `B i = ↑U⁻¹ * pauli i * ↑(U⁻¹)⁻¹`.
  simp only [twistedTensor, spinHalfCover_apply, akltCartesian_apply]
  rw [pauli_conj_eq U⁻¹ i]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [pauliConjAd_swap U i j]

/-- The AKLT tensor is on-site symmetric under the `SU(2)`-cover-parametrized
rotations `R(U)`.  The physical site carries the spin-`1` representation `R(U)`
while the virtual bond index transforms in the projective spin-`½`
representation, with the gauge for `U` given by `U⁻¹`.  This cover form is
strictly stronger bookkeeping than the `SO(3)` statement
`aklt_isOnSiteSymmetric_SO3`, which follows from it by the surjectivity of the
cover `spinHalfCover_surjective_onto_SO3` (arXiv:2011.12127, around line 1159). -/
theorem aklt_isOnSiteSymmetric_spinHalfCover :
    IsOnSiteSymmetric akltCartesian spinHalfCover :=
  fun U => (aklt_gaugeEquiv_spinHalfCover U).sameMPV

/-- The columns of `R(U)` are orthonormal: `∑ₖ R(U)ₖᵢ R(U)ₖⱼ = δᵢⱼ`.  Cyclicity of
the trace cancels the conjugating factors, reducing the bilinear pairing to
`½ tr(σᵢ σⱼ) = δᵢⱼ`. -/
lemma pauliConjAd_orthogonal (U : GL (Fin 2) ℂ) (i j : Fin 3) :
    ∑ k, pauliConjAd U k i * pauliConjAd U k j = if i = j then 1 else 0 := by
  have hUU : ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
      (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    rw [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  have key : (((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli i *
        ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
      ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
        ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ))).trace =
      (pauli i * pauli j).trace := by
    rw [show ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli i *
          ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) *
        ((U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
          ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) =
        (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli i *
          (((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) *
            (U : Matrix (Fin 2) (Fin 2) ℂ)) * (pauli j *
          ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) by
      simp only [Matrix.mul_assoc]]
    rw [hUU, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.trace_mul_comm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  rw [pauli_conj_eq, pauli_conj_eq] at key
  rw [pauli_mul_pauli_trace] at key
  rw [Matrix.sum_mul] at key
  simp only [Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_sum,
    Matrix.trace_smul, smul_eq_mul] at key
  rw [Finset.sum_comm] at key
  simp only [pauli_mul_pauli_trace, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at key
  -- key : ∑ x, pauliConjAd U x j * (pauliConjAd U x i * 2) = if i = j then 2 else 0
  have hsum : (∑ k, pauliConjAd U k i * pauliConjAd U k j) * 2 =
      ∑ x, pauliConjAd U x j * (pauliConjAd U x i * 2) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  refine mul_right_cancel₀ (b := (2 : ℂ)) (by norm_num) ?_
  rw [hsum, key]
  split <;> ring

/-- The rotation matrices `R(U)` are orthogonal: `R(U)ᵀ R(U) = 1` for every
`U ∈ GL (Fin 2) ℂ`.  This is the matrix form of `pauliConjAd_orthogonal`. -/
lemma transpose_mul_pauliConjAd (U : GL (Fin 2) ℂ) :
    (pauliConjAd U)ᵀ * pauliConjAd U = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Matrix.transpose_apply]
  rw [pauliConjAd_orthogonal]

/-! ### Generators of `SU(2)` and `SO(3)`

The surjectivity of the spin-`½` cover is proved through an explicit
Euler-angle factorization.  Every rotation of three-space is a product of a
rotation about the `z`-axis, a rotation about the `x`-axis, and a further
rotation about the `z`-axis, and each of these one-parameter families is the
image under the cover of a one-parameter family in `SU(2)`. -/

/-- The diagonal `SU(2)` matrix `diag(e^{-iθ/2}, e^{iθ/2})` covering a rotation by
`θ` about the `z`-axis. -/
def su2Diag (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(θ / 2) * Complex.I), 0; 0, Complex.exp (θ / 2 * Complex.I)]

/-- The `SU(2)` matrix covering a rotation by `β` about the `x`-axis. -/
def su2Xrot (β : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Real.cos (β / 2), -Complex.I * Real.sin (β / 2);
    -Complex.I * Real.sin (β / 2), Real.cos (β / 2)]

/-- The rotation by `θ` about the `z`-axis. -/
def rotZ (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]

/-- The rotation by `β` about the `x`-axis. -/
def rotX (β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos β, -Real.sin β; 0, Real.sin β, Real.cos β]

lemma su2Diag_mem_specialUnitaryGroup (θ : ℝ) :
    su2Diag θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [su2Diag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Matrix.one_apply, Complex.star_def, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, ← Complex.exp_conj, ← Complex.exp_add, map_zero, mul_zero,
        zero_mul, add_zero, zero_add, Fin.isValue, Fin.reduceEq, if_true, if_false] <;>
      first
        | rfl
        | (rw [← Complex.exp_zero]; congr 1
           simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_div₀,
             map_neg, map_ofNat]
           ring)
  · rw [su2Diag, Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.exp_add]
    rw [show -(θ / 2) * Complex.I + θ / 2 * Complex.I = 0 by ring, Complex.exp_zero]

lemma su2Xrot_mem_specialUnitaryGroup (β : ℝ) :
    su2Xrot β ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  have hp : ((Real.cos (β / 2) : ℂ)) ^ 2 + ((Real.sin (β / 2) : ℂ)) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [su2Xrot, Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply,
        Matrix.one_apply, Fin.mk_zero, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.cons_val', Matrix.empty_val',
        Matrix.cons_val_fin_one, Complex.star_def, map_neg, map_mul,
        Complex.conj_I, Complex.conj_ofReal, Fin.isValue, Fin.reduceEq,
        if_true, if_false] <;>
      first
        | linear_combination hp - (Real.sin (β / 2) : ℂ) ^ 2 * Complex.I_sq
        | ring
  · rw [su2Xrot, Matrix.det_fin_two_of]
    linear_combination hp - (Real.sin (β / 2) : ℂ) ^ 2 * Complex.I_sq

lemma rotZ_mem_specialOrthogonalGroup (θ : ℝ) :
    rotZ θ ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotZ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq θ]
  · rw [Matrix.det_fin_three]
    simp only [rotZ, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.cons_val_two, Matrix.tail_cons]
    nlinarith [Real.sin_sq_add_cos_sq θ]

lemma rotX_mem_specialOrthogonalGroup (β : ℝ) :
    rotX β ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rotX, Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq β]
  · rw [Matrix.det_fin_three]
    simp only [rotX, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.head_fin_const, Matrix.cons_val_fin_one, Matrix.empty_val',
      Matrix.cons_val_two, Matrix.tail_cons]
    nlinarith [Real.sin_sq_add_cos_sq β]

/-! ### Lifting `SU(2)` matrices into the general linear group -/

/-- A special unitary matrix has nonzero determinant, hence lifts to the general
linear group. -/
def su2ToGL (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A
    (by rw [(Matrix.mem_specialUnitaryGroup_iff.mp hA).2]; exact one_ne_zero)

@[simp] lemma su2ToGL_coe (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((su2ToGL A hA : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A := by
  simp [su2ToGL]

/-- The matrix coercion of the inverse of a lifted special unitary matrix is the
matrix inverse, which for unit determinant is the adjugate. -/
lemma su2ToGL_inv_coe (A : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (((su2ToGL A hA)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = A.adjugate := by
  rw [Matrix.GeneralLinearGroup.coe_inv, su2ToGL_coe, Matrix.inv_def,
    (Matrix.mem_specialUnitaryGroup_iff.mp hA).2]
  simp

/-! ### The cover sends the chosen generators to the coordinate rotations -/

/-- Conjugating the Pauli vector by the diagonal cover `su2Diag θ` realizes the
rotation by `θ` about the `z`-axis. -/
lemma R_su2Diag_eq_rotZ (θ : ℝ) :
    pauliConjAd (su2ToGL (su2Diag θ) (su2Diag_mem_specialUnitaryGroup θ))
      = (rotZ θ).map Complex.ofReal := by
  have hexpP : Complex.exp ((θ : ℂ) / 2 * Complex.I)
      = (Real.cos (θ / 2) : ℂ) + (Real.sin (θ / 2) : ℂ) * Complex.I := by
    rw [show (θ : ℂ) / 2 = ((θ / 2 : ℝ) : ℂ) by push_cast; ring, Complex.exp_mul_I,
      Complex.ofReal_cos, Complex.ofReal_sin]
  have hexpN : Complex.exp (-((θ : ℂ) / 2 * Complex.I))
      = (Real.cos (θ / 2) : ℂ) - (Real.sin (θ / 2) : ℂ) * Complex.I := by
    have harg : -((θ : ℂ) / 2 * Complex.I) = ((-(θ / 2) : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [harg, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin, Complex.ofReal_neg,
      Complex.cos_neg, Complex.sin_neg]
    ring
  have hcos : (Real.cos θ : ℂ)
      = (Real.cos (θ / 2) : ℂ) ^ 2 - (Real.sin (θ / 2) : ℂ) ^ 2 := by
    have h : Real.cos θ = Real.cos (θ / 2) ^ 2 - Real.sin (θ / 2) ^ 2 := by
      rw [← Real.cos_two_mul' (θ / 2), show 2 * (θ / 2) = θ by ring]
    rw [h]; push_cast; ring
  have hsin : (Real.sin θ : ℂ) = 2 * (Real.sin (θ / 2) : ℂ) * (Real.cos (θ / 2) : ℂ) := by
    have h : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      rw [← Real.sin_two_mul, show 2 * (θ / 2) = θ by ring]
    rw [h]; push_cast; ring
  have hpyth : (↑(Real.cos (θ * (1 / 2))) : ℂ) ^ 2
      + (↑(Real.sin (θ * (1 / 2))) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliConjAd, su2ToGL_coe, su2ToGL_inv_coe, pauli, su2Diag, rotZ,
      Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.map_apply, Matrix.cons_val_two, Matrix.tail_cons, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
      neg_mul, mul_neg, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      hexpP, hexpN, hcos, hsin] <;>
    (ring_nf; (try (simp only [Complex.I_sq, Complex.I_pow_four]; ring));
      (try linear_combination hpyth))

/-- Conjugating the Pauli vector by the cover `su2Xrot β` realizes the rotation by
`β` about the `x`-axis. -/
lemma R_su2Xrot_eq_rotX (β : ℝ) :
    pauliConjAd (su2ToGL (su2Xrot β) (su2Xrot_mem_specialUnitaryGroup β))
      = (rotX β).map Complex.ofReal := by
  have hcos : (Real.cos β : ℂ)
      = (Real.cos (β / 2) : ℂ) ^ 2 - (Real.sin (β / 2) : ℂ) ^ 2 := by
    have h : Real.cos β = Real.cos (β / 2) ^ 2 - Real.sin (β / 2) ^ 2 := by
      rw [← Real.cos_two_mul' (β / 2), show 2 * (β / 2) = β by ring]
    rw [h]; push_cast; ring
  have hsin : (Real.sin β : ℂ) = 2 * (Real.sin (β / 2) : ℂ) * (Real.cos (β / 2) : ℂ) := by
    have h : Real.sin β = 2 * Real.sin (β / 2) * Real.cos (β / 2) := by
      rw [← Real.sin_two_mul, show 2 * (β / 2) = β by ring]
    rw [h]; push_cast; ring
  have hpyth : (↑(Real.cos (β * (1 / 2))) : ℂ) ^ 2
      + (↑(Real.sin (β * (1 / 2))) : ℂ) ^ 2 = 1 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_add,
      Real.cos_sq_add_sin_sq, Complex.ofReal_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [pauliConjAd, su2ToGL_coe, su2ToGL_inv_coe, pauli, su2Xrot, rotX,
      Matrix.adjugate_fin_two_of, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply,
      Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
      Matrix.map_apply, Matrix.cons_val_two, Matrix.tail_cons, Fin.reduceFinMk, Fin.zero_eta,
      Fin.mk_one, Fin.isValue, Complex.ofReal_zero, Complex.ofReal_one, Complex.ofReal_neg,
      neg_mul, mul_neg, neg_zero, mul_zero, zero_mul, add_zero, zero_add, mul_one, one_mul,
      hcos, hsin] <;>
    (ring_nf; (try (simp only [Complex.I_sq, Complex.I_pow_four]; ring));
      (try linear_combination hpyth))


/-! ### Surjectivity of the cover via the Euler-angle factorization -/

/-- A point on the unit circle is the cosine-sine pair of an angle.  Existence of
the angle comes from the argument of the corresponding unit complex number. -/
lemma exists_cos_sin {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = c ∧ Real.sin θ = s := by
  have hn : ‖(⟨c, s⟩ : ℂ)‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk, show c * c + s * s = 1 by nlinarith [h]]; simp
  have hz : (⟨c, s⟩ : ℂ) ≠ 0 := by
    intro hc; rw [Complex.ext_iff] at hc
    simp only [Complex.zero_re, Complex.zero_im] at hc; nlinarith [hc.1, hc.2]
  exact ⟨Complex.arg (⟨c, s⟩ : ℂ), by rw [Complex.cos_arg hz, hn]; simp,
    by rw [Complex.sin_arg, hn]; simp⟩

set_option maxHeartbeats 1600000 in
-- The Euler decomposition verifies all nine entries of a three-by-three rotation
-- against the product of three coordinate rotations, each closed by a polynomial
-- certificate over the orthonormality and cofactor relations; this exceeds the
-- default elaboration budget.
lemma so3_euler_decomp (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ α β γ : ℝ, M = rotZ α * rotX β * rotZ γ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff] at hM
  obtain ⟨ho, hdet⟩ := hM
  have hoM : M * Mᵀ = 1 := (Matrix.mem_orthogonalGroup_iff (Fin 3) ℝ).mp ho
  have hoT : Mᵀ * M = 1 := (Matrix.mem_orthogonalGroup_iff' (Fin 3) ℝ).mp ho
  have hadj : Mᵀ = M.adjugate := by
    rw [show Mᵀ = M⁻¹ from (Matrix.inv_eq_right_inv hoM).symm, Matrix.inv_def, hdet]; simp
  -- concrete row/column dot products and cofactors
  have row : ∀ p q : Fin 3, M p 0 * M q 0 + M p 1 * M q 1 + M p 2 * M q 2 =
      if p = q then 1 else 0 := by
    intro p q
    have := congrFun (congrFun hoM p) q
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.one_apply] using this
  have col : ∀ p q : Fin 3, M 0 p * M 0 q + M 1 p * M 1 q + M 2 p * M 2 q =
      if p = q then 1 else 0 := by
    intro p q
    have := congrFun (congrFun hoT p) q
    simpa only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.transpose_apply,
      Matrix.one_apply] using this
  have cof : ∀ p q : Fin 3, M q p = (M.adjugate) p q := by
    intro p q
    have := congrFun (congrFun hadj p) q; rwa [Matrix.transpose_apply] at this
  -- the nine cofactor identities
  have cof00 : M 0 0 = M 1 1 * M 2 2 - M 1 2 * M 2 1 := by
    have := cof 0 0; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, Matrix.empty_val'] at this
    linarith [this]
  have cof01 : M 1 0 = -(M 0 1 * M 2 2) + M 0 2 * M 2 1 := by
    have := cof 0 1; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith [this]
  have cof10 : M 0 1 = -(M 1 0 * M 2 2) + M 1 2 * M 2 0 := by
    have := cof 1 0; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith [this]
  have cof11 : M 1 1 = M 0 0 * M 2 2 - M 0 2 * M 2 0 := by
    have := cof 1 1; simp only [Matrix.adjugate_fin_three, Matrix.of_apply, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val'] at this
    linarith [this]
  -- norms of relevant rows/cols
  have hr22 : M 2 0 * M 2 0 + M 2 1 * M 2 1 + M 2 2 * M 2 2 = 1 := by
    have := row 2 2; rwa [if_pos rfl] at this
  have hc22 : M 0 2 * M 0 2 + M 1 2 * M 1 2 + M 2 2 * M 2 2 = 1 := by
    have := col 2 2; rwa [if_pos rfl] at this
  have hbound : M 2 2 ^ 2 ≤ 1 := by
    nlinarith [hr22, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
  set sβ := Real.sqrt (1 - M 2 2 ^ 2) with hsβdef
  have hsβsq : sβ ^ 2 = 1 - M 2 2 ^ 2 := by
    rw [hsβdef, Real.sq_sqrt (by nlinarith [hbound])]
  have hsβnn : 0 ≤ sβ := Real.sqrt_nonneg _
  obtain ⟨β, hcosβ, hsinβ⟩ := exists_cos_sin (c := M 2 2) (s := sβ) (by nlinarith [hsβsq])
  by_cases hs : sβ = 0
  · -- gimbal lock: sin β = 0, so M 2 2 = ±1 and the off-axis entries vanish
    have h22sq : M 2 2 ^ 2 = 1 := by
      have : sβ ^ 2 = 0 := by rw [hs]; ring
      rw [this] at hsβsq; linarith [hsβsq]
    have hz20 : M 2 0 = 0 := by nlinarith [hr22, h22sq, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
    have hz21 : M 2 1 = 0 := by nlinarith [hr22, h22sq, sq_nonneg (M 2 0), sq_nonneg (M 2 1)]
    have hz02 : M 0 2 = 0 := by nlinarith [hc22, h22sq, sq_nonneg (M 0 2), sq_nonneg (M 1 2)]
    have hz12 : M 1 2 = 0 := by nlinarith [hc22, h22sq, sq_nonneg (M 0 2), sq_nonneg (M 1 2)]
    have hcol0 : M 0 0 ^ 2 + M 1 0 ^ 2 = 1 := by
      have := col 0 0; rw [if_pos rfl] at this; nlinarith [this, hz20]
    obtain ⟨α, hcosα, hsinα⟩ :=
      exists_cos_sin (c := M 0 0) (s := M 1 0) (by nlinarith [hcol0])
    refine ⟨α, β, 0, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
        hcosα, hsinα, hcosβ, hsinβ, Real.cos_zero, Real.sin_zero, hs,
        hz02, hz12, hz20, hz21] <;>
      first
        | linear_combination cof10 + M 1 2 * hz20
        | linear_combination cof11 - M 0 2 * hz20
        | ring
  · have hspos : 0 < sβ := lt_of_le_of_ne hsβnn (Ne.symm hs)
    have hsβne : sβ ≠ 0 := hs
    obtain ⟨α, hcosα, hsinα⟩ := exists_cos_sin (c := -M 1 2 / sβ) (s := M 0 2 / sβ) (by
      rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hsβne)]
      nlinarith [hc22, hsβsq])
    obtain ⟨γ, hcosγ, hsinγ⟩ := exists_cos_sin (c := M 2 1 / sβ) (s := M 2 0 / sβ) (by
      rw [div_pow, div_pow, ← add_div, div_eq_one_iff_eq (pow_ne_zero 2 hsβne)]
      nlinarith [hr22, hsβsq])
    refine ⟨α, β, γ, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [rotZ, rotX, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.head_cons, Matrix.of_apply, Matrix.cons_val',
        Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.cons_val_two,
        Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk,
        hcosα, hsinα, hcosβ, hsinβ, hcosγ, hsinγ] <;>
      field_simp <;>
      first
        | nlinarith [hsβsq, hspos, hr22, hc22, mul_pos hspos hspos]
        | linear_combination M 0 0 * hsβsq + cof00 + M 2 2 * cof11
        | linear_combination M 0 1 * hsβsq + cof10 - M 2 2 * cof01
        | linear_combination M 1 0 * hsβsq + cof01 - M 2 2 * cof10
        | linear_combination M 1 1 * hsβsq + cof11 + M 2 2 * cof00

/-! ### Lifting the cover through products -/

/-- Lifting a product of special unitary matrices agrees with the product of the
lifts in the general linear group. -/
lemma su2ToGL_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hAB : A * B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    su2ToGL (A * B) hAB = su2ToGL A hA * su2ToGL B hB := by
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp [su2ToGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The cover is multiplicative on lifted special unitary matrices. -/
lemma pauliConjAd_su2ToGL_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hAB : A * B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    pauliConjAd (su2ToGL (A * B) hAB)
      = pauliConjAd (su2ToGL A hA) * pauliConjAd (su2ToGL B hB) := by
  rw [← spinHalfCover_apply, ← spinHalfCover_apply, ← spinHalfCover_apply,
    su2ToGL_mul A B hA hB, map_mul]

/-! ### The spin-½ cover is onto `SO(3)` -/

/-- The spin-`½` cover is surjective onto `SO(3)`: every rotation of three-space
is the adjoint action of some `SU(2)` matrix on the Pauli vector.  The witness is
read off the Euler-angle factorization of the rotation. -/
theorem spinHalfCover_surjective_onto_SO3 (M : Matrix (Fin 3) (Fin 3) ℝ)
    (hM : M ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    ∃ U : Matrix (Fin 2) (Fin 2) ℂ, ∃ hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ,
      pauliConjAd (su2ToGL U hU) = M.map Complex.ofReal := by
  obtain ⟨α, β, γ, hαβγ⟩ := so3_euler_decomp M hM
  have hd : ∀ θ, su2Diag θ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    su2Diag_mem_specialUnitaryGroup
  have hx : ∀ b, su2Xrot b ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    su2Xrot_mem_specialUnitaryGroup
  have hU1 : su2Diag α * su2Xrot β ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ (hd α) (hx β)
  have hU : su2Diag α * su2Xrot β * su2Diag γ ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ :=
    Submonoid.mul_mem _ hU1 (hd γ)
  refine ⟨su2Diag α * su2Xrot β * su2Diag γ, hU, ?_⟩
  rw [pauliConjAd_su2ToGL_mul _ _ hU1 (hd γ), pauliConjAd_su2ToGL_mul _ _ (hd α) (hx β),
    R_su2Diag_eq_rotZ, R_su2Xrot_eq_rotX, R_su2Diag_eq_rotZ, hαβγ,
    show (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom from rfl, ← Matrix.map_mul,
    ← Matrix.map_mul]

/-! ### On-site `SO(3)` symmetry of the AKLT tensor -/

/-- The spin-`1` (defining) representation of the rotation group on the physical
index, embedded into the complex matrices. -/
noncomputable def so3DefiningRep :
    Matrix.specialOrthogonalGroup (Fin 3) ℝ →* Matrix (Fin 3) (Fin 3) ℂ where
  toFun M := (M : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal
  map_one' := by simp
  map_mul' M N := by
    have hof : (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom := rfl
    simp only [Submonoid.coe_mul, hof, Matrix.map_mul]

@[simp] lemma so3DefiningRep_apply (M : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    so3DefiningRep M = (M : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal := rfl

/-- The AKLT tensor is on-site symmetric under the full rotation group `SO(3)`
acting through its spin-`1` representation on the physical index.  Surjectivity of
the spin-`½` cover upgrades the `SU(2)`-cover symmetry to a literal `SO(3)`
symmetry: every rotation is the conjugation action of some `SU(2)` matrix, whose
virtual gauge then witnesses the same matrix product vector
(arXiv:2011.12127, around line 1159). -/
theorem aklt_isOnSiteSymmetric_SO3 : IsOnSiteSymmetric akltCartesian so3DefiningRep := by
  intro M
  obtain ⟨U, hU, hRU⟩ := spinHalfCover_surjective_onto_SO3 (M : Matrix (Fin 3) (Fin 3) ℝ) M.2
  have key : twistedTensor akltCartesian so3DefiningRep M
      = twistedTensor akltCartesian spinHalfCover (su2ToGL U hU) := by
    unfold twistedTensor
    simp only [so3DefiningRep_apply, spinHalfCover_apply, ← hRU]
  rw [key]
  exact (aklt_gaugeEquiv_spinHalfCover (su2ToGL U hU)).sameMPV

end MPSTensor

end
