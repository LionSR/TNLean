/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
# The spin-`½` double cover `SU(2) → SO(3)` — algebraic core

This module defines the Pauli matrices, the adjoint action `R(U)ᵢⱼ = ½ tr(σᵢ U σⱼ U⁻¹)`,
the monoid homomorphism `spinHalfCover : GL(2,ℂ) →* Mat(3,ℂ)`, and proves its
basic algebraic properties (multiplicativity, orthogonality).  It also lifts special
unitary matrices into the general linear group and defines the real corestriction
`spinHalfCoverSO3 : SU(2) →* SO(3)`.

The Euler-angle factorization and surjectivity onto `SO(3)`, which rely on
trigonometric imports, live in `TNLean.Algebra.SpinCover`.

## Main definitions

* `SpinCover.pauli` : the three Pauli matrices indexed by `Fin 3`
* `SpinCover.pauliConjAd` : the rotation matrix `R(U)ᵢⱼ = ½ tr(σᵢ U σⱼ U⁻¹)`
* `SpinCover.spinHalfCover` : `R` packaged as a `MonoidHom` on `GL (Fin 2) ℂ`
* `SpinCover.spinHalfCoverSO3` : the cover corestricted to a `MonoidHom`
  `Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ`

## Main results

* `SpinCover.pauli_expansion` : every `2×2` matrix expands in `{1, σx, σy, σz}`
* `SpinCover.pauli_conj_eq` : the covariance `U σⱼ U⁻¹ = ∑ᵢ R(U)ᵢⱼ σᵢ`
* `SpinCover.transpose_mul_pauliConjAd` : the rotations `R(U)` are orthogonal,
  `R(U)ᵀ R(U) = 1`

## References

* RMP review (arXiv:2011.12127) around line 1159 (`A^i = σ^i`, on-site `SO(3)`)
-/

open scoped Matrix BigOperators
open Matrix Finset

noncomputable section

namespace SpinCover

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

/-! ### Pauli multiplication table

The nine products `σᵢ σⱼ` are computed once as explicit `2×2` matrices so that
every downstream consumer (`pauli_mul_pauli_trace`, trace-pairing identities,
rotation-matrix entries) can reuse the table without re-doing the matrix
multiplication. -/

/-- The multiplication table of the three Pauli matrices, computed as explicit
`2×2` matrices.
```
        σₓ          σ_y           σ_z
σₓ  [1 0]     [ i  0]      [ 0 -1]
    [0 1]     [ 0 -i]      [ 1  0]

σ_y [-i 0]    [1 0]        [0  i]
    [ 0 i]    [0 1]        [i  0]

σ_z [ 0 1]    [0 -i]       [1  0]
    [-1 0]    [-i 0]       [0  1]
``` -/
lemma pauli_mul_eq (i j : Fin 3) : pauli i * pauli j =
    match i, j with
    | 0, 0 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
    | 0, 1 => !![Complex.I, 0; 0, -Complex.I]
    | 0, 2 => !![0, -1; 1, 0]
    | 1, 0 => !![(-Complex.I), 0; 0, Complex.I]
    | 1, 1 => (1 : Matrix (Fin 2) (Fin 2) ℂ)
    | 1, 2 => !![0, Complex.I; Complex.I, 0]
    | 2, 0 => !![0, 1; -1, 0]
    | 2, 1 => !![0, -Complex.I; -Complex.I, 0]
    | 2, 2 => (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  fin_cases i <;> fin_cases j <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [pauli, Matrix.mul_apply, Fin.sum_univ_two]

/-- The trace pairing of two Pauli matrices: `tr(σᵢ σⱼ) = 2 δᵢⱼ`.
Uses the precomputed multiplication table to avoid re-deriving the products. -/
lemma pauli_mul_pauli_trace (i j : Fin 3) :
    (pauli i * pauli j).trace = if i = j then 2 else 0 := by
  rw [pauli_mul_eq]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.trace_fin_two]

/-! ### The spin-`½` rotation `R(U)` -/

/-- The rotation matrix `R(U)ᵢⱼ = ½ tr(σᵢ U σⱼ U⁻¹)` obtained by conjugating the
Pauli vector by `U`.  It is the spin-`1` (adjoint) action of `U` on the Pauli
vector (arXiv:2011.12127, around line 1159). -/
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

/-- Trace cyclicity exchanges `U` and `U⁻¹` while transposing the rotation:
`R(U)ᵢⱼ = R(U⁻¹)ⱼᵢ`. -/
lemma pauliConjAd_swap (U : GL (Fin 2) ℂ) (i j : Fin 3) :
    pauliConjAd U i j = pauliConjAd U⁻¹ j i := by
  simp only [pauliConjAd, inv_inv]
  apply congrArg (fun z : ℂ => z / 2)
  rw [show pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ) * pauli j *
      ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) =
      (pauli i * (U : Matrix (Fin 2) (Fin 2) ℂ)) *
        (pauli j * ((U⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ)) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

/-! ### Orthogonality of the rotations -/

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

/-! ### The conjugate transpose of a Pauli matrix is itself: `σᵢᴴ = σᵢ`. -/

private lemma pauli_star (k : Fin 3) : star (pauli k) = pauli k := by
  fin_cases k <;>
    (ext a b; fin_cases a <;> fin_cases b <;>
      simp [pauli, Matrix.star_apply, Complex.conj_I])

/-- For a special unitary matrix, the coercion of the inverse of its general-linear
lift is the conjugate transpose. -/
private lemma su2ToGL_inv_coe_eq_star (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (((su2ToGL U hU)⁻¹ : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ) = star U := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hU
  rw [su2ToGL_inv_coe]
  have hinv_adj : U⁻¹ = U.adjugate := by rw [Matrix.inv_def, hdet]; simp
  have hinv_star : U⁻¹ = star U := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hu)
  rw [← hinv_adj, hinv_star]

/-- The rotation `R(U)` is real-valued for special unitary `U`: each entry equals
its own complex conjugate.  Conjugating the trace transposes the product, and the
Hermitian Pauli matrices together with `U⁻¹ = Uᴴ` restore the original under trace
cyclicity. -/
private lemma pauliConjAd_su2_conj (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    starRingEnd ℂ (pauliConjAd (su2ToGL U hU) i j) = pauliConjAd (su2ToGL U hU) i j := by
  have hUinv := su2ToGL_inv_coe_eq_star U hU
  rw [pauliConjAd, starRingEnd_apply, star_div₀, ← Matrix.trace_conjTranspose,
    show star (2 : ℂ) = 2 from by norm_num]
  congr 1
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    su2ToGL_coe, hUinv]
  simp only [← Matrix.star_eq_conjTranspose, star_star, pauli_star, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm (pauli i)]
  simp only [Matrix.mul_assoc]

/-- The rotation entries have zero imaginary part for special unitary `U`. -/
private lemma pauliConjAd_su2_im (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) (i j : Fin 3) :
    (pauliConjAd (su2ToGL U hU) i j).im = 0 :=
  Complex.conj_eq_iff_im.mp (pauliConjAd_su2_conj U hU i j)

/-- The rotation `R(U)` has unit determinant for special unitary `U`: the entries
factor through the column norm `|U₀₀|² + |U₁₀|² = 1`, whose cube is the
determinant. -/
private lemma pauliConjAd_su2_det (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (pauliConjAd (su2ToGL U hU)).det = 1 := by
  obtain ⟨hu, hdet⟩ := Matrix.mem_specialUnitaryGroup_iff.mp hU
  have hinv_adj : U⁻¹ = U.adjugate := by rw [Matrix.inv_def, hdet]; simp
  have hinv_star : U⁻¹ = star U := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hu)
  have hkey : U.adjugate = star U := by rw [← hinv_adj, hinv_star]
  rw [Matrix.adjugate_fin_two] at hkey
  have e11 := congrFun (congrFun hkey 0) 0
  have e01 := congrFun (congrFun hkey 0) 1
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.star_apply,
    Complex.star_def] at e11 e01
  rw [Matrix.det_fin_two] at hdet
  have hU01 : U 0 1 = -starRingEnd ℂ (U 1 0) := by linear_combination -e01
  have hnorm : U 0 0 * starRingEnd ℂ (U 0 0) + U 1 0 * starRingEnd ℂ (U 1 0) = 1 := by
    rw [e11, hU01] at hdet; linear_combination hdet
  rw [Matrix.det_fin_three]
  simp only [pauliConjAd, su2ToGL_coe, su2ToGL_inv_coe, Matrix.adjugate_fin_two, pauli,
    Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
    Matrix.empty_val', Matrix.cons_val_fin_one, Fin.isValue]
  rw [e11, hU01]
  ring_nf
  rw [Complex.I_sq]
  set p := U 0 0 * starRingEnd ℂ (U 0 0)
  set q := U 1 0 * starRingEnd ℂ (U 1 0)
  linear_combination (p ^ 2 + 2 * p * q + q ^ 2 + p + q + 1) * hnorm

/-! ### Corestricting the cover to `SO(3)`

For a special unitary `U`, the conjugating factor is the conjugate transpose, so
the rotation `R(U)` is real, orthogonal, and of unit determinant.  These three
facts realize `R` as a monoid homomorphism into the rotation group, the
corestriction of the cover. -/

/-- The real matrix underlying the spin-`½` rotation `R(U)` for special unitary
`U`, obtained by taking the real part of each entry. -/
noncomputable def pauliConjAdReal (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (pauliConjAd (su2ToGL U hU) i j).re

/-- Embedding the real rotation back into the complex matrices recovers `R(U)`. -/
private lemma pauliConjAdReal_map (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    (pauliConjAdReal U hU).map Complex.ofReal = pauliConjAd (su2ToGL U hU) := by
  ext i j
  rw [Matrix.map_apply, pauliConjAdReal]
  exact Complex.conj_eq_iff_re.mp (pauliConjAd_su2_conj U hU i j)

/-- For special unitary `U` the real rotation `R(U)` lies in `SO(3)`: it is
orthogonal by the column orthonormality and has unit determinant. -/
private lemma pauliConjAdReal_mem (U : Matrix (Fin 2) (Fin 2) ℂ)
    (hU : U ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    pauliConjAdReal U hU ∈ Matrix.specialOrthogonalGroup (Fin 3) ℝ := by
  rw [Matrix.mem_specialOrthogonalGroup_iff]
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_orthogonalGroup_iff']
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [Matrix.transpose_apply, pauliConjAdReal]
    have hortho := pauliConjAd_orthogonal (su2ToGL U hU) i j
    have hre : ∀ k, (pauliConjAd (su2ToGL U hU) k i).re * (pauliConjAd (su2ToGL U hU) k j).re
        = (pauliConjAd (su2ToGL U hU) k i * pauliConjAd (su2ToGL U hU) k j).re := by
      intro k
      rw [Complex.mul_re, pauliConjAd_su2_im U hU k i, zero_mul, sub_zero]
    rw [Finset.sum_congr rfl (fun k _ => hre k), ← Complex.re_sum, hortho]
    split <;> simp
  · apply Complex.ofReal_injective
    rw [show (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom from rfl, map_one, RingHom.map_det,
      show Complex.ofRealHom.mapMatrix (pauliConjAdReal U hU)
        = (pauliConjAdReal U hU).map Complex.ofReal from rfl, pauliConjAdReal_map]
    exact pauliConjAd_su2_det U hU

/-- The real rotation of the identity is the identity. -/
private lemma pauliConjAdReal_one :
    pauliConjAdReal (1 : Matrix (Fin 2) (Fin 2) ℂ) (Submonoid.one_mem _) = 1 := by
  apply Matrix.map_injective Complex.ofReal_injective
  change (pauliConjAdReal _ _).map Complex.ofReal
      = (1 : Matrix (Fin 3) (Fin 3) ℝ).map Complex.ofReal
  rw [pauliConjAdReal_map, Matrix.map_one _ Complex.ofReal_zero Complex.ofReal_one,
    show su2ToGL (1 : Matrix (Fin 2) (Fin 2) ℂ) (Submonoid.one_mem _) = 1 from ?_]
  · exact pauliConjAd_one
  · apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [su2ToGL, Matrix.GeneralLinearGroup.mkOfDetNeZero]

/-- The real rotations compose. -/
private lemma pauliConjAdReal_mul (A B : Matrix (Fin 2) (Fin 2) ℂ)
    (hA : A ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hB : B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ)
    (hAB : A * B ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    pauliConjAdReal (A * B) hAB = pauliConjAdReal A hA * pauliConjAdReal B hB := by
  apply Matrix.map_injective Complex.ofReal_injective
  change (pauliConjAdReal _ _).map Complex.ofReal
      = (pauliConjAdReal A hA * pauliConjAdReal B hB).map Complex.ofReal
  rw [pauliConjAdReal_map,
    show (Complex.ofReal : ℝ → ℂ) = ⇑Complex.ofRealHom from rfl, Matrix.map_mul,
    show (⇑Complex.ofRealHom : ℝ → ℂ) = Complex.ofReal from rfl,
    pauliConjAdReal_map, pauliConjAdReal_map]
  exact pauliConjAd_su2ToGL_mul A B hA hB hAB

/-- The spin-`½` double cover corestricted to a monoid homomorphism
`Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ`.
This is the cover `R` of `spinHalfCover` landing in the rotation group, made
possible by the real-valuedness, orthogonality, and unit-determinant of `R(U)` for
special unitary `U` (arXiv:2011.12127, around line 1159). -/
noncomputable def spinHalfCoverSO3 :
    Matrix.specialUnitaryGroup (Fin 2) ℂ →* Matrix.specialOrthogonalGroup (Fin 3) ℝ where
  toFun A := ⟨pauliConjAdReal (A : Matrix (Fin 2) (Fin 2) ℂ) A.2, pauliConjAdReal_mem _ A.2⟩
  map_one' := by
    ext i j
    simp only [Submonoid.coe_one]
    exact congrFun (congrFun pauliConjAdReal_one i) j
  map_mul' A B := by
    ext i j
    simp only [Submonoid.coe_mul]
    exact congrFun (congrFun
      (pauliConjAdReal_mul _ _ A.2 B.2 (Submonoid.mul_mem _ A.2 B.2)) i) j

/-- The corestricted cover embeds back into the complex matrices as `R(U)`. -/
@[simp] lemma spinHalfCoverSO3_coe_map (A : Matrix.specialUnitaryGroup (Fin 2) ℂ) :
    ((spinHalfCoverSO3 A : Matrix (Fin 3) (Fin 3) ℝ)).map Complex.ofReal
      = pauliConjAd (su2ToGL (A : Matrix (Fin 2) (Fin 2) ℂ) A.2) :=
  pauliConjAdReal_map _ A.2

end SpinCover
