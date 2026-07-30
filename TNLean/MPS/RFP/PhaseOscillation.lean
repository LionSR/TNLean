/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.RFP.BNTOrthogonality
import TNLean.MPS.RFP.PhaseMultiplicityCounterexample

/-!
# Phase oscillation in the canonical-form renormalization flow

The modulus normalization in the canonical form of arXiv:1606.00608 does not force the phases of
repeated normal blocks to agree. For a primitive cube root of unity `ω`, the one-letter tensor
`diag(1, ω)` is the canonical assembly of two copies of the scalar normal tensor, with weights `1`
and `ω`. Its transfer map sends the lower off-diagonal matrix unit to `ω` times that matrix unit.
Consequently its dyadic transfer-map orbit alternates between the factors `ω` and `ω²`.

This gives an obstruction to the unrestricted convergence assertion in arXiv:1606.00608,
Appendix B, lines 1211--1244. It does not affect the primitive single-block convergence theorem
`rg_flow_converges_of_cf`.

See `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`.
-/

open Filter Topology
open scoped Matrix BigOperators

namespace MPSTensor

/-- The standard primitive cube root of unity. -/
noncomputable def primitiveCubeRoot : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I / 3)

/-- The canonical weights `1` and `primitiveCubeRoot`. -/
noncomputable def cubePhaseWeight : Fin 2 → ℂ
  | 0 => 1
  | 1 => primitiveCubeRoot

/-- The two scalar blocks in the cube-phase example both have bond dimension one. -/
@[reducible] def cubePhaseBondDim : Fin 2 → ℕ := fun _ => 1

private noncomputable def cubePhaseBlock (k : Fin 2) :
    MPSTensor 1 (cubePhaseBondDim k) :=
  fun i => cubePhaseWeight k • scalarUnitTensor i

/-- The direct sum of two scalar normal tensors with relative phase a primitive cube root. -/
noncomputable def cubePhaseTensor :
    MPSTensor 1 (∑ k : Fin 2, cubePhaseBondDim k) :=
  toTensorFromBlocks cubePhaseWeight (fun _ => scalarUnitTensor)

private theorem cubePhaseTensor_eq_directSum :
    cubePhaseTensor = directSumTensor cubePhaseBlock := by
  ext i
  rfl

private noncomputable def lowerMatrixUnit :
    Matrix ((k : Fin 2) × Fin (cubePhaseBondDim k))
      ((k : Fin 2) × Fin (cubePhaseBondDim k)) ℂ :=
  Matrix.single ⟨1, 0⟩ ⟨0, 0⟩ 1

private noncomputable def reindexedLowerMatrixUnit :
    Matrix (Fin (∑ k : Fin 2, cubePhaseBondDim k))
      (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ :=
  Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv lowerMatrixUnit

private lemma blockTransferSum_lowerMatrixUnit :
    blockTransferSum cubePhaseBlock lowerMatrixUnit =
      primitiveCubeRoot • lowerMatrixUnit := by
  ext ⟨i, ii⟩ ⟨j, jj⟩
  change
    (blockTransferSum cubePhaseBlock lowerMatrixUnit).submatrix
        (blockIncl i cubePhaseBondDim) (blockIncl j cubePhaseBondDim) ii jj =
      (primitiveCubeRoot • lowerMatrixUnit).submatrix
        (blockIncl i cubePhaseBondDim) (blockIncl j cubePhaseBondDim) ii jj
  rw [show
    (blockTransferSum cubePhaseBlock lowerMatrixUnit).submatrix
        (blockIncl i cubePhaseBondDim) (blockIncl j cubePhaseBondDim) =
      mixedTransferMap₂ (cubePhaseBlock i) (cubePhaseBlock j)
        (lowerMatrixUnit.submatrix
          (blockIncl i cubePhaseBondDim) (blockIncl j cubePhaseBondDim)) by
    simpa only [blockTransferSum] using
      blockDiagonal'_transferSum_toBlock cubePhaseBlock lowerMatrixUnit i j]
  fin_cases i <;> fin_cases ii <;> fin_cases j <;> fin_cases jj <;>
    simp [cubePhaseBlock, lowerMatrixUnit, cubePhaseWeight, cubePhaseBondDim,
      blockIncl, scalarUnitTensor]

private lemma transferMap_lowerMatrixUnit :
    transferMap cubePhaseTensor reindexedLowerMatrixUnit =
      primitiveCubeRoot • reindexedLowerMatrixUnit := by
  rw [cubePhaseTensor_eq_directSum, reindexedLowerMatrixUnit,
    transferMap_directSumTensor_reindex, blockTransferSum_lowerMatrixUnit]
  ext i j
  simp

private lemma transferMap_pow_lowerMatrixUnit (n : ℕ) :
    (transferMap cubePhaseTensor ^ n) reindexedLowerMatrixUnit =
      primitiveCubeRoot ^ n • reindexedLowerMatrixUnit := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, Module.End.mul_apply, transferMap_lowerMatrixUnit,
        map_smul, ih, smul_smul, pow_succ, mul_comm]

private theorem primitiveCubeRoot_isPrimitiveRoot :
    IsPrimitiveRoot primitiveCubeRoot 3 := by
  simpa [primitiveCubeRoot, mul_assoc] using
    Complex.isPrimitiveRoot_exp 3 (by norm_num)

private lemma two_pow_even_mod_three (n : ℕ) : 2 ^ (2 * n) % 3 = 1 := by
  have h := Nat.ModEq.pow n (show 4 ≡ 1 [MOD 3] by decide)
  simpa [Nat.ModEq, pow_mul] using h

private lemma two_pow_odd_mod_three (n : ℕ) : 2 ^ (2 * n + 1) % 3 = 2 := by
  rw [pow_add, pow_one, Nat.mul_mod, two_pow_even_mod_three]

private lemma primitiveCubeRoot_two_pow_even (n : ℕ) :
    primitiveCubeRoot ^ (2 ^ (2 * n)) = primitiveCubeRoot := by
  rw [pow_eq_pow_mod _ primitiveCubeRoot_isPrimitiveRoot.pow_eq_one,
    two_pow_even_mod_three, pow_one]

private lemma primitiveCubeRoot_two_pow_odd (n : ℕ) :
    primitiveCubeRoot ^ (2 ^ (2 * n + 1)) = primitiveCubeRoot ^ 2 := by
  rw [pow_eq_pow_mod _ primitiveCubeRoot_isPrimitiveRoot.pow_eq_one,
    two_pow_odd_mod_three]

private theorem primitiveCubeRoot_two_pow_not_tendsto (z : ℂ) :
    ¬ Tendsto (fun n : ℕ => primitiveCubeRoot ^ (2 ^ n)) atTop (𝓝 z) := by
  intro h
  have heven : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hodd : Tendsto (fun n : ℕ => 2 * n + 1) atTop atTop := by
    refine tendsto_atTop.2 fun b => ?_
    filter_upwards [eventually_ge_atTop b] with a ha
    omega
  have hzEven : z = primitiveCubeRoot := by
    have he := h.comp heven
    have he' : Tendsto (fun _ : ℕ => primitiveCubeRoot) atTop (𝓝 z) :=
      he.congr' (Filter.Eventually.of_forall fun n => primitiveCubeRoot_two_pow_even n)
    exact tendsto_nhds_unique he' tendsto_const_nhds
  have hzOdd : z = primitiveCubeRoot ^ 2 := by
    have ho := h.comp hodd
    have ho' : Tendsto (fun _ : ℕ => primitiveCubeRoot ^ 2) atTop (𝓝 z) :=
      ho.congr' (Filter.Eventually.of_forall fun n => primitiveCubeRoot_two_pow_odd n)
    exact tendsto_nhds_unique ho' tendsto_const_nhds
  have hpows : primitiveCubeRoot ^ 1 = primitiveCubeRoot ^ 2 := by
    simpa [pow_one] using hzEven.symm.trans hzOdd
  have : (1 : ℕ) = 2 :=
    primitiveCubeRoot_isPrimitiveRoot.pow_inj (by norm_num) (by norm_num) hpows
  omega

private theorem scalarUnitTensor_transferMap :
    transferMap scalarUnitTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [transferMap_apply, scalarUnitTensor]

private theorem scalarUnitTensor_isNormalTensor :
    IsNormalTensor scalarUnitTensor :=
  isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    scalarUnitTensor scalarUnitTensor_transferMap

/-- Canonical-form data for the two scalar normal blocks with weights `1` and
`primitiveCubeRoot`.

Source: arXiv:1606.00608, equations `eq:II_ABasicTensors` and `II_CF1`, lines 219--246. -/
noncomputable def cubePhaseCanonicalData : CPSVCanonicalFormData cubePhaseTensor := by
  exact CPSVCanonicalFormData.ofBlocks
    (fun _ => by simp) cubePhaseWeight (fun _ => scalarUnitTensor)
    (fun _ => scalarUnitTensor_isNormalTensor)

private theorem cubePhaseCanonicalData_isWeightNormalized :
    cubePhaseCanonicalData.IsWeightNormalized := by
  refine {
    weight_norm_le_one := ?_
    weight_unit_exists := ?_ }
  · change ∀ k : Fin 2, ‖cubePhaseWeight k‖ ≤ 1
    intro k
    fin_cases k
    · simp [cubePhaseWeight]
    · simp [cubePhaseWeight, primitiveCubeRoot, Complex.norm_exp, Complex.mul_re]
  · change cubePhaseTensor ≠ 0 → ∃ k : Fin 2, ‖cubePhaseWeight k‖ = 1
    intro _
    exact ⟨0, by simp [cubePhaseWeight]⟩

/-- A normalized CPSV canonical-form tensor whose dyadically iterated transfer maps do not
converge pointwise.

The lower off-diagonal matrix unit is an eigenvector with eigenvalue `primitiveCubeRoot`; its
dyadic orbit alternates between the distinct phases `primitiveCubeRoot` and
`primitiveCubeRoot ^ 2`. This disproves the unrestricted convergence assertion in
arXiv:1606.00608, Appendix B, lines 1211--1244.

See `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`. -/
theorem cubePhaseTensor_not_tendsto_dyadic_transferMap :
    IsCPSVCanonicalForm cubePhaseTensor ∧
      cubePhaseCanonicalData.IsWeightNormalized ∧
      ¬ (∃ E :
        Matrix (Fin (∑ k : Fin 2, cubePhaseBondDim k))
            (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ →
          Matrix (Fin (∑ k : Fin 2, cubePhaseBondDim k))
            (Fin (∑ k : Fin 2, cubePhaseBondDim k)) ℂ,
        ∀ ρ, Tendsto (fun n : ℕ => (transferMap cubePhaseTensor ^ (2 ^ n)) ρ)
          atTop (𝓝 (E ρ))) := by
  refine ⟨cubePhaseCanonicalData.isCPSVCanonicalForm,
    cubePhaseCanonicalData_isWeightNormalized, ?_⟩
  rintro ⟨E, hE⟩
  let row : Fin (∑ k : Fin 2, cubePhaseBondDim k) := finSigmaFinEquiv ⟨1, 0⟩
  let col : Fin (∑ k : Fin 2, cubePhaseBondDim k) := finSigmaFinEquiv ⟨0, 0⟩
  have hrow := tendsto_pi_nhds.mp (hE reindexedLowerMatrixUnit) row
  have hentry := tendsto_pi_nhds.mp hrow col
  simp_rw [transferMap_pow_lowerMatrixUnit] at hentry
  apply primitiveCubeRoot_two_pow_not_tendsto (E reindexedLowerMatrixUnit row col)
  simpa only [Matrix.smul_apply, smul_eq_mul, reindexedLowerMatrixUnit,
    Matrix.reindex_apply, Matrix.submatrix_apply, lowerMatrixUnit, row, col,
    Equiv.symm_apply_apply, Matrix.single_apply_same, mul_one] using hentry

end MPSTensor
