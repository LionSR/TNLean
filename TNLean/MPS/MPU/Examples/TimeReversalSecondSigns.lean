/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Examples.TimeReversalTraceSigns
import TNLean.MPS.MPU.StandardFormDoubling
import TNLean.MPS.MPU.StandardFormFromGates
import TNLean.MPS.MPU.TimeReversalSignIntrinsic
import TNLean.Algebra.MonomialMatrix


/-!
# Second time-reversal signs of the example standard forms

For the four gate pairs `(u, v)` of the time-reversal examples of arXiv:1703.09188
(lines 1906--1962), let `W` be the tensor in standard form built from `u` and `v`. The second
sign `σ⁽²⁾` is the normalized intrinsic trace of the two-site periodic operator of the blocking
of `W` (equation `eq:sigma-from-trace`, lines 1595--1611):

| `u` | `v` | `σ⁽²⁾` |
|---|---|---|
| `CZ (X ⊗ X)` | `CZ` | `-1` |
| `1` | `1` | `1` |
| `i 1` | `1` | `1` |
| `i CZ (X ⊗ X)` | `CZ` | `-1` |

Here `W` plays the role of the two-site block `𝒰₂` of the convention of
`TwoSiteStandardFormData.timeReversalSign_blocking_parity`, so `σ⁽²⁾` is the intrinsic sign of
the four-site blocking of the underlying MPU.

The sign is computed from the doubled standard form of `W`
(`TwoSiteStandardFormData.doubled`): all gates are monomial matrices with integer phases, so the
trace is a signed count of fixed points of a permutation of `256` configurations, evaluated
exactly over `ℤ`. A scalar `c` on `u` enters the doubled unshifted gate as `c²`, hence the trace
as `c⁴`; this gives the last two values from the first two.

## Main results

* `MPOTensor.TimeReversalExamples.intrinsicTimeReversalSign_blockTwo_czx`,
  `intrinsicTimeReversalSign_blockTwo_one`, `intrinsicTimeReversalSign_blockTwo_I_smul_one`,
  `intrinsicTimeReversalSign_blockTwo_I_smul_czx`: the four second signs.
-/

open scoped Matrix Kronecker
open Matrix

namespace Matrix

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

theorem kronecker_monomial_intCast (σ : Equiv.Perm ι) (τ : Equiv.Perm κ) (f : ι → ℤ)
    (g : κ → ℤ) :
    monomial σ (fun s ↦ (f s : ℂ)) ⊗ₖ monomial τ (fun s ↦ (g s : ℂ)) =
      monomial (σ.prodCongr τ) (fun p ↦ ((f p.1 * g p.2 : ℤ) : ℂ)) := by
  ext ⟨t₁, t₂⟩ ⟨s₁, s₂⟩
  simp only [kroneckerMap_apply, monomial_apply, Equiv.prodCongr_apply, Prod.map,
    Prod.mk.injEq, Int.cast_mul]
  by_cases h₁ : t₁ = σ s₁ <;> by_cases h₂ : t₂ = τ s₂ <;> simp [h₁, h₂]

theorem submatrix_monomial_intCast {μ : Type*} [DecidableEq μ] (e f : μ ≃ ι)
    (σ : Equiv.Perm ι) (φ : ι → ℤ) :
    (monomial σ (fun s ↦ (φ s : ℂ))).submatrix e f =
      monomial (f.trans (σ.trans e.symm)) (fun s ↦ (φ (f s) : ℂ)) := by
  ext t s
  simp only [submatrix_apply, monomial_apply]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (by simp [Equiv.eq_symm_apply, h₁]) h₂
  · exact absurd (by simpa [Equiv.eq_symm_apply] using h₂) h₁
  · rfl

theorem monomial_mul_monomial_intCast [Fintype ι] (σ τ : Equiv.Perm ι) (f g : ι → ℤ) :
    monomial σ (fun s ↦ (f s : ℂ)) * monomial τ (fun s ↦ (g s : ℂ)) =
      monomial (σ * τ) (fun s ↦ ((f (τ s) * g s : ℤ) : ℂ)) := by
  rw [monomial_mul_monomial]
  simp only [Int.cast_mul]

theorem trace_monomial_intCast [Fintype ι] (σ : Equiv.Perm ι) (f : ι → ℤ) :
    trace (monomial σ (fun s ↦ (f s : ℂ))) =
      ((∑ s, if σ s = s then f s else 0 : ℤ) : ℂ) := by
  rw [trace_monomial]
  push_cast
  rfl

theorem one_eq_monomial_intCast : (1 : Matrix ι ι ℂ) = monomial 1 (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  rw [Int.cast_one, monomial_one]

end Matrix

namespace MPOTensor

namespace TimeReversalExamples

variable {d : ℕ}

/-- Regrouping of four sites `(12)(34)` as `1(23)4`. -/
private def middleRegroup (A B C E : Type*) : (A × B) × (C × E) ≃ (A × (B × C)) × E where
  toFun x := ((x.1.1, (x.1.2, x.2.1)), x.2.2)
  invFun y := ((y.1.1, y.1.2.1), (y.1.2.2, y.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem staircaseMiddle_monomial (σ : Equiv.Perm (Fin d × Fin d))
    (φ : Fin d × Fin d → ℤ) :
    staircaseMiddle (A := Fin d) (E := Fin d) (monomial σ (fun s ↦ (φ s : ℂ))) =
      monomial ((middleRegroup _ _ _ _).trans
          ((((1 : Equiv.Perm (Fin d)).prodCongr σ).prodCongr 1).trans
            (middleRegroup _ _ _ _).symm))
        (fun s ↦ ((1 * φ (s.1.2, s.2.1) * 1 : ℤ) : ℂ)) := by
  have h : staircaseMiddle (A := Fin d) (E := Fin d) (monomial σ (fun s ↦ (φ s : ℂ))) =
      ((((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ monomial σ (fun s ↦ (φ s : ℂ))) ⊗ₖ
        (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix (middleRegroup _ _ _ _)
          (middleRegroup _ _ _ _) := rfl
  rw [h, one_eq_monomial_intCast, kronecker_monomial_intCast, kronecker_monomial_intCast,
    submatrix_monomial_intCast]
  rfl

private theorem pairSwap_eq_monomial :
    Matrix.reindex (finProdFinEquiv.prodCongr finProdFinEquiv).symm
      (finProdFinEquiv.prodCongr finProdFinEquiv).symm (Matrix.swapMatrix (d * d)) =
      monomial (Equiv.prodComm (Fin d × Fin d) (Fin d × Fin d)) (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [reindex_apply, submatrix_apply, Equiv.symm_symm, Equiv.prodCongr_apply,
    Prod.map, swapMatrix_apply, monomial_apply, Equiv.prodComm_apply, Prod.swap,
    Prod.mk.injEq, EmbeddingLike.apply_eq_iff_eq, Int.cast_one]

/-- The doubled shifted gate as a relabelled Kronecker product. -/
private theorem doubledV_eq_submatrix (v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledV v = ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix
      (doubledShiftOutEquiv d).symm (doubledShiftInEquiv d d d).symm := rfl

/-- The doubled unshifted gate as a product of two relabelled Kronecker products. -/
private theorem doubledU_eq_mul (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    doubledU u v =
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (v ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))).submatrix
          (doubledOutEquiv d d d).symm (doubledOutEquiv d d d).symm *
        (u ⊗ₖ u).submatrix ((doubledOutEquiv d d d).symm.trans (doubledMidEquiv d d).symm)
          (doubledInEquiv d).symm := by
  rw [doubledU, reindex_apply, ← submatrix_mul_equiv _ _ _ (doubledOutEquiv d d d).symm]
  rfl

private theorem controlledZ_eq_monomial :
    controlledZ = monomial 1 (fun p ↦ ((if p = (1, 1) then -1 else 1 : ℤ) : ℂ)) := by
  ext p q
  simp only [controlledZ, diagonal_apply, monomial_apply, Equiv.Perm.coe_one, id_eq]
  split_ifs <;> simp_all

private theorem pauliXX_eq_monomial :
    pauliX ⊗ₖ pauliX = monomial ((Equiv.swap (0 : Fin 2) 1).prodCongr (Equiv.swap 0 1))
      (fun _ ↦ ((1 : ℤ) : ℂ)) := by
  ext ⟨a, b⟩ ⟨c, e⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases e <;>
    simp [pauliX, monomial_apply]

/-- A scalar on the unshifted gate enters the doubled unshifted gate squared. -/
private theorem doubledU_smul_left {ℓ r : ℕ} (c : ℂ) (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ)
    (v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ) :
    doubledU (c • u) v = (c * c) • doubledU u v := by
  rw [doubledU, doubledU, smul_kronecker, kronecker_smul, smul_smul]
  ext i j
  simp only [reindex_apply, submatrix_apply, Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul,
    Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ ↦ mul_left_comm _ _ _

/-- The time-reversal sign of the doubled gates of `CZ (X ⊗ X)` and `CZ`. -/
private theorem timeReversalSign_doubled_czx :
    timeReversalSign (doubledU (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ)
      (doubledV controlledZ) = -1 := by
  rw [timeReversalSign, timeReversalTrace, doubledU_eq_mul, doubledV_eq_submatrix,
    controlledZ_eq_monomial, pauliXX_eq_monomial, monomial_mul_monomial_intCast]
  simp only [one_eq_monomial_intCast, kronecker_monomial_intCast, submatrix_monomial_intCast,
    monomial_mul_monomial_intCast, pairSwap_eq_monomial, staircaseMiddle_monomial,
    trace_monomial_intCast]
  have h : ∀ n : ℤ, n = -16 → (((2 * 2 * (2 * 2) : ℕ) : ℂ))⁻¹ * (n : ℂ) = -1 := by
    rintro n rfl
    norm_num
  apply h
  decide +kernel

/-- The time-reversal sign of the doubled gates of `1` and `1`. -/
private theorem timeReversalSign_doubled_one :
    timeReversalSign (doubledU (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1)
      (doubledV 1) = 1 := by
  rw [timeReversalSign, timeReversalTrace, doubledU_eq_mul, doubledV_eq_submatrix]
  simp only [one_eq_monomial_intCast, kronecker_monomial_intCast, submatrix_monomial_intCast,
    monomial_mul_monomial_intCast, pairSwap_eq_monomial, staircaseMiddle_monomial,
    trace_monomial_intCast]
  have h : ∀ n : ℤ, n = 16 → (((2 * 2 * (2 * 2) : ℕ) : ℂ))⁻¹ * (n : ℂ) = 1 := by
    rintro n rfl
    norm_num
  apply h
  decide +kernel

private theorem isUnitaryBetween_monomial {ι : Type*} [Fintype ι] [DecidableEq ι]
    (σ : Equiv.Perm ι) (φ : ι → ℂ) (h : ∀ s, star (φ s) * φ s = 1) :
    (monomial σ φ).IsUnitaryBetween :=
  (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (monomial_mem_unitaryGroup σ φ h)

private theorem isUnitaryBetween_controlledZ : controlledZ.IsUnitaryBetween := by
  rw [controlledZ_eq_monomial]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by split_ifs <;> simp

private theorem isUnitaryBetween_czx : (controlledZ * (pauliX ⊗ₖ pauliX)).IsUnitaryBetween := by
  rw [controlledZ_eq_monomial, pauliXX_eq_monomial, monomial_mul_monomial_intCast]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by split_ifs <;> simp

private theorem isUnitaryBetween_one :
    (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ).IsUnitaryBetween := by
  rw [one_eq_monomial_intCast]
  exact isUnitaryBetween_monomial _ _ fun s ↦ by simp

private theorem isUnitaryBetween_I_smul {M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ}
    (hM : M.IsUnitaryBetween) : (Complex.I • M).IsUnitaryBetween := by
  rw [isUnitaryBetween_iff_mem_unitaryGroup, mem_unitaryGroup_iff] at *
  rw [star_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hM]
  simp [Complex.conj_I]

/-! ### The second signs -/

/-- **CZX, second sign.** -/
theorem intrinsicTimeReversalSign_blockTwo_czx :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (controlledZ * (pauliX ⊗ₖ pauliX)) controlledZ)) = -1 := by
  rw [← (standardFormTensorOfGatesData _ _ isUnitaryBetween_czx
    isUnitaryBetween_controlledZ).doubled.timeReversalSign_eq_intrinsic]
  exact timeReversalSign_doubled_czx

theorem intrinsicTimeReversalSign_blockTwo_one :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) 1)) = 1 := by
  rw [← (standardFormTensorOfGatesData _ _ isUnitaryBetween_one
    isUnitaryBetween_one).doubled.timeReversalSign_eq_intrinsic]
  exact timeReversalSign_doubled_one

theorem intrinsicTimeReversalSign_blockTwo_I_smul_one :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (Complex.I • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ))
        1)) = 1 := by
  rw [← (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_one)
    isUnitaryBetween_one).doubled.timeReversalSign_eq_intrinsic, doubledU_smul_left,
    timeReversalSign_smul_left, timeReversalSign_doubled_one]
  simp

theorem intrinsicTimeReversalSign_blockTwo_I_smul_czx :
    intrinsicTimeReversalSign (MPOTensor.blockTwo
      (standardFormTensorOfGates (Complex.I • (controlledZ * (pauliX ⊗ₖ pauliX)))
        controlledZ)) = -1 := by
  rw [← (standardFormTensorOfGatesData _ _ (isUnitaryBetween_I_smul isUnitaryBetween_czx)
    isUnitaryBetween_controlledZ).doubled.timeReversalSign_eq_intrinsic, doubledU_smul_left,
    timeReversalSign_smul_left, timeReversalSign_doubled_czx]
  simp

end TimeReversalExamples

end MPOTensor
