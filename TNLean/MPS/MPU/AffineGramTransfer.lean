/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Algebra.KroneckerFactorPositivity
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Density-weighted Gram transfer for MPU intervals

This file records the finite matrix identities used in the affine determinant
normalization in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. The physical input state
may be entangled across all sites of an interval. Testing every density matrix
determines the entire input Gram matrix, including its off-diagonal entries.

The determinant maximization and the resulting circuit theorem are separate
assertions and are not claimed to be formalized in this file.
-/

open Matrix
open scoped Matrix ComplexOrder Kronecker

namespace MPUCircuit

variable {o i l m : Type*} [Fintype o] [Fintype i] [Fintype l] [Fintype m]

/-- Transfer of a left bond Gram by an interval with density-weighted physical
input. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def intervalGramTransfer (A : o → i → Matrix l m ℂ)
    (ρ : Matrix i i ℂ) (P : Matrix l l ℂ) : Matrix m m ℂ :=
  ∑ a, ∑ b, ∑ c, ρ c b • ((A a b)ᴴ * P * A a c)

/-- A prefix has a one-dimensional left virtual bond; its input density
determines the Gram on its right virtual bond. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def prefixInputGram (F : o → i → Matrix Unit m ℂ)
    (ρ : Matrix i i ℂ) : Matrix m m ℂ :=
  intervalGramTransfer F ρ 1

/-- Transfer is linear in the left Gram. In particular it respects the real
affine combinations used in the determinant normalization. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def intervalGramTransferLinearMap (A : o → i → Matrix l m ℂ)
    (ρ : Matrix i i ℂ) : Matrix l l ℂ →ₗ[ℂ] Matrix m m ℂ where
  toFun := intervalGramTransfer A ρ
  map_add' P P' := by
    simp only [intervalGramTransfer, Matrix.mul_add, Matrix.add_mul, smul_add,
      Finset.sum_add_distrib]
  map_smul' c P := by
    simp only [intervalGramTransfer, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, RingHom.id_apply, Finset.smul_sum]
    simp only [mul_comm]

/-- The physical input Gram obtained by closing both virtual bonds of an
interval. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def intervalInputGram (A : o → i → Matrix l m ℂ)
    (P : Matrix l l ℂ) (Q : Matrix m m ℂ) : Matrix i i ℂ :=
  fun b c ↦ ∑ a, trace ((A a b)ᴴ * P * A a c * Q)

/-- Density-weighted transfer composes under concatenation. Taking the first
left bond to be one-dimensional gives exactly the prefix Gram identity for
`ρ ⊗ σ`. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalGramTransfer_concat
    {o' i' n : Type*} [Fintype o'] [Fintype i']
    (A : o → i → Matrix l m ℂ) (B : o' → i' → Matrix m n ℂ)
    (ρ : Matrix i i ℂ) (σ : Matrix i' i' ℂ) (P : Matrix l l ℂ) :
    intervalGramTransfer (fun (a : o × o') (b : i × i') ↦
      A a.1 b.1 * B a.2 b.2) (ρ ⊗ₖ σ) P =
      intervalGramTransfer B σ (intervalGramTransfer A ρ P) := by
  classical
  let e : ((o × o') × ((i × i') × (i × i'))) ≃
      ((o' × (i' × i')) × (o × (i × i))) :=
    { toFun := fun x ↦ ((x.1.2, (x.2.1.2, x.2.2.2)),
        (x.1.1, (x.2.1.1, x.2.2.1)))
      invFun := fun x ↦ ((x.2.1, x.1.1),
        ((x.2.2.1, x.1.2.1), (x.2.2.2, x.1.2.2)))
      left_inv := by rintro ⟨⟨a, a'⟩, ⟨⟨b, b'⟩, ⟨c, c'⟩⟩⟩; rfl
      right_inv := by rintro ⟨⟨a', ⟨b', c'⟩⟩, ⟨a, ⟨b, c⟩⟩⟩; rfl }
  have hsum := Fintype.sum_equiv e
    (fun x ↦ (ρ x.2.2.1 x.2.1.1 * σ x.2.2.2 x.2.1.2) •
      ((A x.1.1 x.2.1.1 * B x.1.2 x.2.1.2)ᴴ * P *
        (A x.1.1 x.2.2.1 * B x.1.2 x.2.2.2)))
    (fun x ↦ σ x.1.2.2 x.1.2.1 •
      ((B x.1.1 x.1.2.1)ᴴ *
        (ρ x.2.2.2 x.2.2.1 • ((A x.2.1 x.2.2.1)ᴴ * P * A x.2.1 x.2.2.2)) *
          B x.1.1 x.1.2.2)) (by
      intro x
      simp only [e, Equiv.coe_fn_mk, conjTranspose_mul, Matrix.mul_assoc,
        Matrix.mul_smul, Matrix.smul_mul, smul_smul]
      rw [mul_comm (ρ x.2.2.1 x.2.1.1) (σ x.2.2.2 x.2.1.2)])
  simpa only [Fintype.sum_prod_type, intervalGramTransfer, kronecker_apply,
    Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum] using hsum

/-- The prefix Gram of a product input density is the interval transfer of
the earlier prefix Gram. Neither density is restricted to product states
inside its own physical interval. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixInputGram_concat {o' i' n : Type*}
    [Fintype o'] [Fintype i']
    (F : o → i → Matrix Unit m ℂ) (A : o' → i' → Matrix m n ℂ)
    (ρ : Matrix i i ℂ) (σ : Matrix i' i' ℂ) :
    prefixInputGram (fun (a : o × o') (b : i × i') ↦ F a.1 b.1 * A a.2 b.2)
      (ρ ⊗ₖ σ) = intervalGramTransfer A σ (prefixInputGram F ρ) := by
  exact intervalGramTransfer_concat F A ρ σ 1

/-- Closing a density-weighted transfer is the trace pairing with the full
physical input Gram. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem trace_intervalGramTransfer (A : o → i → Matrix l m ℂ)
    (ρ : Matrix i i ℂ) (P : Matrix l l ℂ) (Q : Matrix m m ℂ) :
    trace (Q * intervalGramTransfer A ρ P) = trace (ρ * intervalInputGram A P Q) := by
  classical
  rw [trace_mul_comm Q]
  simp only [intervalGramTransfer, Matrix.sum_mul, trace_sum, Matrix.smul_mul, trace_smul,
    smul_eq_mul]
  change (∑ a, ∑ b, ∑ c, ρ c b * trace ((A a b)ᴴ * P * A a c * Q)) = _
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext b
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  simp only [trace, diag, mul_apply, intervalInputGram, Finset.mul_sum]

/-- Density matrices separate complex matrix quadratic forms. No Hermitian
hypothesis on the tested matrix is needed. Source: the all-density tests in
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem eq_one_of_trace_density_mul_eq_one [DecidableEq i] {K : Matrix i i ℂ}
    (hK : ∀ ρ : Matrix i i ℂ, ρ.PosSemidef → trace ρ = 1 → trace (ρ * K) = 1) :
    K = 1 := by
  classical
  have hquad (v : i → ℂ) : star v ⬝ᵥ K *ᵥ v = star v ⬝ᵥ v := by
    by_cases hv : v = 0
    · simp [hv]
    let S : Matrix i i ℂ := vecMulVec v (star v)
    have hS : S.PosSemidef := posSemidef_vecMulVec_self_star v
    have ht : trace S ≠ 0 := by
      simpa [S, trace_vecMulVec, dotProduct_comm] using
        mt (dotProduct_star_self_eq_zero (v := v)).mp hv
    have hρ := hK ((trace S)⁻¹ • S) (hS.smul (inv_nonneg.mpr hS.trace_nonneg))
      (by simp [trace_smul, ht])
    have htrace : trace (S * K) = trace S := by
      rw [smul_mul, trace_smul, smul_eq_mul] at hρ
      exact (inv_mul_eq_iff_eq_mul₀ ht).mp hρ |>.trans (mul_one _)
    rw [show S = vecMulVec v (star v) from rfl, vecMulVec_mul,
      trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec] at htrace
    simpa [S, trace_vecMulVec, dotProduct_comm] using htrace
  have hzero : K - 1 = 0 := eq_zero_of_forall_star_dotProduct_mulVec_eq_zero fun v ↦ by
    simp only [sub_mulVec, dotProduct_sub, one_mulVec, hquad, sub_self]
  exact sub_eq_zero.mp hzero

/-- Every density-matrix normalization identity determines all entries of the
physical input Gram. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalInputGram_eq_one_of_density_tests [DecidableEq i]
    (A : o → i → Matrix l m ℂ) (P : Matrix l l ℂ) (Q : Matrix m m ℂ)
    (h : ∀ ρ : Matrix i i ℂ, ρ.PosSemidef → trace ρ = 1 →
      trace (Q * intervalGramTransfer A ρ P) = 1) :
    intervalInputGram A P Q = 1 := by
  apply eq_one_of_trace_density_mul_eq_one
  intro ρ hρ htrace
  rw [← trace_intervalGramTransfer]
  exact h ρ hρ htrace

/-- The interval map obtained by vectorizing both weighted virtual bonds.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
noncomputable def vectorizedWeightedInterval (A : o → i → Matrix l m ℂ)
    (L : Matrix l l ℂ) (R : Matrix m m ℂ) : Matrix (o × (m × l)) i ℂ :=
  fun p b ↦ vec (L * A p.1 b * R) p.2

omit [Fintype i] in
/-- The vectorized interval Gram is the trace-closed virtual Gram. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem vectorizedWeightedInterval_gram (A : o → i → Matrix l m ℂ)
    (L : Matrix l l ℂ) (R : Matrix m m ℂ) :
    (vectorizedWeightedInterval A L R)ᴴ * vectorizedWeightedInterval A L R =
      intervalInputGram A (Lᴴ * L) (R * Rᴴ) := by
  classical
  ext b c
  simp only [mul_apply, conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  change (∑ a, star (vec (L * A a b * R)) ⬝ᵥ vec (L * A a c * R)) = _
  simp_rw [star_vec_dotProduct_vec]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = trace (Rᴴ * ((A a b)ᴴ * (Lᴴ * L) * A a c) * R) := by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    _ = _ := by
      rw [trace_mul_cycle']
      simp only [Matrix.mul_assoc]

/-- Density tests imply that the explicit vectorized interval map is an
isometry. The conclusion includes the off-diagonal Gram entries. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem vectorizedWeightedInterval_isometry_of_density_tests [DecidableEq i]
    (A : o → i → Matrix l m ℂ) (L : Matrix l l ℂ) (R : Matrix m m ℂ)
    (h : ∀ ρ : Matrix i i ℂ, ρ.PosSemidef → trace ρ = 1 →
      trace ((R * Rᴴ) * intervalGramTransfer A ρ (Lᴴ * L)) = 1) :
    (vectorizedWeightedInterval A L R)ᴴ * vectorizedWeightedInterval A L R = 1 := by
  rw [vectorizedWeightedInterval_gram]
  exact intervalInputGram_eq_one_of_density_tests A (Lᴴ * L) (R * Rᴴ) h

end MPUCircuit
