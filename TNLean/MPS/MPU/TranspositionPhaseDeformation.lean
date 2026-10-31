/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.TwoSiteStandardForm
import TNLean.MPS.MPU.StaircaseGates
import TNLean.MPS.MPDO.SimpleScaling
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic.FunProp

/-!
# Removing the local transposition phase along actual standard forms

The explicit path multiplies the unshifted gate and its tensor by
exp(-itφ/2), retaining the shifted gate and both half factors. Its local phase
is exp(i(1-t)φ). The periodic operators remain unitary, and every transpose
symmetry of the original periodic family is preserved at the same lengths.
No continuous choice of a phase argument or of source factors is required.

Source: arXiv:1703.09188, immediately after `UUtransposetrick`,
`paper_v2.tex` lines 1285–1288. The construction applies directly to any
supplied two-site standard form, independently of the chosen canonical
presentation used to derive the local criterion in the preceding modules.
-/

open scoped Matrix Kronecker BigOperators

namespace MPOTensor

/-- The gate scalar used to remove the local phase in CPSV17,
`paper_v2.tex` lines 1285–1288. -/
noncomputable def transpositionPhaseScalar (φ t : ℝ) : ℂ :=
  Complex.exp (((-(t * φ / 2) : ℝ) : ℂ) * Complex.I)

/-- The phase-removing scalar has unit norm at every real parameter.
Source: CPSV17, lines 1285–1288. -/
theorem norm_transpositionPhaseScalar (φ t : ℝ) :
    ‖transpositionPhaseScalar φ t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- The two unshifted gates change the local phase by the square of their
common scalar. Source: CPSV17, lines 1285–1288. -/
theorem transpositionPhaseScalar_sq_mul (φ t : ℝ) :
    transpositionPhaseScalar φ t ^ 2 * Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((((1 - t) * φ : ℝ) : ℂ) * Complex.I) := by
  rw [transpositionPhaseScalar, pow_two, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The scalar deformation is continuous. Source: CPSV17, lines 1285–1288. -/
theorem continuous_transpositionPhaseScalar (φ : ℝ) :
    Continuous (transpositionPhaseScalar φ) := by
  unfold transpositionPhaseScalar
  fun_prop

/-- The phase-removing path starts at the original scalar.
Source: CPSV17, lines 1285–1288. -/
@[simp] theorem transpositionPhaseScalar_zero (φ : ℝ) :
    transpositionPhaseScalar φ 0 = 1 := by
  simp [transpositionPhaseScalar]

/-- A unit-modulus multiple of a unitary between two coordinate spaces is again unitary,
since `c * star c = 1`. -/
private theorem unitaryBetween_smul_of_norm_eq_one
    {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {A : Matrix a b ℂ} (hA : A.IsUnitaryBetween) (c : ℂ) (hc : ‖c‖ = 1) :
    (c • A).IsUnitaryBetween := by
  have hcc : c * star c = 1 := by
    have h := Complex.mul_conj c
    rw [Complex.normSq_eq_norm_sq, hc] at h
    simpa only [one_pow, Complex.ofReal_one, starRingEnd_apply] using h
  have hcc' : star c * c = 1 := by rw [mul_comm, hcc]
  constructor
  · change (c • A)ᴴ * (c • A) = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcc', one_smul]
    exact hA.1
  · change (c • A) * (c • A)ᴴ = 1
    rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hcc, one_smul]
    exact hA.2

/-- The explicit phase path consists of actual supplied standard forms,
with the original half factors and shifted gate. Source: CPSV17,
`paper_v2.tex` lines 1285–1288. -/
noncomputable def TwoSiteStandardFormData.transpositionPhaseDeformation
    {d D ℓ r : ℕ} {W : MPOTensor (d * d) D}
    {u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ}
    {v : Matrix (Fin d × Fin d) (Fin r × Fin ℓ) ℂ}
    (S : TwoSiteStandardFormData W u v) (φ t : ℝ) :
    TwoSiteStandardFormData (transpositionPhaseScalar φ t • W)
      (transpositionPhaseScalar φ t • u) v where
  phys_pos := S.phys_pos
  bond_pos := S.bond_pos
  left_pos := S.left_pos
  right_pos := S.right_pos
  X₁ := S.X₁
  X₂ := S.X₂
  u_unitary := unitaryBetween_smul_of_norm_eq_one S.u_unitary _
    (norm_transpositionPhaseScalar φ t)
  v_unitary := S.v_unitary
  v_apply := S.v_apply
  W_apply := by
    intro i j α γ
    change transpositionPhaseScalar φ t * W i j α γ = _
    rw [S.W_apply, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    change _ = S.X₂ _ l * (transpositionPhaseScalar φ t * u _ _) * S.X₁ _ r
    ring

/-- Removing the phase preserves exactly the lengths at which the actual
periodic tensor was transpose invariant. Source: CPSV17, lines 1285–1288. -/
theorem mpo_transpositionPhaseDeformation_eq_transpose
    {d D : ℕ} (W : MPOTensor d D) (φ t : ℝ) (N : ℕ)
    (hW : mpo W N = (mpo W N)ᵀ) :
    mpo (transpositionPhaseScalar φ t • W) N =
      (mpo (transpositionPhaseScalar φ t • W) N)ᵀ := by
  rw [mpo_smul, Matrix.transpose_smul, ← hW]

/-- Both the tensor and the unshifted gate vary continuously along the
explicit scalar path. Source: CPSV17, lines 1285–1288. -/
theorem continuous_transpositionPhaseDeformation
    {d D ℓ r : ℕ} (W : MPOTensor (d * d) D)
    (u : Matrix (Fin ℓ × Fin r) (Fin d × Fin d) ℂ) (φ : ℝ) :
    Continuous (fun t : ℝ ↦ transpositionPhaseScalar φ t • W) ∧
      Continuous (fun t : ℝ ↦ transpositionPhaseScalar φ t • u) := by
  exact ⟨(continuous_transpositionPhaseScalar φ).smul continuous_const,
    (continuous_transpositionPhaseScalar φ).smul continuous_const⟩

/-- The original four-spin equation has phase exp(i(1-t)φ) along the
actual gate deformation. Source: CPSV17, `UUtransposetrick` and the following
phase-removal paragraph, lines 1270–1288. -/
theorem transposition_local_phase_deformation
    {d : ℕ} (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (φ t : ℝ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      Complex.exp ((φ : ℂ) * Complex.I) •
        ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
            (staircaseMiddle v)ᵀ) :
    staircaseMiddle (A := Fin d) (E := Fin d) v *
        ((transpositionPhaseScalar φ t • u) ⊗ₖ (transpositionPhaseScalar φ t • u)) =
      Complex.exp ((((1 - t) * φ : ℝ) : ℂ) * Complex.I) •
        ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
            (staircaseMiddle v)ᵀ := by
  simp only [Matrix.smul_kronecker, Matrix.kronecker_smul, Matrix.mul_smul, smul_smul]
  rw [hlocal]
  simp only [Matrix.smul_mul, smul_smul]
  rw [← pow_two, transpositionPhaseScalar_sq_mul]

/-- At the endpoint the local phase is one, with the same virtual unitary
and shifted gate. Source: CPSV17, lines 1285–1288. -/
theorem transposition_local_phase_deformation_one
    {d : ℕ} (u v : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (x : Matrix.unitaryGroup (Fin d × Fin d) ℂ) (φ : ℝ)
    (hlocal : staircaseMiddle (A := Fin d) (E := Fin d) v * (u ⊗ₖ u) =
      Complex.exp ((φ : ℂ) * Complex.I) •
        ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
          (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) *
            (staircaseMiddle v)ᵀ) :
    staircaseMiddle (A := Fin d) (E := Fin d) v *
        ((transpositionPhaseScalar φ 1 • u) ⊗ₖ (transpositionPhaseScalar φ 1 • u)) =
      ((x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) ⊗ₖ
        (x : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)ᵀ) * (staircaseMiddle v)ᵀ := by
  simpa using transposition_local_phase_deformation u v x φ 1 hlocal

end MPOTensor
