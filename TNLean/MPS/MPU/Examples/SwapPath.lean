/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Topology.Instances.Matrix
import QICLean.Channel.MaximallyEntangled

/-!
# A continuous unitary path to the factor swap

arXiv:1703.09188 requires a continuous unitary interpolation from the identity
matrix to the factor swap in Proposition `prop:U2-U3-trivial-tr-transpose`,
lines 2143--2155, and Proposition `prop:U1-U2-equiv-ancillatrick`, lines
2226--2235.

The factor swap acts by `Matrix.swapMatrix d`. We give a concrete interpolation
by decomposing the tensor-square space into its symmetric and antisymmetric
subspaces and rotating only the antisymmetric subspace by the phase
`exp (π x I)`.
-/

open scoped ComplexConjugate Matrix

namespace Matrix

variable (d : ℕ)

/-- The orthogonal projection onto the symmetric subspace of the tensor square. -/
noncomputable def swapSymmetricProjection :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  (2 : ℂ)⁻¹ • (1 + swapMatrix d)

/-- The orthogonal projection onto the antisymmetric subspace of the tensor square. -/
noncomputable def swapAntisymmetricProjection :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  1 - swapSymmetricProjection d

/-- The symmetric-subspace projection is self-adjoint and idempotent. -/
theorem isStarProjection_swapSymmetricProjection :
    IsStarProjection (swapSymmetricProjection d) := by
  rw [isStarProjection_iff']
  constructor
  · unfold swapSymmetricProjection
    rw [Matrix.smul_mul, Matrix.mul_smul, add_mul, one_mul, mul_add, mul_one,
      swapMatrix_mul_self]
    module
  · change (swapSymmetricProjection d)ᴴ = swapSymmetricProjection d
    simp [swapSymmetricProjection, swapMatrix_conjTranspose]

/-- The antisymmetric-subspace projection is self-adjoint and idempotent. -/
theorem isStarProjection_swapAntisymmetricProjection :
    IsStarProjection (swapAntisymmetricProjection d) := by
  exact (isStarProjection_swapSymmetricProjection d).one_sub

/-- The unit complex phase used on the antisymmetric subspace. -/
noncomputable def swapPhase (x : ℝ) : ℂ :=
  Complex.exp ((Real.pi * x : ℝ) * Complex.I)

/-- The swap phase times its complex conjugate is one. -/
theorem swapPhase_mul_star (x : ℝ) :
    swapPhase x * star (swapPhase x) = 1 := by
  change Complex.exp ((Real.pi * x : ℝ) * Complex.I) *
    conj (Complex.exp ((Real.pi * x : ℝ) * Complex.I)) = 1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq,
    Complex.norm_exp_ofReal_mul_I]
  norm_num

/-- A concrete path from the identity to the factor swap.

It acts as the identity on the symmetric subspace and by `exp (π x I)` on the
antisymmetric subspace. This realizes the interpolation required in
arXiv:1703.09188, lines 2148--2151 and 2229--2234. -/
noncomputable def swapPath (x : ℝ) :
    Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ :=
  swapSymmetricProjection d + swapPhase x • swapAntisymmetricProjection d

/-- Applying a unit-modulus phase to the complement of a star projection is unitary. -/
private theorem projection_add_phase_complement_mem_unitaryGroup
    {n : Type*} [Fintype n] [DecidableEq n]
    (p : Matrix n n ℂ) (hp : IsStarProjection p) (c : ℂ)
    (hc : c * star c = 1) :
    p + c • (1 - p) ∈ unitaryGroup n ℂ := by
  rw [mem_unitaryGroup_iff]
  have hq := hp.one_sub
  have hpH : pᴴ = p := by
    rw [← Matrix.star_eq_conjTranspose, hp.isSelfAdjoint.star_eq]
  have hqH : (1 - p)ᴴ = 1 - p := by
    rw [← Matrix.star_eq_conjTranspose, hq.isSelfAdjoint.star_eq]
  rw [Matrix.star_eq_conjTranspose, conjTranspose_add, conjTranspose_smul,
    hpH, hqH]
  rw [mul_add, add_mul, hp.isIdempotentElem.eq,
    Matrix.smul_mul, hp.one_sub_mul_self, smul_zero,
    Matrix.mul_smul, add_mul, hp.mul_one_sub_self,
    Matrix.smul_mul, hq.isIdempotentElem.eq, zero_add,
    smul_smul, mul_comm (star c) c, hc, one_smul]
  module

/-- Every matrix on the swap path is unitary. -/
theorem swapPath_mem_unitaryGroup (x : ℝ) :
    swapPath d x ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  exact projection_add_phase_complement_mem_unitaryGroup
    (swapSymmetricProjection d) (isStarProjection_swapSymmetricProjection d)
    (swapPhase x) (swapPhase_mul_star x)

/-- The path starts at the identity matrix. -/
@[simp] theorem swapPath_zero : swapPath d 0 = 1 := by
  simp [swapPath, swapPhase, swapAntisymmetricProjection]

/-- The path ends at the factor-swap matrix. -/
@[simp] theorem swapPath_one : swapPath d 1 = swapMatrix d := by
  rw [swapPath, swapPhase, show (Real.pi * (1 : ℝ) : ℝ) = Real.pi by ring,
    Complex.exp_pi_mul_I]
  simp only [neg_smul, one_smul, swapAntisymmetricProjection,
    swapSymmetricProjection]
  module

/-- The explicit matrix-valued swap path is continuous. -/
theorem continuous_swapPath : Continuous (swapPath d) := by
  apply continuous_const.add
  exact (Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_const.mul continuous_id)).mul
      continuous_const)).smul continuous_const

/-- There is a continuous unitary path from the identity to the factor swap.

This supplies the operator $\mathbb S(x)$ required in arXiv:1703.09188,
Proposition `prop:U2-U3-trivial-tr-transpose`, lines 2148--2151, and reused in
Proposition `prop:U1-U2-equiv-ancillatrick`, lines 2229--2234. -/
theorem exists_continuous_unitary_swapPath :
    ∃ S : ℝ → Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ,
      Continuous S ∧ S 0 = 1 ∧ S 1 = swapMatrix d ∧
        ∀ x : ℝ, S x ∈ unitaryGroup (Fin d × Fin d) ℂ := by
  exact ⟨swapPath d, continuous_swapPath d, swapPath_zero d,
    swapPath_one d, swapPath_mem_unitaryGroup d⟩

end Matrix
