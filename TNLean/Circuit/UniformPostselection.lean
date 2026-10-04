/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.ExactSubspaceAmplification
import TNLean.Algebra.ComplexSqrt
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Tactic.Linarith

/-!
# Exact amplification from a uniform postselection probability

Suppose that `V` is an isometry and `P` is an orthogonal projection, and
that `Vᴴ * P * V = p² • 1` for `0 < p < 1`. The normalized successful
and unsuccessful parts of `V` are orthogonal isometries. This decomposition
identifies `V` with the isometric plane used by the two-reflection
amplification argument.

In particular, a uniform success amplitude `sin (π / (4ℓ + 2))` becomes
exact success after `ℓ` rounds. The conclusion concerns the action of a
unitary matrix on an isometric subspace; it does not assert a circuit
synthesis theorem. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.
-/

open scoped Matrix ComplexOrder

namespace Matrix

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The successful part normalized by its uniform amplitude.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def postselectionSuccess (V : Matrix n m ℂ) (P : Matrix n n ℂ) (p : ℝ) :
    Matrix n m ℂ :=
  (p : ℂ)⁻¹ • (P * V)

/-- The unsuccessful part normalized by its complementary amplitude.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def postselectionFailure (V : Matrix n m ℂ) (P : Matrix n n ℂ) (p : ℝ) :
    Matrix n m ℂ :=
  (Real.sqrt (1 - p ^ 2) : ℂ)⁻¹ • ((1 - P) * V)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
private lemma projection_gram (V : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hP : IsStarProjection P) : (P * V)ᴴ * (P * V) = Vᴴ * P * V := by
  have hself : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  simp only [conjTranspose_mul, hself, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc Vᴴ P P, hP.isIdempotentElem.eq]

omit [Fintype m] [DecidableEq n] in
private lemma normalized_projection_gram (V : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hP : IsStarProjection P) (p : ℝ) (hp : p ≠ 0)
    (hprob : Vᴴ * P * V = (p : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    ((p : ℂ)⁻¹ • (P * V))ᴴ * ((p : ℂ)⁻¹ • (P * V)) = 1 := by
  simp only [conjTranspose_smul, Complex.star_def,
    Matrix.smul_mul, Matrix.mul_smul, projection_gram V P hP, hprob, smul_smul]
  simp only [map_inv₀, Complex.conj_ofReal]
  match_scalars
  field_simp [Complex.ofReal_ne_zero.mpr hp]

omit [Fintype m] in
private lemma complement_probability (V : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hV : Vᴴ * V = 1) (p : ℝ)
    (hprob : Vᴴ * P * V = (p : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    Vᴴ * (1 - P) * V = (1 - (p : ℂ) ^ 2) • (1 : Matrix m m ℂ) := by
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, hprob]
  module

omit [Fintype m] [DecidableEq m] in
private lemma projected_parts_orthogonal (V : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hP : IsStarProjection P) : (P * V)ᴴ * ((1 - P) * V) = 0 := by
  have hself : Pᴴ = P := hP.isSelfAdjoint.isHermitian.eq
  rw [conjTranspose_mul, hself, ← Matrix.mul_assoc, Matrix.mul_assoc Vᴴ P (1 - P)]
  simp only [Matrix.mul_sub, Matrix.mul_one, hP.isIdempotentElem.eq, sub_self,
    Matrix.mul_zero, Matrix.zero_mul]

omit [Fintype m] in
/-- Uniform probability yields orthogonal success and failure isometries,
their projection identities, and reconstruction of the original isometry.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem uniformPostselection_decomposition (V : Matrix n m ℂ) (P : Matrix n n ℂ)
    (hV : Vᴴ * V = 1) (hP : IsStarProjection P) (p : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hprob : Vᴴ * P * V = (p : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    let G := postselectionSuccess V P p
    let H := postselectionFailure V P p
    Gᴴ * G = 1 ∧ Hᴴ * H = 1 ∧ Gᴴ * H = 0 ∧ P * G = G ∧ P * H = 0 ∧
      (p : ℂ) • G + (Real.sqrt (1 - p ^ 2) : ℂ) • H = V := by
  have hdef : 0 < 1 - p ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact normalized_projection_gram V P hP p hp.ne' hprob
  · apply normalized_projection_gram V (1 - P) hP.one_sub
      (Real.sqrt (1 - p ^ 2)) (Real.sqrt_pos.mpr hdef).ne'
    simpa only [Complex.ofReal_sqrt_sq _ hdef.le, Complex.ofReal_sub,
      Complex.ofReal_one, Complex.ofReal_pow] using complement_probability V P hV p hprob
  · simp only [postselectionSuccess, postselectionFailure, conjTranspose_smul,
      Matrix.smul_mul, Matrix.mul_smul, projected_parts_orthogonal V P hP, smul_zero]
  · simp only [postselectionSuccess, Matrix.mul_smul, ← Matrix.mul_assoc,
      hP.isIdempotentElem.eq]
  · simp only [postselectionFailure, Matrix.mul_smul, ← Matrix.mul_assoc,
      Matrix.mul_sub, Matrix.mul_one, hP.isIdempotentElem.eq, sub_self,
      Matrix.zero_mul, smul_zero]
  · simp only [postselectionSuccess, postselectionFailure, smul_smul,
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne'),
      mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hdef).ne'),
      one_smul, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]

/-- The amplification operator defined directly from the initial isometry.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def postselectionAmplificationStep (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) : Matrix n n ℂ :=
  -(subspaceReflection (V * Vᴴ) * subspaceReflection P)

/-- The amplification operator is unitary on its entire output space.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem postselectionAmplificationStep_mem_unitaryGroup (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P) :
    postselectionAmplificationStep V P ∈ unitaryGroup n ℂ := by
  have hprod : subspaceReflection (V * Vᴴ) * subspaceReflection P ∈ unitaryGroup n ℂ :=
    (unitaryGroup n ℂ).mul_mem
      (subspaceReflection_mem_unitaryGroup _
        (isStarProjection_mul_conjTranspose_of_isometry V hV))
      (subspaceReflection_mem_unitaryGroup P hP)
  simpa only [postselectionAmplificationStep, mem_unitaryGroup_iff, star_neg, neg_mul_neg]
    using hprod

private lemma sin_bounds_of_first_quadrant (θ : ℝ) (hθ0 : 0 < θ)
    (hθ1 : θ < Real.pi / 2) : 0 < Real.sin θ ∧ Real.sin θ < 1 := by
  refine ⟨Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos]), ?_⟩
  simpa only [Real.sin_pi_div_two] using
    Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) le_rfl hθ1

omit [Fintype m] in
/-- The derived success and failure isometries reproduce the initial isometry
at its success angle.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem amplificationPlane_postselection_eq_self (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : Vᴴ * P * V = (Real.sin θ : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    amplificationPlane (postselectionSuccess V P (Real.sin θ))
      (postselectionFailure V P (Real.sin θ)) θ = V := by
  obtain ⟨hp, hp1⟩ := sin_bounds_of_first_quadrant θ hθ0 hθ1
  simpa only [amplificationPlane,
    ← Real.cos_eq_sqrt_one_sub_sin_sq (by linarith [Real.pi_pos]) hθ1.le] using
      (uniformPostselection_decomposition V P hV hP (Real.sin θ) hp hp1 hprob).2.2.2.2.2

/-- Repeated reflection steps rotate the derived decomposition by twice the
success angle per round.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem postselectionAmplificationStep_pow_mul (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hprob : Vᴴ * P * V = (Real.sin θ : ℂ) ^ 2 • (1 : Matrix m m ℂ)) (k : ℕ) :
    postselectionAmplificationStep V P ^ k * V =
      amplificationPlane (postselectionSuccess V P (Real.sin θ))
        (postselectionFailure V P (Real.sin θ)) (θ + (k : ℝ) * (2 * θ)) := by
  obtain ⟨hp, hp1⟩ := sin_bounds_of_first_quadrant θ hθ0 hθ1
  obtain ⟨hG, hH, hGH, hPG, hPH, _⟩ :=
    uniformPostselection_decomposition V P hV hP (Real.sin θ) hp hp1 hprob
  simpa only [postselectionAmplificationStep, subspaceAmplificationStep,
    amplificationPlane_postselection_eq_self V P hV hP θ hθ0 hθ1 hprob] using
      subspaceAmplificationStep_pow_mul_plane _ _ P hG hH hGH hPG hPH θ θ k

private lemma exact_amplification_angle_bounds (ℓ : ℕ) (hℓ : 0 < ℓ) :
    0 < Real.pi / (4 * (ℓ : ℝ) + 2) ∧
      Real.pi / (4 * (ℓ : ℝ) + 2) < Real.pi / 2 := by
  refine ⟨by positivity, ?_⟩
  apply (div_lt_div_iff₀ (by positivity) (by norm_num : (0 : ℝ) < 2)).mpr
  nlinarith [Real.pi_pos, (Nat.cast_pos.mpr hℓ : 0 < (ℓ : ℝ))]

/-- A prescribed uniform success amplitude is amplified exactly, without
assuming separate success or failure isometries.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem postselectionAmplificationStep_pow_eq_success (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (ℓ : ℕ) (hℓ : 0 < ℓ)
    (hprob : Vᴴ * P * V =
      (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2)) : ℂ) ^ 2 • (1 : Matrix m m ℂ)) :
    postselectionAmplificationStep V P ^ ℓ * V =
      postselectionSuccess V P (Real.sin (Real.pi / (4 * (ℓ : ℝ) + 2))) := by
  obtain ⟨hθ0, hθ1⟩ := exact_amplification_angle_bounds ℓ hℓ
  obtain ⟨hp, hp1⟩ := sin_bounds_of_first_quadrant _ hθ0 hθ1
  obtain ⟨hG, hH, hGH, hPG, hPH, _⟩ :=
    uniformPostselection_decomposition V P hV hP _ hp hp1 hprob
  simpa only [postselectionAmplificationStep, subspaceAmplificationStep,
    amplificationPlane_postselection_eq_self V P hV hP _ hθ0 hθ1 hprob] using
      subspaceAmplificationStep_pow_eq_good _ _ P hG hH hGH hPG hPH ℓ

omit [Fintype m] [DecidableEq n] in
/-- Uniform success probability one already puts the entire image in the
successful subspace.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem projection_mul_eq_self_of_uniform_probability_one (V : Matrix n m ℂ)
    (P : Matrix n n ℂ) (hV : Vᴴ * V = 1) (hP : IsStarProjection P)
    (hprob : Vᴴ * P * V = 1) : P * V = V := by
  classical
  have hzero : ((1 - P) * V)ᴴ * ((1 - P) * V) = 0 := by
    rw [projection_gram V (1 - P) hP.one_sub]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hV, hprob, sub_self]
  have hcomp := conjTranspose_mul_self_eq_zero.mp hzero
  simpa only [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero, eq_comm] using hcomp

end Matrix
