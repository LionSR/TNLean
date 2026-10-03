/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FlatDensityEntropy
import TNLean.Algebra.ComplexSqrt
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Channel.MaximallyEntangled
import QICLean.Channel.PartialTrace

/-!
# Reduced densities of a fixed boundary factor

A normalized ancillary vector gives an isometric embedding of the relative
boundary labels. Its image of the maximally mixed boundary state has the same
rank and flat nonzero spectrum as that state. A complementary coefficient
changes only the scalar multiplying the unnormalized reduced matrix.

These finite matrix identities are used with the actual common boundary factor
of SCP10, arXiv:1001.3807, lines 1935–1990 and 2043–2072. They do not supply a
factorization of any contracted PEPS.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped BigOperators Matrix ComplexOrder
open Matrix

namespace TNLean.PEPS

variable {D A B : Type*} [Fintype D] [DecidableEq D] [Nonempty D]
variable [Fintype A] [Fintype B]

/-- Attach one fixed ancillary coefficient to each relative boundary label. -/
def boundaryAncillaMap (φ : A → ℂ) : Matrix (D × A) D ℂ :=
  fun p r => if p.1 = r then φ p.2 else 0

omit [Nonempty D] in
/-- The boundary embedding has the ancillary squared norm as its Gram scalar. -/
theorem boundaryAncillaMap_conjTranspose_mul (φ : A → ℂ) :
    (boundaryAncillaMap (D := D) φ).conjTranspose * boundaryAncillaMap φ =
      (star φ ⬝ᵥ φ) • (1 : Matrix D D ℂ) := by
  classical
  ext r s
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply,
    boundaryAncillaMap, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul]
  by_cases hrs : r = s
  · subst s
    simp [eq_comm, dotProduct]
  · simp [hrs, eq_comm, dotProduct]

/-- The normalized common density supported on the fixed ancillary vector. -/
noncomputable def fixedBoundaryFactorDensity (φ : A → ℂ) : Matrix (D × A) (D × A) ℂ :=
  (Fintype.card D : ℂ)⁻¹ •
    (boundaryAncillaMap (D := D) φ * (boundaryAncillaMap φ).conjTranspose)

/-- A normalized ancillary vector gives a positive density of trace one, full
boundary rank, and flat nonzero spectrum. -/
theorem fixedBoundaryFactorDensity_properties (φ : A → ℂ) (hφ : star φ ⬝ᵥ φ = 1) :
    (fixedBoundaryFactorDensity (D := D) φ).PosSemidef ∧
      (fixedBoundaryFactorDensity (D := D) φ).trace = 1 ∧
      (fixedBoundaryFactorDensity (D := D) φ).rank = Fintype.card D ∧
      fixedBoundaryFactorDensity (D := D) φ * fixedBoundaryFactorDensity φ =
        (Fintype.card D : ℂ)⁻¹ • fixedBoundaryFactorDensity φ := by
  classical
  let J := boundaryAncillaMap (D := D) φ
  have hJ : J.conjTranspose * J = 1 := by
    rw [boundaryAncillaMap_conjTranspose_mul, hφ, one_smul]
  have hD : (Fintype.card D : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hP : J * J.conjTranspose * (J * J.conjTranspose) = J * J.conjTranspose := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc J.conjTranspose, hJ, Matrix.one_mul]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hp := posSemidef_self_mul_conjTranspose
      ((Real.sqrt (Fintype.card D : ℝ) : ℂ)⁻¹ • J)
    simpa only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      star_inv₀, Complex.star_def, Complex.conj_ofReal,
      Complex.ofReal_sqrt_inv_mul_self (Fintype.card D : ℝ) (by positivity),
      Complex.ofReal_natCast, fixedBoundaryFactorDensity, J] using hp
  · rw [fixedBoundaryFactorDensity, trace_smul, trace_mul_comm, hJ]
    simp [hD]
  · rw [fixedBoundaryFactorDensity, rank_smul_of_mem_nonZeroDivisors _
      (mem_nonZeroDivisors_of_ne_zero (inv_ne_zero hD)), rank_self_mul_conjTranspose]
    exact Matrix.IsIsometry.rank_eq_card _ hJ
  · simp only [fixedBoundaryFactorDensity, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [hP]

/-- The von Neumann entropy of the common density is the logarithm of the
relative-boundary dimension. -/
theorem vonNeumannEntropy_fixedBoundaryFactorDensity [DecidableEq A] (φ : A → ℂ)
    (hφ : star φ ⬝ᵥ φ = 1) :
    vonNeumannEntropy (fixedBoundaryFactorDensity (D := D) φ)
      (fixedBoundaryFactorDensity_properties (D := D) φ hφ).1.isHermitian =
        Real.log (Fintype.card D : ℝ) := by
  have h := fixedBoundaryFactorDensity_properties (D := D) φ hφ
  apply vonNeumannEntropy_of_mul_self_eq_inv_smul h.1 h.2.1
  simpa only [Complex.ofReal_natCast] using h.2.2.2

/-- The Schmidt matrix of the fixed maximally entangled boundary factor with
specified ancillary coefficients on its two sides. -/
noncomputable def boundaryFactorSchmidtMatrix (φ : A → ℂ) (χ : B → ℂ) :
    Matrix (D × A) (D × B) ℂ :=
  (Real.sqrt (Fintype.card D : ℝ) : ℂ)⁻¹ •
    (boundaryAncillaMap (D := D) φ * (boundaryAncillaMap (D := D) χ).transpose)

omit [Fintype A] [Fintype B] [Nonempty D] in
/-- The fixed-factor Schmidt coefficients separate the boundary equality and
both ancillary coefficients. -/
theorem boundaryFactorSchmidtMatrix_apply (φ : A → ℂ) (χ : B → ℂ)
    (r : D) (a : A) (s : D) (b : B) :
    boundaryFactorSchmidtMatrix φ χ (r, a) (s, b) =
      (if r = s then (Real.sqrt (Fintype.card D : ℝ) : ℂ)⁻¹ else 0) * φ a * χ b := by
  classical
  simp only [boundaryFactorSchmidtMatrix, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_apply, Matrix.transpose_apply, boundaryAncillaMap]
  by_cases hrs : r = s
  · subst s
    simp [mul_assoc]
  · simp [hrs]

omit [Fintype A] in
/-- The complementary ancillary coefficient changes only the norm scalar of the
unnormalized reduced matrix. -/
theorem boundaryFactorSchmidtMatrix_mul_conjTranspose (φ : A → ℂ) (χ : B → ℂ) :
    boundaryFactorSchmidtMatrix (D := D) φ χ *
      (boundaryFactorSchmidtMatrix φ χ).conjTranspose =
        (star χ ⬝ᵥ χ) • fixedBoundaryFactorDensity (D := D) φ := by
  classical
  have hB : (boundaryAncillaMap (D := D) χ).transpose *
      (boundaryAncillaMap χ).transpose.conjTranspose =
      (star χ ⬝ᵥ χ) • (1 : Matrix D D ℂ) := by
    rw [conjTranspose_transpose_eq_transpose_conjTranspose, ← transpose_mul,
      boundaryAncillaMap_conjTranspose_mul, transpose_smul, transpose_one]
  simp only [boundaryFactorSchmidtMatrix, conjTranspose_smul, conjTranspose_mul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [star_inv₀, Complex.star_def, Complex.conj_ofReal,
    Complex.ofReal_sqrt_inv_mul_self (Fintype.card D : ℝ) (by positivity)]
  change (Fintype.card D : ℂ)⁻¹ •
    ((boundaryAncillaMap φ * (boundaryAncillaMap χ).transpose) *
      ((boundaryAncillaMap χ).transpose.conjTranspose * (boundaryAncillaMap φ).conjTranspose)) = _
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (boundaryAncillaMap χ).transpose, hB]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, fixedBoundaryFactorDensity,
    smul_smul, mul_comm]

/-- A unitary on the complementary physical indices leaves the reduced matrix
unchanged. The ordinary transpose is the coefficient-matrix convention. -/
theorem mul_unitary_transpose_mul_conjTranspose {P Q : Type*} [Fintype Q]
    [DecidableEq Q] (C : Matrix P Q ℂ) (U : Matrix Q Q ℂ)
    (hU : U ∈ Matrix.unitaryGroup Q ℂ) :
    (C * U.transpose) * (C * U.transpose).conjTranspose = C * C.conjTranspose := by
  have ht := Matrix.mem_unitaryGroup_iff.mp (Matrix.transpose_mem_unitaryGroup_iff.mpr hU)
  rw [Matrix.star_eq_conjTranspose] at ht
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
    ← Matrix.mul_assoc U.transpose, ht, Matrix.one_mul]

omit [Fintype A] in
/-- Reindexing the fixed factor gives the same scalar reduced matrix in the
original physical coordinates. -/
theorem boundaryFactorSchmidtMatrix_submatrix_mul_conjTranspose
    {P Q : Type*} [Fintype Q]
    (eP : P ≃ D × A) (eQ : Q ≃ D × B) (φ : A → ℂ) (χ : B → ℂ) :
    ((boundaryFactorSchmidtMatrix (D := D) φ χ).submatrix eP eQ) *
      ((boundaryFactorSchmidtMatrix φ χ).submatrix eP eQ).conjTranspose =
        (star χ ⬝ᵥ χ) • (fixedBoundaryFactorDensity (D := D) φ).submatrix eP eP := by
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    boundaryFactorSchmidtMatrix_mul_conjTranspose]
  rfl

/-- The fixed density retains positivity, trace, boundary rank, and flat spectrum
in any physical coordinate system. -/
theorem fixedBoundaryFactorDensity_submatrix_properties
    {P : Type*} [Fintype P] (eP : P ≃ D × A) (φ : A → ℂ)
    (hφ : star φ ⬝ᵥ φ = 1) :
    ((fixedBoundaryFactorDensity (D := D) φ).submatrix eP eP).PosSemidef ∧
      ((fixedBoundaryFactorDensity (D := D) φ).submatrix eP eP).trace = 1 ∧
      ((fixedBoundaryFactorDensity (D := D) φ).submatrix eP eP).rank = Fintype.card D ∧
      (fixedBoundaryFactorDensity (D := D) φ).submatrix eP eP *
          (fixedBoundaryFactorDensity φ).submatrix eP eP =
        (Fintype.card D : ℂ)⁻¹ • (fixedBoundaryFactorDensity φ).submatrix eP eP := by
  classical
  have h := fixedBoundaryFactorDensity_properties (D := D) φ hφ
  refine ⟨h.1.submatrix _, ?_, ?_, ?_⟩
  · rw [Matrix.trace_submatrix_equiv, h.2.1]
  · rw [Matrix.rank_submatrix, h.2.2.1]
  · rw [Matrix.submatrix_mul_equiv, h.2.2.2]
    rfl

/-- A nonzero coefficient matrix with a scalar common reduced matrix normalizes
to that density. Positivity of the normalization is derived from the matrix. -/
theorem normalized_reducedMatrix_eq_of_scalar
    {P Q : Type*} [Fintype P] [Fintype Q]
    (C : Matrix P Q ℂ) (ρ : Matrix P P ℂ) (hρ : ρ.trace = 1)
    (a : ℂ) (hC : C * C.conjTranspose = a • ρ) (hne : C ≠ 0) :
    0 < (C * C.conjTranspose).trace ∧
      (C * C.conjTranspose).trace⁻¹ • (C * C.conjTranspose) = ρ := by
  classical
  have ha : (C * C.conjTranspose).trace = a := by
    rw [hC, trace_smul, hρ, smul_eq_mul, mul_one]
  have hn : (C * C.conjTranspose).trace ≠ 0 := by
    exact mt Matrix.trace_mul_conjTranspose_self_eq_zero_iff.mp hne
  refine ⟨lt_of_le_of_ne (Matrix.posSemidef_self_mul_conjTranspose C).trace_nonneg
    (Ne.symm hn), ?_⟩
  rw [ha, hC, smul_smul, inv_mul_cancel₀ (ha ▸ hn), one_smul]

end TNLean.PEPS
