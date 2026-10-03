/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.ComplexSqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Basis

/-!
# The isometry which restores representation multiplicities on a bond

For a multiplicity space of dimension \(m>0\), the map
\(X\mapsto m^{-1/2}X\otimes I_m\) preserves the Hilbert–Schmidt inner product.
Applied independently to the irreducible blocks, it is the bond isometry in the
semi-regular bond-dimension reduction of Schuch, Cirac, and Pérez-García,
arXiv:1001.3807, Section 7, `Papers/1001.3807/paper_v3.tex`, lines 2992–3019.
The source takes \(m_i=d_i\), the multiplicity of the \(i\)-th irreducible
representation in the regular representation.

This module proves the stated bond isometry and its action on representation
matrices. The identification of its product over lattice bonds with a complete
PEPS contraction is a separate assertion.

## References

- [arXiv:1001.3807](https://arxiv.org/abs/1001.3807) -- N. Schuch, J. I. Cirac,
  D. Pérez-García, *PEPS as ground states: degeneracy and topology*
-/

open scoped Matrix Kronecker

namespace TNLean.PEPS

variable {ι μ : Type*} [DecidableEq μ] [Fintype μ]

/-- Restore a multiplicity space by adjoining its normalized identity matrix.
Source: SCP10, Section 7, lines 3008–3019; the source takes its dimension equal
to the dimension of the corresponding irreducible representation. -/
noncomputable def multiplicityBondMap : Matrix ι ι ℂ →ₗ[ℂ] Matrix (ι × μ) (ι × μ) ℂ :=
  (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ •
    (Matrix.kroneckerBilinear (R := ℂ)).flip (1 : Matrix μ μ ℂ)

/-- The bond map adjoins the identity on the multiplicity factor. -/
@[simp]
theorem multiplicityBondMap_apply (X : Matrix ι ι ℂ) :
    multiplicityBondMap (μ := μ) X =
      (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ • (X ⊗ₖ (1 : Matrix μ μ ℂ)) := rfl

variable [DecidableEq ι]

/-- A matrix unit is sent to the normalized sum over equal multiplicity indices.
This is the explicit basis map of SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondMap_single (a b : ι) :
    multiplicityBondMap (μ := μ) (Matrix.single a b 1) =
      (Real.sqrt (Fintype.card μ : ℝ) : ℂ)⁻¹ •
        ∑ c : μ, Matrix.single (a, c) (b, c) 1 := by
  rw [multiplicityBondMap_apply, ← Matrix.sum_single_one]
  change _ • (Matrix.kroneckerBilinear (R := ℂ) (Matrix.single a b 1)
    (∑ c : μ, Matrix.single c c 1)) = _
  rw [map_sum]
  change _ • (∑ c : μ, (Matrix.single a b (1 : ℂ)) ⊗ₖ Matrix.single c c 1) = _
  simp only [Matrix.single_kronecker_single, one_mul]

omit [DecidableEq ι] in
/-- The multiplicity-restoring bond map preserves the Hilbert–Schmidt inner product.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem trace_multiplicityBondMap_conjTranspose_mul [Fintype ι] [Nonempty μ] (X Y : Matrix ι ι ℂ) :
    Matrix.trace ((multiplicityBondMap (μ := μ) X).conjTranspose *
      multiplicityBondMap (μ := μ) Y) = Matrix.trace (X.conjTranspose * Y) := by
  simp only [multiplicityBondMap_apply, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, ← Matrix.mul_kronecker_mul,
    Matrix.one_mul, Matrix.trace_smul, Matrix.trace_kronecker, Matrix.trace_one,
    star_inv₀, Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, Complex.ofReal_sqrt_inv_mul_self _ (Nat.cast_nonneg _),
    mul_left_comm, Complex.ofReal_natCast,
    inv_mul_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero), mul_one]

omit [DecidableEq ι] in
/-- The square-root weight of the semi-regular bond becomes the ordinary
multiplicity block. Source: SCP10, Section 7, lines 2992–3007. -/
theorem multiplicityBondMap_sqrt_smul [Nonempty μ] (X : Matrix ι ι ℂ) :
    multiplicityBondMap (μ := μ) ((Real.sqrt (Fintype.card μ : ℝ) : ℂ) • X) =
      X ⊗ₖ (1 : Matrix μ μ ℂ) := by
  simp only [multiplicityBondMap_apply, Matrix.smul_kronecker, smul_smul]
  rw [inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))), one_smul]

omit [DecidableEq ι] in
/-- The multiplicity-restoring map loses no bond vector.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondMap_injective [Nonempty μ] :
    Function.Injective (multiplicityBondMap (ι := ι) (μ := μ)) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro X hX
  obtain ⟨c⟩ := ‹Nonempty μ›
  ext i j
  have h := congrArg (fun Z => Z (i, c) (j, c)) hX
  simp only [multiplicityBondMap_apply, Matrix.smul_apply, Matrix.kronecker_apply,
    Matrix.one_apply_eq, mul_one, smul_eq_mul, Matrix.zero_apply] at h
  exact (mul_eq_zero.mp h).resolve_left (inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr Fintype.card_pos))))

section Families

variable {I : Type*} (ν κ : I → Type*)
variable [∀ i, Fintype (κ i)] [∀ i, DecidableEq (κ i)]

/-- Restore the multiplicities independently in each irreducible bond block.
Source: SCP10, Section 7, lines 2992–3019. -/
noncomputable def multiplicityBondFamilyMap :
    (∀ i, Matrix (ν i) (ν i) ℂ) →ₗ[ℂ]
      (∀ i, Matrix (ν i × κ i) (ν i × κ i) ℂ) :=
  LinearMap.pi fun i => multiplicityBondMap ∘ₗ LinearMap.proj i

/-- The family map acts separately on every irreducible block. -/
@[simp]
theorem multiplicityBondFamilyMap_apply (X : ∀ i, Matrix (ν i) (ν i) ℂ) (i : I) :
    multiplicityBondFamilyMap ν κ X i = multiplicityBondMap (μ := κ i) (X i) := rfl

/-- The direct sum of bond maps preserves the Hilbert–Schmidt inner product.
This is the full block isometry of SCP10, Section 7, lines 3008–3019. -/
theorem sum_trace_multiplicityBondFamilyMap_conjTranspose_mul
    [Fintype I] [∀ i, Fintype (ν i)] [∀ i, Nonempty (κ i)]
    (X Y : ∀ i, Matrix (ν i) (ν i) ℂ) :
    (∑ i, Matrix.trace ((multiplicityBondFamilyMap ν κ X i).conjTranspose *
      multiplicityBondFamilyMap ν κ Y i)) =
        ∑ i, Matrix.trace ((X i).conjTranspose * Y i) := by
  exact Finset.sum_congr rfl fun i _ => trace_multiplicityBondMap_conjTranspose_mul _ _

/-- Independent restoration of all multiplicities is injective.
Source: SCP10, Section 7, lines 3008–3019. -/
theorem multiplicityBondFamilyMap_injective [∀ i, Nonempty (κ i)] :
    Function.Injective (multiplicityBondFamilyMap ν κ) := by
  intro X Y h
  exact funext fun i => multiplicityBondMap_injective (congr_fun h i)

/-- The weighted semi-regular bond matrices are carried to their repeated blocks.
For the regular representation the multiplicity is the irreducible dimension.
Source: SCP10, Section 7, lines 2992–3007. -/
theorem multiplicityBondFamilyMap_sqrt_smul [∀ i, Nonempty (κ i)]
    (X : ∀ i, Matrix (ν i) (ν i) ℂ) :
    multiplicityBondFamilyMap ν κ
      (fun i => (Real.sqrt (Fintype.card (κ i) : ℝ) : ℂ) • X i) =
        fun i => X i ⊗ₖ (1 : Matrix (κ i) (κ i) ℂ) := by
  exact funext fun i => multiplicityBondMap_sqrt_smul _

end Families

end TNLean.PEPS
