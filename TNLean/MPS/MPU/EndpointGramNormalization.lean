/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.AffineGramHull
import QICLean.Algebra.MatrixUnitaryBetween
import QICLean.Algebra.MatrixAux

/-!
# Endpoint normalization for MPU prefix Grams

At the two endpoints of an open matrix product operator, the virtual bond
has dimension one. An isometric physical prefix then has the same virtual
Gram for every input density matrix: the identity. Its real affine Gram
hull is consequently a singleton. These identities establish the endpoint
metrics used in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`.

This file does not assert the full matrix product unitary circuit theorem.
-/

open Matrix
open scoped ComplexOrder

namespace MPUCircuit

variable {o i : Type*} [Fintype o] [Fintype i]

/-- The physical operator represented by a prefix with two scalar virtual
bonds. Source: the endpoint convention in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def scalarPrefixOperator (F : o → i → Matrix Unit Unit ℂ) : Matrix o i ℂ :=
  fun a b ↦ F a b () ()

omit [Fintype i] in
/-- Closing the two scalar virtual bonds gives the ordinary physical
input Gram. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem intervalInputGram_scalar_bonds (F : o → i → Matrix Unit Unit ℂ) :
    intervalInputGram F 1 1 = (scalarPrefixOperator F)ᴴ * scalarPrefixOperator F := by
  classical
  ext b c
  simp [intervalInputGram, scalarPrefixOperator, trace, diag, mul_apply,
    conjTranspose_apply]

/-- An isometric prefix with scalar endpoint bonds has virtual Gram
equal to the input trace times the identity, for every complex input
matrix. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixInputGram_eq_trace_smul_one_of_isIsometry [DecidableEq i]
    (F : o → i → Matrix Unit Unit ℂ) (hF : (scalarPrefixOperator F).IsIsometry)
    (ρ : Matrix i i ℂ) : prefixInputGram F ρ = trace ρ • 1 := by
  have ht := trace_intervalGramTransfer F ρ 1 1
  rw [intervalInputGram_scalar_bonds, hF, Matrix.mul_one, Matrix.one_mul] at ht
  change trace (prefixInputGram F ρ) = trace ρ at ht
  ext x y
  cases x
  cases y
  simpa [trace, diag] using ht

/-- Every density input gives the identity Gram at a scalar endpoint;
a nonempty input space supplies a density matrix. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem densityPrefixGrams_eq_singleton_one_of_isIsometry
    [DecidableEq i] [Nonempty i]
    (F : o → i → Matrix Unit Unit ℂ) (hF : (scalarPrefixOperator F).IsIsometry) :
    densityPrefixGrams F = {1} := by
  ext P
  constructor
  · rintro ⟨ρ, _, hρtrace, hρP⟩
    rw [prefixInputGram_eq_trace_smul_one_of_isIsometry F hF, hρtrace,
      one_smul] at hρP
    exact hρP.symm
  · intro hP
    have hP' : P = 1 := hP
    subst P
    refine ⟨faithfulDensity i, (faithfulDensity_posDef i).posSemidef,
      faithfulDensity_trace i, ?_⟩
    rw [prefixInputGram_eq_trace_smul_one_of_isIsometry F hF,
      faithfulDensity_trace, one_smul]

/-- The real affine hull of scalar endpoint Grams is the singleton
identity, without an additional choice of bond metric. Source: Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem prefixGramAffineHull_eq_singleton_one_of_isIsometry
    [DecidableEq i] [Nonempty i]
    (F : o → i → Matrix Unit Unit ℂ) (hF : (scalarPrefixOperator F).IsIsometry) :
    prefixGramAffineHull F = ({1} : AffineSubspace ℝ (Matrix Unit Unit ℂ)) := by
  rw [prefixGramAffineHull, densityPrefixGrams_eq_singleton_one_of_isIsometry F hF,
    AffineSubspace.affineSpan_singleton]

/-- The empty prefix has one physical input, one physical output, and
the identity scalar bond. Source: the endpoint convention in Section 5
of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
def emptyPrefixCap : Unit → Unit → Matrix Unit Unit ℂ := fun _ _ ↦ 1

/-- The physical operator of the empty prefix is an isometry. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem emptyPrefixCap_isIsometry : (scalarPrefixOperator emptyPrefixCap).IsIsometry := by
  change (1 : Matrix Unit Unit ℂ).IsIsometry
  simp [Matrix.IsIsometry]

/-- The affine Gram hull of the empty prefix is the singleton identity.
Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem emptyPrefixCap_prefixGramAffineHull :
    prefixGramAffineHull emptyPrefixCap =
      ({1} : AffineSubspace ℝ (Matrix Unit Unit ℂ)) := by
  exact prefixGramAffineHull_eq_singleton_one_of_isIsometry
    emptyPrefixCap emptyPrefixCap_isIsometry

/-- In a one-dimensional bond space, the dual metric of the identity is
the identity. Source: the endpoint normalization in Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_one_of_card_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hcard : Fintype.card ι = 1) : dualGramMetric (1 : Matrix ι ι ℂ) = 1 := by
  simp [dualGramMetric, hcard]

/-- The scalar endpoint identity is its own dual Gram metric. Source:
Section 5 of `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. -/
theorem dualGramMetric_one_unit : dualGramMetric (1 : Matrix Unit Unit ℂ) = 1 := by
  exact dualGramMetric_one_of_card_eq_one (by simp)

end MPUCircuit
