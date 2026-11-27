/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Circuit.CutMetrics.BalancedIntervalMerging
import QICLean.Circuit.Gate.PartialIsometryDilation
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import QICLean.Algebra.Matrix.RankOneSandwich

/-!
# An explicit unitary dilation of the normalized bond contraction

The normalized balanced bond contraction has vectorized squared norm one.
Sending this linear functional to a specified basis vector gives a square
partial isometry. Its two-copy dilation is therefore unitary, and its first
output branch records the normalized contraction with the bond registers
reset to that basis vector.

The partial-isometry identity and the unitary dilation are derived from the
normalization; neither is supplied as a hypothesis. Source: Section 5 of
`docs/audits/2026-10-02_mpu_rank_two_circuits.tex`. These finite-dimensional
identities do not assert the complete recursive circuit construction.
-/

open scoped Matrix ComplexOrder MatrixOrder

namespace MPUCircuit

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

/-- The normalized balanced contraction, with output in a specified bond basis state.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def normalizedBondReset (P : Matrix ι ι ℂ) (z : ι × ι) :
    Matrix (ι × ι) (ι × ι) ℂ :=
  vecMulVec (Pi.single z 1) (vec (normalizedBalancedGramContraction P))

/-- The normalized bond reset is a partial isometry.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem normalizedBondReset_mul_conjTranspose_mul
    {P : Matrix ι ι ℂ} (hP : P.PosDef) (z : ι × ι) :
    normalizedBondReset P z * (normalizedBondReset P z)ᴴ * normalizedBondReset P z =
      normalizedBondReset P z := by
  exact Matrix.vecMulVec_single_mul_conjTranspose_mul z _
    (normalizedBalancedGramContraction_vec_inner hP)

/-- The explicit one-flag dilation of the normalized bond reset.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
noncomputable def normalizedBondDilation (P : Matrix ι ι ℂ) (z : ι × ι) :
    Matrix ((ι × ι) ⊕ (ι × ι)) ((ι × ι) ⊕ (ι × ι)) ℂ :=
  partialIsometryDilation (normalizedBondReset P z)

/-- A positive definite balanced metric gives a unitary normalized bond dilation.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem normalizedBondDilation_mem_unitaryGroup {P : Matrix ι ι ℂ}
    (hP : P.PosDef) (z : ι × ι) :
    normalizedBondDilation P z ∈ unitaryGroup ((ι × ι) ⊕ (ι × ι)) ℂ := by
  exact partialIsometryDilation_mem_unitaryGroup _ (normalizedBondReset_mul_conjTranspose_mul hP z)

omit [Nonempty ι] in
/-- On a clean flag input, the dilation separates the contraction and its
complementary initial component.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem normalizedBondDilation_mul_fromRows {m : Type*}
    (P : Matrix ι ι ℂ) (z : ι × ι) (V : Matrix (ι × ι) m ℂ) :
    normalizedBondDilation P z * fromRows V 0 =
      fromRows (normalizedBondReset P z * V)
        ((1 - (normalizedBondReset P z)ᴴ * normalizedBondReset P z) * V) := by
  exact Matrix.partialIsometryDilation_mul_fromRows _ V

omit [Nonempty ι] in
/-- The first flag branch applies exactly the normalized contraction and
resets the contracted bond to the specified basis state.
Source: `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5. -/
theorem normalizedBondDilation_first_branch {m : Type*}
    (P : Matrix ι ι ℂ) (z : ι × ι) (V : Matrix (ι × ι) m ℂ) :
    toRows₁ (normalizedBondDilation P z * fromRows V 0) =
      vecMulVec (Pi.single z 1) (vec (normalizedBalancedGramContraction P) ᵥ* V) := by
  rw [normalizedBondDilation_mul_fromRows, toRows₁_fromRows, normalizedBondReset, vecMulVec_mul]

end MPUCircuit
