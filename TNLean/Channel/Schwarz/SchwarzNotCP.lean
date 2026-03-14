/-
Copyright (c) 2025 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.ChoiJamiolkowski
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Wolf Example 5.3: a Schwarz map which is not completely positive

This file records the concrete map from Wolf, Example 5.3,

$$T_*(A) = \frac{1}{2} A^T + \frac{1}{4} \operatorname{tr}(A) I,$$

on $M_2(\mathbb{C})$. It is positive and satisfies the Schwarz inequality, but
it is not completely positive.

## Main declarations

* `wolfExample53`
* `wolfExample53_isPositive`
* `wolfExample53_satisfies_schwarz`
* `wolfExample53_not_cp`

## References

* [M. Wolf, *Quantum Channels & Operations: Guided Tour*, Example 5.3][Wolf2012QChannels]
-/

open scoped Matrix ComplexOrder MatrixOrder
open Matrix Finset

local notation "M2" => Matrix (Fin 2) (Fin 2) ℂ
local notation "M4" => Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

private lemma complex_one_half_nonneg : (0 : ℂ) ≤ (1 / 2 : ℂ) := by
  rw [Complex.nonneg_iff]
  norm_num

private lemma complex_one_quarter_nonneg : (0 : ℂ) ≤ (1 / 4 : ℂ) := by
  rw [Complex.nonneg_iff]
  norm_num

/-- Wolf Example 5.3: the linear map
`T_*(A) = (1/2) A^T + (1/4) tr(A) I` on `M₂(ℂ)`. -/
noncomputable def wolfExample53 : M2 →ₗ[ℂ] M2 where
  toFun A := (1 / 2 : ℂ) • Aᵀ + (1 / 4 : ℂ) • (Matrix.trace A • (1 : M2))
  map_add' := by
    intro A B
    simp [add_smul, smul_add, Matrix.trace_add, add_assoc, add_left_comm]
  map_smul' := by
    intro c A
    simp [smul_add, smul_smul, Matrix.trace_smul, mul_comm, mul_left_comm]

@[simp] theorem wolfExample53_apply (A : M2) :
    wolfExample53 A = (1 / 2 : ℂ) • (Aᵀ + (1 / 2 : ℂ) • (Matrix.trace A • (1 : M2))) := by
  ext i j
  simp [wolfExample53, smul_smul]
  ring

@[simp] theorem wolfExample53_one : wolfExample53 (1 : M2) = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [wolfExample53]
    ring
  · simp [wolfExample53, hij]

/-- The Wolf Example 5.3 map is positive, as a convex combination of transpose
and trace-times-identity. -/
theorem wolfExample53_isPositive : IsPositiveMap wolfExample53 := by
  intro A hA
  have htranspose : ((1 / 2 : ℂ) • Aᵀ).PosSemidef := by
    exact hA.transpose.smul complex_one_half_nonneg
  have htraceId : ((1 / 4 : ℂ) • (Matrix.trace A • (1 : M2))).PosSemidef := by
    have htrace : ((Matrix.trace A) • (1 : M2)).PosSemidef := by
      exact Matrix.PosSemidef.one.smul hA.trace_nonneg
    exact htrace.smul complex_one_quarter_nonneg
  simpa [wolfExample53] using htranspose.add htraceId

/-- Wolf Example 5.3 satisfies the Schwarz inequality.

The intended proof is the concrete $2 \times 2$ argument from Wolf: after
shifting by a scalar multiple of the identity one may assume `trace A = 0`, and
then the Schwarz gap dominates `(1/2) • (Aᴴ * A)ᵀ`. -/
theorem wolfExample53_satisfies_schwarz (A : M2) :
    (wolfExample53 (Aᴴ * A) - wolfExample53 (Aᴴ) * wolfExample53 A).PosSemidef := by
  sorry -- Wolf Ex 5.3

/-- A concrete antisymmetric witness for the non-CP statement. -/
noncomputable def wolfExample53AntisymmVec : Fin 2 × Fin 2 → ℂ
  | (0, 1) => 1
  | (1, 0) => -1
  | _ => 0

/-- The Choi matrix of `wolfExample53` has a negative expectation value on the
antisymmetric vector `|01⟩ - |10⟩`, hence is not positive semidefinite. -/
theorem wolfExample53_choi_negative_antisymm :
    star wolfExample53AntisymmVec ⬝ᵥ
        (ChoiJamiolkowski.choiMatrix wolfExample53).mulVec wolfExample53AntisymmVec =
      (- (1 / 4 : ℂ)) := by
  sorry -- Wolf Ex 5.3

/-- Wolf Example 5.3 is not completely positive. -/
theorem wolfExample53_not_cp : ¬ IsCPMap wolfExample53 := by
  intro hcp
  have hpsd : (ChoiJamiolkowski.choiMatrix wolfExample53).PosSemidef :=
    (ChoiJamiolkowski.cp_iff_choi_posSemidef (D := 2) (T := wolfExample53)).mp hcp
  have hnonneg := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 wolfExample53AntisymmVec
  have hneg : ¬ (0 : ℂ) ≤
      star wolfExample53AntisymmVec ⬝ᵥ
        (ChoiJamiolkowski.choiMatrix wolfExample53).mulVec wolfExample53AntisymmVec := by
    rw [wolfExample53_choi_negative_antisymm, Complex.nonneg_iff]
    norm_num
  exact hneg hnonneg
