/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import QICLean.Kraus.Injectivity
import TNLean.Algebra.MatrixSingleSpan

/-!
# Normality of tensors with a forced outgoing bond

Suppose that for every bond label `j` some letter `ℓ j` of a tensor has a single nonzero
column, the column `j`, filled with a vector `v j`. The product of two such letters is
`A^{ℓ j} A^{ℓ k} = v_k(j) · v_j e_kᵀ`. If the vectors `v j` form a basis and no entry `v_k(j)`
vanishes, the products of two letters therefore span the full matrix algebra: the tensor is
injective after blocking two sites, hence normal. Clock and controlled-phase tensors, whose
outgoing bond copies the physical input, are of this form.

## Main results

* `MPSTensor.isNBlkInjective_two_of_forced_column`: two-site block injectivity.
* `MPSTensor.isNormal_of_forced_column`: normality.
-/

open scoped BigOperators Matrix

namespace MPSTensor

variable {d D : ℕ}

/-- **Two-site block injectivity of a tensor with a forced outgoing bond.** If for every bond
label `j` the letter `ℓ j` is the matrix whose only nonzero column is the column `j`, equal to
`v j`, if no entry of the vectors `v j` vanishes, and if the vectors `v j` are the columns of an
invertible matrix, then the words of length two span the full matrix algebra. -/
theorem isNBlkInjective_two_of_forced_column {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (ℓ : Fin D → Fin d) (v : Fin D → Fin D → ℂ)
    (hA : ∀ j, A (ℓ j) = Matrix.of fun l r ↦ if r = j then v j l else 0)
    (hv : ∀ j k, v k j ≠ 0) (hdet : (Matrix.of fun l j ↦ v j l).det ≠ 0) :
    Kraus.IsNBlkInjective A 2 := by
  have hM := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet)
  generalize (Matrix.of fun l j ↦ v j l)⁻¹ = P at hM
  have hword : ∀ j k, Kraus.evalWord A (List.ofFn ![ℓ j, ℓ k]) =
      v k j • Matrix.of fun l r ↦ if r = k then v j l else 0 := by
    intro j k
    ext l r
    simp only [List.ofFn_succ, List.ofFn_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Kraus.evalWord_cons, Kraus.evalWord_nil, Matrix.mul_one, hA, Matrix.mul_apply,
      Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, ite_mul, zero_mul,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    split_ifs <;> ring
  rw [Kraus.IsNBlkInjective, Kraus.wordSpan]
  refine Submodule.eq_top_of_forall_single_mem _ fun l k ↦ ?_
  have hsum : Matrix.single l k (1 : ℂ) =
      ∑ j, (P j l * (v k j)⁻¹) • Kraus.evalWord A (List.ofFn ![ℓ j, ℓ k]) := by
    ext l' r
    have h1 := congrFun (congrFun hM l') l
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply] at h1
    simp only [hword, Matrix.sum_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul,
      Matrix.single_apply]
    by_cases hr : r = k
    · subst hr
      simp only [ite_true, and_true, eq_comm (a := l)]
      rw [← h1]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      field_simp [hv j r]
    · simp [hr, Ne.symm hr]
  rw [hsum]
  exact Submodule.sum_mem _ fun j _ ↦
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨![ℓ j, ℓ k], rfl⟩)

/-- **Normality of a tensor with a forced outgoing bond**: under the hypotheses of
`isNBlkInjective_two_of_forced_column` the tensor is normal. -/
theorem isNormal_of_forced_column {A : Fin d → Matrix (Fin D) (Fin D) ℂ}
    (ℓ : Fin D → Fin d) (v : Fin D → Fin D → ℂ)
    (hA : ∀ j, A (ℓ j) = Matrix.of fun l r ↦ if r = j then v j l else 0)
    (hv : ∀ j k, v k j ≠ 0) (hdet : (Matrix.of fun l j ↦ v j l).det ≠ 0) :
    Kraus.IsNormal A :=
  ⟨2, two_pos, isNBlkInjective_two_of_forced_column ℓ v hA hv hdet⟩

end MPSTensor
