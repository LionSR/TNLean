/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.FundamentalTheorem.PositiveLinearExtension
import TNLean.MPS.MPDO.PositiveMinimalRealizationCounterexample

/-!
# Closed matrix product vectors do not force a positive virtual extension

The explicit nonunitary-similarity tensors from
`PositiveMinimalRealizationCounterexample` are regarded as one-block families.
Their per-block linear extension is not positive, despite equality of every
closed matrix product vector.

## Main result

* `perBlockLinearExtension_not_positive`: the explicit one-block extension is
  not a positive map.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.4, lines 2048--2057, and Proposition 4.13, lines 1898--1921
-/

open scoped Matrix

noncomputable section

namespace MPSTensor.PositiveMinimalRealizationCounterexample

/-- The source tensor, regarded as a one-block family. -/
def tensorFamily : (k : Fin 1) → MPSTensor 4 ((fun _ : Fin 1 ↦ 2) k) :=
  fun _ ↦ tensor

/-- The nonunitarily conjugated tensor, regarded as a one-block family. -/
def gaugedTensorFamily : (k : Fin 1) → MPSTensor 4 ((fun _ : Fin 1 ↦ 2) k) :=
  fun _ ↦ gaugedTensor

/-- The source one-block family is injective. -/
lemma tensorFamily_isInjective : ∀ k, IsInjective (tensorFamily k) :=
  fun _ ↦ tensor_isInjective

/-- Corresponding blocks of the two families have the same closed matrix
product vectors. -/
lemma tensorFamily_sameMPV_gaugedTensorFamily :
    ∀ k, SameMPV (tensorFamily k) (gaugedTensorFamily k) :=
  fun _ ↦ tensor_gaugeEquiv_gaugedTensor.sameMPV

/-- Equality of all closed matrix product vectors does not force positivity of
the associated per-block linear extension.

If this extension were positive, positive Skolem--Noether would give a unitary
implementer.  Its action on the four tensor letters would produce the positive
isometric realization excluded by `no_positive_isometric_realization`.

This distinguishes the generic virtual extension from the positive maps
induced by physical channels in arXiv:1606.00608, Appendix C.4.  In the
converse argument at lines 2048--2057, such channels are constructed only
after the unitary gauges are asserted.  Proposition 4.13, lines 1898--1921,
instead compares actual physical sector realizations. -/
theorem perBlockLinearExtension_not_positive :
    ¬ IsPositiveMap
      (perBlockLinearExtension tensorFamily gaugedTensorFamily
        tensorFamily_isInjective tensorFamily_sameMPV_gaugedTensorFamily 0) := by
  intro hPos
  obtain ⟨U, hU⟩ := exists_unitary_conj_of_positive_perBlockLinearExtension
    tensorFamily gaugedTensorFamily tensorFamily_isInjective
      tensorFamily_sameMPV_gaugedTensorFamily 0 hPos
  have hUnitary :
      (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
        (U : Matrix (Fin 2) (Fin 2) ℂ) = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (Matrix.mem_unitaryGroup_iff'.mp U.property)
  apply no_positive_isometric_realization
  refine ⟨1, (U : Matrix (Fin 2) (Fin 2) ℂ), by norm_num, hUnitary, ?_⟩
  intro i
  have hSpec := perBlockLinearExtension_spec tensorFamily gaugedTensorFamily
    tensorFamily_isInjective tensorFamily_sameMPV_gaugedTensorFamily 0 i
  simp only [tensorFamily, gaugedTensorFamily] at hSpec
  have hLetter : gaugedTensor i =
      (U : Matrix (Fin 2) (Fin 2) ℂ) * tensor i *
        (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ :=
    hSpec.symm.trans (hU (tensor i))
  rw [hLetter]
  simp only [Complex.ofReal_one, one_smul]
  calc
    (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
          ((U : Matrix (Fin 2) (Fin 2) ℂ) * tensor i *
            (U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ) *
        (U : Matrix (Fin 2) (Fin 2) ℂ) =
        ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
          (U : Matrix (Fin 2) (Fin 2) ℂ)) * tensor i *
            ((U : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
              (U : Matrix (Fin 2) (Fin 2) ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = tensor i := by rw [hUnitary, Matrix.one_mul, Matrix.mul_one]

end MPSTensor.PositiveMinimalRealizationCounterexample
