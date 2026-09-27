/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Examples.AKLT
import TNLean.MPS.Symmetry.TimeReversalIndex

/-!
# AKLT state: time-reversal and reflection symmetry with non-trivial index

**Source.** Cirac, Pérez-García, Schuch, Verstraete (arXiv:2011.12127), §III.A,
`Papers/2011.12127/TN-Review-main.tex` line 1159: the SPT character of the AKLT
state "can be protected by multiple distinct physical symmetries: on-site `SO(3)`
…, on-site `Z₂ × Z₂` …, time-reversal, or reflection symmetry.  In all these cases,
the AKLT MPS tensor transforms projectively."  The time-reversal and reflection
indices are the signs `X X* = ±1` of lines 1116–1120.
Review: arXiv:2011.12127, Appendix A, "The AKLT state".

**Formalized here.** In the basis `(m = 0, m = +1, m = -1)` of `akltTensor`,
time reversal acts as complex conjugation composed with the spin-`1` rotation
`e^{iπ S_y}`, the matrix `akltSpinRotationY`.  The AKLT tensor satisfies
`conj(∑ⱼ (e^{iπ S_y})ᵢⱼ Aʲ) = X† Aⁱ X` and `(Aⁱ)ᵀ = -X† Aⁱ X` with
`X = iσ_y`, and `X X* = -1`.  Every unitary gauge of either symmetry has the same
index `-1`, so both indices are non-trivial.

The cohomology counts of lines 1161–1162 are not formalized here.

## Main definitions

* `MPSTensor.akltSpinRotationY` : the spin-`1` rotation `e^{iπ S_y}`
* `MPSTensor.akltAntisymmetricGauge` : the unitary gauge `iσ_y`

## Main results

* `MPSTensor.akltTensor_timeReversal`, `MPSTensor.akltTensor_reflection`
* `MPSTensor.akltAntisymmetricGauge_mul_map_star`
* `MPSTensor.aklt_timeReversal_index_eq_neg_one`
* `MPSTensor.aklt_reflection_index_eq_neg_one`

## References

- [arXiv:2011.12127](https://arxiv.org/abs/2011.12127) -- Cirac, Pérez-García,
  Schuch, Verstraete, *Matrix product states and projected entangled pair states:
  Concepts, symmetries, theorems*
-/

open scoped Matrix BigOperators

noncomputable section

namespace MPSTensor

/-- The spin-`1` rotation `e^{iπ S_y}` in the basis `(m = 0, m = +1, m = -1)` of
`akltTensor`: it sends `|0⟩ ↦ -|0⟩` and exchanges `|+1⟩` and `|-1⟩`.  Source:
arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex` line 1159). -/
def akltSpinRotationY : Matrix (Fin 3) (Fin 3) ℂ :=
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

/-- The rotation `e^{iπ S_y}` is real and squares to the identity, so time reversal
`K e^{iπ S_y}` squares to the identity on the spin-`1` site. -/
theorem akltSpinRotationY_mul_map_star :
    akltSpinRotationY * akltSpinRotationY.map (starRingEnd ℂ) = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [akltSpinRotationY, Matrix.mul_apply, Fin.sum_univ_three]

/-- The antisymmetric unitary gauge `iσ_y = !![0, 1; -1, 0]`. -/
def akltAntisymmetricGauge : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨!![0, 1; -1, 0], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_eq_conjTranspose]⟩

@[simp] lemma akltAntisymmetricGauge_val :
    (akltAntisymmetricGauge : Matrix (Fin 2) (Fin 2) ℂ) = !![0, 1; -1, 0] := rfl

/-- The gauge `iσ_y` satisfies `X X* = -1`. -/
theorem akltAntisymmetricGauge_mul_map_star :
    (akltAntisymmetricGauge : Matrix (Fin 2) (Fin 2) ℂ) *
      (akltAntisymmetricGauge : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = -1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- **Time-reversal symmetry of the AKLT tensor.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
line 1159): time reversal `A ↦ conj(e^{iπ S_y} A)` is implemented by the virtual
gauge `iσ_y` with trivial phase. -/
theorem akltTensor_timeReversal (i : Fin 3) :
    (∑ j : Fin 3, akltSpinRotationY i j • akltTensor j).map (starRingEnd ℂ) =
      (akltAntisymmetricGauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * akltTensor i *
        akltAntisymmetricGauge := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltSpinRotationY, akltTensor, Fin.sum_univ_three, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- **Reflection symmetry of the AKLT tensor.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1120 and 1159): reflection transposes the MPS matrices, and
`(Aⁱ)ᵀ = -X† Aⁱ X` with `X = iσ_y`. -/
theorem akltTensor_reflection (i : Fin 3) :
    (akltTensor i)ᵀ = (-1 : ℂ) • ((akltAntisymmetricGauge : Matrix (Fin 2) (Fin 2) ℂ)ᴴ *
      akltTensor i * akltAntisymmetricGauge) := by
  fin_cases i <;> ext a b <;> fin_cases a <;> fin_cases b <;>
    simp [akltTensor, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply]

/-- **The AKLT time-reversal index is `-1`.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1117 and 1159).  For every unitary gauge `X` and scalar `ζ` implementing time
reversal, `conj(∑ⱼ (e^{iπ S_y})ᵢⱼ Aʲ) = ζ X† Aⁱ X`, the index is `X X* = -1`. -/
theorem aklt_timeReversal_index_eq_neg_one (X : Matrix.unitaryGroup (Fin 2) ℂ) {ζ : ℂ}
    (h : ∀ i, (∑ j : Fin 3, akltSpinRotationY i j • akltTensor j).map (starRingEnd ℂ) =
      ζ • ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * akltTensor i * X)) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = -1 := by
  -- Conjugating the physical mixing gives the antiunitary twist by `conj(e^{iπ S_y})`.
  have hmix : ∀ (M : Matrix (Fin 3) (Fin 3) ℂ) (i : Fin 3),
      (∑ j : Fin 3, M i j • akltTensor j).map (starRingEnd ℂ) =
        ∑ j : Fin 3, M.map (starRingEnd ℂ) i j • (akltTensor j).map (starRingEnd ℂ) := by
    intro M i; ext a b; simp [Matrix.sum_apply]
  have hP : akltSpinRotationY.map (starRingEnd ℂ) *
      (akltSpinRotationY.map (starRingEnd ℂ)).map (starRingEnd ℂ) = 1 := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [akltSpinRotationY, Matrix.mul_apply, Fin.sum_univ_three]
  rw [mul_map_star_eq_of_timeReversal_gauges aklt_isNormal hP X akltAntisymmetricGauge
    (fun i => (hmix _ i).symm.trans (h i))
    (fun i => by rw [← hmix, akltTensor_timeReversal, one_smul])]
  exact akltAntisymmetricGauge_mul_map_star

/-- **The AKLT reflection index is `-1`.**
Source: arXiv:2011.12127, §III.A (`Papers/2011.12127/TN-Review-main.tex`
lines 1120 and 1159).  For every unitary gauge `X` and scalar `ζ` with
`(Aⁱ)ᵀ = ζ X† Aⁱ X`, the index is `X X* = -1`. -/
theorem aklt_reflection_index_eq_neg_one (X : Matrix.unitaryGroup (Fin 2) ℂ) {ζ : ℂ}
    (h : ∀ i, (akltTensor i)ᵀ = ζ • ((X : Matrix (Fin 2) (Fin 2) ℂ)ᴴ * akltTensor i * X)) :
    (X : Matrix (Fin 2) (Fin 2) ℂ) * (X : Matrix (Fin 2) (Fin 2) ℂ).map (starRingEnd ℂ) = -1 := by
  rw [mul_map_star_eq_of_reflection_gauges aklt_isNormal X akltAntisymmetricGauge h
    akltTensor_reflection]
  exact akltAntisymmetricGauge_mul_map_star

end MPSTensor
