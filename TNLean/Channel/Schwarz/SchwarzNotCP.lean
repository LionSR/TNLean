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

private noncomputable def wolfExample53Gap (A : M2) : M2 :=
  wolfExample53 (Aᴴ * A) - wolfExample53 (Aᴴ) * wolfExample53 A

private def wolfExample53J : M2 := ![![0, -1], ![1, 0]]

private lemma trace_smul_one_sub_eq_wolfExample53J_mul_transpose_mul_conjTranspose (M : M2) :
    Matrix.trace M • (1 : M2) - M = wolfExample53J * Mᵀ * wolfExample53Jᴴ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [wolfExample53J, Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two]

private lemma trace_smul_one_sub_posSemidef_of_posSemidef (M : M2) (hM : M.PosSemidef) :
    (Matrix.trace M • (1 : M2) - M).PosSemidef := by
  rw [trace_smul_one_sub_eq_wolfExample53J_mul_transpose_mul_conjTranspose]
  exact (hM.transpose).mul_mul_conjTranspose_same wolfExample53J

private lemma add_smul_one_mul_add_smul_one (X Y : M2) (a b : ℂ) :
    (X + a • (1 : M2)) * (Y + b • (1 : M2)) =
      X * Y + b • X + a • Y + (a * b) • (1 : M2) := by
  calc
    (X + a • (1 : M2)) * (Y + b • (1 : M2))
        = X * Y + X * (b • (1 : M2)) + (a • (1 : M2)) * Y + (a • (1 : M2)) * (b • (1 : M2)) := by
            simp [Matrix.add_mul, Matrix.mul_add, add_assoc, add_left_comm, add_comm]
    _ = X * Y + b • X + a • Y + (a * b) • (1 : M2) := by
            simp [smul_smul, add_assoc, add_left_comm, add_comm, mul_comm]

private lemma wolfExample53_smul_one (z : ℂ) :
    wolfExample53 (z • (1 : M2)) = z • (1 : M2) := by
  rw [map_smul, wolfExample53_one]

private lemma wolfExample53_add_smul_one (X : M2) (z : ℂ) :
    wolfExample53 (X + z • (1 : M2)) = wolfExample53 X + z • (1 : M2) := by
  rw [map_add, wolfExample53_smul_one]

private lemma wolfExample53Gap_translate (A : M2) (z : ℂ) :
    wolfExample53Gap (A + z • (1 : M2)) = wolfExample53Gap A := by
  have hmul :
      (A + z • (1 : M2))ᴴ * (A + z • (1 : M2)) =
        Aᴴ * A + z • Aᴴ + star z • A + (star z * z) • (1 : M2) := by
    calc
      (A + z • (1 : M2))ᴴ * (A + z • (1 : M2))
          = (Aᴴ + star z • (1 : M2)) * (A + z • (1 : M2)) := by simp
      _ = Aᴴ * A + z • Aᴴ + star z • A + (star z * z) • (1 : M2) :=
        add_smul_one_mul_add_smul_one (X := Aᴴ) (Y := A) (a := star z) (b := z)
  have hleft : wolfExample53 ((A + z • (1 : M2))ᴴ) = wolfExample53 Aᴴ + star z • (1 : M2) := by
    calc
      wolfExample53 ((A + z • (1 : M2))ᴴ)
          = wolfExample53 (Aᴴ + star z • (1 : M2)) := by simp
      _ = wolfExample53 Aᴴ + star z • (1 : M2) :=
        wolfExample53_add_smul_one (X := Aᴴ) (z := star z)
  have hright : wolfExample53 (A + z • (1 : M2)) = wolfExample53 A + z • (1 : M2) :=
    wolfExample53_add_smul_one (X := A) (z := z)
  have himage :
      wolfExample53 ((A + z • (1 : M2))ᴴ * (A + z • (1 : M2))) =
        wolfExample53 (Aᴴ * A) + z • wolfExample53 Aᴴ + star z • wolfExample53 A +
          (star z * z) • (1 : M2) := by
    rw [hmul, map_add, map_add, map_add, map_smul, map_smul, wolfExample53_smul_one]
  have hprod :
      (wolfExample53 Aᴴ + star z • (1 : M2)) * (wolfExample53 A + z • (1 : M2)) =
        wolfExample53 Aᴴ * wolfExample53 A + z • wolfExample53 Aᴴ +
          star z • wolfExample53 A + (star z * z) • (1 : M2) :=
    add_smul_one_mul_add_smul_one (X := wolfExample53 Aᴴ) (Y := wolfExample53 A)
      (a := star z) (b := z)
  calc
    wolfExample53Gap (A + z • (1 : M2))
        = (wolfExample53 (Aᴴ * A) + z • wolfExample53 Aᴴ + star z • wolfExample53 A +
              (star z * z) • (1 : M2)) -
            ((wolfExample53 Aᴴ + star z • (1 : M2)) * (wolfExample53 A + z • (1 : M2))) := by
          rw [wolfExample53Gap, himage, hleft, hright]
    _ = (wolfExample53 (Aᴴ * A) + z • wolfExample53 Aᴴ + star z • wolfExample53 A +
            (star z * z) • (1 : M2)) -
          (wolfExample53 Aᴴ * wolfExample53 A + z • wolfExample53 Aᴴ +
            star z • wolfExample53 A + (star z * z) • (1 : M2)) := by rw [hprod]
    _ = wolfExample53Gap A := by
          simp [wolfExample53Gap, sub_eq_add_neg]
          abel_nf

private lemma wolfExample53Gap_eq_of_trace_zero (A : M2) (htr : Matrix.trace A = 0) :
    wolfExample53Gap A =
      (1 / 2 : ℂ) • (Aᴴ * A)ᵀ +
        (1 / 4 : ℂ) • ((Matrix.trace (Aᴴ * A) • (1 : M2) - A * Aᴴ)ᵀ) := by
  have hA : wolfExample53 A = (1 / 2 : ℂ) • Aᵀ := by
    simp [wolfExample53, htr]
  have hAadj : wolfExample53 Aᴴ = (1 / 2 : ℂ) • (Aᴴ)ᵀ := by
    simp [wolfExample53, Matrix.trace_conjTranspose, htr]
  have hquarter : ((1 / 2 : ℂ) * (1 / 2 : ℂ)) = (1 / 4 : ℂ) := by
    ring
  have hprod : wolfExample53 Aᴴ * wolfExample53 A = (1 / 4 : ℂ) • ((A * Aᴴ)ᵀ) := by
    calc
      wolfExample53 Aᴴ * wolfExample53 A
          = ((1 / 2 : ℂ) • (Aᴴ)ᵀ) * ((1 / 2 : ℂ) • Aᵀ) := by rw [hAadj, hA]
      _ = ((1 / 2 : ℂ) * (1 / 2 : ℂ)) • ((Aᴴ)ᵀ * Aᵀ) := by
            simp [smul_smul]
      _ = (1 / 4 : ℂ) • ((A * Aᴴ)ᵀ) := by
            rw [hquarter]
            have hmulT : (A * Aᴴ)ᵀ = (Aᴴ)ᵀ * Aᵀ := by
              exact Matrix.transpose_mul A Aᴴ
            rw [hmulT]
  calc
    wolfExample53Gap A = wolfExample53 (Aᴴ * A) - (1 / 4 : ℂ) • ((A * Aᴴ)ᵀ) := by
      rw [wolfExample53Gap, hprod]
    _ = ((1 / 2 : ℂ) • (Aᴴ * A)ᵀ + (1 / 4 : ℂ) • (Matrix.trace (Aᴴ * A) • (1 : M2))) -
            (1 / 4 : ℂ) • ((A * Aᴴ)ᵀ) := by
      rfl
    _ = (1 / 2 : ℂ) • (Aᴴ * A)ᵀ +
          (1 / 4 : ℂ) • ((Matrix.trace (Aᴴ * A) • (1 : M2) - A * Aᴴ)ᵀ) := by
      simp [sub_eq_add_neg, smul_add, add_left_comm, add_comm]

private lemma wolfExample53Gap_posSemidef_of_trace_zero (A : M2) (htr : Matrix.trace A = 0) :
    (wolfExample53Gap A).PosSemidef := by
  rw [wolfExample53Gap_eq_of_trace_zero A htr]
  have h1 : ((1 / 2 : ℂ) • (Aᴴ * A)ᵀ).PosSemidef := by
    exact (Matrix.posSemidef_conjTranspose_mul_self A).transpose.smul complex_one_half_nonneg
  have h2base : (Matrix.trace (A * Aᴴ) • (1 : M2) - A * Aᴴ).PosSemidef := by
    exact trace_smul_one_sub_posSemidef_of_posSemidef (A * Aᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose A)
  have htrace : Matrix.trace (Aᴴ * A) = Matrix.trace (A * Aᴴ) := by
    simpa using Matrix.trace_mul_comm Aᴴ A
  have h2 : ((1 / 4 : ℂ) • ((Matrix.trace (Aᴴ * A) • (1 : M2) - A * Aᴴ)ᵀ)).PosSemidef := by
    have h2' : ((Matrix.trace (Aᴴ * A) • (1 : M2) - A * Aᴴ)ᵀ).PosSemidef := by
      simpa [htrace] using h2base.transpose
    exact h2'.smul complex_one_quarter_nonneg
  exact h1.add h2

/-- Wolf Example 5.3 satisfies the Schwarz inequality.

The intended proof is the concrete $2 \times 2$ argument from Wolf: after
shifting by a scalar multiple of the identity one may assume `trace A = 0`, and
then the Schwarz gap dominates `(1/2) • (Aᴴ * A)ᵀ`. -/
theorem wolfExample53_satisfies_schwarz (A : M2) :
    (wolfExample53 (Aᴴ * A) - wolfExample53 (Aᴴ) * wolfExample53 A).PosSemidef := by
  let B : M2 := A - ((Matrix.trace A) / 2 : ℂ) • (1 : M2)
  have hBtr : Matrix.trace B = 0 := by
    simp [B, Matrix.trace, Fin.sum_univ_two]
    ring
  have htranslate : wolfExample53Gap B = wolfExample53Gap A := by
    simpa [B, sub_eq_add_neg] using wolfExample53Gap_translate A (-(Matrix.trace A / 2 : ℂ))
  have hB : (wolfExample53Gap B).PosSemidef := wolfExample53Gap_posSemidef_of_trace_zero B hBtr
  have hA' : (wolfExample53Gap A).PosSemidef := by
    simpa [htranslate] using hB
  simpa [wolfExample53Gap] using hA'

/-- A concrete antisymmetric witness for the non-CP statement. -/
noncomputable def wolfExample53AntisymmVec : Fin 2 × Fin 2 → ℂ
  | (0, 1) => 1
  | (1, 0) => -1
  | _ => 0

private lemma omegaCoeff_fin2 :
    (((1 : ℂ) / ((2 : ℝ).sqrt : ℂ)) * star ((1 : ℂ) / ((2 : ℝ).sqrt : ℂ))) =
      (1 / 2 : ℂ) := by
  have hstar :
      star ((1 : ℂ) / ((2 : ℝ).sqrt : ℂ)) = (1 : ℂ) / ((2 : ℝ).sqrt : ℂ) := by
    simp [Complex.conj_ofReal]
  rw [hstar]
  have hne : (((2 : ℝ).sqrt : ℂ)) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    positivity
  field_simp [hne]
  have hsqR : ((2 : ℝ).sqrt) ^ 2 = 2 := by
    simp [Real.sq_sqrt]
  have hsq : (((2 : ℝ).sqrt : ℂ) ^ 2) = (2 : ℂ) := by
    exact_mod_cast hsqR
  simpa using hsq.symm

private lemma omegaSlice_fin2 (i j : Fin 2) :
    Matrix.bipartiteSlice (Matrix.omegaProj 2) i j = (1 / 2 : ℂ) • Matrix.single i j (1 : ℂ) := by
  ext a b
  by_cases ha : a = i <;> by_cases hb : b = j
  · subst ha; subst hb
    simp [Matrix.bipartiteSlice, Matrix.omegaProj_apply, Matrix.omegaVec_apply]
    simpa [one_div, Complex.conj_ofReal] using omegaCoeff_fin2
  · simp [Matrix.bipartiteSlice, Matrix.omegaProj_apply, Matrix.omegaVec_apply, Matrix.single_apply,
      ha, hb]
    simpa [eq_comm] using hb
  · simp [Matrix.bipartiteSlice, Matrix.omegaProj_apply, Matrix.omegaVec_apply, Matrix.single_apply,
      ha, hb]
    simpa [eq_comm] using ha
  · have hleft : Matrix.bipartiteSlice (Matrix.omegaProj 2) i j a b = 0 := by
      simp [Matrix.bipartiteSlice, Matrix.omegaProj_apply, Matrix.omegaVec_apply, ha]
    have hright : ((1 / 2 : ℂ) • Matrix.single i j (1 : ℂ)) a b = 0 := by
      have hia : ¬ i = a := by
        simpa [eq_comm] using ha
      simp [Matrix.smul_apply, hia]
    exact hleft.trans hright.symm

private lemma wolfExample53_choi_apply (i1 i2 j1 j2 : Fin 2) :
    ChoiJamiolkowski.choiMatrix wolfExample53 (i1, i2) (j1, j2) =
      (1 / 4 : ℂ) * (if i1 = j2 ∧ i2 = j1 then 1 else 0) +
      (1 / 8 : ℂ) * (if i1 = j1 ∧ i2 = j2 then 1 else 0) := by
  rw [ChoiJamiolkowski.choiMatrix_apply, omegaSlice_fin2]
  fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2 <;>
    simp [wolfExample53, Matrix.trace] <;> ring

/-- The Choi matrix of `wolfExample53` has a negative expectation value on the
antisymmetric vector `|01⟩ - |10⟩`, hence is not positive semidefinite. -/
theorem wolfExample53_choi_negative_antisymm :
    star wolfExample53AntisymmVec ⬝ᵥ
        (ChoiJamiolkowski.choiMatrix wolfExample53).mulVec wolfExample53AntisymmVec =
      (- (1 / 4 : ℂ)) := by
  simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, wolfExample53AntisymmVec,
    wolfExample53_choi_apply]
  ring

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
