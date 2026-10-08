import TNLean.PEPS.AreaLaw.RegularizedPatchMinimum
import TNLeanTest.Support.SingleQubitConfig

/-! Two independent singular densities on the same physical qubit give noncommuting filters. -/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix TNLean.PEPS TNLeanTest.SingleQubitConfig

private def firstDensity : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

private noncomputable def secondDensity : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private theorem firstDensity_psd : firstDensity.PosSemidef := by
  have h : firstDensity = diagonal ![1, 0] := by ext i j; fin_cases i <;> fin_cases j <;> rfl
  rw [h]
  apply PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

private theorem secondDensity_psd : secondDensity.PosSemidef := by
  have h : secondDensity = (1 / 2 : ℝ) • Matrix.vecMulVec ![1, 1] (star ![1, 1]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [secondDensity, Matrix.vecMulVec]
  rw [h]
  exact (Matrix.posSemidef_vecMulVec_self_star ![1, 1]).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)

private noncomputable def densities (j : Fin 2) : Matrix Config Config ℂ :=
  Matrix.reindex configEquiv configEquiv (if j = 0 then firstDensity else secondDensity)

private theorem densities_feasible :
    densities ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) := by
  intro j
  constructor
  · change ((if j = 0 then firstDensity else secondDensity).submatrix
      configEquiv.symm configEquiv.symm).PosSemidef
    apply Matrix.PosSemidef.submatrix
    split_ifs
    · exact firstDensity_psd
    · exact secondDensity_psd
  · change (∑ i, (if j = 0 then firstDensity else secondDensity)
      (configEquiv.symm i) (configEquiv.symm i)) = 1
    refine (configEquiv.symm.sum_comp
      (fun i ↦ (if j = 0 then firstDensity else secondDensity) i i)).trans ?_
    split_ifs <;> norm_num [firstDensity, secondDensity, Fin.sum_univ_two]

example : firstDensity.det = 0 ∧ secondDensity.det = 0 := by
  norm_num [firstDensity, secondDensity, Matrix.det_fin_two]

open Classical in
private theorem filter_eq_inverse (j : Fin 2) :
    regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities j = (densities j + 1)⁻¹ := by
  classical
  rw [regularizedPatchFilter, lift_univ]
  norm_num only [one_smul, show -(2 : ℝ) / 2 = -1 by norm_num]
  rw [Matrix.nonsing_inv_eq_ringInverse]
  symm
  have hp : IsStrictlyPositive (densities j + 1) := by
    simpa only [one_smul] using ((densities_feasible j).1.add_smul_one_posDef
      (b := 1) zero_lt_one).isStrictlyPositive
  convert! CFC.inverse_eq_rpow_neg_one hp using 2 <;> congr!

private theorem first_inverse : (firstDensity + 1)⁻¹ = !![1 / 2, 0; 0, 1] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [firstDensity, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem second_inverse : (secondDensity + 1)⁻¹ = !![3 / 4, -(1 / 4); -(1 / 4), 3 / 4] := by
  apply Matrix.inv_eq_left_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondDensity, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]

private theorem filters_not_commute : ¬ Commute
    (regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 0)
    (regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 1) := by
  rw [filter_eq_inverse, filter_eq_inverse]
  have he (A : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix.reindex configEquiv configEquiv A + 1 =
        Matrix.reindex configEquiv configEquiv (A + 1) := by
    simp [Matrix.reindex_apply, Matrix.submatrix_add]
  change ¬ Commute ((Matrix.reindex configEquiv configEquiv firstDensity + 1)⁻¹)
    ((Matrix.reindex configEquiv configEquiv secondDensity + 1)⁻¹)
  rw [he, he, Matrix.inv_reindex, Matrix.inv_reindex, first_inverse, second_inverse]
  intro h
  have hm : Commute (!![1 / 2, 0; 0, 1] : Matrix (Fin 2) (Fin 2) ℂ)
      !![3 / 4, -(1 / 4); -(1 / 4), 3 / 4] := by
    convert h.map (Matrix.reindexRingEquiv ℂ configEquiv.symm).toMonoidHom using 1 <;>
      ext i j <;> simp [Matrix.reindexRingEquiv, Matrix.reindex_apply]
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 1) hm.eq
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at hc

private theorem operator_two :
    regularizedPatchOperator (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities =
    regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 1 *
      regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 0 := by
  classical
  simp only [regularizedPatchOperator, List.ofFn_succ, Fin.isValue, Fin.succ_zero_eq_one,
    List.ofFn_zero, List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.prod_cons, List.prod_nil, Matrix.mul_one]
  congr!

example :
    regularizedPatchOperator (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities ≠
    regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 0 *
      regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 2 ↦ Finset.univ)
      (fun _ ↦ 2) 1 densities 1 := by
  rw [operator_two]
  intro h
  exact filters_not_commute h.symm

private noncomputable def unitVector : EuclideanSpace ℂ Config :=
  PiLp.single 2 (configEquiv 0) 1

private theorem unitVector_norm : ‖unitVector‖ = 1 := by simp [unitVector]

example :
    (1 / 4 : ℝ) ≤ regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) (fun _ ↦ 2) 1 unitVector densities ∧
    regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) (fun _ ↦ 2) 1 unitVector densities ≤ 1 := by
  have h := regularizedPatchObjective_bounds (Out := fun _ : Unit ↦ Fin 2)
    (fun _ : Fin 2 ↦ Finset.univ) (fun _ ↦ 2) (by intro j; norm_num) zero_lt_one
    unitVector unitVector_norm densities_feasible
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

example :
    ‖normalizedRegularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) (fun _ ↦ 2) 1 unitVector densities‖ = 1 :=
  norm_normalizedRegularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2)
    (fun _ : Fin 2 ↦ Finset.univ) (fun _ ↦ 2) (by intro j; norm_num) zero_lt_one
    unitVector unitVector_norm densities_feasible
