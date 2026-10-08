import TNLean.PEPS.AreaLaw.RegularizedPatchMarginal
import TNLeanTest.Support.SingleQubitConfig

/-! A zero coordinate weight does not force its minimizing density to commute
with the marginal of the actual normalized output. -/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix TNLean.PEPS TNLeanTest.SingleQubitConfig

private def regions : Fin 1 → Finset Unit := fun _ ↦ Finset.univ

private noncomputable def plusDensity : Matrix (Fin 2) (Fin 2) ℂ :=
  !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

private def zeroDensity : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

private noncomputable def densities (_ : Fin 1) : Matrix Config Config ℂ :=
  Matrix.reindex configEquiv configEquiv plusDensity

private theorem plusDensity_posSemidef : plusDensity.PosSemidef := by
  have h : plusDensity = (1 / 2 : ℝ) • Matrix.vecMulVec ![1, 1] (star ![1, 1]) := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [plusDensity, Matrix.vecMulVec]
  rw [h]
  exact (Matrix.posSemidef_vecMulVec_self_star ![1, 1]).smul
    (by norm_num : (0 : ℝ) ≤ 1 / 2)

private theorem densities_feasible :
    densities ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions := by
  intro j
  constructor
  · exact plusDensity_posSemidef.submatrix configEquiv.symm
  · change (∑ σ, plusDensity (configEquiv.symm σ) (configEquiv.symm σ)) = 1
    refine (configEquiv.symm.sum_comp (fun i ↦ plusDensity i i)).trans ?_
    norm_num [plusDensity, Fin.sum_univ_two]

private noncomputable def unitVector : EuclideanSpace ℂ Config :=
  PiLp.single 2 (configEquiv 0) 1

private theorem unitVector_norm : ‖unitVector‖ = 1 := by simp [unitVector]

open Classical in
private theorem zeroFilter_eq_one (x : Fin 1 → Matrix Config Config ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions)
    (j : Fin 1) :
    regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2) regions (fun _ ↦ 0) 1 x j = 1 := by
  classical
  simp only [regularizedPatchFilter, neg_zero, zero_div]
  have hp : (x j + (1 : ℝ) • 1) ^ (0 : ℝ) = 1 :=
    CFC.rpow_zero _ ((hx j).1.add_smul_one_posDef (b := 1) zero_lt_one).posSemidef.nonneg
  convert! (congrArg (dependentRegionOperatorLift (Out := fun _ : Unit ↦ Fin 2)
    (regions j)) hp).trans (dependentRegionOperatorLift_one (regions j)) using 1
  congr 8 <;> first | exact Subsingleton.elim _ _ | exact proof_irrel_heq _ _

private theorem zeroOperator_eq_one (x : Fin 1 → Matrix Config Config ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) :
    regularizedPatchOperator (Out := fun _ : Unit ↦ Fin 2) regions (fun _ ↦ 0) 1 x = 1 := by
  classical
  simp [regularizedPatchOperator, zeroFilter_eq_one x hx,
    List.ofFn_succ, List.ofFn_zero]

private theorem zeroOutput_eq (x : Fin 1 → Matrix Config Config ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) :
    regularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector x = unitVector := by
  classical
  simp [regularizedPatchOutput, zeroOperator_eq_one x hx]

private theorem zeroObjective_eq_one (x : Fin 1 → Matrix Config Config ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) :
    regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector x = 1 := by
  change ‖regularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2) regions
    (fun _ ↦ 0) 1 unitVector x‖ = 1
  rw [zeroOutput_eq x hx, unitVector_norm]

private theorem zeroNormalizedOutput_eq (x : Fin 1 → Matrix Config Config ℂ)
    (hx : x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) :
    normalizedRegularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector x = unitVector := by
  change (regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
    (fun _ ↦ 0) 1 unitVector x)⁻¹ •
      regularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2) regions
        (fun _ ↦ 0) 1 unitVector x = unitVector
  rw [zeroObjective_eq_one x hx,
    zeroOutput_eq x hx, inv_one, one_smul]

private theorem densities_minimize :
    IsMinOn (regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector)
      (regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) densities := by
  intro x hx
  change regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
    (fun _ ↦ 0) 1 unitVector densities ≤
      regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector x
  rw [zeroObjective_eq_one densities densities_feasible, zeroObjective_eq_one x hx]

private theorem reducedPure_univ (ξ : EuclideanSpace ℂ Config) :
    FiniteProduct.reducedPure (fun _ : Unit ↦ Fin 2)
      (dependentGlobalConfigIsometry ξ) Finset.univ =
        Matrix.vecMulVec (WithLp.ofLp ξ) (star (WithLp.ofLp ξ)) := by
  classical
  have hs (α : Config)
      (τ : FiniteProduct.Configuration (fun _ : Unit ↦ Fin 2)
        ((Finset.univ : Finset Unit)ᶜ)) :
      dependentGlobalConfigIsometry ξ
          ((FiniteProduct.splitEquiv (fun _ : Unit ↦ Fin 2) Finset.univ).symm (α, τ)) =
        ξ α := by
    rw [dependentGlobalConfigIsometry_apply]
    apply congrArg (fun σ : Config ↦ ξ σ)
    funext v
    exact FiniteProduct.splitEquiv_symm_apply_of_mem
      (fun _ : Unit ↦ Fin 2) Finset.univ α τ v.1 (Finset.mem_univ _)
  ext α β
  simp only [FiniteProduct.reducedPure, FiniteProduct.reducedMatrix_apply,
    Matrix.vecMulVec_apply, Pi.star_apply]
  simp [hs, FiniteProduct.Configuration]

private theorem unitVector_density :
    Matrix.vecMulVec (WithLp.ofLp unitVector) (star (WithLp.ofLp unitVector)) =
      Matrix.reindex configEquiv configEquiv zeroDensity := by
  classical
  ext α β
  obtain ⟨i, rfl⟩ := configEquiv.surjective α
  obtain ⟨j, rfl⟩ := configEquiv.surjective β
  fin_cases i <;> fin_cases j <;>
    simp [unitVector, zeroDensity, Matrix.vecMulVec_apply, Matrix.reindex_apply]

private theorem actualMarginal_eq :
    normalizedRegularizedPatchMarginal (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector densities
      Finset.univ = Matrix.reindex configEquiv configEquiv zeroDensity := by
  unfold normalizedRegularizedPatchMarginal
  rw [zeroNormalizedOutput_eq densities densities_feasible]
  convert! (reducedPure_univ unitVector).trans unitVector_density using 1

private theorem actualMarginal_not_commute :
    ¬ Commute (densities 0)
      (normalizedRegularizedPatchMarginal (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector densities
        Finset.univ) := by
  rw [actualMarginal_eq]
  intro h
  have hm : Commute plusDensity zeroDensity := by
    convert h.map (Matrix.reindexRingEquiv ℂ configEquiv.symm).toMonoidHom using 1 <;>
      ext i j <;> simp [densities, Matrix.reindexRingEquiv, Matrix.reindex_apply]
  have hc := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ ↦ M 0 1) hm.eq
  norm_num [plusDensity, zeroDensity, Matrix.mul_apply, Fin.sum_univ_two] at hc

/-- Even an actual feasible global minimizer need not commute with its actual
output marginal when the selected coordinate has zero weight. -/
example :
    ∃ x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions,
      IsMinOn (regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector)
        (regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) regions) x ∧
      ¬ Commute (x 0)
        (normalizedRegularizedPatchMarginal (Out := fun _ : Unit ↦ Fin 2) regions
      (fun _ ↦ 0) 1 unitVector x
          Finset.univ) :=
  ⟨densities, densities_feasible, densities_minimize, actualMarginal_not_commute⟩
