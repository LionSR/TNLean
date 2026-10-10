import TNLean.PEPS.AreaLaw.RegularizedPatchStationarity
import TNLeanTest.Support.SingleQubitConfig

/-! A feasible singular density with nonzero first variation is not a minimizer. -/

open scoped BigOperators Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix TNLean.PEPS TNLeanTest.SingleQubitConfig

noncomputable local instance : DecidableEq Config := Classical.typeDecidableEq _

private def generator : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

private noncomputable def localFilter : Matrix (Fin 2) (Fin 2) ℂ :=
  !![3 / 4, -(1 / 4); -(1 / 4), 3 / 4]

private noncomputable def x (_ : Fin 1) : Matrix Config Config ℂ :=
  Matrix.reindex configEquiv configEquiv plusDensity

private noncomputable def B : Matrix Config Config ℂ :=
  Matrix.reindex configEquiv configEquiv generator

private noncomputable def Ω : EuclideanSpace ℂ Config :=
  WithLp.toLp 2 (fun σ ↦ ![1, 0] (configEquiv.symm σ))

private theorem feasible :
    x ∈ regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 1 ↦ Finset.univ) := by
  intro j
  constructor
  · exact plusDensity_posSemidef.submatrix configEquiv.symm
  · change (∑ i, plusDensity (configEquiv.symm i) (configEquiv.symm i)) = 1
    refine (configEquiv.symm.sum_comp (fun i ↦ plusDensity i i)).trans ?_
    norm_num [plusDensity, Fin.sum_univ_two]

private theorem B_skew : star B = -B := by
  ext σ τ
  obtain ⟨i, rfl⟩ := configEquiv.surjective σ
  obtain ⟨j, rfl⟩ := configEquiv.surjective τ
  fin_cases i <;> fin_cases j <;>
    norm_num [B, generator, Matrix.reindex_apply, Matrix.conjTranspose_apply]

example : plusDensity.det = 0 := by
  norm_num [plusDensity, Matrix.det_fin_two]

/-- Repeated copies of one region remain independent coordinates. -/
example (z : Fin 2 → Matrix Config Config ℂ) (U : Matrix Config Config ℂ) :
    regularizedPatchCoordinateUpdate (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) z 0 U 1 = z 1 := by
  simp [regularizedPatchCoordinateUpdate]

open Classical in
example (a : Fin 2 → ℝ) (b : ℝ) (z : Fin 2 → Matrix Config Config ℂ)
    (K : Matrix Config Config ℂ) :
    regularizedPatchInsertion (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) a b Ω z 0 K =
      WithLp.toLp 2 ((regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2)
        (fun _ : Fin 2 ↦ Finset.univ) a b z 1 * K) *ᵥ Ω) := by
  rw [regularizedPatchInsertion_apply]
  simp [List.ofFn_succ, lift_univ]
  congr 1

open Classical in
example (a : Fin 2 → ℝ) (b : ℝ) (z : Fin 2 → Matrix Config Config ℂ)
    (K : Matrix Config Config ℂ) :
    regularizedPatchInsertion (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 2 ↦ Finset.univ) a b Ω z 1 K =
      WithLp.toLp 2 ((K * regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2)
        (fun _ : Fin 2 ↦ Finset.univ) a b z 0) *ᵥ Ω) := by
  rw [regularizedPatchInsertion_apply]
  simp [List.ofFn_succ, lift_univ]
  congr 1

open Classical in
private theorem shifted_power :
    (x 0 + (1 : ℝ) • 1) ^ (-(2 : ℝ) / 2) =
      Matrix.reindex configEquiv configEquiv localFilter := by
  have hp : IsStrictlyPositive (x 0 + 1) := by
    simpa only [one_smul] using ((feasible 0).1.add_smul_one_posDef
      (b := 1) zero_lt_one).isStrictlyPositive
  have hinv : (plusDensity + 1)⁻¹ = localFilter := by
    apply Matrix.inv_eq_left_inv
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [plusDensity, localFilter, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply]
  norm_num only [one_smul, show -(2 : ℝ) / 2 = -1 by norm_num]
  have hpow : (x 0 + 1) ^ (-1 : ℝ) = (x 0 + 1)⁻¹ := by
    rw [Matrix.nonsing_inv_eq_ringInverse]
    convert! (CFC.inverse_eq_rpow_neg_one hp).symm using 2
  rw [hpow]
  have he : x 0 + 1 = Matrix.reindex configEquiv configEquiv (plusDensity + 1) := by
    simp [x, Matrix.reindex_apply, Matrix.submatrix_add]
  rw [he, Matrix.inv_reindex, hinv]

open Classical in
private theorem insertion_single (K : Matrix Config Config ℂ) :
    regularizedPatchInsertion (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 1 ↦ Finset.univ)
      (fun _ ↦ 2) 1 Ω x 0 K = WithLp.toLp 2 (K *ᵥ Ω) := by
  rw [regularizedPatchInsertion_apply]
  simp [List.ofFn_succ, lift_univ]
  congr 1

private theorem inner_conjugated (A C : Matrix (Fin 2) (Fin 2) ℂ) :
    inner ℂ (WithLp.toLp 2 ((Matrix.reindex configEquiv configEquiv A) *ᵥ Ω))
      (WithLp.toLp 2 ((Matrix.reindex configEquiv configEquiv C) *ᵥ Ω)) =
      inner ℂ (WithLp.toLp 2 (A *ᵥ ![1, 0])) (WithLp.toLp 2 (C *ᵥ ![1, 0])) := by
  have hm (M : Matrix (Fin 2) (Fin 2) ℂ) (σ : Config) :
      ((Matrix.reindex configEquiv configEquiv M) *ᵥ Ω) σ =
        (M *ᵥ ![1, 0]) (configEquiv.symm σ) := by
    change (∑ τ, M (configEquiv.symm σ) (configEquiv.symm τ) *
      ![1, 0] (configEquiv.symm τ)) = _
    exact configEquiv.symm.sum_comp
      (fun τ : Fin 2 ↦ M (configEquiv.symm σ) τ * (![1, 0] : Fin 2 → ℂ) τ)
  simp only [PiLp.inner_apply, hm]
  exact configEquiv.symm.sum_comp (fun i : Fin 2 ↦
    inner ℂ ((A *ᵥ (![1, 0] : Fin 2 → ℂ)) i) ((C *ᵥ (![1, 0] : Fin 2 → ℂ)) i))

open Classical in
private theorem pairing_nonzero :
    (inner ℂ
      (regularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2)
        (fun _ : Fin 1 ↦ Finset.univ) (fun _ ↦ 2) 1 Ω x)
      (regularizedPatchInsertion (Out := fun _ : Unit ↦ Fin 2)
        (fun _ : Fin 1 ↦ Finset.univ) (fun _ ↦ 2) 1 Ω x 0
          (B * (x 0 + (1 : ℝ) • 1) ^ (-(2 : ℝ) / 2) -
            (x 0 + (1 : ℝ) • 1) ^ (-(2 : ℝ) / 2) * B))).re = 3 / 8 := by
  have hf : regularizedPatchFilter (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 1 ↦ Finset.univ) (fun _ ↦ 2) 1 x 0 =
        Matrix.reindex configEquiv configEquiv localFilter := by
    rw [regularizedPatchFilter, lift_univ]
    convert! shifted_power using 1
    congr!
  have hy : regularizedPatchOutput (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 1 ↦ Finset.univ) (fun _ ↦ 2) 1 Ω x =
        WithLp.toLp 2 ((Matrix.reindex configEquiv configEquiv localFilter) *ᵥ Ω) := by
    simp [regularizedPatchOutput, regularizedPatchOperator, List.ofFn_succ, hf]
    congr 1
  rw [hy, insertion_single]
  simp only [shifted_power]
  have hc : B * Matrix.reindex configEquiv configEquiv localFilter -
      Matrix.reindex configEquiv configEquiv localFilter * B =
      Matrix.reindex configEquiv configEquiv
        (generator * localFilter - localFilter * generator) := by
    simp [B, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_sub]
  rw [hc, inner_conjugated]
  norm_num [generator, localFilter, PiLp.inner_apply, Fin.sum_univ_two,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, map_ofNat]

example : ¬ IsMinOn
    (regularizedPatchObjective (Out := fun _ : Unit ↦ Fin 2)
      (fun _ : Fin 1 ↦ Finset.univ) (fun _ ↦ 2) 1 Ω)
    (regularizedPatchDomain (Out := fun _ : Unit ↦ Fin 2) (fun _ : Fin 1 ↦ Finset.univ)) x := by
  intro hmin
  have h := regularizedPatchFirstVariation_eq_zero (Out := fun _ : Unit ↦ Fin 2)
    (fun _ : Fin 1 ↦ Finset.univ)
    (fun _ ↦ 2) (by norm_num : (0 : ℝ) < 1) Ω feasible hmin 0 B B_skew
  have he : (3 / 8 : ℝ) = 0 := by
    rw [← pairing_nonzero]
    convert h using 1
    congr 12 <;> exact Subsingleton.elim _ _
  norm_num at he
