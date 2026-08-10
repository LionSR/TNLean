/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.SharedInfra.Scaling

/-!
# Coefficient absorption need not preserve CPSV normality

This file gives the two-sector, bond-one example suggested by the normalization
convention of arXiv:1606.00608, lines 224--246, inside the simple Case-II
argument at lines 1646--1782.  The two normal representatives have disjoint
physical support and global weights `(1 / √2, 1)`.  Absorbing the first weight
changes its transfer spectral radius from one to one half.

The example refutes only the printed intermediate inference that every absorbed
representative is again normal.  It is not a counterexample to Theorem 4.9.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

namespace MPOTensor.CaseIIAbsorptionCounterexample

/-- The coefficient $1/\sqrt 2$, viewed as a complex number. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

lemma invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := by
  rw [invSqrtTwo]
  exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))

lemma norm_invSqrtTwo : ‖invSqrtTwo‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrtTwo, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos]
  exact Real.sqrt_pos.2 (by norm_num)

lemma invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [← pow_two, invSqrtTwo]
  change ((↑((Real.sqrt 2)⁻¹) : ℂ) ^ 2) = 1 / 2
  rw [← Complex.ofReal_pow, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

lemma star_invSqrtTwo : starRingEnd ℂ invSqrtTwo = invSqrtTwo := by
  simp [invSqrtTwo]

/-- The first normal representative, supported on doubled symbols `(0,0)` and `(1,1)`,
which are indices `0` and `4` under `finProdFinEquiv`. -/
noncomputable def firstBasisTensor : MPSTensor (3 * 3) 1 :=
  fun i ↦ if i = 0 ∨ i = 4 then Matrix.of fun _ _ ↦ invSqrtTwo else 0

/-- The second normal representative, supported only on doubled symbol `(2,2)`,
which is index `8` under `finProdFinEquiv`. -/
noncomputable def secondBasisTensor : MPSTensor (3 * 3) 1 :=
  fun i ↦ if i = 8 then 1 else 0

/-- The two bond-one representatives on disjoint doubled physical supports. -/
noncomputable def basis (s : Fin 2) : MPSTensor (3 * 3) 1 :=
  if s = 0 then firstBasisTensor else secondBasisTensor

/-- The global CPSV weights $(1/\sqrt2,1)$. -/
noncomputable def weight (s : Fin 2) : ℂ := if s = 0 then invSqrtTwo else 1

/-- The two weights satisfy exactly the global CPSV16 line-246 convention. -/
lemma weight_globally_normalized :
    (∀ s : Fin 2, ‖weight s‖ ≤ 1) ∧ ∃ s : Fin 2, ‖weight s‖ = 1 := by
  constructor
  · intro s
    fin_cases s
    · change ‖invSqrtTwo‖ ≤ 1
      rw [norm_invSqrtTwo]
      exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))
    · change ‖(1 : ℂ)‖ ≤ 1
      simp
  · exact ⟨1, by simp [weight]⟩

/-- The source-faithful two-sector decomposition, with one copy per representative. -/
noncomputable def sectors : MPSTensor.SectorDecomposition (3 * 3) where
  basisCount := 2
  basisDim := fun _ ↦ 1
  basis := basis
  sectors :=
    { copies := fun _ ↦ 1
      copies_pos := fun _ ↦ by omega
      weight := fun s _ ↦ weight s
      weight_ne_zero := by
        intro s q
        fin_cases s <;> simp [weight, invSqrtTwo_ne_zero] }

/-- Copy independence is automatic because every representative has one copy. -/
lemma weights_copy_independent :
    ∀ (s : Fin sectors.basisCount) (q q' : Fin (sectors.copies s)),
      sectors.weight s q = sectors.weight s q' := by
  intro s q q'
  fin_cases q
  fin_cases q'
  rfl

private lemma firstBasis_transferMap :
    MPSTensor.transferMap firstBasisTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  have hterm :
      invSqrtTwo * X 0 0 * starRingEnd ℂ invSqrtTwo +
          invSqrtTwo * X 0 0 * starRingEnd ℂ invSqrtTwo = X 0 0 := by
    rw [star_invSqrtTwo]
    calc
      invSqrtTwo * X 0 0 * invSqrtTwo + invSqrtTwo * X 0 0 * invSqrtTwo =
          (invSqrtTwo * invSqrtTwo + invSqrtTwo * invSqrtTwo) * X 0 0 := by ring
      _ = X 0 0 := by rw [invSqrtTwo_mul_self]; ring
  simpa [MPSTensor.transferMap_apply, firstBasisTensor, Fin.sum_univ_succ,
    Matrix.mul_apply] using hterm

private lemma secondBasis_transferMap :
    MPSTensor.transferMap secondBasisTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [MPSTensor.transferMap_apply, secondBasisTensor, Matrix.mul_apply]

lemma basis_isNormalTensor (s : Fin 2) : MPSTensor.IsNormalTensor (basis s) := by
  fin_cases s
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      _ firstBasis_transferMap
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      _ secondBasis_transferMap


/-- The first representative after the source absorbs its common weight. -/
noncomputable def firstAbsorbed : MPSTensor (3 * 3) 1 :=
  fun i ↦ invSqrtTwo • basis 0 i

lemma firstAbsorbed_eq :
    firstAbsorbed = fun i ↦ invSqrtTwo • firstBasisTensor i := by
  rfl

/-- The first absorbed representative has transfer spectral radius exactly $1/2$. -/
theorem spectralRadius_transferMap_firstAbsorbed :
    spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin 1) (Fin 1) ℂ))
          (MPSTensor.transferMap firstAbsorbed)) = (2 : ENNReal)⁻¹ := by
  rw [firstAbsorbed_eq, MPSTensor.spectralRadius_transferMap_smul
    invSqrtTwo invSqrtTwo_ne_zero firstBasisTensor]
  rw [(MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    firstBasisTensor firstBasis_transferMap).spectral_radius_one]
  rw [mul_one]
  have hn : ‖invSqrtTwo‖₊ ^ 2 = (2 : NNReal)⁻¹ := by
    apply NNReal.eq
    simp only [NNReal.coe_pow, NNReal.coe_inv, NNReal.coe_ofNat]
    rw [show (‖invSqrtTwo‖₊ : ℝ) = ‖invSqrtTwo‖ by rfl, norm_invSqrtTwo]
    rw [inv_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (ENNReal.ofNNReal ‖invSqrtTwo‖₊) ^ 2 =
        ENNReal.ofNNReal (‖invSqrtTwo‖₊ ^ 2) := by rw [ENNReal.coe_pow]
    _ = ENNReal.ofNNReal ((2 : NNReal)⁻¹) := congrArg ENNReal.ofNNReal hn
    _ = (2 : ENNReal)⁻¹ := by norm_num

/-- Consequently the first absorbed representative is not a CPSV normal tensor. -/
theorem firstAbsorbed_not_isNormalTensor :
    ¬ MPSTensor.IsNormalTensor firstAbsorbed := by
  intro h
  have hr := h.spectral_radius_one
  rw [spectralRadius_transferMap_firstAbsorbed] at hr
  norm_num at hr

/-- The ambient two-sector MPO.  Its bond diagonal is the direct sum of the two
absorbed bond-one representatives. -/
noncomputable def ambient : MPOTensor 3 2 :=
  fun i j ↦ if i = j then Matrix.diagonal fun s ↦
    if s = 0 then (if i = 2 then 0 else (1 / 2 : ℂ))
    else if i = 2 then 1 else 0
  else 0

/-- The ambient tensor is literally the bond-diagonal assembly of the two
weighted representatives. -/
lemma ambient_eq_weighted_basis_blocks (i j : Fin 3) :
    ambient i j = Matrix.diagonal fun s : Fin 2 ↦
      if s = 0 then
        (invSqrtTwo • basis 0 (finProdFinEquiv (i, j))) 0 0
      else (basis 1 (finProdFinEquiv (i, j))) 0 0 := by
  ext s t
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [ambient, basis, firstBasisTensor, secondBasisTensor,
      invSqrtTwo_mul_self, Matrix.smul_apply, finProdFinEquiv]

/-- The ambient physical-trace transfer is literally the identity. -/
lemma physTraceTransfer_ambient : physTraceTransfer ambient = 1 := by
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp [physTraceTransfer, ambient, Fin.sum_univ_succ]
  all_goals norm_num

/-- Thus the source's literal physical-trace ZCL equation holds, without a
scale-invariant replacement. -/
theorem ambient_literal_physTrace_ZCL :
    physTraceTransfer ambient * physTraceTransfer ambient =
      physTraceTransfer ambient := by
  rw [physTraceTransfer_ambient, one_mul]

/-- The decisive source-normalization obstruction: the global weights are
$(1/\sqrt2,1)$, both unabsorbed blocks are normal, literal physical-trace ZCL
holds for their ambient direct sum, but the first absorbed block has transfer
spectral radius $1/2$ and is not normal.

This theorem does not package the standing Case-II biCF, simplicity, MPDO, or
SAL predicates; those interfaces are tracked separately in the accompanying
gap notes.  It therefore refutes the coefficient-absorption proof step, not
CPSV16 Theorem 4.9. -/
theorem printed_absorbed_normality_step_is_false :
    weight 0 = invSqrtTwo ∧ weight 1 = 1 ∧
      (∀ s, ‖weight s‖ ≤ 1) ∧ (∃ s, ‖weight s‖ = 1) ∧
      (∀ s, MPSTensor.IsNormalTensor (basis s)) ∧
      (∀ i j, ambient i j = Matrix.diagonal fun s : Fin 2 ↦
        if s = 0 then
          (invSqrtTwo • basis 0 (finProdFinEquiv (i, j))) 0 0
        else (basis 1 (finProdFinEquiv (i, j))) 0 0) ∧
      physTraceTransfer ambient * physTraceTransfer ambient =
        physTraceTransfer ambient ∧
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin 1) (Fin 1) ℂ))
            (MPSTensor.transferMap firstAbsorbed)) = (2 : ENNReal)⁻¹ ∧
      ¬ MPSTensor.IsNormalTensor firstAbsorbed := by
  exact ⟨rfl, rfl, weight_globally_normalized.1, weight_globally_normalized.2,
    basis_isNormalTensor, ambient_eq_weighted_basis_blocks,
    ambient_literal_physTrace_ZCL, spectralRadius_transferMap_firstAbsorbed,
    firstAbsorbed_not_isNormalTensor⟩

end MPOTensor.CaseIIAbsorptionCounterexample
