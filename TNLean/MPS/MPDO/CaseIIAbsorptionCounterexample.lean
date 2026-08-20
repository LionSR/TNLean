/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPDO.NeighboringPreparation
import TNLean.MPS.MPDO.PhysicalBlocking
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.SimpleTensor
import TNLean.MPS.MPDO.StackedLayers
import TNLean.MPS.MPDO.ZCL
import TNLean.MPS.MPDO.Theorem49RepeatedCopyCounterexample
import TNLean.MPS.SharedInfra.WordTupleGauge
import TNLean.MPS.SharedInfra.Scaling

/-!
# Coefficient absorption need not preserve CPSV normality

This file gives the two-sector, bond-one example suggested by the normalization
convention of arXiv:1606.00608, lines 224--246, inside the simple Case-II
argument at lines 1646--1782.  The two normal representatives have disjoint
physical support and global weights $(1 / √2, 1)$.  Absorbing the first weight
changes its transfer spectral radius from one to one half.

The example refutes only the printed intermediate inference that every
absorbed representative is again normal. The distinct repeated-copy
counterexample to the literal implication (iv)$\Rightarrow$(v) is formalized in
`TNLean.MPS.MPDO.Theorem49RepeatedCopyCounterexample`.
-/

open scoped Matrix BigOperators ComplexOrder Matrix.Norms.Operator

namespace MPOTensor.CaseIIAbsorptionCounterexample

/-- The coefficient $1/\sqrt 2$, viewed as a complex number. -/
noncomputable def invSqrtTwo : ℂ := ((Real.sqrt 2)⁻¹ : ℝ)

private lemma invSqrtTwo_ne_zero : invSqrtTwo ≠ 0 := by
  rw [invSqrtTwo]
  exact_mod_cast inv_ne_zero (ne_of_gt (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)))

private lemma norm_invSqrtTwo : ‖invSqrtTwo‖ = (Real.sqrt 2)⁻¹ := by
  rw [invSqrtTwo, Complex.norm_real, Real.norm_eq_abs, abs_inv, abs_of_pos]
  exact Real.sqrt_pos.2 (by norm_num)

private lemma invSqrtTwo_mul_self : invSqrtTwo * invSqrtTwo = (1 / 2 : ℂ) := by
  rw [← pow_two, invSqrtTwo]
  change ((↑((Real.sqrt 2)⁻¹) : ℂ) ^ 2) = 1 / 2
  rw [← Complex.ofReal_pow, inv_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

private lemma star_invSqrtTwo : starRingEnd ℂ invSqrtTwo = invSqrtTwo := by
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
private lemma weight_globally_normalized :
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

/-- The two normal representatives have disjoint doubled-physical support. -/
lemma basis_disjoint_support :
    ∀ i, basis 0 i ≠ 0 → basis 1 i = 0 := by
  intro i
  fin_cases i <;> simp [basis, firstBasisTensor, secondBasisTensor]

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

/-- Each of the two displayed bond-one representatives is a normal tensor.

Source: arXiv:1606.00608, the normal representatives in the BNT decomposition
`eq:II_ABasicTensors`, lines 271--301. -/
lemma basis_isNormalTensor (s : Fin 2) : MPSTensor.IsNormalTensor (basis s) := by
  fin_cases s
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      _ firstBasis_transferMap
  · exact MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
      _ secondBasis_transferMap

/-- The two representatives are not related by a virtual gauge and a phase.
Their disjoint physical supports distinguish them already at the letters `0`
and `8`.

Source: arXiv:1606.00608, the distinct normal representatives in the BNT
decomposition `eq:II_ABasicTensors`, lines 271--301. -/
private theorem basis_not_gaugePhaseEquiv :
    MPSTensor.BlocksNotGaugePhaseEquiv (d := 3 * 3) basis := by
  intro j k hjk hdim
  fin_cases j <;> fin_cases k
  · exact absurd rfl hjk
  · change ¬ MPSTensor.GaugePhaseEquiv (basis 0) (basis 1)
    rintro ⟨X, ζ, hζ, hX⟩
    have h := congrFun (congrFun (hX 8) 0) 0
    simp only [basis, Fin.isValue, one_ne_zero, ↓reduceIte, secondBasisTensor,
      Nat.reduceMul, Matrix.one_apply_eq, firstBasisTensor, Fin.reduceEq,
      or_self, mul_zero, Matrix.coe_units_inv, Matrix.inv_subsingleton,
      Ring.inverse_eq_inv', zero_mul, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul] at h
  · change ¬ MPSTensor.GaugePhaseEquiv (basis 1) (basis 0)
    rintro ⟨X, ζ, hζ, hX⟩
    have h := congrFun (congrFun (hX 0) 0) 0
    simp only [basis, Fin.isValue, ↓reduceIte, firstBasisTensor, Nat.reduceMul,
      Fin.reduceEq, or_false, Matrix.of_apply, one_ne_zero, secondBasisTensor,
      mul_zero, Matrix.coe_units_inv, Matrix.inv_subsingleton,
      Ring.inverse_eq_inv', zero_mul, Matrix.smul_apply, Matrix.zero_apply,
      smul_eq_mul] at h
    exact invSqrtTwo_ne_zero h
  · exact absurd rfl hjk

/-- The two representatives with weights $(1/\sqrt 2,1)$ form a normalized
basis-of-normal-tensors decomposition. Each representative occurs once, so
equality of weights within a fixed representative is vacuous and does not
equate these two displayed weights.

Source: arXiv:1606.00608, canonical-form normalization at lines 224--246 and
the BNT decomposition `eq:II_ABasicTensors`, lines 271--301. -/
theorem sectors_isBNTCanonicalForm :
    MPSTensor.IsBNTCanonicalForm sectors := by
  refine {
    basis_dim_pos := by simp [sectors]
    basis_irreducible := fun s => (basis_isNormalTensor s).no_invariant_proj
    basis_left_canonical := by
      intro s
      fin_cases s
      · change MPSTensor.IsLeftCanonical firstBasisTensor
        rw [MPSTensor.IsLeftCanonical]
        ext a b
        fin_cases a
        fin_cases b
        simp only [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_one,
          Matrix.conjTranspose_apply]
        simp only [Nat.reduceMul, Fin.isValue, Fin.zero_eta, RCLike.star_def,
          Matrix.one_apply_eq]
        have hsum :
            (∑ x : Fin (3 * 3),
              starRingEnd ℂ (firstBasisTensor x 0 0) *
                firstBasisTensor x 0 0) =
              starRingEnd ℂ invSqrtTwo * invSqrtTwo +
                starRingEnd ℂ invSqrtTwo * invSqrtTwo := by
          simp [firstBasisTensor, Fin.sum_univ_succ]
        rw [hsum, star_invSqrtTwo, invSqrtTwo_mul_self]
        ring
      · change MPSTensor.IsLeftCanonical secondBasisTensor
        rw [MPSTensor.IsLeftCanonical]
        ext a b
        fin_cases a
        fin_cases b
        simp only [Matrix.sum_apply, Matrix.mul_apply, Fin.sum_univ_one,
          Matrix.conjTranspose_apply]
        simp [secondBasisTensor, Fin.sum_univ_succ]
    basis_normalized_self_overlap := by
      intro s
      exact (basis_isNormalTensor s).selfOverlap_tendsto_one
    bnt_data := by
      rw [MPSTensor.HasBNTSectorData]
      simpa [sectors] using
        (MPSTensor.exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv
          basis basis_isNormalTensor basis_not_gaugePhaseEquiv)
    basis_distinct := by
      intro j k hjk hdim
      exact basis_not_gaugePhaseEquiv j k hjk hdim
    weight_norm_le_one := by
      change ∀ (s : Fin 2) (_q : Fin 1), ‖weight s‖ ≤ 1
      intro s q
      exact weight_globally_normalized.1 s
    weight_unit_exists := by
      change ∃ (s : Fin 2) (_q : Fin 1), ‖weight s‖ = 1
      obtain ⟨s, hs⟩ := weight_globally_normalized.2
      exact ⟨s, 0, hs⟩ }

/-- The letters `0` and `8` independently span the two bond-one
representatives, so their simultaneous one-letter tuple span is the entire
direct sum.

Source: arXiv:1606.00608, Definition `defnbi` of biCF, lines 317--326; the
condition is used in the Case-II argument in Appendix C.2, lines 1628--1633. -/
theorem sectors_wordTupleSpanTop_one :
    MPSTensor.WordTupleSpanTop sectors.basis 1 := by
  change MPSTensor.WordTupleSpanTop basis 1
  unfold MPSTensor.WordTupleSpanTop
  apply top_unique
  intro Y hY
  let w₀ : Fin 1 → Fin (3 * 3) := fun _ ↦ 0
  let w₁ : Fin 1 → Fin (3 * 3) := fun _ ↦ 8
  have hw₀ : MPSTensor.wordTuple basis 1 w₀ ∈
      Submodule.span ℂ (Set.range (MPSTensor.wordTuple basis 1)) :=
    Submodule.subset_span (Set.mem_range_self w₀)
  have hw₁ : MPSTensor.wordTuple basis 1 w₁ ∈
      Submodule.span ℂ (Set.range (MPSTensor.wordTuple basis 1)) :=
    Submodule.subset_span (Set.mem_range_self w₁)
  have hEq : Y =
      (Y 0 0 0 * invSqrtTwo⁻¹) • MPSTensor.wordTuple basis 1 w₀ +
        Y 1 0 0 • MPSTensor.wordTuple basis 1 w₁ := by
    funext s
    fin_cases s <;> ext a b <;> fin_cases a <;> fin_cases b
    · simp [MPSTensor.wordTuple, w₀, w₁, basis, firstBasisTensor,
        MPSTensor.evalWord, invSqrtTwo_ne_zero]
    · simp [MPSTensor.wordTuple, w₀, w₁, basis, secondBasisTensor,
        MPSTensor.evalWord]
  rw [hEq]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ hw₀) (Submodule.smul_mem _ _ hw₁)

/-- The two normal representatives satisfy the biCF condition, witnessed by
their simultaneous one-letter tuple span.

Source: arXiv:1606.00608, Definition `defnbi`, lines 317--326; the condition is
used in the Case-II argument in Appendix C.2, lines 1628--1633. -/
theorem sectors_hasBiCF : MPSTensor.HasBiCF sectors.basis :=
  MPSTensor.hasBiCF_of_wordTupleSpanTop sectors.basis sectors_wordTupleSpanTop_one

/-- The first representative after the source absorbs its common weight. -/
noncomputable def firstAbsorbed : MPSTensor (3 * 3) 1 :=
  fun i ↦ invSqrtTwo • basis 0 i

private lemma firstAbsorbed_eq :
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
weighted representatives.

Source: arXiv:1606.00608, the BNT decomposition
`eq:II_ABasicTensors` and canonical-form assembly `Eq19`, lines 271--308. -/
lemma ambient_eq_weighted_basis_blocks (i j : Fin 3) :
    ambient i j = Matrix.diagonal fun s : Fin 2 ↦
      if s = 0 then
        (invSqrtTwo • basis 0 (finProdFinEquiv (i, j))) 0 0
      else (basis 1 (finProdFinEquiv (i, j))) 0 0 := by
  ext s t
  fin_cases i <;> fin_cases j <;> fin_cases s <;> fin_cases t <;>
    simp [ambient, basis, firstBasisTensor, secondBasisTensor,
      invSqrtTwo_mul_self, Matrix.smul_apply, finProdFinEquiv]

/-- Evaluation of the assembled decomposition in its two flattened bond
coordinates.

Source: arXiv:1606.00608, canonical-form assembly in equation `Eq19`, lines
304--308. -/
private theorem sectors_toTensor_apply
    (p : Fin (3 * 3)) (a b : Fin 2) :
    sectors.toTensor p a b =
      (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv
        (Matrix.blockDiagonal' fun k : Fin 2 => weight k • basis k p)) a b := by
  have hflat (k : Fin 2) : sectors.flatIndexEquiv.symm k =
      ⟨k, ⟨0, sectors.copies_pos k⟩⟩ := by
    change (finSigmaFinEquiv : (Σ _s : Fin 2, Fin 1) ≃ Fin 2).symm k = ⟨k, 0⟩
    fin_cases k <;> rfl
  simp only [MPSTensor.SectorDecomposition.toTensor,
    MPSTensor.toTensorFromBlocks]
  have hBlocks :
      (fun k => sectors.flatWeight k • sectors.flatBasis k p) =
        fun k : Fin 2 => weight k • basis k p := by
    funext k
    unfold MPSTensor.SectorDecomposition.flatWeight
      MPSTensor.SectorDecomposition.flatBasis
    rw [hflat k]
    rfl
  rw [hBlocks]
  rfl

/-- The assembled sector tensor is the diagonal sum of the two weighted
bond-one representatives.

Source: arXiv:1606.00608, the BNT display `eq:II_ABasicTensors` and its
canonical-form assembly `Eq19`, lines 271--308. -/
private theorem sectors_toTensor_eq_diagonal (p : Fin (3 * 3)) :
    sectors.toTensor p = Matrix.diagonal fun s : Fin 2 =>
      if s = 0 then (invSqrtTwo • basis 0 p) 0 0 else (basis 1 p) 0 0 := by
  let e : (Σ _s : Fin 2, Fin 1) ≃ Fin 2 := finSigmaFinEquiv
  have hsymm (s : Fin 2) : e.symm s = ⟨s, 0⟩ := by
    fin_cases s <;> rfl
  change (fun a : Fin 2 => fun b : Fin 2 => sectors.toTensor p a b) = _
  funext a b
  rw [sectors_toTensor_apply]
  change (Matrix.reindex e e (Matrix.blockDiagonal' fun k : Fin 2 =>
      weight k • basis k p)) a b = _
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hsymm]
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.blockDiagonal'_apply, weight]

/-- The doubled-index ambient tensor is exactly the source canonical-form
assembly, not merely an MPO with the same periodic contractions.

Source: arXiv:1606.00608, canonical form at lines 237--246 and equations
`eq:II_ABasicTensors` and `Eq19`, lines 271--308. -/
theorem ambient_toMPSTensor_eq_sectors_toTensor :
    ambient.toMPSTensor = sectors.toTensor := by
  funext p
  rw [← finProdFinEquiv.apply_symm_apply p]
  obtain ⟨i, j⟩ := finProdFinEquiv.symm p
  change ambient (finProdFinEquiv (i, j)).divNat
      (finProdFinEquiv (i, j)).modNat = _
  rw [MPSTensor.finProdFinEquiv_divNat i j,
    MPSTensor.finProdFinEquiv_modNat i j]
  rw [sectors_toTensor_eq_diagonal]
  exact ambient_eq_weighted_basis_blocks i j

/-- The ambient MPO is in normalized BNT-refined horizontal form, with the
displayed sector decomposition and identity gauge on both bond-one blocks.

**Scope restriction (BNT-refined horizontal form):** this is the project's
normalized refinement of the literal CPSV canonical form; see
`docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.

Source: arXiv:1606.00608, canonical form at lines 237--246 and the BNT
decomposition `eq:II_ABasicTensors` at lines 271--301. -/
theorem ambient_isHorizontalCF : MPOTensor.IsHorizontalCF ambient := by
  refine ⟨sectors, sectors_isBNTCanonicalForm, ?_⟩
  have hTotal : sectors.totalDim = 2 := by
    change (∑ _ : Fin 2, 1) = 2
    simp
  let X : (s : Fin sectors.totalCopies) →
      GL (Fin (sectors.flatDim s)) ℂ := fun _ => 1
  refine ⟨hTotal, X, ?_⟩
  have hGauge : MPSTensor.globalGaugeOfBlocks X = 1 := by
    change Units.map _ (Units.map _ ((MulEquiv.piUnits).symm X)) = 1
    rw [show X = 1 by rfl]
    simp
  intro p
  rw [ambient_toMPSTensor_eq_sectors_toTensor]
  simp only [hGauge, Units.val_one, inv_one, one_mul, mul_one]
  exact (cast_eq _ _).symm

/-- The doubled physical-trace transfer of the first normal representative is
the nonzero scalar $2/\sqrt 2$ on its one-dimensional bond space.

Source: arXiv:1606.00608, the transfer matrices $\mathcal B_k$ in Definition
4.7, lines 815--822. -/
private theorem doubledPhysTraceTransfer_firstBasisTensor :
    doubledPhysTraceTransfer 3 firstBasisTensor =
      (2 * invSqrtTwo) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a
  fin_cases b
  simp [doubledPhysTraceTransfer, firstBasisTensor, Fin.sum_univ_succ,
    Matrix.smul_apply, finProdFinEquiv]
  ring

/-- The doubled physical-trace transfer of the second normal representative
is the identity on its one-dimensional bond space.

Source: arXiv:1606.00608, the transfer matrices $\mathcal B_k$ in Definition
4.7, lines 815--822. -/
private theorem doubledPhysTraceTransfer_secondBasisTensor :
    doubledPhysTraceTransfer 3 secondBasisTensor =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext a b
  fin_cases a
  fin_cases b
  simp [doubledPhysTraceTransfer, secondBasisTensor, Fin.sum_univ_succ,
    finProdFinEquiv]

/-- Neither displayed BNT representative has nilpotent physical-trace
transfer. This proves only the representative-level nonnilpotency clause and
does not assert simple canonical form, simplicity, the MPDO property, or SAL.

Source: arXiv:1606.00608, Definition 4.7, lines 815--822. -/
theorem sectors_basis_doubledPhysTraceTransfer_not_isNilpotent
    (j : Fin sectors.basisCount) :
    ¬ IsNilpotent (doubledPhysTraceTransfer 3 (sectors.basis j)) := by
  change Fin 2 at j
  change ¬ IsNilpotent (doubledPhysTraceTransfer 3 (basis j))
  fin_cases j
  · change ¬ IsNilpotent (doubledPhysTraceTransfer 3 firstBasisTensor)
    rw [doubledPhysTraceTransfer_firstBasisTensor]
    intro hnil
    have htrace := Matrix.isNilpotent_trace_of_isNilpotent hnil
    apply invSqrtTwo_ne_zero
    simpa [Matrix.trace] using htrace.eq_zero
  · change ¬ IsNilpotent (doubledPhysTraceTransfer 3 secondBasisTensor)
    rw [doubledPhysTraceTransfer_secondBasisTensor]
    exact not_isNilpotent_one

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

This statement isolates the scalar-normalization step and does not assert the
standing Case-II biCF, simplicity, MPDO, or SAL hypotheses. It therefore
refutes the coefficient-absorption step, not CPSV16 Theorem 4.9. -/
theorem printed_absorbed_normality_step_is_false :
    weight 0 = invSqrtTwo ∧ weight 1 = 1 ∧
      (∀ s, ‖weight s‖ ≤ 1) ∧ (∃ s, ‖weight s‖ = 1) ∧
      (∀ s, MPSTensor.IsNormalTensor (basis s)) ∧
      (∀ i, basis 0 i ≠ 0 → basis 1 i = 0) ∧
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
    basis_isNormalTensor, basis_disjoint_support,
    ambient_eq_weighted_basis_blocks,
    ambient_literal_physTrace_ZCL, spectralRadius_transferMap_firstAbsorbed,
    firstAbsorbed_not_isNormalTensor⟩

end MPOTensor.CaseIIAbsorptionCounterexample
