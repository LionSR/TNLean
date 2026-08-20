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
import TNLean.MPS.SharedInfra.WordTupleGauge
import TNLean.MPS.SharedInfra.Scaling

/-!
# Coefficient absorption need not preserve CPSV normality

This file gives the two-sector, bond-one example suggested by the normalization
convention of arXiv:1606.00608, lines 224--246, inside the simple Case-II
argument at lines 1646--1782.  The two normal representatives have disjoint
physical support and global weights $(1 / √2, 1)$.  Absorbing the first weight
changes its transfer spectral radius from one to one half.

The first example refutes only the printed intermediate inference that every
absorbed representative is again normal.  The second example retains one
normal BNT representative with two raw copies of weights $1$ and $1/2$.  It
satisfies the printed standing hypotheses and condition (iv), but the
two-site-blocked tensor cannot satisfy Definition 4.1.  Thus it refutes the
literal implication (iv)$\Rightarrow$(v) printed in Theorem 4.9.
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
    simp [basis, firstBasisTensor, secondBasisTensor] at h
  · change ¬ MPSTensor.GaugePhaseEquiv (basis 1) (basis 0)
    rintro ⟨X, ζ, hζ, hX⟩
    have h := congrFun (congrFun (hX 0) 0) 0
    simp [basis, firstBasisTensor, secondBasisTensor] at h
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
        simp [firstBasisTensor, Fin.sum_univ_succ]
        rw [star_invSqrtTwo, invSqrtTwo_mul_self]
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

Source: arXiv:1606.00608, the biCF hypothesis used in Appendix C.2, lines
1628--1633. -/
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

Source: arXiv:1606.00608, Appendix C.2, lines 1628--1633. -/
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

/-! ### A counterexample to the literal implication (iv) implies (v) -/

/-- The sole BNT representative underlying `repeatedCopyTensor`.

This is the scalar normal tensor used in condition (iv) of arXiv:1606.00608,
Theorem 4.9 (lines 863--889). -/
noncomputable def scalarBNT : MPOTensor 1 1 := fun _ _ ↦ 1

/-- The one-sector, two-copy BNT presentation of `repeatedCopyTensor`.

The copy weights are exactly $\mu_{0,0}=1$ and $\mu_{0,1}=1/2$, allowed by
the global normalization of arXiv:1606.00608, line 246. -/
@[reducible] noncomputable def repeatedCopyDecomposition :
    MPSTensor.SectorDecomposition 1 where
  basisCount := 1
  basisDim := fun _ ↦ 1
  basis := fun _ ↦ scalarBNT.toMPSTensor
  sectors :=
    { copies := fun _ ↦ 2
      copies_pos := fun _ ↦ by omega
      weight := fun _ q ↦ if q = 0 then 1 else 1 / 2
      weight_ne_zero := by
        intro _ q
        split_ifs
        · exact one_ne_zero
        · norm_num }

/-- The scalar repeated-copy MPO with raw BNT weights $1$ and $1/2$.

Its doubled-index MPS tensor is literally the canonical assembly
`repeatedCopyDecomposition` from the line-246 normalization convention of
arXiv:1606.00608 (lines 237--246 and 271--301). -/
noncomputable def repeatedCopyTensor :
    MPOTensor 1 repeatedCopyDecomposition.totalDim :=
  fun _ _ ↦ repeatedCopyDecomposition.toTensor 0

/-- The concrete repeated-copy MPO is exactly the raw-weight BNT assembly,
not merely an MPO with the same periodic contractions.

Source: arXiv:1606.00608, canonical form at lines 237--246 and equation
`eq:II_ABasicTensors` at lines 271--301. -/
theorem repeatedCopyTensor_toMPSTensor :
    repeatedCopyTensor.toMPSTensor = repeatedCopyDecomposition.toTensor := by
  funext i
  fin_cases i
  rfl

private lemma scalarBNT_evalWord (w : List (Fin 1)) :
    MPSTensor.evalWord scalarBNT.toMPSTensor w = 1 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      rw [MPSTensor.evalWord_cons, ih]
      simp [scalarBNT, toMPSTensor]

/-- The raw repeated-copy presentation satisfies the source's BNT canonical
form, including the global unit-weight convention but no equal-modulus
condition on repeated copies.

Source: arXiv:1606.00608, canonical-form normalization at lines 237--246 and
the BNT display at lines 271--301. -/
theorem repeatedCopyDecomposition_isBNTCanonicalForm :
    MPSTensor.IsBNTCanonicalForm repeatedCopyDecomposition := by
  refine {
    basis_dim_pos := by simp [repeatedCopyDecomposition]
    basis_irreducible := fun _ ↦
      MPSTensor.isIrreducibleTensor_of_bondDim_one scalarBNT.toMPSTensor
    basis_left_canonical := by
      intro j
      simp [MPSTensor.IsLeftCanonical, repeatedCopyDecomposition,
        scalarBNT, toMPSTensor]
    basis_normalized_self_overlap := by
      intro j
      simp [MPSTensor.mpvOverlap, MPSTensor.mpv, scalarBNT_evalWord,
        Matrix.trace]
    bnt_data := by
      refine ⟨0, ?_⟩
      intro N hN
      apply LinearIndependent.of_subsingleton (i := (0 : Fin 1))
      intro hzero
      have h := congrArg
        (fun v : MPSTensor.MPVSpace 1 N ↦ v (fun _ ↦ (0 : Fin 1))) hzero
      simp [MPSTensor.mpvState_apply, MPSTensor.mpv, scalarBNT_evalWord,
        Matrix.trace] at h
    basis_distinct := by
      intro j k hjk
      exact absurd (Subsingleton.elim j k) hjk
    weight_norm_le_one := by
      intro j q
      change ‖(if q = 0 then (1 : ℂ) else 1 / 2)‖ ≤ 1
      split_ifs <;> norm_num
    weight_unit_exists := by
      refine ⟨0, 0, ?_⟩
      change ‖(if (0 : Fin 2) = 0 then (1 : ℂ) else 1 / 2)‖ = 1
      simp }

private lemma scalarBNT_mpv {N : ℕ} (σ : Fin N → Fin 1) :
    MPSTensor.mpv scalarBNT.toMPSTensor σ = 1 := by
  simp [MPSTensor.mpv, scalarBNT_evalWord, Matrix.trace]

/-- Every periodic contraction of the repeated-copy MPO is
$1+(1/2)^N$.

This is the scalar coefficient of the canonical display in
arXiv:1606.00608, equations `eq:II_ABasicTensors` and `Eq19`, lines
271--308. -/
theorem repeatedCopyTensor_mpo (N : ℕ) (σ τ : Fin N → Fin 1) :
    mpo repeatedCopyTensor N σ τ = 1 + (1 / 2 : ℂ) ^ N := by
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
  rw [repeatedCopyTensor_toMPSTensor]
  rw [repeatedCopyDecomposition.mpv_toTensor_eq_sum_sectors]
  rw [Fin.sum_univ_one, Fin.sum_univ_two]
  rw [scalarBNT_mpv]
  simp only [mul_one]
  change (if (0 : Fin 2) = 0 then 1 else (1 / 2 : ℂ)) ^ N +
      (if (1 : Fin 2) = 0 then 1 else (1 / 2 : ℂ)) ^ N =
        1 + (1 / 2 : ℂ) ^ N
  norm_num

/-- The repeated-copy tensor generates a positive semidefinite operator at
every positive length, as required by the standing MPDO hypothesis of
arXiv:1606.00608, Theorem 4.9 (lines 851--856). -/
theorem repeatedCopyTensor_isMPDO : IsMPDO repeatedCopyTensor := by
  intro N hN
  have hMpo : mpo repeatedCopyTensor N =
      (1 + (1 / 2 : ℂ) ^ N) •
        (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
    ext σ τ
    have hστ : σ = τ := Subsingleton.elim _ _
    subst τ
    rw [repeatedCopyTensor_mpo]
    simp
  rw [hMpo]
  exact Matrix.PosSemidef.one.smul (by positivity)

/-- The scalar BNT representative generates positive operators at every
positive length, as required explicitly in condition (iv) of
arXiv:1606.00608, Theorem 4.9 (lines 863--868). -/
theorem scalarBNT_isMPDO : IsMPDO scalarBNT := by
  intro N hN
  have hMpo : mpo scalarBNT N =
      (1 : Matrix (Fin N → Fin 1) (Fin N → Fin 1) ℂ) := by
    ext σ τ
    have hστ : σ = τ := Subsingleton.elim _ _
    subst τ
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig]
    rw [scalarBNT_mpv]
    simp
  rw [hMpo]
  exact Matrix.PosSemidef.one

/-- The physical-trace transfer of the sole BNT representative is the
one-by-one identity. -/
theorem physTraceTransfer_scalarBNT : physTraceTransfer scalarBNT = 1 := by
  ext a b
  fin_cases a
  fin_cases b
  simp [physTraceTransfer, scalarBNT]

/-- The sole BNT representative is nonnilpotent, which is precisely the
simplicity clause of arXiv:1606.00608, Definition 4.7 (lines 815--822). -/
theorem scalarBNT_physTraceTransfer_not_nilpotent :
    ¬ IsNilpotent (physTraceTransfer scalarBNT) := by
  rw [physTraceTransfer_scalarBNT]
  exact not_isNilpotent_one

/-- The unique normal representative already has simultaneous one-letter
span. This is the biCF condition used in Appendix C.2 of
arXiv:1606.00608, lines 1628--1633, specialized to one BNT element. -/
theorem scalarBNT_wordTupleSpanTop :
    MPSTensor.WordTupleSpanTop (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 := by
  unfold MPSTensor.WordTupleSpanTop
  apply top_unique
  intro X hX
  let w : Fin 1 → Fin 1 := fun _ ↦ 0
  have hGenerator :
      MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 w ∈
        Submodule.span ℂ (Set.range
          (MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1)) :=
    Submodule.subset_span (Set.mem_range_self w)
  have hEq : X = X 0 0 0 •
      MPSTensor.wordTuple (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 w := by
    funext k
    ext a b
    fin_cases k
    fin_cases a
    fin_cases b
    simp [MPSTensor.wordTuple, w, scalarBNT, toMPSTensor]
  rw [hEq]
  exact Submodule.smul_mem _ _ hGenerator

/-- Distinct BNT layers vanish under ordinary vertical composition.  In the
one-representative example the distinct-label premise is empty, but this is
the literal equation `KxKy=0` of condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 863--868. -/
theorem scalarBNT_layer_orthogonal :
    ∀ x y : Fin 1, x ≠ y →
      layerMul ((fun _ : Fin 1 ↦ scalarBNT) y)
        ((fun _ : Fin 1 ↦ scalarBNT) x) = 0 := by
  intro x y hxy
  exact absurd (Subsingleton.elim x y) hxy

/-- The one-dimensional physical space as one sector with one-dimensional
left and right factors.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def scalarSectorEquiv :
    Fin 1 ≃ Sigma fun _k : Fin 1 ↦ Fin 1 × Fin 1 where
  toFun _ := ⟨0, (0, 0)⟩
  invFun _ := 0
  left_inv i := Subsingleton.elim _ _
  right_inv := by
    rintro ⟨k, x, y⟩
    fin_cases k
    fin_cases x
    fin_cases y
    rfl

/-- The scalar BNT representative has the one-sector physical
factorization asserted in condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 869--889, and Appendix C.2,
equation `AppUkU=rl`, lines 1381--1388. -/
noncomputable def scalarFactorization :
    PhysicalSectorFactorization scalarBNT where
  sectorCount := 1
  leftDim := fun _ ↦ 1
  rightDim := fun _ ↦ 1
  leftDim_pos := fun _ ↦ by omega
  rightDim_pos := fun _ ↦ by omega
  sectorEquiv := scalarSectorEquiv
  physicalIsometry := 1
  physicalIsometry_isometry := by simp
  leftTensor := fun _ _ ↦ 1
  rightTensor := fun _ _ ↦ 1
  factorization := by
    intro beta alpha
    ext q r
    obtain ⟨k, x, y⟩ := q
    obtain ⟨h, u, v⟩ := r
    fin_cases k
    fin_cases h
    fin_cases x
    fin_cases y
    fin_cases u
    fin_cases v
    fin_cases beta
    fin_cases alpha
    simp [Matrix.reindex_apply, scalarSectorEquiv, physicalSlice, scalarBNT,
      Matrix.blockDiagonal'_apply_eq]

/-- The sole neighboring operator of `scalarFactorization` is the identity
density matrix.

Source: arXiv:1606.00608, Appendix C.2, equation `etarl`, lines 1441--1445. -/
theorem scalarFactorization_neighboringOperator (k h) :
    scalarFactorization.neighboringOperator k h = 1 := by
  ext x y
  obtain ⟨xR, xL⟩ := x
  obtain ⟨yR, yL⟩ := y
  fin_cases k
  fin_cases h
  fin_cases xR
  fin_cases xL
  fin_cases yR
  fin_cases yL
  simp [PhysicalSectorFactorization.neighboringOperator_apply,
    scalarFactorization]

/-- The scalar factorization has positive neighboring operators and the
rank-one trace factorization required in condition (iv).

Source: arXiv:1606.00608, Theorem 4.9(iv), lines 869--889, and Appendix C.2,
lines 1389--1403. -/
noncomputable def scalarNeighboringTraceFactorization :
    PhysicalSectorFactorization.NeighboringTraceFactorization
      scalarFactorization where
  neighboringOperator_pos := by
    intro k h
    rw [scalarFactorization_neighboringOperator]
    exact Matrix.PosSemidef.one
  a := fun _ ↦ 1
  b := fun _ ↦ 1
  trace_neighboringOperator := by
    intro k h
    fin_cases k
    fin_cases h
    rw [scalarFactorization_neighboringOperator]
    simp only [Matrix.trace_one, Fintype.card_prod, Fintype.card_fin]
    dsimp [scalarFactorization]
    norm_num
  sum_mul := by
    change ∑ _ : Fin 1, (1 : ℝ) * 1 = 1
    simp

private lemma evalWord_replicate_repeatedCopyTensor (N : ℕ) :
    evalWord repeatedCopyTensor (List.replicate N 0) (List.replicate N 0) =
      (repeatedCopyTensor 0 0) ^ N := by
  induction N with
  | zero => rfl
  | succ N ih =>
      rw [List.replicate_succ, evalWord_cons, ih, pow_succ']

/-- The trace of the `N`-th power of the sole local matrix retains the two
raw copy weights as $1+2^{-N}$.

Source: arXiv:1606.00608, equations `eq:II_ABasicTensors` and `Eq19`, lines
271--308. -/
theorem trace_repeatedCopyTensor_pow (N : ℕ) :
    Matrix.trace ((repeatedCopyTensor 0 0) ^ N) =
      1 + (1 / 2 : ℂ) ^ N := by
  have h := repeatedCopyTensor_mpo N (fun _ ↦ 0) (fun _ ↦ 0)
  rw [mpo_apply, mpoMatrixEntry] at h
  simpa [List.ofFn_const, evalWord_replicate_repeatedCopyTensor] using h

/-- The physical-trace transfer after two-site blocking is the square of the
sole local matrix. -/
theorem physTraceTransfer_blockTwo_repeatedCopyTensor :
    physTraceTransfer (blockTwo repeatedCopyTensor) =
      (repeatedCopyTensor 0 0) ^ 2 := by
  rw [physTraceTransfer, Fin.sum_univ_one]
  change repeatedCopyTensor 0 0 * repeatedCopyTensor 0 0 =
    (repeatedCopyTensor 0 0) ^ 2
  rw [pow_two]

/-- The two-site-blocked repeated-copy tensor cannot satisfy the tp-CP-map
renormalization-fixed-point equations of Definition 4.1.

Indeed, Definition 4.1 would make its physical-trace transfer idempotent.  In
this example that would identify the traces $1+2^{-4}$ and $1+2^{-2}$.

Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and the claimed
conclusion (v) of Theorem 4.9 at lines 890--892. -/
theorem blockTwo_repeatedCopyTensor_not_isRFPViaTS :
    ¬ IsRFPViaTS (blockTwo repeatedCopyTensor) := by
  intro hRFP
  have hsq := physTraceTransfer_sq_of_isRFPViaTS
    (blockTwo repeatedCopyTensor) hRFP
  rw [physTraceTransfer_blockTwo_repeatedCopyTensor] at hsq
  have hpowers : (repeatedCopyTensor 0 0) ^ 4 =
      (repeatedCopyTensor 0 0) ^ 2 := by
    calc
      (repeatedCopyTensor 0 0) ^ 4 =
          (repeatedCopyTensor 0 0) ^ 2 *
            (repeatedCopyTensor 0 0) ^ 2 := by noncomm_ring
      _ = (repeatedCopyTensor 0 0) ^ 2 := hsq
  have htrace := congrArg Matrix.trace hpowers
  rw [trace_repeatedCopyTensor_pow, trace_repeatedCopyTensor_pow] at htrace
  norm_num at htrace

/-- A counterexample to the literal implication (iv)$\Rightarrow$(v) printed
in arXiv:1606.00608, Theorem 4.9.

The tensor is exactly its raw BNT canonical assembly with weights $1$ and
$1/2$, generates MPDOs, and has a nonnilpotent sole normal representative.
That representative has simultaneous one-letter span, generates MPDOs,
satisfies the distinct-layer equation, and admits the full physical-sector
and neighboring-trace factorization of condition (iv).  Nevertheless the
two-site block, which still generates MPDOs, fails Definition 4.1.

Thus the literal implication (iv)$\Rightarrow$(v) is a refuted, unfaithful
statement.  The source proof has proof-path drift: lines 1646--1665 first use
condition (ii), zero correlation length, to make repeated-copy weights equal
and absorb their common value before invoking Proposition C.7.  That stronger
(ii)$\Rightarrow$(v) route is not contradicted by this example.

Source: arXiv:1606.00608, Theorem 4.9 at lines 851--892; canonical-form
normalization at lines 237--246; Appendix C.2 at lines 1381--1403 and
1646--1665; Definition 4.1 at lines 638--660. -/
theorem printed_theorem49_iv_to_v_is_false :
    repeatedCopyDecomposition.weight 0 0 = 1 ∧
      repeatedCopyDecomposition.weight 0 1 = (1 / 2 : ℂ) ∧
      repeatedCopyTensor.toMPSTensor = repeatedCopyDecomposition.toTensor ∧
      MPSTensor.IsBNTCanonicalForm repeatedCopyDecomposition ∧
      IsMPDO repeatedCopyTensor ∧
      ¬ IsNilpotent (physTraceTransfer scalarBNT) ∧
      MPSTensor.WordTupleSpanTop
        (fun _ : Fin 1 ↦ scalarBNT.toMPSTensor) 1 ∧
      IsMPDO scalarBNT ∧
      (∀ x y : Fin 1, x ≠ y →
        layerMul ((fun _ : Fin 1 ↦ scalarBNT) y)
          ((fun _ : Fin 1 ↦ scalarBNT) x) = 0) ∧
      Nonempty (PhysicalSectorFactorization.NeighboringTraceFactorization
        scalarFactorization) ∧
      IsMPDO (blockTwo repeatedCopyTensor) ∧
      ¬ IsRFPViaTS (blockTwo repeatedCopyTensor) := by
  exact ⟨rfl, rfl, repeatedCopyTensor_toMPSTensor,
    repeatedCopyDecomposition_isBNTCanonicalForm, repeatedCopyTensor_isMPDO,
    scalarBNT_physTraceTransfer_not_nilpotent, scalarBNT_wordTupleSpanTop,
    scalarBNT_isMPDO, scalarBNT_layer_orthogonal,
    ⟨scalarNeighboringTraceFactorization⟩,
    repeatedCopyTensor_isMPDO.blockTwo,
    blockTwo_repeatedCopyTensor_not_isRFPViaTS⟩

end MPOTensor.CaseIIAbsorptionCounterexample
