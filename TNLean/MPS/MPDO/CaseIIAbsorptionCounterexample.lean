/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.Channel.SupportCompletion
import TNLean.MPS.MPDO.RFPViaTSSAL
import TNLean.MPS.MPDO.SimpleTensor

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
    Kraus.transferMap firstBasisTensor = LinearMap.id := by
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
  simpa [Kraus.transferMap_apply, firstBasisTensor, Fin.sum_univ_succ,
    Matrix.mul_apply] using hterm

private lemma secondBasis_transferMap :
    Kraus.transferMap secondBasisTensor = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext a b
  fin_cases a
  fin_cases b
  simp [secondBasisTensor, Matrix.mul_apply]

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
        invSqrtTwo_ne_zero]
    · simp [MPSTensor.wordTuple, w₀, w₁, basis, secondBasisTensor]
  rw [hEq]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ hw₀) (Submodule.smul_mem _ _ hw₁)

/-- The two normal representatives satisfy the biCF condition, witnessed by
their simultaneous one-letter tuple span.

Source: arXiv:1606.00608, Definition `defnbi`, lines 317--326; the condition is
used in the Case-II argument in Appendix C.2, lines 1628--1633. -/
theorem sectors_hasBiCF : MPSTensor.HasBiCF sectors.basis :=
  MPSTensor.hasBiCF_of_wordTupleSpanTop sectors.basis sectors_wordTupleSpanTop_one

/-- The first representative after common-weight absorption.
Source: arXiv:1606.00608, lines 1646--1665. -/
noncomputable def firstAbsorbed : MPSTensor (3 * 3) 1 :=
  fun i ↦ invSqrtTwo • basis 0 i

private lemma firstAbsorbed_eq :
    firstAbsorbed = fun i ↦ invSqrtTwo • firstBasisTensor i := by
  rfl

/-- The first absorbed representative has transfer spectral radius exactly $1/2$.
Source: arXiv:1606.00608, the absorption step at lines 1646--1665. -/
theorem spectralRadius_transferMap_firstAbsorbed :
    spectralRadius ℂ
        ((Module.End.toContinuousLinearMap (Matrix (Fin 1) (Fin 1) ℂ))
          (Kraus.transferMap firstAbsorbed)) = (2 : ENNReal)⁻¹ := by
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

/-- Consequently the first absorbed representative is not a CPSV normal tensor.
Source: arXiv:1606.00608, the claimed absorbed normal form at lines 1646--1665. -/
theorem firstAbsorbed_not_isNormalTensor :
    ¬ MPSTensor.IsNormalTensor firstAbsorbed := by
  intro h
  have hr := h.spectral_radius_one
  rw [spectralRadius_transferMap_firstAbsorbed] at hr
  norm_num at hr

/-- The ambient two-sector MPO, assembled from the absorbed representatives.
Source: arXiv:1606.00608, lines 1646--1665. -/
noncomputable def ambient : MPOTensor 3 2 :=
  fun i j ↦ if i = j then Matrix.diagonal fun s ↦
    if s = 0 then (if i = 2 then 0 else (1 / 2 : ℂ))
    else if i = 2 then 1 else 0
  else 0

/-- The scalar on one virtual sector and one doubled physical letter.
This is the entrywise weighted canonical assembly in
arXiv:1606.00608, lines 237--246 and 1646--1665. -/
private noncomputable def ambientVirtualWeight
    (s : Fin 2) (i j : Fin 3) : ℂ :=
  if i = j then
    if s = 0 then (if i = 2 then 0 else 1 / 2)
    else if i = 2 then 1 else 0
  else 0

/-- Each ambient letter is diagonal in the two BNT sector coordinates.
Source: arXiv:1606.00608, canonical assembly at lines 237--246 and
1646--1665. -/
private lemma ambient_eq_diagonal (i j : Fin 3) :
    ambient i j = Matrix.diagonal fun s ↦ ambientVirtualWeight s i j := by
  by_cases hij : i = j <;> simp [ambient, ambientVirtualWeight, hij]

/-- Ambient-letter products remain diagonal, with sectorwise scalar products.
Source: arXiv:1606.00608, periodic canonical contractions at lines 237--246
and the absorbed BNT display at lines 1660--1665. -/
private lemma prod_ambient {N : ℕ} (σ τ : Fin N → Fin 3) :
    (List.ofFn fun k ↦ ambient (σ k) (τ k)).prod =
      Matrix.diagonal fun s ↦ ∏ k, ambientVirtualWeight s (σ k) (τ k) := by
  induction N with
  | zero =>
      simp only [List.ofFn_zero, List.prod_nil, Fin.prod_univ_zero]
      exact (Matrix.diagonal_one (n := Fin 2)).symm
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, ambient_eq_diagonal,
        ih (fun k ↦ σ k.succ) (fun k ↦ τ k.succ),
        Matrix.diagonal_mul_diagonal]
      congr 1
      funext s
      rw [Fin.prod_univ_succ]

/-- The periodic ambient operator is diagonal in the physical configuration
basis, with one nonnegative product contribution from each BNT sector.
Source: arXiv:1606.00608, the periodic MPDO contraction at lines 623--630 and
the absorbed BNT display at lines 1660--1665. -/
private lemma mpo_ambient_eq_diagonal (N : ℕ) :
    mpo ambient N = Matrix.diagonal fun σ ↦
      ∑ s : Fin 2, ∏ k, ambientVirtualWeight s (σ k) (σ k) := by
  ext σ τ
  by_cases hστ : σ = τ
  · subst τ
    rw [Matrix.diagonal_apply_eq, mpo_apply, mpoMatrixEntry, evalWord_ofFn,
      prod_ambient, Matrix.trace_diagonal]
  · rw [Matrix.diagonal_apply_ne _ hστ, mpo_apply, mpoMatrixEntry,
      evalWord_ofFn, prod_ambient, Matrix.trace_diagonal]
    obtain ⟨k, hk⟩ := Function.ne_iff.mp hστ
    apply Finset.sum_eq_zero
    intro s _
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    simp [ambientVirtualWeight, hk]

/-- The ambient weighted two-sector tensor generates a positive semidefinite operator at every
positive chain length.
This verifies the standing MPDO hypothesis of the simple Case-II argument in
arXiv:1606.00608, line 1628, using the density-operator definition at lines
623--630. -/
theorem ambient_isMPDO : IsMPDO ambient := by
  intro N _hN
  rw [mpo_ambient_eq_diagonal]
  apply Matrix.PosSemidef.diagonal
  intro σ
  apply Finset.sum_nonneg
  intro s _
  apply Finset.prod_nonneg
  intro k _
  fin_cases s <;> by_cases hk : σ k = 2 <;>
    norm_num [ambientVirtualWeight, hk, Complex.nonneg_iff]

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
displayed sector decomposition and identity gauge on both bond-one blocks. -/
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

/-- The ambient tensor has the displayed simple canonical form: it generates
positive periodic operators, its two normal BNT representatives have
nonnilpotent physical-trace transfer, and their weighted direct sum is exactly
the ambient doubled-index tensor.
**Scope restriction (normalized fixed representative):** this is the
project's fixed-representative predicate, which includes the global
unit-weight convention of arXiv:1606.00608, line 246. See
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>.
Source: arXiv:1606.00608, canonical form at lines 224--246, simplicity at
lines 815--822, and the Case-II standing hypothesis at line 1628. -/
theorem ambient_isSimpleCanonicalForm : IsSimpleCanonicalForm ambient := by
  refine ⟨ambient_isMPDO, sectors, sectors_isBNTCanonicalForm,
    sectors_basis_doubledPhysTraceTransfer_not_isNilpotent, ?_⟩
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

/-- The ambient physical-trace transfer is literally the identity.
Source: arXiv:1606.00608, Definition 4.2, lines 735--739. -/
lemma physTraceTransfer_ambient : physTraceTransfer ambient = 1 := by
  ext s t
  fin_cases s <;> fin_cases t <;>
    simp [physTraceTransfer, ambient, Fin.sum_univ_succ]
  all_goals norm_num

/-- Every periodic ambient operator, including the empty contraction, has trace two.
For positive lengths this is the normalization factor implicit in the MPDO
and SAL standing assumptions of arXiv:1606.00608, lines 623--630, 811--815,
and 1628. -/
theorem trace_mpo_ambient (N : ℕ) : Matrix.trace (mpo ambient N) = 2 := by
  rw [trace_mpo_eq_trace_verticalLoop_pow,
    verticalLoop_eq_physTraceTransfer, physTraceTransfer_ambient, one_pow]
  simp [Matrix.trace]

/-- The trace used to normalize every positive-length ambient MPDO is strictly positive.
Source: arXiv:1606.00608, density-operator normalization at lines 623--630
and the SAL definition at lines 811--815. -/
theorem trace_mpo_ambient_pos (N : ℕ) :
    0 < Matrix.trace (mpo ambient N) := by
  rw [trace_mpo_ambient]
  norm_num

/-- The one-site projection onto the binary physical sector of the ambient example.
This is the two-dimensional sector selected by the first BNT representative
in the Case-II decomposition of arXiv:1606.00608, lines 1628--1665. -/
private noncomputable def binaryProjection : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i ↦ if i = 2 then 0 else 1

/-- The binary-sector matrix is positive semidefinite.
Source: arXiv:1606.00608, the orthogonal Case-II sector projections at lines
1680--1691. -/
private lemma binaryProjection_posSemidef :
    binaryProjection.PosSemidef := by
  rw [binaryProjection]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> simp

/-- The binary-sector projection is idempotent.
Source: arXiv:1606.00608, the orthogonal Case-II sector projections at lines
1680--1691. -/
private lemma binaryProjection_mul_self :
    binaryProjection * binaryProjection = binaryProjection := by
  rw [binaryProjection, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  fin_cases i <;> norm_num

/-- The binary physical sector has dimension, and hence projection trace, equal to two.
Source: arXiv:1606.00608, the physical-sector splitting used at lines
1680--1712. -/
private lemma trace_binaryProjection : Matrix.trace binaryProjection = 2 := by
  rw [binaryProjection, Matrix.trace_diagonal]
  rw [Fin.sum_univ_three]
  change (1 + 1 + 0 : ℂ) = 2
  norm_num

/-- The complementary one-site projection onto the physical symbol `2`.
This is the second physical sector of the explicit Case-II decomposition,
corresponding to arXiv:1606.00608, lines 1628--1665. -/
private noncomputable def terminalProjection : Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.diagonal fun i ↦ if i = 2 then 1 else 0

/-- The terminal one-site sector is positive semidefinite.
Source: arXiv:1606.00608, the orthogonal Case-II sector projections at lines
1680--1691. -/
private lemma terminalProjection_posSemidef :
    terminalProjection.PosSemidef := by
  rw [terminalProjection]
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> simp

/-- The terminal sector has projection trace one.
Source: arXiv:1606.00608, the physical-sector splitting used at lines
1680--1712. -/
private lemma trace_terminalProjection : Matrix.trace terminalProjection = 1 := by
  rw [terminalProjection, Matrix.trace_diagonal, Fin.sum_univ_three]
  change (0 + 0 + 1 : ℂ) = 1
  norm_num

/-- The terminal projection is exactly the orthogonal complement of the binary projection.
Source: arXiv:1606.00608, the complete orthogonal sector resolution at lines
1680--1691. -/
private lemma one_sub_binaryProjection :
    1 - binaryProjection = terminalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [binaryProjection, terminalProjection]

/-- The normalized two-site state uniformly supported on the four binary physical pairs.
This is the refinement target for the first absorbed sector in the
Definition 4.1 equations of arXiv:1606.00608, lines 638--660. -/
private noncomputable def binaryPairState :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (1 / 4 : ℂ) • Matrix.kronecker binaryProjection binaryProjection

/-- The binary two-site preparation state is positive semidefinite.
Source: arXiv:1606.00608, the positive two-site physical operator in
Definition 4.1, lines 638--660. -/
private lemma binaryPairState_posSemidef : binaryPairState.PosSemidef := by
  exact (binaryProjection_posSemidef.kronecker
    binaryProjection_posSemidef).smul (by norm_num [Complex.nonneg_iff])

/-- The binary two-site preparation state has trace one.
Source: arXiv:1606.00608, trace preservation in Definition 4.1, lines
638--660. -/
private lemma trace_binaryPairState : Matrix.trace binaryPairState = 1 := by
  simp [binaryPairState, Matrix.trace_kronecker, trace_binaryProjection]
  norm_num

/-- The pure two-site state supported on the physical pair `(2,2)`.
This is the refinement target for the second absorbed sector in the
Definition 4.1 equations of arXiv:1606.00608, lines 638--660. -/
private noncomputable def terminalPairState :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.kronecker terminalProjection terminalProjection

/-- The terminal two-site preparation state is positive semidefinite.
Source: arXiv:1606.00608, the positive two-site physical operator in
Definition 4.1, lines 638--660. -/
private lemma terminalPairState_posSemidef : terminalPairState.PosSemidef := by
  exact terminalProjection_posSemidef.kronecker terminalProjection_posSemidef

/-- The terminal two-site preparation state has trace one.
Source: arXiv:1606.00608, trace preservation in Definition 4.1, lines
638--660. -/
private lemma trace_terminalPairState : Matrix.trace terminalPairState = 1 := by
  simp [terminalPairState, Matrix.trace_kronecker,
    trace_terminalProjection]

/-- The two-to-one physical channel obtained by tracing out the second site.
This is an explicit coarse-graining map of the type required by equation
`eq:Smap` in arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private noncomputable def ambientCoarseMap :
    Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ →ₗ[ℂ]
      Matrix (Fin 3) (Fin 3) ℂ :=
  Matrix.partialTraceRightLM

/-- The ambient coarse-graining map is trace preserving and completely positive.
Source: arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private lemma ambientCoarseMap_isKrausCPTP :
    IsKrausCPTP ambientCoarseMap := by
  exact Matrix.partialTraceRightLM_isKrausCPTP

/-- On the binary one-site sector, measure its trace and prepare the uniform binary two-site state.
This is the active part of an explicit refinement map for equation `eq:Tmap`
in arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private noncomputable def ambientRefineActive :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ]
      Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  (Matrix.tracePrepareMap binaryPairState).comp
    (singleKrausMap binaryProjection)

/-- The active binary refinement is completely positive.
Source: arXiv:1606.00608, complete positivity in Definition 4.1, lines
638--660. -/
private lemma ambientRefineActive_isKrausCP :
    IsKrausCP ambientRefineActive := by
  rw [ambientRefineActive]
  exact isKrausCP_comp
    (singleKrausMap_isKrausCP binaryProjection)
    (Matrix.tracePrepareMap_isKrausCP
      binaryPairState binaryPairState_posSemidef)

/-- The active refinement preserves exactly the trace selected by the binary projection.
This is the trace identity needed to complete the refinement to a
trace-preserving map in arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private lemma trace_ambientRefineActive (X : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.trace (ambientRefineActive X) =
      Matrix.trace (binaryProjection * X) := by
  rw [ambientRefineActive, LinearMap.comp_apply,
    Matrix.tracePrepareMap_trace, trace_binaryPairState, mul_one,
    singleKrausMap_apply, binaryProjection_posSemidef.isHermitian.eq]
  calc
    Matrix.trace (binaryProjection * X * binaryProjection) =
        Matrix.trace ((binaryProjection * binaryProjection) * X) := by
      exact Matrix.trace_mul_cycle binaryProjection X binaryProjection
    _ = Matrix.trace (binaryProjection * X) := by
      rw [binaryProjection_mul_self]

/-- The trace-preserving refinement map refines the binary sector uniformly and prepares the pure
`(2,2)` state from the complementary trace.
This explicitly witnesses the map in equation `eq:Tmap` of
arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private noncomputable def ambientRefineMap :
    Matrix (Fin 3) (Fin 3) ℂ →ₗ[ℂ]
      Matrix (Fin 3 × Fin 3) (Fin 3 × Fin 3) ℂ :=
  Matrix.supportCompletion ambientRefineActive binaryProjection
    terminalPairState

/-- The completed ambient refinement is trace preserving and completely positive.
Source: arXiv:1606.00608, Definition 4.1, lines 638--660. -/
private lemma ambientRefineMap_isKrausCPTP :
    IsKrausCPTP ambientRefineMap := by
  exact Matrix.supportCompletion_isKrausCPTP
    ambientRefineActive binaryProjection terminalPairState
    ambientRefineActive_isKrausCP
    binaryProjection_posSemidef.isHermitian
    binaryProjection_mul_self trace_ambientRefineActive
    terminalPairState_posSemidef trace_terminalPairState

/-- The one-site physical closure separates into its binary and terminal sector weights.
This is the explicit one-site operator in figure `MPDO_XM` and Definition 4.1
of arXiv:1606.00608, lines 638--660, for the present Case-II tensor. -/
private lemma physClose1_ambient (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physClose1 ambient X =
      (X 0 0 / 2) • binaryProjection +
        X 1 1 • terminalProjection := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [physClose1_apply, ambient, binaryProjection, terminalProjection,
      Matrix.mul_apply, Matrix.trace, Fin.sum_univ_two, Matrix.smul_apply] <;>
    ring

/-- The two-site physical closure is the corresponding sum of the uniform binary-pair state and the
pure terminal-pair state.
This is the explicit two-site operator in figure `MPDO_XMM` and Definition
4.1 of arXiv:1606.00608, lines 638--660, for the present Case-II tensor. -/
private lemma physClose2_ambient (X : Matrix (Fin 2) (Fin 2) ℂ) :
    physClose2 ambient X =
      X 0 0 • binaryPairState + X 1 1 • terminalPairState := by
  ext p q
  obtain ⟨i₁, i₂⟩ := p
  obtain ⟨j₁, j₂⟩ := q
  fin_cases i₁ <;> fin_cases i₂ <;> fin_cases j₁ <;> fin_cases j₂ <;>
    simp [physClose2_apply, ambient, binaryPairState, terminalPairState,
      binaryProjection, terminalProjection, Matrix.mul_apply, Matrix.trace,
      Fin.sum_univ_two, Matrix.smul_apply, Matrix.kronecker] <;>
    ring

/-- Tracing out the second physical site carries the two-site closure to the one-site closure.
This is equation `eq:Smap` of arXiv:1606.00608, Definition 4.1, lines
638--660, for the present Case-II tensor. -/
private lemma ambientCoarseMap_physClose2 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ambientCoarseMap (physClose2 ambient X) = physClose1 ambient X := by
  rw [physClose2_ambient, physClose1_ambient]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [ambientCoarseMap, Matrix.partialTraceRightLM,
      Matrix.partialTraceRight_apply, binaryPairState, terminalPairState,
      binaryProjection, terminalProjection, Matrix.kronecker,
      Fin.sum_univ_three, Matrix.smul_apply] <;>
    ring

/-- The completed preparation channel carries the one-site closure to the two-site closure.
This is equation `eq:Tmap` of arXiv:1606.00608, Definition 4.1, lines
638--660, for the present Case-II tensor. -/
private lemma ambientRefineMap_physClose1 (X : Matrix (Fin 2) (Fin 2) ℂ) :
    ambientRefineMap (physClose1 ambient X) = physClose2 ambient X := by
  have hPQ : binaryProjection * terminalProjection = 0 := by
    rw [← one_sub_binaryProjection]
    calc
      binaryProjection * (1 - binaryProjection) =
          binaryProjection - binaryProjection * binaryProjection := by noncomm_ring
      _ = 0 := by rw [binaryProjection_mul_self]; simp
  have hQP : terminalProjection * binaryProjection = 0 := by
    rw [← one_sub_binaryProjection]
    calc
      (1 - binaryProjection) * binaryProjection =
          binaryProjection - binaryProjection * binaryProjection := by noncomm_ring
      _ = 0 := by rw [binaryProjection_mul_self]; simp
  have hQQ : terminalProjection * terminalProjection = terminalProjection := by
    rw [← one_sub_binaryProjection]
    calc
      (1 - binaryProjection) * (1 - binaryProjection) =
          1 - binaryProjection - binaryProjection +
            binaryProjection * binaryProjection := by noncomm_ring
      _ = 1 - binaryProjection := by rw [binaryProjection_mul_self]; abel
  rw [physClose1_ambient, physClose2_ambient, ambientRefineMap,
    Matrix.supportCompletion_apply, ambientRefineActive,
    LinearMap.comp_apply, Matrix.tracePrepareMap_apply, singleKrausMap_apply,
    Matrix.supportComplementMap_apply, one_sub_binaryProjection,
    binaryProjection_posSemidef.isHermitian.eq,
    terminalProjection_posSemidef.isHermitian.eq]
  simp [Matrix.mul_add, binaryProjection_mul_self, hPQ, hQP, hQQ,
    Matrix.trace_smul, trace_binaryProjection, trace_terminalProjection]

/-- The explicit coarse-graining and refinement channels witness the local renormalization
fixed-point equations.
Source: arXiv:1606.00608, Definition 4.1, equations `eq:Smap` and `eq:Tmap`,
lines 638--660. -/
private theorem ambient_isRFPViaTS : IsRFPViaTS ambient := by
  exact ⟨ambientCoarseMap, ambientRefineMap,
    ambientCoarseMap_isKrausCPTP, ambientRefineMap_isKrausCPTP,
    ambientCoarseMap_physClose2, ambientRefineMap_physClose1⟩

/-- The ambient Case-II tensor saturates the area law.
The proof uses the explicit trace-preserving completely positive maps from
Definition 4.1 and the positive normalization of every nonempty periodic
operator. Source: arXiv:1606.00608, Definition 4.1, lines 638--660, and
Proposition `propsimple`, Appendix C, lines 1333--1341. -/
theorem ambient_isSAL : IsSAL ambient := by
  exact isSAL_of_isRFPViaTS_of_trace_ne_zero ambient ambient_isMPDO
    (fun N _hN => (trace_mpo_ambient_pos N).ne') ambient_isRFPViaTS

/-- The source's literal physical-trace ZCL equation holds, without rescaling.
Source: arXiv:1606.00608, Definition 4.2, lines 735--739. -/
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
refutes the coefficient-absorption step, not CPSV16 Theorem 4.9.
Source: arXiv:1606.00608, lines 1646--1665. -/
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
            (Kraus.transferMap firstAbsorbed)) = (2 : ENNReal)⁻¹ ∧
      ¬ MPSTensor.IsNormalTensor firstAbsorbed := by
  exact ⟨rfl, rfl, weight_globally_normalized.1, weight_globally_normalized.2,
    basis_isNormalTensor, basis_disjoint_support,
    ambient_eq_weighted_basis_blocks,
    ambient_literal_physTrace_ZCL, spectralRadius_transferMap_firstAbsorbed,
    firstAbsorbed_not_isNormalTensor⟩

/-- The explicit Case-II tensor meets all conditions used in Appendix C.2: it
is an MPDO with positive periodic normalization, satisfies
SAL, has the displayed simple BNT canonical form and biCF representatives,
and obeys the literal physical-trace zero-correlation equation. Nevertheless,
absorbing the first representative's common copy weight produces a tensor
which is not normal.
Copy independence here is only within the copies of one representative; it
does not equate the two weights `1 / √2` and `1`. Thus the conclusion isolates
the printed coefficient-absorption inference at lines 1646--1665. It does not
refute the conclusion of Proposition `prop2to3` or Theorem 4.9.
**Scope restriction (normalized fixed representative):** simplicity is the
project's fixed-representative predicate, including the line-246 unit-weight
convention. See
<https://sirui-lu.com/QICLean/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.pdf>.
Source: arXiv:1606.00608, canonical normalization at lines 224--246,
Definition 4.1 at lines 638--660, and the simple Case-II argument at lines
1628--1665 and 1740--1782. -/
theorem
    ambient_isSAL_isSimpleCanonicalForm_and_firstAbsorbed_not_isNormalTensor :
    IsMPDO ambient ∧
      (∀ N, 0 < N → 0 < Matrix.trace (mpo ambient N)) ∧
      IsSAL ambient ∧
      IsSimpleCanonicalForm ambient ∧
      MPSTensor.IsBNTCanonicalForm sectors ∧
      MPSTensor.HasBiCF sectors.basis ∧
      ambient.toMPSTensor = sectors.toTensor ∧
      (∀ (s : Fin sectors.basisCount)
          (q q' : Fin (sectors.copies s)),
        sectors.weight s q = sectors.weight s q') ∧
      weight 0 = invSqrtTwo ∧ weight 1 = 1 ∧
      (∀ s, ‖weight s‖ ≤ 1) ∧ (∃ s, ‖weight s‖ = 1) ∧
      (∀ s, MPSTensor.IsNormalTensor (basis s)) ∧
      (∀ i, basis 0 i ≠ 0 → basis 1 i = 0) ∧
      physTraceTransfer ambient * physTraceTransfer ambient =
        physTraceTransfer ambient ∧
      spectralRadius ℂ
          ((Module.End.toContinuousLinearMap (Matrix (Fin 1) (Fin 1) ℂ))
            (Kraus.transferMap firstAbsorbed)) = (2 : ENNReal)⁻¹ ∧
      ¬ MPSTensor.IsNormalTensor firstAbsorbed := by
  exact ⟨ambient_isMPDO, fun N _hN => trace_mpo_ambient_pos N,
    ambient_isSAL, ambient_isSimpleCanonicalForm,
    sectors_isBNTCanonicalForm, sectors_hasBiCF,
    ambient_toMPSTensor_eq_sectors_toTensor, weights_copy_independent,
    rfl, rfl, weight_globally_normalized.1, weight_globally_normalized.2,
    basis_isNormalTensor, basis_disjoint_support, ambient_literal_physTrace_ZCL,
    spectralRadius_transferMap_firstAbsorbed,
    firstAbsorbed_not_isNormalTensor⟩

end MPOTensor.CaseIIAbsorptionCounterexample
