/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.BondTwoSingletonBaseModel
import TNLean.MPS.MPDO.InvariantProjection
import TNLean.MPS.CanonicalForm.CPSVBlocking

/-!
# Physical similarities of the bond-two singleton base model

This module applies an invertible physical similarity to the explicit positive
MPO in `BondTwoSingletonBaseModel`.  Positivity of the resulting one- and
two-site operators forces the similarity's Gram matrix to be a positive scalar
multiple of the identity.  The concrete nonunitary gauge from
`BondTwoSingletonGramBoundary` therefore does not preserve the MPDO property.

The calculation is motivated by arXiv:1606.00608, Appendix C.4, lines
2048--2057, together with the metric argument of Proposition 4.13, lines
1898--1921.  It is a model-specific necessary-condition calculation, not a
theorem stated in the source.
-/

open scoped BigOperators ComplexOrder Matrix Kronecker

noncomputable section

open MPOTensor

namespace MPOTensor.BondTwoSingletonBaseModel

open BondTwoSingletonGramBoundary

private abbrev I := Fin 2

/-- The base MPO after ket-left multiplication by `X` and bra-right
multiplication by `X⁻¹`.

This is the physical-similarity deformation used in the model-specific
calculation motivated by arXiv:1606.00608, Appendix C.4, lines 2048--2057. -/
def gaugeDeformedBaseMPO (X : GL I ℂ) : MPOTensor 2 4 :=
  (baseMPO.ketLeftMul (X : Matrix I I ℂ)).braRightMul
    ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)

/-- The vertical tensor of the physically deformed MPO is the corresponding
letterwise similarity of the retained singleton tensor.

This is the explicit model attachment needed for the calculation motivated by
arXiv:1606.00608, Appendix C.4, lines 2048--2057; it is not a source theorem. -/
theorem verticalTensor_gaugeDeformedBaseMPO (X : GL I ℂ) :
    verticalTensor (gaugeDeformedBaseMPO X) = fun v ↦
      (X : Matrix I I ℂ) * singletonTensor v *
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ) := by
  funext v
  dsimp only [gaugeDeformedBaseMPO]
  rw [verticalTensor_braRightMul, verticalTensor_ketLeftMul,
    verticalTensor_baseMPO]

/-- After the canonical one-site reindexing, the deformed MPO is the similarity
of the terminal matrix `terminalJ`.

This is a model-specific one-site calculation motivated by
arXiv:1606.00608, Proposition 4.13, lines 1898--1921, not a theorem stated in
the source. -/
theorem oneSite_gaugeDeformedBaseMPO_eq_terminalJ (X : GL I ℂ) :
    Matrix.reindex (Equiv.funUnique (Fin 1) I) (Equiv.funUnique (Fin 1) I)
        (mpo (gaugeDeformedBaseMPO X) 1) =
      (X : Matrix I I ℂ) * terminalJ *
        ((X⁻¹ : GL I ℂ) : Matrix I I ℂ) := by
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.funUnique_symm_apply]
  change mpo (gaugeDeformedBaseMPO X) 1 (fun _ ↦ i) (fun _ ↦ j) = _
  rw [mpo_apply]
  unfold mpoMatrixEntry
  rw [List.ofFn_succ, List.ofFn_succ]
  simp only [evalWord_cons]
  simp [gaugeDeformedBaseMPO, ketLeftMul, braRightMul, baseMPO, Matrix.trace,
    terminalJ, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_four,
    Matrix.single]
  have h00 : finProdFinEquiv ((0 : I), (0 : I)) = (0 : Fin 4) := by decide
  have h10 : finProdFinEquiv ((1 : I), (0 : I)) = (2 : Fin 4) := by decide
  have h01 : finProdFinEquiv ((0 : I), (1 : I)) = (1 : Fin 4) := by decide
  have h11 : finProdFinEquiv ((1 : I), (1 : I)) = (3 : Fin 4) := by decide
  simp [h00, h10, h01, h11]
  ring

/-- After the canonical two-site reindexing, the deformed MPO is the similarity
of the companion Bell projector, with `X ⊗ₖ X` on the left.

This is a model-specific two-site calculation motivated by
arXiv:1606.00608, Proposition 4.13, lines 1898--1921, not a theorem stated in
the source. -/
theorem twoSite_gaugeDeformedBaseMPO_eq_bellProjector (X : GL I ℂ) :
    Matrix.reindex (finTwoArrowEquiv I) (finTwoArrowEquiv I)
        (mpo (gaugeDeformedBaseMPO X) 2) =
      ((X : Matrix I I ℂ) ⊗ₖ (X : Matrix I I ℂ)) * bellProjector *
        (((X⁻¹ : GL I ℂ) : Matrix I I ℂ) ⊗ₖ
          ((X⁻¹ : GL I ℂ) : Matrix I I ℂ)) := by
  ext p q
  rcases p with ⟨p₀, p₁⟩
  rcases q with ⟨q₀, q₁⟩
  fin_cases p₀ <;>
    fin_cases p₁ <;>
      fin_cases q₀ <;>
        fin_cases q₁ <;>
          simp [Matrix.reindex_apply, mpo_apply, mpoMatrixEntry, evalWord,
            gaugeDeformedBaseMPO, ketLeftMul, braRightMul, baseMPO, Matrix.trace,
            bellProjector, bellVector, Matrix.vecMulVec, Matrix.mul_apply,
            Matrix.kroneckerMap_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
            Fin.sum_univ_four, finTwoArrowEquiv, piFinTwoEquiv_apply, Matrix.single,
            finProdFinEquiv] <;> ring

/-- If the physically deformed base model is an MPDO, then the physical
similarity has positive scalar Gram matrix.

This model-specific necessary condition combines one- and two-site Hermiticity
with the metric calculation motivated by arXiv:1606.00608, Appendix C.4, lines
2048--2057, and Proposition 4.13, lines 1898--1921.  It is not a theorem stated
in the source. -/
theorem gaugeGram_eq_pos_smul_one_of_gaugeDeformedBaseMPO_isMPDO
    (X : GL I ℂ) (hM : IsMPDO (gaugeDeformedBaseMPO X)) :
    ∃ ω : ℝ, 0 < ω ∧
      (X : Matrix I I ℂ)ᴴ * (X : Matrix I I ℂ) = (ω : ℂ) • 1 := by
  apply gaugeGram_eq_pos_smul_one_of_terminal_companionBell_isHermitian X
  · have h := (hM 1 (by norm_num)).isHermitian.reindex
      (Equiv.funUnique (Fin 1) I)
    rwa [oneSite_gaugeDeformedBaseMPO_eq_terminalJ] at h
  · have h := (hM 2 (by norm_num)).isHermitian.reindex (finTwoArrowEquiv I)
    rwa [twoSite_gaugeDeformedBaseMPO_eq_bellProjector] at h

/-- The concrete nonunitary gauge has no scalar Gram matrix, strengthening
`gauge_gram_ne_one` to every real scalar.

This explicit obstruction supports the model-specific calculation motivated
by arXiv:1606.00608, Appendix C.4, lines 2048--2057; it is not a source
theorem. -/
lemma gauge_gram_ne_smul_one (ω : ℝ) :
    (gauge : Matrix I I ℂ)ᴴ * (gauge : Matrix I I ℂ) ≠ (ω : ℂ) • 1 := by
  intro h
  have h01 := congrArg (fun M : Matrix I I ℂ ↦ M 0 1) h
  norm_num [gaugeMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_two, Matrix.smul_apply, map_ofNat] at h01

/-- The concrete physical deformation by `gauge` is not an MPDO.

This is the model-specific obstruction motivated by arXiv:1606.00608,
Appendix C.4, lines 2048--2057, and Proposition 4.13, lines 1898--1921.  It is
not a theorem stated in the source. -/
theorem gaugeDeformedBaseMPO_gauge_not_isMPDO :
    ¬ IsMPDO (gaugeDeformedBaseMPO gauge) := by
  intro hM
  obtain ⟨ω, _hω, hGram⟩ :=
    gaugeGram_eq_pos_smul_one_of_gaugeDeformedBaseMPO_isMPDO gauge hM
  exact gauge_gram_ne_smul_one ω hGram


/-! ### Tensor-algebra and horizontal canonical-form boundary -/

/-- The normalized retained singleton after the concrete nonunitary virtual similarity. -/
def gaugedNormalizedSingletonTensor : MPSTensor (4 * 4) 2 :=
  fun v ↦ (gauge : Matrix I I ℂ) * normalizedSingletonTensor v *
    ((gauge⁻¹ : GL I ℂ) : Matrix I I ℂ)

private def gaugedNormalizedSingletonFamily :
    (alpha : Fin 1) → MPSTensor (4 * 4) 2 :=
  fun _ ↦ gaugedNormalizedSingletonTensor

private lemma singletonScale_pos_physicalGauge : 0 < singletonScale := by
  simp [singletonScale]

private lemma normalizedSingletonTensor_gaugeEquiv_gauged :
    MPSTensor.GaugeEquiv normalizedSingletonTensor
      gaugedNormalizedSingletonTensor :=
  ⟨gauge, fun _ ↦ rfl⟩

/-- The gauged normalized singleton remains a CPSV normal tensor.

This is the virtual-similarity invariance used in CPSV16, Appendix C.4,
lines 2048--2057. -/
theorem gaugedNormalizedSingletonTensor_isNormalTensor :
    MPSTensor.IsNormalTensor gaugedNormalizedSingletonTensor :=
  MPSTensor.IsNormalTensor.of_gaugeEquiv normalizedSingletonTensor_isNormalTensor
    normalizedSingletonTensor_gaugeEquiv_gauged.symm

private lemma mpo_verticalBNTMPO_gaugedNormalizedSingletonTensor
    (L : ℕ) :
    mpo (verticalBNTMPO gaugedNormalizedSingletonTensor) L =
      mpo (verticalBNTMPO normalizedSingletonTensor) L := by
  ext sigma tau
  rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
    ← MPSTensor.mpv_toMPSTensor_pairConfig,
    verticalBNTMPO_toMPSTensor, verticalBNTMPO_toMPSTensor]
  exact (MPSTensor.GaugeEquiv.sameMPV
    normalizedSingletonTensor_gaugeEquiv_gauged L
      (fun n ↦ finProdFinEquiv (sigma n, tau n))).symm

private lemma gaugedNormalizedSingleton_verticalAssembledTensor :
    verticalAssembledTensor (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ 1)
      (fun _ _ ↦ (singletonScale : ℂ)⁻¹) gaugedNormalizedSingletonFamily =
        (fun v ↦ Matrix.reindex singletonRetainedCoordinateEquiv.symm
          singletonRetainedCoordinateEquiv.symm (gaugedSingletonTensor v)) := by
  let e : (Σ _k : Fin 1, Fin 2) ≃ Fin 2 := finSigmaFinEquiv
  have hsymm (i : Fin 2) : e.symm i = ⟨0, i⟩ := by
    apply e.injective
    rw [e.apply_symm_apply]
    ext
    exact (@finSigmaFinEquiv_one (fun _ : Fin 1 ↦ 2) ⟨(0 : Fin 1), i⟩).symm
  have hs : (singletonScale : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt singletonScale_pos_physicalGauge
  have hscaled (v : Fin (4 * 4)) :
      (singletonScale : ℂ)⁻¹ • gaugedNormalizedSingletonTensor v =
        gaugedSingletonTensor v := by
    unfold gaugedNormalizedSingletonTensor gaugedSingletonTensor
    rw [normalizedSingletonTensor, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, inv_mul_cancel₀ hs, one_smul]
  funext v
  ext i j
  simp only [verticalAssembledTensor, verticalCopyWeights, verticalCopyBlocks,
    verticalCopyDim, MPSTensor.toTensorFromBlocks,
    gaugedNormalizedSingletonFamily]
  change (Matrix.reindex e e
      (Matrix.blockDiagonal' (fun _k : Fin 1 ↦
        (singletonScale : ℂ)⁻¹ • gaugedNormalizedSingletonTensor v))) i j =
    (Matrix.reindex singletonRetainedCoordinateEquiv.symm
      singletonRetainedCoordinateEquiv.symm (gaugedSingletonTensor v)) i j
  simp only [Matrix.reindex_apply, hscaled]
  fin_cases i <;> fin_cases j <;> rfl

private theorem gaugeDeformedBaseMPO_isCPSVBasis :
    MPSTensor.IsCPSVBasisOfNormalTensors
      (verticalTensor (gaugeDeformedBaseMPO gauge))
      (fun _alpha : Fin 1 ↦ ⟨2, gaugedNormalizedSingletonTensor⟩) := by
  refine {
    blocks_normal := fun _ ↦ gaugedNormalizedSingletonTensor_isNormalTensor
    spans_mpv := ?_
    eventually_li := ?_
  }
  · intro N hN
    obtain ⟨c, hc⟩ := normalizedSingleton_isCPSVBasis.spans_mpv N hN
    refine ⟨c, fun sigma ↦ ?_⟩
    calc
      MPSTensor.mpv (verticalTensor (gaugeDeformedBaseMPO gauge)) sigma =
          MPSTensor.mpv singletonTensor sigma := by
        rw [verticalTensor_gaugeDeformedBaseMPO]
        exact (MPSTensor.GaugeEquiv.sameMPV
          singletonTensor_gaugeEquiv_gaugedSingletonTensor N sigma).symm
      _ = ∑ alpha, c alpha * MPSTensor.mpv normalizedSingletonTensor sigma := hc sigma
      _ = ∑ alpha, c alpha * MPSTensor.mpv gaugedNormalizedSingletonTensor sigma := by
        apply Finset.sum_congr rfl
        intro alpha _halpha
        congr 1
        exact MPSTensor.GaugeEquiv.sameMPV
          normalizedSingletonTensor_gaugeEquiv_gauged N sigma
  · obtain ⟨N₀, hLI⟩ := normalizedSingleton_isCPSVBasis.eventually_li
    refine ⟨N₀, fun N hN ↦ ?_⟩
    have hstates :
        (fun _alpha : Fin 1 ↦
          MPSTensor.mpvState gaugedNormalizedSingletonTensor N) =
        (fun _alpha : Fin 1 ↦
          MPSTensor.mpvState normalizedSingletonTensor N) := by
      funext alpha
      fin_cases alpha
      apply PiLp.ext
      intro sigma
      simpa only [MPSTensor.mpvState_apply] using
        (MPSTensor.GaugeEquiv.sameMPV
          normalizedSingletonTensor_gaugeEquiv_gauged N sigma).symm
    rw [hstates]
    exact hLI N hN

private theorem gaugeDeformedBaseMPO_vertical_forward (v : Fin (4 * 4)) :
    singletonVerticalCoisometry * verticalTensor (gaugeDeformedBaseMPO gauge) v *
        singletonVerticalCoisometryᴴ =
      verticalAssembledTensor (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ 1)
        (fun _ _ ↦ (singletonScale : ℂ)⁻¹)
        gaugedNormalizedSingletonFamily v := by
  rw [verticalTensor_gaugeDeformedBaseMPO,
    gaugedNormalizedSingleton_verticalAssembledTensor]
  exact singletonVerticalCoisometry_conj (gaugedSingletonTensor v)

private theorem gaugeDeformedBaseMPO_vertical_reconstruction (v : Fin (4 * 4)) :
    verticalTensor (gaugeDeformedBaseMPO gauge) v =
      singletonVerticalCoisometryᴴ *
        verticalAssembledTensor (fun _ : Fin 1 ↦ 2) (fun _ : Fin 1 ↦ 1)
          (fun _ _ ↦ (singletonScale : ℂ)⁻¹)
          gaugedNormalizedSingletonFamily v *
        singletonVerticalCoisometry := by
  rw [verticalTensor_gaugeDeformedBaseMPO,
    gaugedNormalizedSingleton_verticalAssembledTensor]
  exact (singletonVerticalCoisometry_reconstruction
    (gaugedSingletonTensor v)).symm

private noncomputable def gaugedNormalizedSingletonAlgebraClause :
    BNTAlgebraClause normalizedSingletonCoeffs
      (verticalBNTOperatorFamily gaugedNormalizedSingletonFamily)
      (verticalBNTTraceScalarFamily
        (fun _ : Fin 1 ↦ fun _ : Fin 1 ↦ (singletonScale : ℂ)⁻¹)) := by
  refine {
    positiveChi := PositiveBNTLabelChiTracePowerForm.ofChi
      normalizedSingletonChi ?_
    sameLengthProduct := ?_
    idempotent := ?_
  }
  · intro alpha beta gamma q
    simpa [normalizedSingletonChi] using
      (Complex.zero_lt_real.mpr singletonScale_pos_physicalGauge)
  · intro L hL alpha beta
    fin_cases alpha
    fin_cases beta
    simp only [verticalBNTOperatorFamily_operator,
      gaugedNormalizedSingletonFamily, normalizedSingletonCoeffs_coeff,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [mpo_verticalBNTMPO_gaugedNormalizedSingletonTensor]
    simpa using normalized_singleton_geometric_algebra L hL
  · intro gamma
    fin_cases gamma
    have hs : (singletonScale : ℂ) ≠ 0 := by
      exact_mod_cast ne_of_gt singletonScale_pos_physicalGauge
    simp only [verticalBNTTraceScalarFamily_traceScalar,
      Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      normalizedSingletonCoeffs_coeff]
    field_simp

/-- The concrete nonunitary deformation carries a genuine one-label
`BNTAlgebraTensorClause`, including positive chi, the same-length product law,
the idempotent scalar law, and exact forward and reconstruction identities.

This declaration formalizes the tensor attachment used in CPSV16, Appendix
C.4, lines 2048--2057, for the concrete boundary model.  The algebra clause is
the premise of CPSV16, Theorem 4.14(ii); this model is not a counterexample to
the theorem because MPDO positivity fails at length two. -/
noncomputable def gaugeDeformedBaseMPOBNTAlgebraTensorClause :
    BNTAlgebraTensorClause (gaugeDeformedBaseMPO gauge) where
  labelCount := 1
  bondDim := fun _ ↦ 2
  multiplicity := fun _ ↦ 1
  weight := fun _ _ ↦ (singletonScale : ℂ)⁻¹
  tensor := gaugedNormalizedSingletonFamily
  verticalCoisometry := singletonVerticalCoisometry
  multiplicity_pos := by simp
  weight_pos := by
    intro alpha q
    have hs : (0 : ℂ) < (singletonScale : ℂ) :=
      Complex.zero_lt_real.mpr singletonScale_pos_physicalGauge
    simpa using inv_pos.mpr hs
  coisometry := singletonVerticalCoisometry_coisometry
  isCPSVBNT := gaugeDeformedBaseMPO_isCPSVBasis
  forward := gaugeDeformedBaseMPO_vertical_forward
  reconstruction := gaugeDeformedBaseMPO_vertical_reconstruction
  coeffs := normalizedSingletonCoeffs
  algebraClause := gaugedNormalizedSingletonAlgebraClause

@[simp] private lemma finProdFinEquiv_zero_zero :
    finProdFinEquiv ((0 : I), (0 : I)) = (0 : Fin 4) := by decide

@[simp] private lemma finProdFinEquiv_zero_one :
    finProdFinEquiv ((0 : I), (1 : I)) = (1 : Fin 4) := by decide

@[simp] private lemma finProdFinEquiv_one_zero :
    finProdFinEquiv ((1 : I), (0 : I)) = (2 : Fin 4) := by decide

@[simp] private lemma finProdFinEquiv_one_one :
    finProdFinEquiv ((1 : I), (1 : I)) = (3 : Fin 4) := by decide

@[simp] private lemma fin4_zero_ne_one : (0 : Fin 4) ≠ 1 := by decide
@[simp] private lemma fin4_zero_ne_two : (0 : Fin 4) ≠ 2 := by decide
@[simp] private lemma fin4_zero_ne_three : (0 : Fin 4) ≠ 3 := by decide
@[simp] private lemma fin4_one_ne_two : (1 : Fin 4) ≠ 2 := by decide
@[simp] private lemma fin4_one_ne_three : (1 : Fin 4) ≠ 3 := by decide
@[simp] private lemma fin4_two_ne_three : (2 : Fin 4) ≠ 3 := by decide

private def gaugeDeformedSymbolCoefficient (p a : Fin 4) : ℂ :=
  if p = 0 then
    if a = 0 then 9 / 8 else if a = 1 then -3 / 8 else
      if a = 2 then 3 / 8 else -1 / 8
  else if p = 1 then
    if a = 0 then -3 / 8 else if a = 1 then 9 / 8 else
      if a = 2 then -1 / 8 else 3 / 8
  else if p = 2 then
    if a = 0 then 3 / 8 else if a = 1 then -1 / 8 else
      if a = 2 then 9 / 8 else -3 / 8
  else
    if a = 0 then -1 / 8 else if a = 1 then 3 / 8 else
      if a = 2 then -3 / 8 else 9 / 8

set_option maxHeartbeats 800000 in
-- The explicit six-index case split expands to 64 concrete matrix calculations.
private theorem gaugeDeformedBaseMPO_toMPSTensor_apply
    (p x y : Fin 4) :
    (gaugeDeformedBaseMPO gauge).toMPSTensor p x y =
      if x = y then gaugeDeformedSymbolCoefficient p x else 0 := by
  simp only [gaugeDeformedBaseMPO, gauge_inv_val]
  obtain ⟨⟨pi, pj⟩, rfl⟩ :=
    (finProdFinEquiv : I × I ≃ Fin 4).surjective p
  obtain ⟨⟨xi, xj⟩, rfl⟩ :=
    (finProdFinEquiv : I × I ≃ Fin 4).surjective x
  obtain ⟨⟨yi, yj⟩, rfl⟩ :=
    (finProdFinEquiv : I × I ≃ Fin 4).surjective y
  fin_cases pi <;> fin_cases pj <;> fin_cases xi <;> fin_cases xj <;>
    fin_cases yi <;> fin_cases yj <;>
      norm_num [toMPSTensor, ketLeftMul, braRightMul, baseMPO, gaugeMatrix,
        gaugeDeformedSymbolCoefficient, Matrix.mul_apply, Fin.sum_univ_two,
        Fin.sum_univ_four, Matrix.single, Fin.modNat, Fin.divNat] <;>
        simp_all


/-- The normalized bond-one horizontal block attached to a doubled virtual
symbol of the concrete deformation. -/
def gaugeDeformedSymbolTensor (a : Fin 4) : MPSTensor 4 1 :=
  fun p ↦ ((4 / 5 : ℂ) * gaugeDeformedSymbolCoefficient p a) •
    (1 : Matrix (Fin 1) (Fin 1) ℂ)

private theorem gaugeDeformedSymbolTensor_transferMap (a : Fin 4) :
    MPSTensor.transferMap (gaugeDeformedSymbolTensor a) = LinearMap.id := by
  apply LinearMap.ext
  intro X
  ext x y
  fin_cases a <;> fin_cases x <;> fin_cases y <;>
    norm_num [MPSTensor.transferMap_apply, gaugeDeformedSymbolTensor,
      gaugeDeformedSymbolCoefficient, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.smul_apply, Matrix.one_apply, map_ofNat] <;>
      simp_all <;> ring

/-- Every displayed horizontal block of the concrete deformation is a CPSV
normal tensor. -/
theorem gaugeDeformedSymbolTensor_isNormalTensor (a : Fin 4) :
    MPSTensor.IsNormalTensor (gaugeDeformedSymbolTensor a) :=
  MPSTensor.isNormalTensor_of_bondDim_one_of_transferMap_eq_id
    (gaugeDeformedSymbolTensor a) (gaugeDeformedSymbolTensor_transferMap a)

private def gaugeDeformedSymbolBlocks : (a : Fin 4) → MPSTensor 4 1 :=
  gaugeDeformedSymbolTensor

private theorem gaugeDeformedBaseMPO_toMPSTensor_eq_symbolBlocks :
    (gaugeDeformedBaseMPO gauge).toMPSTensor =
      MPSTensor.toTensorFromBlocks (fun _ : Fin 4 ↦ (5 / 4 : ℂ))
        gaugeDeformedSymbolBlocks := by
  let e : (Σ _k : Fin 4, Fin 1) ≃ Fin 4 := finSigmaFinEquiv
  have hflat (k : Fin 4) : e ⟨k, 0⟩ = k := by
    fin_cases k <;> rfl
  have hflat_symm (k : Fin 4) : e.symm k = ⟨k, 0⟩ := by
    apply e.injective
    rw [e.apply_symm_apply, hflat]
  funext p
  ext x y
  simp only [MPSTensor.toTensorFromBlocks, gaugeDeformedSymbolBlocks,
    gaugeDeformedSymbolTensor]
  change (gaugeDeformedBaseMPO gauge).toMPSTensor p x y =
    Matrix.blockDiagonal' (fun k : Fin 4 ↦
      (5 / 4 : ℂ) • (((4 / 5 : ℂ) *
        gaugeDeformedSymbolCoefficient p k) •
          (1 : Matrix (Fin 1) (Fin 1) ℂ))) (e.symm x) (e.symm y)
  rw [hflat_symm x, hflat_symm y]
  by_cases hxy : x = y
  · subst y
    simp [gaugeDeformedBaseMPO_toMPSTensor_apply, Matrix.smul_apply]
    ring
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hxy]
    simp [gaugeDeformedBaseMPO_toMPSTensor_apply, hxy]

/-- The horizontal doubled-index tensor of the concrete nonunitary deformation
is in the literal CPSV canonical form of `II_CF1`.

Source: CPSV16, Section II.A, lines 214--245, and the use of horizontal
canonical form in Theorem 4.14(ii). -/
theorem gaugeDeformedBaseMPO_toMPSTensor_isCPSVCanonicalForm :
    MPSTensor.IsCPSVCanonicalForm
      (gaugeDeformedBaseMPO gauge).toMPSTensor := by
  rw [gaugeDeformedBaseMPO_toMPSTensor_eq_symbolBlocks]
  exact (MPSTensor.CPSVCanonicalFormData.ofBlocks
    (fun _ : Fin 4 ↦ by simp) (fun _ : Fin 4 ↦ (5 / 4 : ℂ))
    gaugeDeformedSymbolBlocks
    (fun a ↦ gaugeDeformedSymbolTensor_isNormalTensor a)).isCPSVCanonicalForm

/-- The concrete deformation satisfies the tensor-attached algebra clause and
literal horizontal canonical-form premises of CPSV16, Theorem 4.14(ii), but is
not an MPDO.

The failure occurs already at length two.  Accordingly this theorem is not a
full-contract counterexample and does not construct an
`IdentityMarkedRealization`; it isolates all-length MPDO positivity as the
failed standing hypothesis in this family.  Source: CPSV16, Appendix C.4,
lines 2048--2057, and Theorem 4.14(ii). -/
theorem gaugeDeformedBaseMPO_algebraClause_canonicalForm_not_isMPDO :
    Nonempty (BNTAlgebraTensorClause (gaugeDeformedBaseMPO gauge)) ∧
      MPSTensor.IsCPSVCanonicalForm
        (gaugeDeformedBaseMPO gauge).toMPSTensor ∧
      ¬ IsMPDO (gaugeDeformedBaseMPO gauge) :=
  ⟨⟨gaugeDeformedBaseMPOBNTAlgebraTensorClause⟩,
    gaugeDeformedBaseMPO_toMPSTensor_isCPSVCanonicalForm,
    gaugeDeformedBaseMPO_gauge_not_isMPDO⟩

end MPOTensor.BondTwoSingletonBaseModel
