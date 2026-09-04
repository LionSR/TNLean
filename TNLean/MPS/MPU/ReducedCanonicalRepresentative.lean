/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.CPSVCanonicalFormII
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.Tactic.Basic

/-!
# Reduced canonical representatives of matrix product unitaries

This file constructs the reduced canonical-form-II representative used before
the matrix product unitary arguments of Cirac--Perez-Garcia--Schuch--Verstraete.
The construction removes zero and upper-triangular virtual sectors, normalizes
the retained irreducible blocks through the shifted transfer traces, and then
applies the canonical-form-II gauge.

The reduction follows arXiv:1606.00608, lines 195--255 and 1058--1077. Its use
for matrix product unitaries follows arXiv:1703.09188, lines 257--294, 319--326,
and 344--356. The final gauge is the inclusion of the unique retained block, so
the representative is written in ambient coordinates whose right fixed matrix is
the positive diagonal trace-one matrix of equation `Erightleft`, lines 269--281.

**Scope boundary (representative reduction):** The result constructs a new
tensor of no larger bond dimension with the same positive-length periodic
operator family. Equality at length zero is neither asserted nor generally
true. The construction does not transport compact-SVD source spaces or source
factors from the reduced tensor back to the original auxiliary space. See
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPOTensor

variable {d D : ℕ}

private theorem mpvOverlap_two_eq_zero_of_bondDim_eq_zero
    {e E : ℕ} (A : MPSTensor e E) (hE : E = 0) :
    MPSTensor.mpvOverlap A A 2 = 0 := by
  subst E
  simp [MPSTensor.mpvOverlap, MPSTensor.mpv, MPSTensor.coeff, Matrix.trace]

/-- The unit shifted transfer traces of a matrix product unitary pass to every
tensor generating the same positive-length matrix product vectors as its
normalized flattening.

Source: arXiv:1703.09188, lines 344--356. -/
private theorem trace_transferMatrix_pow_eq_one_of_sameMPV
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : U.IsMPU)
    {E : ℕ} [NeZero E] {A : MPSTensor (d * d) E}
    (hSame : MPSTensor.SameMPV₂Pos U.normalizedFlattening A)
    (N : ℕ) (hN : 1 < N) :
    Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1 := by
  calc
    Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) =
        MPSTensor.mpvOverlap A A N :=
      MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap A N
    _ = MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening N :=
      (MPSTensor.mpvOverlap_eq_of_pos_mpv_eq
        (fun {N} hN => hSame N hN) (fun {N} hN => hSame N hN)
        (Nat.zero_lt_of_lt hN)).symm
    _ = Matrix.trace
        (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) :=
      (MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap
        U.normalizedFlattening N).symm
    _ = 1 := hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN

/-- Assemble a canonical-form-II presentation of a matrix product unitary from
canonical data for a tensor equal to its normalized flattening.

Source: arXiv:1703.09188, lines 269--281 and 344--356. -/
private def mpuCanonicalFormIIOfNormalizedFlatteningEq
    {E : ℕ} {V : MPOTensor d E} {A : MPSTensor (d * d) E}
    (hA : V.normalizedFlattening = A) (hV : V.IsMPU)
    (cfii : MPSTensor.CPSVCanonicalFormIIData A)
    (hfull : cfii.toCPSVCanonicalFormData.HasFullSupport)
    (ρ : Matrix (Fin E) (Fin E) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρtrace : Matrix.trace ρ = 1) (hρfix : Kraus.transferMap A ρ = ρ) :
    IsMPUCanonicalFormII V := by
  subst hA
  exact
    { isMPU := hV
      cfii := cfii
      fullSupport_eq := hfull
      ρ := ρ
      ρ_posDef := hρpd
      ρ_isDiag := hρdiag
      ρ_trace := hρtrace
      ρ_fixed := hρfix }

/-- Every matrix product unitary has a positive-dimensional, normal,
full-support canonical-form-II representative of its normalized flattening,
written in ambient bond coordinates whose right fixed matrix is positive,
diagonal, and of trace one. The representative has no larger bond dimension
and generates the same matrix product vectors at every positive length.

The canonical-form convention in arXiv:1703.09188, lines 257--294 and 319--326,
replaces a tensor by one generating the same matrix product vectors. For a
matrix product unitary, lines 344--356 then use the shifted transfer traces to
obtain a normal representative in canonical form II. Lines 269--294 record the
further gauge transformation placing the right fixed matrix `ρ` of equation
`Erightleft` in the diagonal positive trace-one form; here that gauge is the
inclusion of the unique retained block, which carries its own diagonal fixed
matrix into the ambient coordinates. The dimension-bounded irreducible
reduction and canonical-form-II gauge are those of arXiv:1606.00608, lines
195--255 and 1058--1077. This theorem combines those steps; it is not a
separately stated theorem of either paper. -/
theorem IsMPU.exists_reduced_normalizedFlattening_cfii
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : U.IsMPU) :
    ∃ (Dred : ℕ) (_hDred : 0 < Dred) (Ared : MPSTensor (d * d) Dred)
      (cfii : MPSTensor.CPSVCanonicalFormIIData Ared)
      (ρ : Matrix (Fin Dred) (Fin Dred) ℂ),
      Dred ≤ D ∧
      MPSTensor.SameMPV₂Pos U.normalizedFlattening Ared ∧
      MPSTensor.IsNormalTensor Ared ∧
      cfii.toCPSVCanonicalFormData.HasFullSupport ∧
      ρ.PosDef ∧ ρ.IsDiag ∧ Matrix.trace ρ = 1 ∧
      Kraus.transferMap Ared ρ = ρ := by
  classical
  obtain ⟨r, dim, blocks, hIrr, hNonzero, hDim, hSame, hDimLe⟩ :=
    MPSTensor.exists_irreducible_blockDecomp_nonzeroBlocks U.normalizedFlattening
  let Dred : ℕ := ∑ k : Fin r, dim k
  let Ared : MPSTensor (d * d) Dred :=
    MPSTensor.toTensorFromBlocks (fun _ : Fin r => (1 : ℂ)) blocks
  have hOriginalOverlap :
      MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening 2 = 1 := by
    rw [← MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap]
    exact hU.trace_transferMatrix_normalizedFlattening_pow_eq_one (by omega)
  have hReducedOverlap : MPSTensor.mpvOverlap Ared Ared 2 = 1 := by
    calc
      MPSTensor.mpvOverlap Ared Ared 2 =
          MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening 2 :=
        (MPSTensor.mpvOverlap_eq_of_pos_mpv_eq
          (fun {N} hN => hSame N hN) (fun {N} hN => hSame N hN) (by omega)).symm
      _ = 1 := hOriginalOverlap
  have hDred : 0 < Dred := by
    by_contra h
    have hDredZero : Dred = 0 := Nat.eq_zero_of_not_pos h
    have hzero := mpvOverlap_two_eq_zero_of_bondDim_eq_zero Ared hDredZero
    rw [hReducedOverlap] at hzero
    exact one_ne_zero hzero
  let _ : NeZero Dred := NeZero.of_pos hDred
  have hTrace : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap Ared) ^ N) = 1 :=
    trace_transferMatrix_pow_eq_one_of_sameMPV hU hSame
  have hBlocksNormal : ∀ k : Fin r, MPSTensor.IsNormalTensor (blocks k) := by
    intro k
    let _ : NeZero (dim k) := NeZero.of_pos (hDim k)
    obtain ⟨ρ, radius, hρ, hRadius, hEigenvector⟩ :=
      MPSTensor.exists_posDef_transferMap_eigenvector_of_irreducible
        (blocks k) (hIrr k) (hNonzero k)
    have hEigenvalue_eq_one : ∀ {μ : ℂ},
        Module.End.HasEigenvalue (Kraus.transferMap (blocks k)) μ → μ ≠ 0 → μ = 1 := by
      intro μ hμ hμ0
      have hAmbient : Module.End.HasEigenvalue (Kraus.transferMap Ared) μ :=
        MPSTensor.hasEigenvalue_transferMap_of_intertwine Ared (blocks k)
          (MPSTensor.blockInclusion dim k)
          (MPSTensor.blockInclusion_conjTranspose_mul_self dim k)
          (fun i => by
            simpa [Ared] using
              MPSTensor.toTensorFromBlocks_mul_blockInclusion
                (fun _ : Fin r => (1 : ℂ)) blocks k i)
          hμ
      have hMatrix : Module.End.HasEigenvalue
          (transferMatrix (Kraus.transferMap Ared)).toLin' μ :=
        (transferMatrix_hasEigenvalue_iff (Kraus.transferMap Ared) μ).mp hAmbient
      have hSpectrum : μ ∈ spectrum ℂ (transferMatrix (Kraus.transferMap Ared)) := by
        simpa using Module.End.hasEigenvalue_iff_mem_spectrum.mp hMatrix
      exact Matrix.eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
        (transferMatrix (Kraus.transferMap Ared)) hTrace hSpectrum hμ0
    have hρne : ρ ≠ 0 := (Matrix.PosDef.isUnit hρ).ne_zero
    have hRadiusEigenvalue : Module.End.HasEigenvalue
        (Kraus.transferMap (blocks k)) (radius : ℂ) :=
      hasEigenvalue_of_eigenvector_eq _ _ ρ hEigenvector hρne
    have hRadiusComplex : (radius : ℂ) = 1 :=
      hEigenvalue_eq_one hRadiusEigenvalue (by exact_mod_cast hRadius.ne')
    have hRadiusOne : radius = 1 := by exact_mod_cast hRadiusComplex
    have hNormal := MPSTensor.isNormalTensor_invSqrt_smul_of_unique_peripheral
      (blocks k) (hIrr k) ρ radius hρ hRadius hEigenvector (fun μ hμ hNorm => by
        have hμ0 : μ ≠ 0 := by
          intro hzero
          subst μ
          simp only [norm_zero] at hNorm
          linarith
        rw [hRadiusOne]
        exact hEigenvalue_eq_one hμ hμ0)
    simpa [hRadiusOne] using hNormal
  let data : MPSTensor.CPSVCanonicalFormData Ared :=
    MPSTensor.CPSVCanonicalFormData.ofBlocks hDim
      (fun _ : Fin r => (1 : ℂ)) (fun _ => one_ne_zero) blocks hBlocksNormal
  have hFull : data.HasFullSupport := by
    rfl
  obtain ⟨B, dataB, hGauge, hTotalDim⟩ :=
    data.exists_gaugeEquiv_canonicalFormIIData
  have hGaugePos : MPSTensor.SameMPV₂Pos Ared B :=
    MPSTensor.SameMPV₂.toSameMPV₂Pos (fun N σ => hGauge.sameMPV N σ)
  have hSameB : MPSTensor.SameMPV₂Pos U.normalizedFlattening B :=
    hSame.trans hGaugePos
  have hTraceB : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap B) ^ N) = 1 :=
    trace_transferMatrix_pow_eq_one_of_sameMPV hU hSameB
  have hFullB : dataB.toCPSVCanonicalFormData.HasFullSupport := by
    change (∑ k : Fin dataB.r, dataB.dim k) = Dred
    exact hTotalDim.trans hFull
  have hBlockCountB : dataB.r = 1 :=
    dataB.toCPSVCanonicalFormData.r_eq_one_of_shifted_transfer_trace hTraceB
  -- Change gauge to the coordinates of the unique retained block. In those
  -- ambient coordinates the diagonal positive trace-one block fixed matrix is
  -- the ambient right fixed matrix of arXiv:1703.09188, equation `Erightleft`,
  -- lines 269--294.
  let baseB := dataB.toCPSVCanonicalFormData
  let k : Fin dataB.r := ⟨0, by omega⟩
  have hdimk : dataB.dim k = Dred :=
    baseB.dim_eq_of_r_eq_one_of_fullSupport hBlockCountB hFullB k
  obtain ⟨Λ₀, hΛ₀pd, hΛ₀diag, hΛ₀fix⟩ := dataB.blocks_fixed_point k
  let _ : Nonempty (Fin (dataB.dim k)) := Fin.pos_iff_nonempty.mp (dataB.dim_pos k)
  let Λ : Matrix (Fin (dataB.dim k)) (Fin (dataB.dim k)) ℂ :=
    (Matrix.trace Λ₀)⁻¹ • Λ₀
  have hΛtracePos : 0 < Matrix.trace Λ₀ := hΛ₀pd.trace_pos
  have hΛpd : Λ.PosDef := hΛ₀pd.smul (inv_pos.mpr hΛtracePos)
  have hΛdiag : Λ.IsDiag := hΛ₀diag.smul _
  have hΛtrace : Matrix.trace Λ = 1 := by
    simp [Λ, Matrix.trace_smul, ne_of_gt hΛtracePos]
  have hΛfix : Kraus.transferMap (dataB.blocks k) Λ = Λ := by
    simp only [Λ, map_smul, hΛ₀fix]
  have hweight : dataB.weights k * starRingEnd ℂ (dataB.weights k) = 1 := by
    simpa [baseB, MPSTensor.CPSVCanonicalFormData.transferEigenvalue] using
      baseB.transferEigenvalue_eq_one hTraceB k
  have hweightedFix :
      Kraus.transferMap (fun i => dataB.weights k • dataB.blocks k i) Λ = Λ := by
    rw [MPSTensor.transferMap_smul, hΛfix, hweight, one_smul]
  let V := baseB.ambientBlockInclusion k
  have hVstarV : Vᴴ * V = 1 :=
    baseB.ambientBlockInclusion_conjTranspose_mul_self k
  have hVVstar : V * Vᴴ = 1 :=
    baseB.ambientBlockInclusion_mul_conjTranspose_eq_one hBlockCountB hFullB k
  have hVfix : Kraus.transferMap B (V * Λ * Vᴴ) = V * Λ * Vᴴ := by
    rw [MPSTensor.transferMap_conj_of_intertwine B
      (fun i => dataB.weights k • dataB.blocks k i) V
      (baseB.mul_ambientBlockInclusion k) Λ, hweightedFix]
  let e : Fin Dred ≃ Fin (dataB.dim k) := finCongr hdimk.symm
  let W : Matrix (Fin Dred) (Fin Dred) ℂ := V.submatrix (Equiv.refl (Fin Dred)) e
  have hWdef : W = V.submatrix (Equiv.refl (Fin Dred)) e := rfl
  have hWconj : Wᴴ = Vᴴ.submatrix e (Equiv.refl (Fin Dred)) := by
    rw [hWdef, Matrix.conjTranspose_submatrix]
  have hWWstar : W * Wᴴ = 1 := by
    rw [hWconj, hWdef, Matrix.submatrix_mul_equiv V Vᴴ (Equiv.refl (Fin Dred)) e
      (Equiv.refl (Fin Dred)), hVVstar]
    simp
  have hWstarW : Wᴴ * W = 1 := by
    rw [hWconj, hWdef,
      Matrix.submatrix_mul_equiv Vᴴ V e (Equiv.refl (Fin Dred)) e,
      hVstarV, Matrix.submatrix_one_equiv]
  let C : MPSTensor (d * d) Dred := fun i => Wᴴ * B i * W
  have hCdef : ∀ i, C i = Wᴴ * B i * W := fun _ => rfl
  let ρ : Matrix (Fin Dred) (Fin Dred) ℂ := Λ.submatrix e e
  have hρdef : ρ = Λ.submatrix e e := rfl
  have hρpd : ρ.PosDef := hΛpd.submatrix e.injective
  have hρdiag : ρ.IsDiag := hΛdiag.submatrix e.injective
  have hρtrace : Matrix.trace ρ = 1 := by
    have hsum : Matrix.trace ρ = Matrix.trace Λ := by
      rw [hρdef]
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.submatrix_apply]
      exact Equiv.sum_comp e fun j => Λ j j
    rw [hsum, hΛtrace]
  have hρconj : W * ρ * Wᴴ = V * Λ * Vᴴ := by
    rw [hWconj, hWdef, hρdef,
      Matrix.submatrix_mul_equiv V Λ (Equiv.refl (Fin Dred)) e e,
      Matrix.submatrix_mul_equiv (V * Λ) Vᴴ (Equiv.refl (Fin Dred)) e
        (Equiv.refl (Fin Dred))]
    simp
  have hcompress : ∀ X : Matrix (Fin Dred) (Fin Dred) ℂ,
      Wᴴ * (W * X * Wᴴ) * W = X := by
    intro X
    calc
      Wᴴ * (W * X * Wᴴ) * W = (Wᴴ * W) * X * (Wᴴ * W) := by
        simp only [Matrix.mul_assoc]
      _ = X := by rw [hWstarW, Matrix.one_mul, Matrix.mul_one]
  have hintertwine : ∀ i, B i * W = W * C i := by
    intro i
    calc
      B i * W = (W * Wᴴ) * B i * W := by rw [hWWstar, Matrix.one_mul]
      _ = W * C i := by rw [hCdef]; simp only [Matrix.mul_assoc]
  have hCfix : Kraus.transferMap C ρ = ρ := by
    have hconj := MPSTensor.transferMap_conj_of_intertwine B C W hintertwine ρ
    calc
      Kraus.transferMap C ρ
          = Wᴴ * (W * Kraus.transferMap C ρ * Wᴴ) * W := (hcompress _).symm
      _ = Wᴴ * (W * ρ * Wᴴ) * W := by rw [← hconj, hρconj, hVfix, ← hρconj]
      _ = ρ := hcompress ρ
  have hrecC : ∀ i, C i = (dataB.ambient_coisometry * W)ᴴ *
      MPSTensor.toTensorFromBlocks dataB.weights dataB.blocks i *
        (dataB.ambient_coisometry * W) := by
    intro i
    rw [Matrix.conjTranspose_mul, hCdef i, dataB.reconstruct i]
    simp only [Matrix.mul_assoc]
  let dataC : MPSTensor.CPSVCanonicalFormIIData C :=
    { dataB with
      ambient_coisometry := dataB.ambient_coisometry * W
      coisometric := by
        rw [Matrix.conjTranspose_mul, Matrix.mul_assoc,
          ← Matrix.mul_assoc W Wᴴ, hWWstar, Matrix.one_mul, dataB.coisometric]
      reconstruct := hrecC }
  have hFullC : dataC.toCPSVCanonicalFormData.HasFullSupport := hFullB
  have hSameBC : MPSTensor.SameMPV₂Pos B C :=
    MPSTensor.sameMPV₂Pos_of_coisometry_reconstruction B C Wᴴ
      (by rw [Matrix.conjTranspose_conjTranspose, hWstarW])
      (fun i => by
        rw [Matrix.conjTranspose_conjTranspose]
        calc
          B i = (W * Wᴴ) * B i * (W * Wᴴ) := by
            rw [hWWstar, Matrix.one_mul, Matrix.mul_one]
          _ = W * C i * Wᴴ := by rw [hCdef]; simp only [Matrix.mul_assoc])
  have hSameC : MPSTensor.SameMPV₂Pos U.normalizedFlattening C :=
    hSameB.trans hSameBC
  have hTraceC : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap C) ^ N) = 1 :=
    trace_transferMatrix_pow_eq_one_of_sameMPV hU hSameC
  obtain ⟨hRadiusC, hPrimitiveC⟩ :=
    spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace
      (Kraus.transferMap C) hTraceC
  have hCNormal : MPSTensor.IsNormalTensor C :=
    dataC.toCPSVCanonicalFormData.isNormalTensor_of_r_eq_one_of_fullSupport
      hBlockCountB hFullC hRadiusC hPrimitiveC
  exact ⟨Dred, hDred, C, dataC, ρ, by simpa [Dred] using hDimLe,
    hSameC, hCNormal, hFullC, hρpd, hρdiag, hρtrace, hCfix⟩

private noncomputable def ofNormalizedFlattening
    (A : MPSTensor (d * d) D) : MPOTensor d D :=
  fun i j => (Real.sqrt d : ℂ) • A (finProdFinEquiv (i, j))

private theorem toMPSTensor_ofNormalizedFlattening
    (A : MPSTensor (d * d) D) :
    (ofNormalizedFlattening A).toMPSTensor =
      fun ij => (Real.sqrt d : ℂ) • A ij := by
  funext ij
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [ofNormalizedFlattening, MPOTensor.toMPSTensor]

private theorem normalizedFlattening_ofNormalizedFlattening [NeZero d]
    (A : MPSTensor (d * d) D) :
    (ofNormalizedFlattening A).normalizedFlattening = A := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast NeZero.pos d
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  change (fun ij => ((Real.sqrt d : ℂ)⁻¹) •
    (ofNormalizedFlattening A).toMPSTensor ij) = A
  rw [toMPSTensor_ofNormalizedFlattening]
  funext ij
  rw [smul_smul, inv_mul_cancel₀ hsqrt, one_smul]

private theorem sqrt_smul_normalizedFlattening [NeZero d]
    (U : MPOTensor d D) :
    (fun ij => (Real.sqrt d : ℂ) • U.normalizedFlattening ij) = U.toMPSTensor := by
  have hd : (0 : ℝ) < d := by
    exact_mod_cast NeZero.pos d
  have hsqrt : (Real.sqrt d : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  funext ij
  simp [MPOTensor.normalizedFlattening, smul_smul, hsqrt]

/-- Every matrix product unitary has a positive-dimensional
canonical-form-II matrix product unitary representative of no larger bond
dimension which generates the same periodic operators at every positive
length.

This is the representative-level form of the replacement used in
arXiv:1703.09188, lines 257--294 and 319--326, with normality supplied by the
shifted-transfer argument at lines 344--356. The canonical-form-II presentation
carries the positive diagonal trace-one ambient right fixed matrix of equation
`Erightleft`, lines 269--281. The dimension reduction and CFII gauge follow
arXiv:1606.00608, lines 195--255 and 1058--1077. This theorem does not identify
a virtual gauge between the original and reduced bond spaces, whose dimensions
may differ. -/
theorem IsMPU.exists_reduced_cfii_representative
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : U.IsMPU) :
    ∃ (Dred : ℕ) (_hDred : 0 < Dred) (Ured : MPOTensor d Dred)
      (_hcfii : IsMPUCanonicalFormII Ured),
      Dred ≤ D ∧
      (∀ N : ℕ, 0 < N → mpo Ured N = mpo U N) := by
  obtain ⟨Dred, hDred, Ared, cfii, ρ, hDimLe, hSame, _hNormal, hFull,
    hρpd, hρdiag, hρtrace, hρfix⟩ :=
    hU.exists_reduced_normalizedFlattening_cfii
  let Ured : MPOTensor d Dred := ofNormalizedFlattening Ared
  have hFlat : Ured.normalizedFlattening = Ared :=
    normalizedFlattening_ofNormalizedFlattening Ared
  have hRaw : MPSTensor.SameMPV₂Pos U.toMPSTensor Ured.toMPSTensor := by
    mpv_ext
    rw [← sqrt_smul_normalizedFlattening U,
      toMPSTensor_ofNormalizedFlattening, MPSTensor.mpv_smul,
      MPSTensor.mpv_smul, hSame N hN σ]
  have hMpo : ∀ N : ℕ, 0 < N → mpo Ured N = mpo U N := by
    intro N hN
    ext σ τ
    rw [← MPSTensor.mpv_toMPSTensor_pairConfig,
      ← MPSTensor.mpv_toMPSTensor_pairConfig]
    exact (hRaw N hN (fun n => finProdFinEquiv (σ n, τ n))).symm
  have hUred : Ured.IsMPU := by
    intro N hN
    rw [hMpo N (Nat.zero_lt_of_lt hN)]
    exact hU N hN
  exact ⟨Dred, hDred, Ured,
    mpuCanonicalFormIIOfNormalizedFlatteningEq hFlat hUred cfii hFull ρ
      hρpd hρdiag hρtrace hρfix,
    hDimLe, hMpo⟩

end MPOTensor
