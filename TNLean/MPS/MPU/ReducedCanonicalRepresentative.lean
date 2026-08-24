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
and 344--356.

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

/-- Every matrix product unitary has a positive-dimensional, normal,
full-support canonical-form-II representative of its normalized flattening.
The representative has no larger bond dimension and generates the same matrix
product vectors at every positive length.

The canonical-form convention in arXiv:1703.09188, lines 257--294 and 319--326,
replaces a tensor by one generating the same matrix product vectors. For a
matrix product unitary, lines 344--356 then use the shifted transfer traces to
obtain a normal representative in canonical form II. The dimension-bounded
irreducible reduction and canonical-form-II gauge are those of
arXiv:1606.00608, lines 195--255 and 1058--1077. This theorem combines those
steps; it is not a separately stated theorem of either paper. -/
theorem IsMPU.exists_reduced_normalizedFlattening_cfii
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : U.IsMPU) :
    ∃ (Dred : ℕ) (_hDred : 0 < Dred) (Ared : MPSTensor (d * d) Dred)
      (cfii : MPSTensor.CPSVCanonicalFormIIData Ared),
      Dred ≤ D ∧
      MPSTensor.SameMPV₂Pos U.normalizedFlattening Ared ∧
      MPSTensor.IsNormalTensor Ared ∧
      cfii.toCPSVCanonicalFormData.HasFullSupport := by
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
      Matrix.trace (transferMatrix (Kraus.transferMap Ared) ^ N) = 1 := by
    intro N hN
    calc
      Matrix.trace (transferMatrix (Kraus.transferMap Ared) ^ N) =
          MPSTensor.mpvOverlap Ared Ared N :=
        MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap Ared N
      _ = MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening N :=
        (MPSTensor.mpvOverlap_eq_of_pos_mpv_eq
          (fun {N} hN => hSame N hN) (fun {N} hN => hSame N hN)
          (Nat.zero_lt_of_lt hN)).symm
      _ = Matrix.trace
          (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) :=
        (MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap
          U.normalizedFlattening N).symm
      _ = 1 := hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
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
      Matrix.trace (transferMatrix (Kraus.transferMap B) ^ N) = 1 := by
    intro N hN
    calc
      Matrix.trace (transferMatrix (Kraus.transferMap B) ^ N) =
          MPSTensor.mpvOverlap B B N :=
        MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap B N
      _ = MPSTensor.mpvOverlap U.normalizedFlattening U.normalizedFlattening N :=
        (MPSTensor.mpvOverlap_eq_of_pos_mpv_eq
          (fun {N} hN => hSameB N hN) (fun {N} hN => hSameB N hN)
          (Nat.zero_lt_of_lt hN)).symm
      _ = Matrix.trace
          (transferMatrix (Kraus.transferMap U.normalizedFlattening) ^ N) :=
        (MPSTensor.trace_transferMatrix_transferMap_pow_eq_mpvOverlap
          U.normalizedFlattening N).symm
      _ = 1 := hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN
  have hFullB : dataB.toCPSVCanonicalFormData.HasFullSupport := by
    change (∑ k : Fin dataB.r, dataB.dim k) = Dred
    exact hTotalDim.trans hFull
  have hBlockCountB : dataB.r = 1 :=
    dataB.toCPSVCanonicalFormData.r_eq_one_of_shifted_transfer_trace hTraceB
  obtain ⟨hRadiusB, hPrimitiveB⟩ :=
    spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace
      (Kraus.transferMap B) hTraceB
  have hBNormal : MPSTensor.IsNormalTensor B :=
    dataB.toCPSVCanonicalFormData.isNormalTensor_of_r_eq_one_of_fullSupport
      hBlockCountB hFullB hRadiusB hPrimitiveB
  exact ⟨Dred, hDred, B, dataB, by simpa [Dred] using hDimLe,
    hSameB, hBNormal, hFullB⟩

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
shifted-transfer argument at lines 344--356. The dimension reduction and CFII
gauge follow arXiv:1606.00608, lines 195--255 and 1058--1077. This theorem does
not identify a virtual gauge between the original and reduced bond spaces,
whose dimensions may differ. -/
theorem IsMPU.exists_reduced_cfii_representative
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : U.IsMPU) :
    ∃ (Dred : ℕ) (_hDred : 0 < Dred) (Ured : MPOTensor d Dred)
      (cfii : MPSTensor.CPSVCanonicalFormIIData Ured.normalizedFlattening),
      Dred ≤ D ∧
      (∀ N : ℕ, 0 < N → mpo Ured N = mpo U N) ∧
      Ured.IsMPU ∧
      cfii.toCPSVCanonicalFormData.HasFullSupport := by
  obtain ⟨Dred, hDred, Ared, cfii, hDimLe, hSame, _hNormal, hFull⟩ :=
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
  refine ⟨Dred, hDred, Ured, ?_⟩
  rw [hFlat]
  exact ⟨cfii, hDimLe, hMpo, hUred, hFull⟩

end MPOTensor
