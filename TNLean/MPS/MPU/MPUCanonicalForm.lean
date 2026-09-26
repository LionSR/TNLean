/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.CanonicalForm.ProjectorClosureSpectral
import TNLean.MPS.CanonicalForm.RetainedBlockReconstruction

/-!
# Canonical form for matrix product unitaries

This file records the canonical form used by arXiv:1703.09188, lines 259--267.
Unlike the stronger CPSV normal-block canonical form, it permits irreducible
periodic blocks. The retained blocks occupy the entire ambient bond space.

**Local fix (nonzero canonical weights and full support):** Every listed block
has nonzero weight, and the retained dimensions sum to the ambient bond
dimension. See `docs/paper-gaps/mpu_canonical_form_nonzero_weights.tex` and
`docs/paper-gaps/mpu_canonical_form_full_support.tex`.

## Main definitions

* `MPSTensor.IsMPUCanonicalBlock`: irreducibility and transfer spectral radius one.
* `MPSTensor.MPUCanonicalFormData`: a weighted retained-block reconstruction.
* `MPSTensor.IsMPUCanonicalForm`: existence of such reconstruction data.
-/

open scoped Matrix BigOperators Matrix.Norms.Operator ComplexOrder MatrixOrder Kraus

namespace MPSTensor

variable {d D : ℕ}

/-- A canonical block for an MPU endpoint is irreducible and has transfer
spectral radius one. Peripheral eigenvalues other than one are allowed.

Source: arXiv:1703.09188, lines 259--267. -/
structure IsMPUCanonicalBlock (A : MPSTensor d D) : Prop where
  /-- The block admits no nontrivial invariant orthogonal projection. -/
  irreducible : Kraus.IsIrreducibleFamily A
  /-- The block transfer map has spectral radius one. -/
  spectral_radius_one :
    spectralRadius ℂ
      ((Module.End.toContinuousLinearMap (Matrix (Fin D) (Fin D) ℂ))
        (Kraus.transferMap (d := d) (D := D) A)) = 1

/-- Witness data for the MPU canonical form, using irreducible
spectral-radius-one blocks and an exact coisometric retained-block
reconstruction in the ambient bond space.

Source: arXiv:1703.09188, lines 259--267. -/
structure MPUCanonicalFormData (A : MPSTensor d D)
    extends RetainedBlockReconstructionData A where
  /-- Every retained block is irreducible and has transfer spectral radius one. -/
  blocks_canonical : ∀ k, IsMPUCanonicalBlock (blocks k)
  /-- The retained blocks fill the ambient bond space.

  Source: arXiv:1703.09188, canonical form, lines 259--265. -/
  total_dim_eq : ∑ k : Fin r, dim k = D

/-- An MPS tensor is in MPU canonical form when it has an exact retained-block
reconstruction whose blocks are irreducible and transfer-normalized.

Source: arXiv:1703.09188, lines 259--267. -/
def IsMPUCanonicalForm (A : MPSTensor d D) : Prop :=
  Nonempty (MPUCanonicalFormData A)

namespace MPUCanonicalFormData

variable {A : MPSTensor d D}

/-- A nonzero scalar multiplies all canonical weights and leaves the blocks
and their spectral normalization unchanged.

Source: arXiv:1703.09188, canonical-form definition, lines 259--265. -/
noncomputable def smul (data : MPUCanonicalFormData A) (c : ℂ) (hc : c ≠ 0) :
    MPUCanonicalFormData (fun i => c • A i) where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun k => c * data.weights k
  weights_ne_zero := fun k => mul_ne_zero hc (data.weights_ne_zero k)
  blocks := data.blocks
  blocks_canonical := data.blocks_canonical
  total_dim_eq := data.total_dim_eq
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro i
    rw [data.reconstruct i,
      RetainedBlockReconstructionData.toTensorFromBlocks_mul_weights]
    simp [Matrix.smul_mul, Matrix.mul_smul]

/-- Each weighted canonical block of a tensor with the MPU shifted trace
identities is normal.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. -/
private theorem weightedBlock_normal (data : MPUCanonicalFormData A)
    (htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1)
    (k : Fin data.r) :
    IsNormalTensor (fun i => data.weights k • data.blocks k i) := by
  let B : MPSTensor d (data.dim k) := fun i => data.weights k • data.blocks k i
  let _ : NeZero (data.dim k) := NeZero.of_pos (data.dim_pos k)
  have hBlockNonzero : ∃ i, data.blocks k i ≠ 0 := by
    by_contra h
    push Not at h
    have hzero : data.blocks k = 0 := by
      funext i
      exact h i
    have hrad := (data.blocks_canonical k).spectral_radius_one
    rw [hzero] at hrad
    have hmap : Kraus.transferMap (0 : MPSTensor d (data.dim k)) = 0 := by
      ext X a b
      simp
    rw [hmap, map_zero, spectrum.spectralRadius_zero] at hrad
    exact zero_ne_one hrad
  have hBnonzero : ∃ i, B i ≠ 0 := by
    obtain ⟨i, hi⟩ := hBlockNonzero
    exact ⟨i, smul_ne_zero (data.weights_ne_zero k) hi⟩
  have hIrr : Kraus.IsIrreducibleFamily B := by
    exact isIrreducibleTensor_smul (data.weights_ne_zero k)
      (data.blocks k) (data.blocks_canonical k).irreducible
  obtain ⟨ρ, radius, hρ, hRadius, hEigenvector⟩ :=
    exists_posDef_transferMap_eigenvector_of_irreducible B hIrr hBnonzero
  have hEigenvalue_eq_one : ∀ {μ : ℂ},
      Module.End.HasEigenvalue (Kraus.transferMap B) μ → μ ≠ 0 → μ = 1 := by
    intro μ hμ hμ0
    have hAmbient : Module.End.HasEigenvalue (Kraus.transferMap A) μ :=
      hasEigenvalue_transferMap_of_intertwine A B
        (data.toRetainedBlockReconstructionData.ambientBlockInclusion k)
        (data.toRetainedBlockReconstructionData.ambientBlockInclusion_conjTranspose_mul_self k)
        (data.toRetainedBlockReconstructionData.mul_ambientBlockInclusion k) hμ
    have hMatrix : Module.End.HasEigenvalue
        (transferMatrix (Kraus.transferMap A)).toLin' μ :=
      (transferMatrix_hasEigenvalue_iff (Kraus.transferMap A) μ).mp hAmbient
    have hSpectrum : μ ∈ spectrum ℂ (transferMatrix (Kraus.transferMap A)) := by
      simpa using Module.End.hasEigenvalue_iff_mem_spectrum.mp hMatrix
    exact Matrix.eq_one_of_mem_spectrum_of_forall_trace_pow_eq_one_of_one_lt
      (transferMatrix (Kraus.transferMap A)) htrace hSpectrum hμ0
  have hρne : ρ ≠ 0 := (Matrix.PosDef.isUnit hρ).ne_zero
  have hRadiusEigenvalue : Module.End.HasEigenvalue (Kraus.transferMap B) (radius : ℂ) :=
    hasEigenvalue_of_eigenvector_eq _ _ ρ hEigenvector hρne
  have hRadiusComplex : (radius : ℂ) = 1 :=
    hEigenvalue_eq_one hRadiusEigenvalue (by exact_mod_cast hRadius.ne')
  have hRadiusOne : radius = 1 := by exact_mod_cast hRadiusComplex
  have hNormal := isNormalTensor_invSqrt_smul_of_unique_peripheral
    B hIrr ρ radius hρ hRadius hEigenvector (fun μ hμ hNorm => by
      have hμ0 : μ ≠ 0 := by
        intro hzero
        subst μ
        simp only [norm_zero] at hNorm
        linarith
      rw [hRadiusOne]
      exact hEigenvalue_eq_one hμ hμ0)
  simpa [B, hRadiusOne] using hNormal

/-- The MPU block decomposition, after absorbing each nonzero weight into its
block, is also a CPSV decomposition whenever the shifted traces are one.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. -/
private noncomputable def toCPSVCanonicalFormData_of_shifted_trace
    (data : MPUCanonicalFormData A)
    (htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1) :
    CPSVCanonicalFormData A where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun _ => 1
  weights_ne_zero := fun _ => one_ne_zero
  blocks := fun k i => data.weights k • data.blocks k i
  blocks_normal := data.weightedBlock_normal htrace
  total_dim_le := le_of_eq data.total_dim_eq
  ambient_coisometry := data.ambient_coisometry
  coisometric := data.coisometric
  reconstruct := by
    intro i
    rw [data.reconstruct i]
    congr 1
    funext x y
    simp [toTensorFromBlocks]

/-- An MPU canonical-form decomposition with full support has one normal
ambient block when its shifted transfer traces equal one.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. -/
theorem isNormalTensor_of_shifted_transfer_trace (data : MPUCanonicalFormData A)
    (htrace : ∀ N : ℕ, 1 < N →
      Matrix.trace (transferMatrix (Kraus.transferMap A) ^ N) = 1) :
    IsNormalTensor A := by
  let cpsv := data.toCPSVCanonicalFormData_of_shifted_trace htrace
  have hr : cpsv.r = 1 := cpsv.r_eq_one_of_shifted_transfer_trace htrace
  have hfull : cpsv.HasFullSupport := data.total_dim_eq
  have hD : 0 < D := by
    rw [← data.total_dim_eq]
    apply Finset.sum_pos'
    · exact fun _ _ => Nat.zero_le _
    · have : 0 < data.r := by change data.r = 1 at hr; omega
      exact ⟨⟨0, this⟩, Finset.mem_univ _, data.dim_pos _⟩
  let _ : NeZero D := NeZero.of_pos hD
  obtain ⟨hrad, hprim⟩ :=
    spectralRadius_eq_one_and_isPrimitive_of_transferMatrix_shifted_trace
      (Kraus.transferMap A) htrace
  exact cpsv.isNormalTensor_of_r_eq_one_of_fullSupport hr hfull hrad hprim

end MPUCanonicalFormData

end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- The normalized tensor of an MPU in canonical form is normal.

The canonical-form predicate excludes zero weights and unused ambient bond
coordinates, as intended in the source argument.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isNormalTensor_normalizedFlattening_of_normalized_mpuCanonicalForm
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPSTensor.IsMPUCanonicalForm U.normalizedFlattening) :
    MPSTensor.IsNormalTensor U.normalizedFlattening := by
  let data := Classical.choice hcf
  exact data.isNormalTensor_of_shifted_transfer_trace
    (fun N hN => hU.trace_transferMatrix_normalizedFlattening_pow_eq_one hN)

/-- The normalized tensor of an MPU in canonical form is normal. The
canonical form is assumed for the original local tensor, as in the source;
normalization multiplies each nonzero block weight by $d^{-1/2}$.

Source: arXiv:1703.09188, Proposition `prop:normal-tensor`, lines 344--354. -/
theorem IsMPU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm
    [NeZero d] [NeZero D] {U : MPOTensor d D} (hU : IsMPU U)
    (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) :
    MPSTensor.IsNormalTensor U.normalizedFlattening := by
  have hd : (0 : ℝ) < d := by exact_mod_cast NeZero.pos d
  have hscale : ((Real.sqrt d : ℂ)⁻¹) ≠ 0 :=
    inv_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne')
  have hcfNormalized : MPSTensor.IsMPUCanonicalForm U.normalizedFlattening := by
    change Nonempty (MPSTensor.MPUCanonicalFormData
      (fun ij => ((Real.sqrt d : ℂ)⁻¹) • U.toMPSTensor ij))
    exact ⟨(Classical.choice hcf).smul _ hscale⟩
  exact hU.isNormalTensor_normalizedFlattening_of_normalized_mpuCanonicalForm
    hcfNormalized

end MPOTensor
