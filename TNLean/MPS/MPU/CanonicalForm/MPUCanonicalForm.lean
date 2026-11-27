/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.SimpleMPU.FullSupport
import TNLean.MPS.CanonicalForm.NormalBlocks.ProjectorClosureSpectral
import TNLean.MPS.CanonicalForm.RetainedBlockReconstruction
import TNLean.MPS.CanonicalForm.Definitions
import TNLean.MPS.MPU.CanonicalForm.VirtualSandwich
import TNLean.MPS.Operator.Periodic.BondSimilarity
import TNLean.MPS.Tensor.Gauge.TPGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.NormalTensorGauge
import TNLean.MPS.CanonicalForm.NormalBlocks.IrreducibleDecomposition

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
* `MPOTensor.exists_canonicalFormII_positiveGauge`,
  `MPOTensor.IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm`: positive gauges and
  canonical representatives of normal MPUs.

## Canonical form from canonical form II

An MPU tensor in canonical form II is in canonical form. Canonical form II
writes the normalized flattening `d^{-1/2} U` as a weighted retained-block
reconstruction with normal blocks; a normal block is irreducible and has
transfer spectral radius one, so the same blocks, with weights multiplied by
`d^{1/2}`, give canonical-form data for the flattening of `U` itself.

### Main results

* `MPOTensor.IsMPUCanonicalFormII.isMPUCanonicalForm`: canonical form II implies
  canonical form.

### References

* Cirac--Perez-Garcia--Schuch--Verstraete, arXiv:1703.09188, canonical form,
  lines 259--267, and canonical form II, lines 269--281 and 344--356.
-/

section MPUCanonicalForm

section

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
        (Kraus.transferMap (ι := Fin d) (n := Fin D) A)) = 1

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
    exact isIrreducibleFamily_smul (data.weights_ne_zero k)
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

end

section

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

namespace IsMPUCanonicalFormII

/-- The retained-block data of canonical form II are canonical-form data for the
normalized flattening: normal blocks are irreducible with transfer spectral radius
one, and the retained blocks fill the bond space.

Source: arXiv:1703.09188, lines 259--267 and 269--281. -/
noncomputable def normalizedFlatteningCanonicalFormData {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) :
    MPSTensor.MPUCanonicalFormData U.normalizedFlattening where
  toRetainedBlockReconstructionData :=
    hU.cfii.toCPSVCanonicalFormData.toRetainedBlockReconstructionData
  blocks_canonical k :=
    ⟨(hU.cfii.blocks_normal k).no_invariant_proj,
      (hU.cfii.blocks_normal k).spectral_radius_one⟩
  total_dim_eq := hU.fullSupport_eq

/-- An MPU tensor in canonical form II is in canonical form: the normal blocks of
the normalized flattening `d^{-1/2} U`, with weights multiplied by `d^{1/2}`,
reconstruct the flattening of `U`.

Source: arXiv:1703.09188, canonical form, lines 259--267, and canonical form II,
lines 269--281 and 344--356. -/
theorem isMPUCanonicalForm [NeZero d] {U : MPOTensor d D}
    (hU : IsMPUCanonicalFormII U) : MPSTensor.IsMPUCanonicalForm U.toMPSTensor := by
  have hc : (Real.sqrt d : ℂ) ≠ 0 := by
    have hd : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
    exact_mod_cast (Real.sqrt_pos.mpr hd).ne'
  have hU' : (fun i => (Real.sqrt d : ℂ) • U.normalizedFlattening i) = U.toMPSTensor := by
    funext i
    simp only [normalizedFlattening, smul_smul, mul_inv_cancel₀ hc, one_smul]
  rw [← hU']
  exact ⟨hU.normalizedFlatteningCanonicalFormData.smul _ hc⟩

end IsMPUCanonicalFormII

end MPOTensor

end

end MPUCanonicalForm

section PositiveCanonicalGauge

/-!
## Positive gauges and canonical representatives of normal MPUs

A positive definite left fixed point determines a trace-preserving bond gauge.
Unitary diagonalization of a right fixed point then gives canonical form II
without changing the bond dimension or the periodic operators.

Source: arXiv:1703.09188, canonical form II, lines 269–281, and the
canonical-gauge step in Proposition IV.5, lines 798–804.

### Canonical form up to similarity

An MPU tensor in canonical form is similar, by one invertible bond matrix, to an MPU tensor in
canonical form II. The source passes to canonical form II "without loss of generality" by a gauge
transformation (arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356); this file
states that gauge as a lemma (the chapter's Lemma "Canonical form up to similarity").

The normalized tensor `d^{-1/2} U` is normal (Proposition `prop:normal-tensor`). A positive
definite fixed point `σ` of the dual transfer map gives the left-canonical gauge
`σ^{1/2} A σ^{-1/2}`, and a unitary `V` diagonalizing the fixed point of the gauged transfer map
then gives canonical form II with one block filling the bond space. The similarity is
`X = V^† σ^{1/2}`.

#### Main results

* `MPOTensor.IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm` — an MPU tensor in
  canonical form is `X⁻¹ U' X` for an invertible `X` and an MPU tensor `U'` in canonical
  form II.
-/

section

open scoped Matrix BigOperators ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- The positive square-root bond gauge preserves every periodic operator.
Source: CPSV17, Proposition IV.5, lines 798–804. -/
private theorem positive_gauge_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (N : ℕ) :
    MPOTensor.mpo (fun ij ↦ CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) N =
      MPOTensor.mpo U N := by
  exact (MPOTensor.mpo_eq_of_conj
    (Matrix.mul_nonsing_inv _ hL.isUnit_det_cfc_sqrt)
    (Matrix.nonsing_inv_mul _ hL.isUnit_det_cfc_sqrt) (fun _ _ ↦ rfl) N).symm

/-- Normalized flattening commutes with conjugation of every letter by fixed
bond matrices. -/
private theorem normalizedFlattening_conj {d D : ℕ}
    (U : MPOTensor d D) (X Y : Matrix (Fin D) (Fin D) ℂ) :
    MPOTensor.normalizedFlattening (fun ij ↦ X * U ij * Y : MPOTensor d D) =
      fun ij ↦ X * U.normalizedFlattening ij * Y := by
  funext ij
  simp only [MPOTensor.normalizedFlattening, MPOTensor.toMPSTensor,
    Matrix.mul_smul, Matrix.smul_mul]

/-- Unitary bond conjugation preserves every periodic operator. -/
private theorem unitary_conj_mpo_eq {d D : ℕ}
    (U : MPOTensor d D) (V : Matrix.unitaryGroup (Fin D) ℂ) (N : ℕ) :
    MPOTensor.mpo
        (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * U ij *
          (V : Matrix (Fin D) (Fin D) ℂ)) N = MPOTensor.mpo U N := by
  exact (MPOTensor.mpo_eq_of_conj
    (by simpa only [Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self V)
    (by simpa only [Matrix.star_eq_conjTranspose] using Unitary.mul_star_self_of_mem V.prop)
    (fun _ _ ↦ rfl) N).symm

/-- A normal left-canonical MPU with a normalized diagonal positive fixed point
has full-support canonical-form-II data in its given coordinates.
Source: CPSV17, canonical form II, lines 269–281. -/
private noncomputable def canonicalFormII_of_normal_leftCanonical
    (U : MPOTensor d D) (hU : U.IsMPU)
    (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (hLeft : MPTensor.IsLeftCanonical U.normalizedFlattening)
    (ρ : Matrix (Fin D) (Fin D) ℂ) (hρpd : ρ.PosDef) (hρdiag : ρ.IsDiag)
    (hρtrace : Matrix.trace ρ = 1)
    (hρfix : Kraus.transferMap U.normalizedFlattening ρ = ρ) :
    MPOTensor.IsMPUCanonicalFormII U := by
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  refine {
    isMPU := hU
    cfii := MPSTensor.CPSVCanonicalFormIIData.ofNormalLeftCanonical
      hNormal hLeft ρ hρpd hρdiag hρfix
    fullSupport_eq := ?_
    ρ := ρ
    ρ_posDef := hρpd
    ρ_isDiag := hρdiag
    ρ_trace := hρtrace
    ρ_fixed := hρfix }
  change (∑ _ : Fin 1, D) = D
  simp

/-- Spectral normality is preserved by unitary bond conjugation. -/
private theorem unitary_conj_normal {r D : ℕ} (A : MPSTensor r D)
    (hA : MPSTensor.IsNormalTensor A) (V : Matrix.unitaryGroup (Fin D) ℂ) :
    MPSTensor.IsNormalTensor
      (fun i ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
        (V : Matrix (Fin D) (Fin D) ℂ)) := by
  apply hA.of_gaugeEquiv
  exact (show MPTensor.GaugeEquiv A
    (fun i ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i *
      (V : Matrix (Fin D) (Fin D) ℂ)) from
    ⟨(MPSTensor.unitaryGL V)⁻¹, fun i ↦ by simp [MPSTensor.unitaryGL]⟩).symm

/-- Unitary diagonalization after the positive square-root gauge.

Source: arXiv:1703.09188, canonical form II, lines 269–281, and the
canonical-gauge step of Proposition IV.5, lines 798–804. -/
private theorem positive_gauge_exists_diagonal_fixedPoint
    (U : MPOTensor d D) (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (hfix : Kraus.mapLM (fun i ↦ (U.normalizedFlattening i)ᴴ) L = L) :
    let A := Kraus.tpGauge U.normalizedFlattening L
    ∃ (V : Matrix.unitaryGroup (Fin D) ℂ) (ρ : Matrix (Fin D) (Fin D) ℂ),
      let B : MPSTensor (d * d) D := fun i ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A i * (V : Matrix (Fin D) (Fin D) ℂ)
      MPTensor.SameMPV₂ A B ∧ ρ.PosDef ∧ ρ.IsDiag ∧ Matrix.trace ρ = 1 ∧
        MPTensor.IsLeftCanonical B ∧ Kraus.transferMap B ρ = ρ := by
  have hNormalTP : MPSTensor.IsNormalTensor (Kraus.tpGauge U.normalizedFlattening L) :=
    hNormal.of_gaugeEquiv (MPSTensor.gaugeEquiv_tpGauge U.normalizedFlattening L hL).symm
  obtain ⟨V, Λ, hSame, hΛ, hdiag, hTP, hΛfix⟩ :=
    MPSTensor.exists_CFII_data_of_TP_of_isIrreducibleFamily _
      (Kraus.tpGauge_isTP_of_map_conjTranspose_fixedPoint _ L hL hfix)
      hNormalTP.no_invariant_proj (Nat.pos_of_ne_zero hNormal.bondDim_ne_zero)
  let : NeZero D := ⟨hNormal.bondDim_ne_zero⟩
  have htrace : 0 < Matrix.trace Λ := hΛ.trace_pos
  refine ⟨V, (Matrix.trace Λ)⁻¹ • Λ, hSame,
    hΛ.smul (RCLike.inv_pos_of_pos htrace), hdiag.smul _, ?_, hTP, ?_⟩
  · simp only [Matrix.trace_smul, smul_eq_mul, inv_mul_cancel₀ (ne_of_gt htrace)]
  · simp only [map_smul, hΛfix]

/-- The positive square-root gauge and unitary diagonalization preserve
both source ranks. Source: CPSV17, Proposition IV.5, lines 797–804. -/
private theorem source_ranks_canonical_gauge {d D : ℕ}
    (W : MPOTensor d D) (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (V : Matrix.unitaryGroup (Fin D) ℂ) :
    let B : MPOTensor d D := fun ij ↦
      (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * W ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)
    MPOTensor.rightRank B = MPOTensor.rightRank W ∧
      MPOTensor.leftRank B = MPOTensor.leftRank W := by
  have hS : IsUnit (CFC.sqrt L) := (Matrix.isUnit_iff_isUnit_det _).2 hL.isUnit_det_cfc_sqrt
  have hSi : IsUnit ((CFC.sqrt L)⁻¹) :=
    (Matrix.isUnit_iff_isUnit_det _).2 hL.isUnit_det_inv_sqrt
  have hV : IsUnit (V : Matrix (Fin D) (Fin D) ℂ) := Unitary.isUnit_coe
  have hVs : IsUnit ((V : Matrix (Fin D) (Fin D) ℂ)ᴴ) := hV.star
  exact ⟨(MPOTensor.rightRank_virtualSandwich _
    (MPOTensor.virtualSandwich (CFC.sqrt L) W (CFC.sqrt L)⁻¹) _ hVs hV).trans
      (MPOTensor.rightRank_virtualSandwich _ W _ hS hSi),
    (MPOTensor.leftRank_virtualSandwich _
      (MPOTensor.virtualSandwich (CFC.sqrt L) W (CFC.sqrt L)⁻¹) _ hVs hV).trans
      (MPOTensor.leftRank_virtualSandwich _ W _ hS hSi)⟩

/-- The positive square-root gauge followed by unitary diagonalization gives
a full-support MPU canonical-form-II representative with the same periodic
operators and both source ranks unchanged.
This construction assumes normality and a positive definite adjoint fixed point.
It is the canonical-gauge step of arXiv:1703.09188, Proposition IV.5,
lines 798–804, with canonical form II as in lines 269–281. -/
theorem exists_canonicalFormII_positiveGauge
    (U : MPOTensor d D) (hU : U.IsMPU)
    (hNormal : MPSTensor.IsNormalTensor U.normalizedFlattening)
    (L : Matrix (Fin D) (Fin D) ℂ) (hL : L.PosDef)
    (hfix : Kraus.mapLM (fun i ↦ (U.normalizedFlattening i)ᴴ) L = L) :
    ∃ V : Matrix.unitaryGroup (Fin D) ℂ,
      let B : MPOTensor d D := fun ij ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
          (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)
      Nonempty (MPOTensor.IsMPUCanonicalFormII B) ∧
        (∀ N, MPOTensor.mpo B N = MPOTensor.mpo U N) ∧
        MPOTensor.rightRank B = MPOTensor.rightRank U ∧
        MPOTensor.leftRank B = MPOTensor.leftRank U := by
  obtain ⟨V, ρ, hSame, hρ, hdiag, hρtr, hLeft, hfix⟩ :=
    positive_gauge_exists_diagonal_fixedPoint U hNormal L hL hfix
  have hnorm : MPOTensor.normalizedFlattening
      (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ) :
          MPOTensor d D) =
      fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        Kraus.tpGauge U.normalizedFlattening L ij * (V : Matrix (Fin D) (Fin D) ℂ) :=
    (normalizedFlattening_conj _ _ _).trans
      (congrArg (fun A : MPSTensor (d * d) D ↦ fun ij ↦
        (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * A ij * (V : Matrix (Fin D) (Fin D) ℂ))
        (normalizedFlattening_conj U (CFC.sqrt L) (CFC.sqrt L)⁻¹))
  have hEq (N : ℕ) : MPOTensor.mpo
      (fun ij ↦ (V : Matrix (Fin D) (Fin D) ℂ)ᴴ *
        (CFC.sqrt L * U ij * (CFC.sqrt L)⁻¹) * (V : Matrix (Fin D) (Fin D) ℂ)) N =
      MPOTensor.mpo U N :=
    (unitary_conj_mpo_eq _ V N).trans (positive_gauge_mpo_eq U L hL N)
  exact ⟨V, ⟨canonicalFormII_of_normal_leftCanonical _
    (fun N hN ↦ (hEq N).symm ▸ hU N hN)
    (hnorm.symm ▸ unitary_conj_normal _
      (hNormal.of_gaugeEquiv (MPSTensor.gaugeEquiv_tpGauge U.normalizedFlattening L hL).symm)
      V)
    (hnorm.symm ▸ hLeft) ρ hρ hdiag hρtr (hnorm.symm ▸ hfix)⟩,
    hEq, source_ranks_canonical_gauge U L hL V⟩

end MPOTensor

end

section

open scoped Matrix ComplexOrder MatrixOrder

namespace MPOTensor

variable {d D : ℕ}

/-- **Canonical form up to similarity.** An MPU tensor `U` in canonical form is similar to an MPU
tensor in canonical form II: there is an invertible bond matrix `X` such that `X U X⁻¹` is in
canonical form II. The similar tensor generates the same periodic operators as `U`.

Source: arXiv:1703.09188, `Papers/1703.09188/paper_v2.tex`, lines 294 and 356 (the gauge to
canonical form II taken without loss of generality); the chapter's Lemma "Canonical form up to
similarity". The proof follows the left-canonical gauge `σ^{1/2} A σ^{-1/2}` of the normal tensor
`A = d^{-1/2} U` by a unitary diagonalization of its fixed point. -/
theorem IsMPU.exists_gauge_isMPUCanonicalFormII_of_isMPUCanonicalForm [NeZero d] [NeZero D]
    {U : MPOTensor d D} (hU : IsMPU U) (hcf : MPSTensor.IsMPUCanonicalForm U.toMPSTensor) :
    ∃ X : GL (Fin D) ℂ, Nonempty (IsMPUCanonicalFormII (virtualSandwich
      (X : Matrix (Fin D) (Fin D) ℂ) U ((X⁻¹ : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ))) := by
  have hNormal := hU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm hcf
  obtain ⟨σ, hσ, hσfix, -⟩ := hNormal.exists_tpGauge
  obtain ⟨V, hV, -⟩ := exists_canonicalFormII_positiveGauge U hU hNormal σ hσ hσfix
  let S : GL (Fin D) ℂ := Matrix.nonsingInvUnit (CFC.sqrt σ) hσ.isUnit_det_cfc_sqrt
  have hX : (((MPSTensor.unitaryGL V)⁻¹ * S : GL (Fin D) ℂ) : Matrix (Fin D) (Fin D) ℂ) =
      (V : Matrix (Fin D) (Fin D) ℂ)ᴴ * CFC.sqrt σ := rfl
  have hXinv : ((((MPSTensor.unitaryGL V)⁻¹ * S)⁻¹ : GL (Fin D) ℂ) :
      Matrix (Fin D) (Fin D) ℂ) = (CFC.sqrt σ)⁻¹ * (V : Matrix (Fin D) (Fin D) ℂ) := rfl
  refine ⟨(MPSTensor.unitaryGL V)⁻¹ * S, ?_⟩
  rw [hX, hXinv]
  convert hV using 3
  funext ij
  simp only [virtualSandwich, Matrix.mul_assoc]

end MPOTensor

end

end PositiveCanonicalGauge
