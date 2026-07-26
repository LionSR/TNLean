/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.FinTupleEquiv
import TNLean.Channel.LocalizedKrausCPTP
import TNLean.MPS.MPDO.RetainedClass
import TNLean.MPS.MPDO.RFPViaTS
import TNLean.MPS.MPDO.SectorTrace

/-!
# Global action of the MPDO renormalization maps

The maps in Definition 4.1 of arXiv:1606.00608 act on one or two neighboring
physical sites. Tensoring them with the identity on the remaining sites gives
trace-preserving completely positive maps whose local closure identities extend
to a chain of any length. These are the channel identities used in the
argument establishing saturation of the area law in arXiv:1606.00608,
Appendix C, lines 1333--1341.

The required local-channel data-processing inequality is proved in
`TNLean.Entropy.MutualInformationDataProcessing`. The remaining steps in the
source argument are recorded in
`docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex`.

## Main definitions

* `MPOTensor.refineFirstSite`: apply the one-to-two map to the first site.
* `MPOTensor.coarsenFirstTwoSites`: apply the two-to-one map to the first two sites.

## Main results

* `MPOTensor.refineFirstSite_isKrausCPTP` and
  `MPOTensor.coarsenFirstTwoSites_isKrausCPTP`: the localized maps are channels.
* `MPOTensor.refineFirstSite_physCloseN` and
  `MPOTensor.coarsenFirstTwoSites_physCloseN`: the localized maps respectively
  insert and remove one tensor in every physical closure.
* `MPOTensor.refineFirstSite_mpo` and `MPOTensor.coarsenFirstTwoSites_mpo`:
  the localized maps respectively insert and remove one tensor in every periodic MPO.
* `MPOTensor.exists_global_renormalization_maps`: a renormalization fixed point
  supplies localized channels with the global physical-closure identities.
* `MPOTensor.trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS`: an MPDO
  in normalized BNT-refined horizontal form satisfying Definition 4.1 has
  nonzero trace at every positive chain length.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 and Appendix C, lines 1333--1341
-/

open scoped Matrix

namespace MPOTensor

variable {d D : ℕ}

/-! ### Localized renormalization maps -/

/-- Apply a one-to-two physical map to the first site and leave the remaining
`N` sites unchanged.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
noncomputable def refineFirstSite
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ :=
  Matrix.equivReindexMap (finAddTwoArrowEquiv (Fin d) N).symm ∘ₗ
    Matrix.tensorMapIdLM (δ := Fin N → Fin d) T ∘ₗ
      Matrix.equivReindexMap (finSuccArrowEquiv (Fin d) N)

/-- Apply a two-to-one physical map to the first two sites and leave the
remaining `N` sites unchanged.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
noncomputable def coarsenFirstTwoSites
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ :=
  Matrix.equivReindexMap (finSuccArrowEquiv (Fin d) N).symm ∘ₗ
    Matrix.tensorMapIdLM (δ := Fin N → Fin d) S ∘ₗ
      Matrix.equivReindexMap (finAddTwoArrowEquiv (Fin d) N)

/-- Localizing a one-to-two channel at the first site again gives a
trace-preserving completely positive map.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem refineFirstSite_isKrausCPTP
    {T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ}
    (hT : IsKrausCPTP T) (N : ℕ) :
    IsKrausCPTP (refineFirstSite T N) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (finSuccArrowEquiv (Fin d) N))
      (Matrix.tensorMapIdLM_isKrausCPTP hT))
    (Matrix.equivReindexMap_isKrausCPTP (finAddTwoArrowEquiv (Fin d) N).symm)

/-- Localizing a two-to-one channel at the first two sites again gives a
trace-preserving completely positive map.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem coarsenFirstTwoSites_isKrausCPTP
    {S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ}
    (hS : IsKrausCPTP S) (N : ℕ) :
    IsKrausCPTP (coarsenFirstTwoSites S N) := by
  exact isKrausCPTP_comp
    (isKrausCPTP_comp
      (Matrix.equivReindexMap_isKrausCPTP (finAddTwoArrowEquiv (Fin d) N))
      (Matrix.tensorMapIdLM_isKrausCPTP hS))
    (Matrix.equivReindexMap_isKrausCPTP (finSuccArrowEquiv (Fin d) N).symm)

/-! ### Action on physical closures -/

/-- The first-factor slice of a regrouped closure is the one-site closure with
the remaining word absorbed into the virtual boundary matrix. -/
private theorem firstSiteSlice_physCloseN (M : MPOTensor d D) (N : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u v : Fin N → Fin d) :
    Matrix.bipartiteSlice
        (Matrix.equivReindexMap (finSuccArrowEquiv (Fin d) N)
          (physCloseN M (N + 1) X)) u v =
      physClose1 M (evalWord M (List.ofFn u) (List.ofFn v) * X) := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, List.ofFn_succ,
    evalWord_cons, Matrix.mul_assoc]

/-- The first-factor slice of a regrouped closure is the two-site closure with
the remaining word absorbed into the virtual boundary matrix. -/
private theorem firstTwoSitesSlice_physCloseN (M : MPOTensor d D) (N : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u v : Fin N → Fin d) :
    Matrix.bipartiteSlice
        (Matrix.equivReindexMap (finAddTwoArrowEquiv (Fin d) N)
          (physCloseN M (N + 2) X)) u v =
      physClose2 M (evalWord M (List.ofFn u) (List.ofFn v) * X) := by
  ext i j
  simp [Matrix.equivReindexMap, Matrix.coe_reindexLinearEquiv,
    Matrix.reindex_apply, Matrix.submatrix_apply, List.ofFn_succ,
    evalWord_cons, Matrix.mul_assoc]

/-- If `T` sends every one-site physical closure to the corresponding two-site
closure, then its localization at the first site inserts one copy of the tensor
in a closure of arbitrary length.

This is the global channel identity used when `T` is applied to the first spin
of the first interval in the proof of saturation of the area law.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem refineFirstSite_physCloseN (M : MPOTensor d D)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : ∀ X, T (physClose1 M X) = physClose2 M X)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    refineFirstSite T N (physCloseN M (N + 1) X) =
      physCloseN M (N + 2) X := by
  ext σ τ
  change Matrix.tensorMapId T
      (Matrix.equivReindexMap (finSuccArrowEquiv (Fin d) N)
        (physCloseN M (N + 1) X))
      (finAddTwoArrowEquiv (Fin d) N σ) (finAddTwoArrowEquiv (Fin d) N τ) = _
  rw [Matrix.tensorMapId_apply]
  simp only [finAddTwoArrowEquiv_apply]
  rw [firstSiteSlice_physCloseN, hT]
  simp [List.ofFn_succ, evalWord_cons, Matrix.mul_assoc, Fin.tail_def]

/-- If `S` sends every two-site physical closure to the corresponding one-site
closure, then its localization at the first two sites removes one copy of the
tensor from a closure of arbitrary length.

This is the global channel identity used when `S` is applied to the first two
spins of the second interval in the proof of saturation of the area law.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem coarsenFirstTwoSites_physCloseN (M : MPOTensor d D)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : ∀ X, S (physClose2 M X) = physClose1 M X)
    (N : ℕ) (X : Matrix (Fin D) (Fin D) ℂ) :
    coarsenFirstTwoSites S N (physCloseN M (N + 2) X) =
      physCloseN M (N + 1) X := by
  ext σ τ
  change Matrix.tensorMapId S
      (Matrix.equivReindexMap (finAddTwoArrowEquiv (Fin d) N)
        (physCloseN M (N + 2) X))
      (finSuccArrowEquiv (Fin d) N σ) (finSuccArrowEquiv (Fin d) N τ) = _
  rw [Matrix.tensorMapId_apply]
  simp only [finSuccArrowEquiv_apply]
  rw [firstTwoSitesSlice_physCloseN, hS]
  simp [List.ofFn_succ, evalWord_cons, Matrix.mul_assoc, Fin.tail_def]

/-- The localized refinement map inserts one site in every periodic MPO
operator whenever the one-to-two closure identity of Definition 4.1 holds.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem refineFirstSite_mpo (M : MPOTensor d D)
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ)
    (hT : ∀ X, T (physClose1 M X) = physClose2 M X) (N : ℕ) :
    refineFirstSite T N (mpo M (N + 1)) = mpo M (N + 2) := by
  rw [← physCloseN_identity_eq_mpo M (N + 1),
    refineFirstSite_physCloseN M T hT N,
    physCloseN_identity_eq_mpo]

/-- The localized coarse-graining map removes one site from every periodic MPO
operator whenever the two-to-one closure identity of Definition 4.1 holds.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
theorem coarsenFirstTwoSites_mpo (M : MPOTensor d D)
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ)
    (hS : ∀ X, S (physClose2 M X) = physClose1 M X) (N : ℕ) :
    coarsenFirstTwoSites S N (mpo M (N + 2)) = mpo M (N + 1) := by
  rw [← physCloseN_identity_eq_mpo M (N + 2),
    coarsenFirstTwoSites_physCloseN M S hS N,
    physCloseN_identity_eq_mpo]

/-- A renormalization fixed point in the sense of Definition 4.1 has one pair
of trace-preserving completely positive maps whose localizations insert and
remove a tensor in physical closures of every length.

This is the global channel statement used to prove saturation of the area law
in arXiv:1606.00608, Appendix C. The parameter `N` counts the sites on which the
identity channel acts; even when `N = 0`, the input closure contains one or two
physical sites, so no empty-chain operator is involved.

Source: arXiv:1606.00608, Definition 4.1 and Appendix C,
lines 1333--1341. -/
theorem exists_global_renormalization_maps (M : MPOTensor d D)
    (h : IsRFPViaTS M) :
    ∃ (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin d) (Fin d) ℂ)
      (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
        Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ),
      IsKrausCPTP S ∧ IsKrausCPTP T ∧
      (∀ N X, coarsenFirstTwoSites S N (physCloseN M (N + 2) X) =
        physCloseN M (N + 1) X) ∧
      (∀ N X, refineFirstSite T N (physCloseN M (N + 1) X) =
        physCloseN M (N + 2) X) := by
  obtain ⟨S, T, hS, hT, hSclose, hTclose⟩ := h
  exact ⟨S, T, hS, hT, coarsenFirstTwoSites_physCloseN M S hSclose,
    refineFirstSite_physCloseN M T hTclose⟩

/-- An MPDO in normalized BNT-refined horizontal form satisfying Definition
4.1 has nonzero trace at every positive chain length.

This horizontal hypothesis is stronger than literal CPSV canonical form.

The BNT representation supplies one sufficiently long nonzero density
operator. Positivity makes its trace nonzero. Definition 4.1 makes the
physical-trace transfer idempotent, so the trace is the same at every positive
length.

Source: arXiv:1606.00608, canonical-form standing assumptions at lines
623--628 and 849--850, Definition 4.1 at lines 657--660, and Proposition
`propsimple` at lines 1333--1340. -/
theorem trace_mpo_ne_zero_of_isHorizontalCF_isMPDO_isRFPViaTS
    (M : MPOTensor d D) (hHorizontal : IsHorizontalCF M) (hMPDO : IsMPDO M)
    (hRFP : IsRFPViaTS M) :
    ∀ N, 0 < N → Matrix.trace (mpo M N) ≠ 0 := by
  have hCorner : ∃ v, (1 : Matrix (Fin d) (Fin d) ℂ) * verticalTensor M v * 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hHorizontal.verticalTensor_ne_zero M
    funext v
    simpa using h v
  obtain ⟨L, hCompression⟩ :=
    hHorizontal.exists_sectorCompression_ne_zero_of_corner M 1 hCorner
  have hMpo : mpo M (L + 1) ≠ 0 := by
    simpa [sectorCompression_def] using hCompression
  have hSeedTrace : Matrix.trace (mpo M (L + 1)) ≠ 0 := by
    intro hTrace
    exact hMpo
      ((Matrix.PosSemidef.trace_eq_zero_iff (hMPDO (L + 1) (by omega))).mp hTrace)
  have hLoopIdempotent : IsIdempotentElem (verticalLoop M) := by
    rw [isIdempotentElem_iff, verticalLoop_eq_physTraceTransfer]
    exact physTraceTransfer_sq_of_isRFPViaTS M hRFP
  intro N hN
  rw [trace_mpo_eq_trace_verticalLoop_pow, hLoopIdempotent.pow_eq hN.ne']
  rw [trace_mpo_eq_trace_verticalLoop_pow,
    hLoopIdempotent.pow_eq (Nat.succ_ne_zero L)] at hSeedTrace
  exact hSeedTrace

end MPOTensor
