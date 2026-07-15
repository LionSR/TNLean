/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.LocalizedKrausCPTP
import TNLean.MPS.MPDO.RFPViaTS

/-!
# Global action of the MPDO renormalization maps

The maps in Definition 4.1 of arXiv:1606.00608 act on one or two neighboring
physical sites. This file tensors those maps with the identity on the remaining
sites and proves that their local closure identities extend to a chain of any
length. These are the channel identities used in the strong-area-law argument
of arXiv:1606.00608, Appendix C, lines 1333--1341.

The remaining local-channel data-processing theorem and the source standing
nonvanishing condition are recorded in
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

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Definition 4.1 and Appendix C, lines 1333--1341
-/

open scoped Matrix BigOperators

namespace MPOTensor

variable {d D : ℕ}

/-! ### Regrouping the first physical sites -/

/-- Separate the first physical index from the remaining `N` indices. -/
def firstSiteRestEquiv (d N : ℕ) :
    (Fin (N + 1) → Fin d) ≃ Fin d × (Fin N → Fin d) :=
  (Fin.consEquiv fun _ : Fin (N + 1) ↦ Fin d).symm

@[simp] theorem firstSiteRestEquiv_apply (d N : ℕ)
    (σ : Fin (N + 1) → Fin d) :
    firstSiteRestEquiv d N σ = (σ 0, Fin.tail σ) :=
  rfl

@[simp] theorem firstSiteRestEquiv_symm_apply (d N : ℕ)
    (p : Fin d × (Fin N → Fin d)) :
    (firstSiteRestEquiv d N).symm p = Fin.cons p.1 p.2 :=
  rfl

/-- Separate the first two physical indices from the remaining `N` indices. -/
def firstTwoSitesRestEquiv (d N : ℕ) :
    (Fin (N + 2) → Fin d) ≃ (Fin d × Fin d) × (Fin N → Fin d) :=
  (firstSiteRestEquiv d (N + 1)).trans
    ((Equiv.prodCongr (Equiv.refl (Fin d)) (firstSiteRestEquiv d N)).trans
      (Equiv.prodAssoc (Fin d) (Fin d) (Fin N → Fin d)).symm)

@[simp] theorem firstTwoSitesRestEquiv_apply (d N : ℕ)
    (σ : Fin (N + 2) → Fin d) :
    firstTwoSitesRestEquiv d N σ = ((σ 0, σ 1), Fin.tail (Fin.tail σ)) :=
  rfl

@[simp] theorem firstTwoSitesRestEquiv_symm_apply (d N : ℕ)
    (p : (Fin d × Fin d) × (Fin N → Fin d)) :
    (firstTwoSitesRestEquiv d N).symm p = Fin.cons p.1.1 (Fin.cons p.1.2 p.2) :=
  rfl

/-! ### Localized renormalization maps -/

/-- Apply a one-to-two physical map to the first site and leave the remaining
`N` sites unchanged.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
noncomputable def refineFirstSite
    (T : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ :=
  Matrix.equivReindexMap (firstTwoSitesRestEquiv d N).symm ∘ₗ
    Matrix.tensorMapIdLM (δ := Fin N → Fin d) T ∘ₗ
      Matrix.equivReindexMap (firstSiteRestEquiv d N)

/-- Apply a two-to-one physical map to the first two sites and leave the
remaining `N` sites unchanged.

Source: arXiv:1606.00608, Appendix C, lines 1337--1341. -/
noncomputable def coarsenFirstTwoSites
    (S : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin d) (Fin d) ℂ) (N : ℕ) :
    Matrix (Fin (N + 2) → Fin d) (Fin (N + 2) → Fin d) ℂ →ₗ[ℂ]
      Matrix (Fin (N + 1) → Fin d) (Fin (N + 1) → Fin d) ℂ :=
  Matrix.equivReindexMap (firstSiteRestEquiv d N).symm ∘ₗ
    Matrix.tensorMapIdLM (δ := Fin N → Fin d) S ∘ₗ
      Matrix.equivReindexMap (firstTwoSitesRestEquiv d N)

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
      (Matrix.equivReindexMap_isKrausCPTP (firstSiteRestEquiv d N))
      (Matrix.tensorMapIdLM_isKrausCPTP hT))
    (Matrix.equivReindexMap_isKrausCPTP (firstTwoSitesRestEquiv d N).symm)

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
      (Matrix.equivReindexMap_isKrausCPTP (firstTwoSitesRestEquiv d N))
      (Matrix.tensorMapIdLM_isKrausCPTP hS))
    (Matrix.equivReindexMap_isKrausCPTP (firstSiteRestEquiv d N).symm)

/-! ### Action on physical closures -/

/-- The first-factor slice of a regrouped closure is the one-site closure with
the remaining word absorbed into the virtual boundary matrix. -/
private theorem firstSiteSlice_physCloseN (M : MPOTensor d D) (N : ℕ)
    (X : Matrix (Fin D) (Fin D) ℂ) (u v : Fin N → Fin d) :
    Matrix.bipartiteSlice
        (Matrix.equivReindexMap (firstSiteRestEquiv d N)
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
        (Matrix.equivReindexMap (firstTwoSitesRestEquiv d N)
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
of the first interval in the proof of the strong area law.

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
      (Matrix.equivReindexMap (firstSiteRestEquiv d N)
        (physCloseN M (N + 1) X))
      (firstTwoSitesRestEquiv d N σ) (firstTwoSitesRestEquiv d N τ) = _
  rw [Matrix.tensorMapId_apply]
  simp only [firstTwoSitesRestEquiv_apply]
  rw [firstSiteSlice_physCloseN, hT]
  simp [List.ofFn_succ, evalWord_cons, Matrix.mul_assoc, Fin.tail_def]

/-- If `S` sends every two-site physical closure to the corresponding one-site
closure, then its localization at the first two sites removes one copy of the
tensor from a closure of arbitrary length.

This is the global channel identity used when `S` is applied to the first two
spins of the second interval in the proof of the strong area law.

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
      (Matrix.equivReindexMap (firstTwoSitesRestEquiv d N)
        (physCloseN M (N + 2) X))
      (firstSiteRestEquiv d N σ) (firstSiteRestEquiv d N τ) = _
  rw [Matrix.tensorMapId_apply]
  simp only [firstSiteRestEquiv_apply]
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

This is the global channel statement used in the proof of the strong area law
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

end MPOTensor
