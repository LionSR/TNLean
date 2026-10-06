/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.ParentHamiltonian.ResidualWindowLeftSectorSum
import TNLean.MPS.ParentHamiltonian.ResidualWindowRightGroundSpace
/-!
# Original ground-space identification for the aligned left residual window

Physical blocking and concatenation identify the left window of the blocked
original tensor with the original prefix boundary map. If the blocked ground
space is the joint span of sector ground spaces, applying this identity
independently at each tail configuration identifies the joint sector window
with the original left-window ground space.

An isometric resolution of the virtual identity and letterwise intertwining
derive the required sector presentation. No primitivity, normalization,
injectivity, or restriction on the lengths is imposed. The isometry condition
ensures that each sector's full square-boundary space is retained faithfully.
These are exact finite-dimensional identities, not projection-defect estimates.

Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`,
lines 434--451; Nachtergaele, arXiv:cond-mat/9410110, Section 3,
equations (3.10)--(3.15), and Lemma `commutation` (ii), lines 2458--2465.
-/

open scoped Matrix InnerProductSpace Matrix.Norms.Frobenius ComplexOrder
namespace MPSTensor
variable {d D L : ℕ}
/-- The blocked original left window equals the reindexed original prefix boundary map.
This includes zero blocking and zero interval lengths. Source: DCCSP17,
arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem residualWindowLeftMapES_blockTensor_eq_reindex_leftBoundaryMapES
    (A : MPSTensor d D) (K M r : ℕ) :
    residualWindowLeftMapES (blockTensor A L) K M r =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
        (residualWindowConfigEquiv d L K M r).symm).toContinuousLinearMap.comp
          (leftBoundaryMapES A ((K + M) * L) r) := by
  ext x ⟨u, v, τ⟩
  change Matrix.trace ((Kraus.evalWord (blockTensor A L) (List.ofFn u) *
    Kraus.evalWord (blockTensor A L) (List.ofFn v)) * boundaryFamilyEquiv (Cfg d r) x τ) =
      leftBoundaryMap A ((K + M) * L) r (boundaryFamilyEquiv (Cfg d r) x)
        (Fin.append (blockedConfigEquiv d (K + M) L (Fin.append u v)) τ)
  rw [leftBoundaryMap_append, groundSpaceMap_apply, ← Kraus.evalWord_append,
    ← List.ofFn_fin_append, evalWord_blockTensor, ← ofFn_blockedConfigEquiv]

/-- An exact blocked-sector ground-space presentation identifies the joint aligned left window
with the original prefix boundary range in the common physical coordinates.
No primitivity or normalization is required. Source context: Nachtergaele,
arXiv:cond-mat/9410110, equations (3.10)--(3.15) and Lemma `commutation` (ii). -/
theorem iSup_range_residualWindowLeftMapES_eq_of_groundSpaceES_eq_iSup
    {ι : Type*} {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (K M r : ℕ)
    (hGS : groundSpaceES (blockTensor A L) (K + M) =
      ⨆ j, groundSpaceES (B j) (K + M)) :
    (⨆ j, (residualWindowLeftMapES (B j) K M r).range) =
      ((leftBoundaryMapES A ((K + M) * L) r).range).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualWindowConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  rw [← LinearMap.range_comp (leftBoundaryMapES A ((K + M) * L) r).toLinearMap
    (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (residualWindowConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap]
  change (⨆ j, (residualWindowLeftMapES (B j) K M r).range) =
    ((LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
      (residualWindowConfigEquiv d L K M r).symm).toContinuousLinearMap.comp
        (leftBoundaryMapES A ((K + M) * L) r)).range
  rw [← residualWindowLeftMapES_blockTensor_eq_reindex_leftBoundaryMapES A K M r]
  simp only [residualWindowLeftMapES_eq_fiberwise, ContinuousLinearMap.toLinearMap_comp,
    LinearMap.range_comp, ← Submodule.map_iSup]
  congr 1
  rw [EuclideanSpace.iSup_range_fiberwiseMap_eq]
  ext x
  simp only [EuclideanSpace.mem_range_fiberwiseMap_iff, Submodule.range_starProjection,
    range_groundSpaceMapES, hGS]

/-- An isometric virtual resolution and blocked letter intertwining derive the original
left-window range as the joint range of the aligned sector windows. All lengths may be zero.
Source: DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451;
Nachtergaele, arXiv:cond-mat/9410110, equations (3.10)--(3.15). -/
theorem iSup_range_residualWindowLeftMapES_eq_reindex_leftBoundaryMapES
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i) (K M r : ℕ) :
    (⨆ j, (residualWindowLeftMapES (B j) K M r).range) =
      ((leftBoundaryMapES A ((K + M) * L) r).range).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualWindowConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  exact iSup_range_residualWindowLeftMapES_eq_of_groundSpaceES_eq_iSup A B K M r
    (groundSpaceES_eq_iSup_of_isometric_sector_resolution
      (blockTensor A L) B V hV hSum hInt (K + M))

/-- The joint left-window range in the physical cover of length `K * L + M * L + r`.
The configuration isometry agrees exactly with that used by the right and full windows.
All virtual hypotheses are the isometric sector resolution, and all lengths may be zero.
Source: Nachtergaele, arXiv:cond-mat/9410110, equation (3.15) and Lemma `commutation` (ii);
DCCSP17, arXiv:1708.00029, Lemma `lem:blocking-arbitrary`, lines 434--451. -/
theorem iSup_range_residualWindowLeftMapES_eq_reindex_cover_leftBoundaryMapES
    {ι : Type*} [Fintype ι] {dim : ι → ℕ}
    (A : MPSTensor d D) (B : ∀ j, MPSTensor (blockPhysDim d L) (dim j))
    (V : ∀ j, Matrix (Fin D) (Fin (dim j)) ℂ)
    (hV : ∀ j, (V j)ᴴ * V j = 1) (hSum : ∑ j, V j * (V j)ᴴ = 1)
    (hInt : ∀ j i, blockTensor A L i * V j = V j * B j i) (K M r : ℕ) :
    (⨆ j, (residualWindowLeftMapES (B j) K M r).range) =
      ((leftBoundaryMapES A (K * L + M * L) r).range).map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (residualCoverConfigEquiv d L K M r).symm).toLinearEquiv.toLinearMap := by
  have hCast {n n' : ℕ} (h : n = n')
      (e : Cfg (blockPhysDim d L) K × (Cfg (blockPhysDim d L) M × Cfg d r) ≃
        Cfg d (n + r)) :
      (leftBoundaryMapES A n r).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e.symm).toLinearEquiv.toLinearMap =
      (leftBoundaryMapES A n' r).range.map
        (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
          (e.trans (Equiv.arrowCongr (finCongr (congrArg (fun n => n + r) h))
            (Equiv.refl (Fin d)))).symm).toLinearEquiv.toLinearMap := by
    subst n'
    simp only [finCongr_refl, Equiv.arrowCongr_refl, Equiv.trans_refl]
  exact (iSup_range_residualWindowLeftMapES_eq_reindex_leftBoundaryMapES
    A B V hV hSum hInt K M r).trans
      (hCast (by rw [Nat.add_mul]) (residualWindowConfigEquiv d L K M r))

end MPSTensor
