/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.CanonicalForm.NormalTensorGauge
import TNLean.MPS.MPU.CanonicalForm
import TNLean.MPS.MPDO.PhysicalAdjoint

/-!
# Reduced canonical-form-II data under physical adjunction

Physical adjunction of an MPO exchanges its two physical coordinates and conjugates every
coefficient. This file transports literal CPSV canonical-form-II data through that operation.
The construction preserves the reduced full-active-support condition and does not compare any
selected compact singular-value decompositions or source factors.

## Main definitions

* `MPSTensor.mapStar`: entrywise complex conjugation of an MPS tensor.
* `MPOTensor.physicalPairSwapEquiv`: exchange of the two flattened physical coordinates.
* `MPSTensor.CPSVCanonicalFormIIData.physicalAdjointNormalizedFlattening`: transformed CFII data.

## References

* Cirac--Pérez-García--Schuch--Verstraete, arXiv:1703.09188, equations
  `eq:transfer-op` and `II_CF`, lines 271--281 and 336--340.
-/

open scoped Matrix BigOperators ComplexOrder

namespace MPSTensor

variable {d D : ℕ}

/-- Entrywise complex conjugation of every letter of an MPS tensor. -/
def mapStar (A : MPSTensor d D) : MPSTensor d D :=
  fun i ↦ (A i).map (starRingEnd ℂ)

@[simp] theorem mapStar_apply (A : MPSTensor d D) (i : Fin d) :
    mapStar A i = (A i).map (starRingEnd ℂ) := rfl

@[simp] theorem mapStar_mapStar (A : MPSTensor d D) :
    mapStar (mapStar A) = A := by
  ext i β α
  simp [mapStar, Matrix.map_apply]

/-- Entrywise conjugation preserves algebraic injectivity. -/
theorem IsInjective.mapStar {A : MPSTensor d D} (hA : IsInjective A) :
    IsInjective (mapStar A) := by
  classical
  rw [IsInjective]
  apply top_unique
  intro X _
  have hmem : X.map (starRingEnd ℂ) ∈ Submodule.span ℂ (Set.range A) := by
    rw [hA]
    trivial
  have hconj : ∀ Y ∈ Submodule.span ℂ (Set.range A),
      Y.map (starRingEnd ℂ) ∈ Submodule.span ℂ (Set.range (MPSTensor.mapStar A)) := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Z hZ =>
        obtain ⟨i, rfl⟩ := hZ
        exact Submodule.subset_span ⟨i, rfl⟩
    | zero => simp
    | add Y Z _ _ hY hZ =>
        rw [show (Y + Z).map (starRingEnd ℂ) =
          Y.map (starRingEnd ℂ) + Z.map (starRingEnd ℂ) by
            exact Matrix.map_add _ (map_add (starRingEnd ℂ)) Y Z]
        exact Submodule.add_mem _ hY hZ
    | smul c Y _ hY =>
        rw [show (c • Y).map (starRingEnd ℂ) =
          star c • Y.map (starRingEnd ℂ) by
            ext i j
            simp [Matrix.map_apply]]
        exact Submodule.smul_mem _ (star c) hY
  have := hconj _ hmem
  convert this using 1
  ext i j
  simp [Matrix.map_apply]

private theorem evalWord_mapStar (A : MPSTensor d D) (w : List (Fin d)) :
    evalWord (mapStar A) w = (evalWord A w).map (starRingEnd ℂ) := by
  induction w with
  | nil => simp [evalWord]
  | cons i w ih =>
      simp only [evalWord, mapStar_apply, ih]
      exact ((starRingEnd ℂ).mapMatrix.map_mul (A i) (evalWord A w)).symm

/-- Entrywise conjugation preserves positive-length block injectivity, hence normality. -/
theorem IsNormal.mapStar {A : MPSTensor d D} (hA : IsNormal A) :
    IsNormal (mapStar A) := by
  obtain ⟨N, hN, hInj⟩ := hA
  refine ⟨N, hN, ?_⟩
  rw [isNBlkInjective_iff_blockTensor_isInjective] at hInj ⊢
  have hConj := hInj.mapStar
  convert hConj using 1
  ext σ β α
  simp [blockTensor, evalWord_mapStar]

/-- Left-canonical normalization is preserved by entrywise complex conjugation. -/
theorem IsLeftCanonical.mapStar {A : MPSTensor d D} (hA : IsLeftCanonical A) :
    IsLeftCanonical (mapStar A) := by
  classical
  rw [IsLeftCanonical] at hA ⊢
  calc
    ∑ i, (MPSTensor.mapStar A i)ᴴ * MPSTensor.mapStar A i =
        (∑ i, (A i)ᴴ * A i).map (starRingEnd ℂ) := by
      rw [show (∑ i, (A i)ᴴ * A i).map (starRingEnd ℂ) =
        ∑ i, ((A i)ᴴ * A i).map (starRingEnd ℂ) by
      exact map_sum ((starRingEnd ℂ).mapMatrix) _ Finset.univ]
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.map_mul, Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])]
      rfl
    _ = 1 := by rw [hA]; simp

/-- A spectrally normalized normal tensor remains normal after entrywise conjugation. -/
theorem IsNormalTensor.mapStar {A : MPSTensor d D} (hA : IsNormalTensor A)
    (hLeft : IsLeftCanonical A) : IsNormalTensor (mapStar A) := by
  letI : NeZero D := ⟨hA.bondDim_ne_zero⟩
  exact isNormalTensor_of_isNormal_leftCanonical _ hA.isNormal.mapStar hLeft.mapStar

private theorem map_star_eq_self_of_posDef_isDiag
    {n : ℕ} {Λ : Matrix (Fin n) (Fin n) ℂ} (hΛpos : Λ.PosDef) (hΛdiag : Λ.IsDiag) :
    Λ.map (starRingEnd ℂ) = Λ := by
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [Matrix.map_apply] using hΛpos.1.apply i i
  · simp [Matrix.map_apply, hΛdiag hij]

private theorem transferMap_mapStar (A : MPSTensor d D)
    (X : Matrix (Fin D) (Fin D) ℂ) :
    transferMap (mapStar A) (X.map (starRingEnd ℂ)) =
      (transferMap A X).map (starRingEnd ℂ) := by
  classical
  simp only [transferMap_apply]
  rw [show (∑ i, A i * X * (A i)ᴴ).map (starRingEnd ℂ) =
      ∑ i, (A i * X * (A i)ᴴ).map (starRingEnd ℂ) by
    exact map_sum ((starRingEnd ℂ).mapMatrix) _ Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.map_mul, Matrix.map_mul,
    Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])]
  rfl


end MPSTensor

namespace MPOTensor

variable {d D : ℕ}

/-- Exchange the two coordinates of a flattened physical pair. -/
def physicalPairSwapEquiv (d : ℕ) : Fin (d * d) ≃ Fin (d * d) where
  toFun ij := finProdFinEquiv (ij.modNat, ij.divNat)
  invFun ij := finProdFinEquiv (ij.modNat, ij.divNat)
  left_inv ij := by
    rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
      exact (finProdFinEquiv.apply_symm_apply ij).symm]
    simp
  right_inv ij := by
    rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
      exact (finProdFinEquiv.apply_symm_apply ij).symm]
    simp

@[simp] theorem physicalPairSwapEquiv_finProdFinEquiv (i j : Fin d) :
    physicalPairSwapEquiv d (finProdFinEquiv (i, j)) = finProdFinEquiv (j, i) := by
  simp [physicalPairSwapEquiv]

@[simp] theorem physicalPairSwapEquiv_symm :
    (physicalPairSwapEquiv d).symm = physicalPairSwapEquiv d := rfl

/-- The normalized flattening of the physical adjoint is obtained by applying entrywise complex
conjugation to every virtual matrix entry and exchanging the two flattened physical coordinates. -/
theorem normalizedFlattening_physicalAdjointTensor (U : MPOTensor d D) :
    (physicalAdjointTensor U).normalizedFlattening =
      MPSTensor.reindexPhysical (physicalPairSwapEquiv d)
        (MPSTensor.mapStar U.normalizedFlattening) := by
  ext ij β α
  rw [show ij = finProdFinEquiv (ij.divNat, ij.modNat) by
    exact (finProdFinEquiv.apply_symm_apply ij).symm]
  simp [normalizedFlattening, MPSTensor.reindexPhysical, MPSTensor.mapStar,
    MPOTensor.toMPSTensor, Matrix.smul_apply, Matrix.map_apply, RCLike.star_def]

end MPOTensor

namespace MPSTensor.CPSVCanonicalFormIIData

variable {d D : ℕ} {U : MPOTensor d D}

/-- Transport literal CPSV canonical-form-II data through physical adjunction.

The block count and dimensions are unchanged. We conjugate the weights, blocks, and ambient
coisometry entrywise, then exchange the two physical coordinates. A diagonal positive-definite
fixed point is real, so the same matrix remains fixed by the transformed transfer map.

This is the reduced-CFII operation used with arXiv:1703.09188, equations `II_CF` and
`eq:transfer-op`, lines 271--281 and 336--340. It makes no assertion about selected compact-SVD
witnesses or source factors. -/
noncomputable def physicalAdjointNormalizedFlattening
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    CPSVCanonicalFormIIData (MPOTensor.physicalAdjointTensor U).normalizedFlattening where
  r := data.r
  dim := data.dim
  dim_pos := data.dim_pos
  weights := fun k ↦ star (data.weights k)
  blocks := fun k ↦ MPSTensor.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
    (MPSTensor.mapStar (data.blocks k))
  blocks_normal := fun k ↦
    (MPSTensor.IsNormalTensor.mapStar (data.blocks_normal k)
      (data.blocks_left_canonical k)).reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
  total_dim_le := data.total_dim_le
  ambient_coisometry := data.ambient_coisometry.map (starRingEnd ℂ)
  coisometric := by
    have hmap := congrArg (fun M ↦ M.map (starRingEnd ℂ)) data.coisometric
    simpa [Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj])] using hmap
  reconstruct := by
    intro i
    rw [MPOTensor.normalizedFlattening_physicalAdjointTensor]
    have hmap := congrArg (fun M ↦ M.map (starRingEnd ℂ))
      (data.reconstruct (MPOTensor.physicalPairSwapEquiv d i))
    have hmiddle :
        (MPSTensor.toTensorFromBlocks data.weights data.blocks
          (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ) =
          MPSTensor.toTensorFromBlocks (fun k ↦ star (data.weights k))
            (fun k ↦ MPSTensor.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
              (MPSTensor.mapStar (data.blocks k))) i := by
      simp only [MPSTensor.toTensorFromBlocks, MPSTensor.reindexPhysical]
      rw [show ((Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
          (Matrix.blockDiagonal' fun k => data.weights k •
            data.blocks k (MPOTensor.physicalPairSwapEquiv d i))).map (starRingEnd ℂ) =
          (Matrix.reindex finSigmaFinEquiv finSigmaFinEquiv)
            ((Matrix.blockDiagonal' fun k => data.weights k •
              data.blocks k (MPOTensor.physicalPairSwapEquiv d i)).map (starRingEnd ℂ)) by
        ext β α
        rfl]
      rw [Matrix.blockDiagonal'_map _ _ (by simp)]
      congr 2
      funext k
      ext β α
      simp [MPSTensor.mapStar, Matrix.map_apply]
    rw [Matrix.map_mul, Matrix.map_mul,
      Matrix.conjTranspose_map (starRingEnd ℂ) (by simp [Function.Semiconj]),
      hmiddle] at hmap
    exact hmap
  blocks_left_canonical := fun k ↦
    (MPSTensor.leftCanonical_reindexPhysical_equiv
      (MPOTensor.physicalPairSwapEquiv d) _).2
      (MPSTensor.IsLeftCanonical.mapStar (data.blocks_left_canonical k))
  blocks_fixed_point := by
    intro k
    obtain ⟨Λ, hΛpos, hΛdiag, hΛfix⟩ := data.blocks_fixed_point k
    refine ⟨Λ, hΛpos, hΛdiag, ?_⟩
    rw [MPSTensor.transferMap_reindexPhysical_equiv]
    rw [← MPSTensor.map_star_eq_self_of_posDef_isDiag hΛpos hΛdiag,
      MPSTensor.transferMap_mapStar, hΛfix,
      MPSTensor.map_star_eq_self_of_posDef_isDiag hΛpos hΛdiag]

@[simp] theorem physicalAdjointNormalizedFlattening_r
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.r = data.r := rfl

@[simp] theorem physicalAdjointNormalizedFlattening_dim
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.dim = data.dim := rfl

@[simp] theorem physicalAdjointNormalizedFlattening_weights
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) (k : Fin data.r) :
    data.physicalAdjointNormalizedFlattening.weights k = star (data.weights k) := rfl

@[simp] theorem physicalAdjointNormalizedFlattening_blocks
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) (k : Fin data.r) :
    data.physicalAdjointNormalizedFlattening.blocks k =
      MPSTensor.reindexPhysical (MPOTensor.physicalPairSwapEquiv d)
        (MPSTensor.mapStar (data.blocks k)) := rfl

@[simp] theorem physicalAdjointNormalizedFlattening_ambientCoisometry
    (data : CPSVCanonicalFormIIData U.normalizedFlattening) :
    data.physicalAdjointNormalizedFlattening.ambient_coisometry =
      data.ambient_coisometry.map (starRingEnd ℂ) := rfl

/-- Physical adjunction preserves full active support of reduced CFII data. -/
theorem hasFullActiveSupport_physicalAdjointNormalizedFlattening
    (data : CPSVCanonicalFormIIData U.normalizedFlattening)
    (hfull : data.toCPSVCanonicalFormData.HasFullActiveSupport) :
    data.physicalAdjointNormalizedFlattening.toCPSVCanonicalFormData.HasFullActiveSupport := by
  classical
  simp only [MPSTensor.CPSVCanonicalFormData.HasFullActiveSupport]
  change (∑ k : {k : Fin data.r // star (data.weights k) ≠ 0}, data.dim k.1) = D
  let e : {k : Fin data.r // star (data.weights k) ≠ 0} ≃
      data.toCPSVCanonicalFormData.Active :=
    Equiv.subtypeEquiv (Equiv.refl _) (fun k ↦ star_ne_zero)
  apply (e.sum_comp (fun k ↦ data.dim k.1)).trans
  exact hfull

end MPSTensor.CPSVCanonicalFormIIData

namespace MPSTensor.IsCPSVCanonicalFormII

variable {d D : ℕ} {U : MPOTensor d D}

/-- Physical adjunction preserves literal CPSV canonical form II of the normalized flattening. -/
theorem physicalAdjointNormalizedFlattening
    (h : MPSTensor.IsCPSVCanonicalFormII U.normalizedFlattening) :
    MPSTensor.IsCPSVCanonicalFormII
      (MPOTensor.physicalAdjointTensor U).normalizedFlattening := by
  obtain ⟨data⟩ := h
  exact ⟨data.physicalAdjointNormalizedFlattening⟩

end MPSTensor.IsCPSVCanonicalFormII
