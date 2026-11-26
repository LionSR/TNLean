/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPU.Symmetry.Phases.ConjugationStrictEquivalence
import TNLean.MPS.Examples.Shift.ShiftStandardForms
import TNLean.MPS.Examples.Shift.ShiftPublicIndex
import TNLean.MPS.MPU.Index.IdentityIndex
import TNLean.MPS.MPU.CanonicalForm.TensorProductCanonicalForm
import TNLean.MPS.MPU.Symmetry.Conjugation.StandardFormConjugation

/-!
# Conjugation phases of the counterpropagating shifts

Proposition `prop:U2-U3-trivial-conjugation` of arXiv:1703.09188 (lines 2110--2134): after
blocking two sites, `U₂ = T† ⊗ T` and `U₃ = T ⊗ T†` are in the trivial phase under conjugation,
the phase of the identity `U₁`.

All three tensors are real and in canonical form II. The two-site blocks of `U₂`, `U₃` have the
standard forms of equations `eq:uv2_U2`, `eq:uv2_U3` with ranks `ℓ = r = d²`, built from
`1 ⊗ 𝕊 ⊗ 1` and `𝕊 ⊗ 𝕊`; the two-site block of `U₁` has the standard form `u = v = 1` with the
same ranks. Since `det (1 ⊗ 𝕊 ⊗ 1) = (det 𝕊)^{d²}`, `det (𝕊 ⊗ 𝕊) = 1` and `det 𝕊 = ±1`, the
odd-rank criterion (`det(uv)` equal) applies for odd `d`, and the even-rank criterion (Case I,
equal determinants) for even `d`.

## Main results

* `MPOTensor.shiftExampleU₂_strictlyEquivalentUnderSymmetry_conjugation`,
  `MPOTensor.shiftExampleU₃_strictlyEquivalentUnderSymmetry_conjugation`: the proposition.
-/

open scoped Matrix Kronecker
open Matrix

namespace MPOTensor

variable {d : ℕ}

private theorem mapStar_tensorProduct {d₁ d₂ D₁ D₂ : ℕ} (A : MPOTensor d₁ D₁)
    (B : MPOTensor d₂ D₂) :
    mapStar (tensorProduct A B) = tensorProduct (mapStar A) (mapStar B) := by
  funext ⟨i, j⟩
  simp only [mapStar, tensorProduct]
  rw [show ∀ M : Matrix _ _ ℂ, (reindex finProdFinEquiv finProdFinEquiv M).map (starRingEnd ℂ) =
      reindex finProdFinEquiv finProdFinEquiv (M.map (starRingEnd ℂ)) from fun _ ↦ rfl,
    map_star_kronecker]

private theorem mapStar_rightShiftTensor : mapStar (rightShiftTensor d) = rightShiftTensor d := by
  funext ⟨i, j⟩
  ext α β
  simp only [mapStar, map_apply, rightShiftTensor_apply]
  split_ifs <;> simp

private theorem mapStar_physicalAdjointTensor {D : ℕ} (K : MPOTensor d D) :
    mapStar (physicalAdjointTensor K) = physicalAdjointTensor (mapStar K) := by
  funext ⟨i, j⟩
  ext α β
  simp [mapStar, physicalAdjointTensor]

private theorem mapStar_leftShiftTensor : mapStar (leftShiftTensor d) = leftShiftTensor d := by
  rw [leftShiftTensor, mapStar_physicalAdjointTensor, mapStar_rightShiftTensor]

private theorem mapStar_identityMPUTensor :
    mapStar (identityMPUTensor d) = identityMPUTensor d := by
  funext ⟨i, j⟩
  simp only [mapStar, identityMPUTensor, idTensor]
  split_ifs <;> simp

/-- The periodic operators of a real tensor, blocked by two, are real. -/
private theorem mpo_blockTwo_map_star_of_mapStar {q D : ℕ} {U : MPOTensor q D}
    (h : mapStar U = U) (N : ℕ) :
    mpo (blockTwo U) N = (mpo (blockTwo U) N).map (starRingEnd ℂ) := by
  rw [← mpo_map_star, ← blockTwo_mapStar, h]

/-- `U₁` is real. -/
theorem shiftExampleU₁_mapStar : mapStar (shiftExampleU₁ d) = shiftExampleU₁ d := by
  rw [shiftExampleU₁, mapStar_tensorProduct, mapStar_identityMPUTensor]

/-- `U₂` is real. -/
theorem shiftExampleU₂_mapStar : mapStar (shiftExampleU₂ d) = shiftExampleU₂ d := by
  rw [shiftExampleU₂, mapStar_tensorProduct, mapStar_leftShiftTensor, mapStar_rightShiftTensor]

/-- `U₃` is real. -/
theorem shiftExampleU₃_mapStar : mapStar (shiftExampleU₃ d) = shiftExampleU₃ d := by
  rw [shiftExampleU₃, mapStar_tensorProduct, mapStar_leftShiftTensor, mapStar_rightShiftTensor]

/-! ### Canonical form II -/

/-- `U₁ = 1 ⊗ 1` is in canonical form II. Source: arXiv:1703.09188, eq. `threeMPU`,
lines 1980--2001, and canonical form II, lines 269--281. -/
noncomputable def shiftExampleU₁CanonicalFormII (d : ℕ) [NeZero d] :
    IsMPUCanonicalFormII (shiftExampleU₁ d) :=
  (identityMPUTensorCanonicalFormII d).tensorProduct (identityMPUTensorCanonicalFormII d)

/-- `U₂ = T† ⊗ T` is in canonical form II. Source: arXiv:1703.09188, eq. `threeMPU`,
lines 1980--2001, and canonical form II, lines 269--281. -/
theorem shiftExampleU₂_canonicalFormII (d : ℕ) [NeZero d] :
    Nonempty (IsMPUCanonicalFormII (shiftExampleU₂ d)) := by
  obtain ⟨h, -⟩ := rightShiftTensor_exists_canonicalFormII d
  exact ⟨h.physicalAdjointTensor.tensorProduct h⟩

/-- `U₃ = T ⊗ T†` is in canonical form II. Source: arXiv:1703.09188, eq. `threeMPU`,
lines 1980--2001, and canonical form II, lines 269--281. -/
theorem shiftExampleU₃_canonicalFormII (d : ℕ) [NeZero d] :
    Nonempty (IsMPUCanonicalFormII (shiftExampleU₃ d)) := by
  obtain ⟨h, -⟩ := rightShiftTensor_exists_canonicalFormII d
  exact ⟨h.tensorProduct h.physicalAdjointTensor⟩

/-! ### The trivial standard form of the blocked identity -/

/-- Entries of `U₁`: the identity on each physical pair, with bond dimension one. -/
theorem shiftExampleU₁_apply (a b : Fin (d * d)) :
    shiftExampleU₁ d (a, b) = if a = b then 1 else 0 := by
  obtain ⟨⟨a₁, a₂⟩, rfl⟩ := finProdFinEquiv.surjective a
  obtain ⟨⟨b₁, b₂⟩, rfl⟩ := finProdFinEquiv.surjective b
  ext α β
  have hα : α = finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)) := Subsingleton.elim _ _
  have hβ : β = finProdFinEquiv ((0 : Fin 1), (0 : Fin 1)) := Subsingleton.elim _ _
  rw [hα, hβ, shiftExampleU₁, tensorProduct_apply]
  simp only [identityMPUTensor, idTensor, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]
  by_cases h₁ : a₁ = b₁ <;> by_cases h₂ : a₂ = b₂ <;> simp [h₁, h₂]

/-- The two-site block of `U₁` has the standard form with gates `u = v = 1` and ranks
`ℓ = r = d²`. Source: arXiv:1703.09188, equation `eq:SF_u1_u3`, lines 2011--2016, read on the
two-site block as in `docs/paper-gaps/mpu_standard_form_canonical_convention.tex`. -/
noncomputable def shiftExampleU₁BlockedStandardForm (d : ℕ) [NeZero d] :
    TwoSiteStandardFormData (blockTwo (shiftExampleU₁ d))
      (1 : Matrix (Fin (d * d) × Fin (d * d)) (Fin (d * d) × Fin (d * d)) ℂ) 1 where
  phys_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  bond_pos := Nat.one_pos
  left_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  right_pos := Nat.mul_pos (NeZero.pos d) (NeZero.pos d)
  X₁ := fun p s ↦ if p.1 = s then 1 else 0
  X₂ := fun p t ↦ if p.2 = t then 1 else 0
  u_unitary := (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  v_unitary := (isUnitaryBetween_iff_mem_unitaryGroup _).mpr (one_mem _)
  v_apply i₁ i₂ s t := by
    simp only [one_apply, Prod.mk.injEq, Fin.sum_univ_one]
    by_cases h₁ : i₁ = s <;> by_cases h₂ : i₂ = t <;> simp [h₁, h₂]
  W_apply i j α γ := by
    simp only [blockTwo_apply, shiftExampleU₁_apply, one_apply]
    rw [Finset.sum_eq_single (finProdFinEquiv.symm i).1, Finset.sum_eq_single
      (finProdFinEquiv.symm i).2]
    · fin_cases α; fin_cases γ
      have : (finProdFinEquiv.symm i = finProdFinEquiv.symm j) ↔ i = j :=
        finProdFinEquiv.symm.injective.eq_iff
      by_cases h₁ : (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 <;>
        by_cases h₂ : (finProdFinEquiv.symm i).2 = (finProdFinEquiv.symm j).2 <;>
        simp_all [Prod.ext_iff]
    · intro s _ hs
      have hs' : s ≠ i.modNat := by simpa using hs
      simp [Ne.symm hs']
    · simp
    · intro t _ ht
      have ht' : t ≠ i.divNat := by simpa using ht
      simp [Ne.symm ht']
    · simp

/-! ### Determinants of the blocked gates -/

private theorem det_swapMatrix_sq : (swapMatrix d).det * (swapMatrix d).det = 1 := by
  rw [← det_mul, swapMatrix_mul_self, det_one]

/-- `1 ⊗ 𝕊 ⊗ 1` in Kronecker form. -/
private def middleRegroup (d : ℕ) :
    (Fin d × Fin d) × (Fin d × Fin d) ≃ Fin d × ((Fin d × Fin d) × Fin d) where
  toFun x := (x.1.1, ((x.1.2, x.2.1), x.2.2))
  invFun y := ((y.1, y.2.1.1), (y.2.1.2, y.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem identitySwapIdentityMatrix_eq :
    identitySwapIdentityMatrix d = reindex (middleRegroup d).symm (middleRegroup d).symm
      ((1 : Matrix (Fin d) (Fin d) ℂ) ⊗ₖ (swapMatrix d ⊗ₖ (1 : Matrix (Fin d) (Fin d) ℂ))) := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
  simp only [identitySwapIdentityMatrix_apply, reindex_apply, submatrix_apply,
    kroneckerMap_apply, one_apply, swapMatrix_apply, Equiv.symm_symm, middleRegroup,
    Equiv.coe_fn_mk]
  by_cases h₁ : a = i <;> by_cases h₂ : b = k <;> by_cases h₃ : c = j <;>
    by_cases h₄ : e = l <;> simp [h₁, h₂, h₃, h₄]

private theorem det_identitySwapIdentityMatrix :
    (identitySwapIdentityMatrix d).det = ((swapMatrix d).det ^ d) ^ d := by
  rw [identitySwapIdentityMatrix_eq, det_reindex_self, det_kronecker, det_kronecker, det_one]
  simp

private theorem det_swapTensorSwapMatrix : (swapTensorSwapMatrix d).det = 1 := by
  rw [swapTensorSwapMatrix, det_kronecker]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← mul_pow, det_swapMatrix_sq, one_pow]

private theorem det_submatrix_id {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (X : Matrix m n ℂ) (σ : m ≃ n) :
    (X.submatrix id σ).det = (X * (1 : Matrix n n ℂ).submatrix id σ).det := by
  congr 1
  ext i j
  simp [mul_apply, one_apply]

private theorem det_identitySwapIdentityMatrix_sq :
    (identitySwapIdentityMatrix d).det * (identitySwapIdentityMatrix d).det = 1 := by
  rw [det_identitySwapIdentityMatrix, ← mul_pow, ← mul_pow, det_swapMatrix_sq, one_pow, one_pow]

private theorem det_identitySwapIdentityMatrix_of_even (hd : Even d) :
    (identitySwapIdentityMatrix d).det = 1 := by
  obtain ⟨k, rfl⟩ := hd
  have hs : (swapMatrix (k + k)).det ^ (k + k) = 1 := by
    rw [pow_add, ← mul_pow, det_swapMatrix_sq, one_pow]
  rw [det_identitySwapIdentityMatrix, hs, one_pow]

private theorem map_star_identitySwapIdentityMatrix :
    (identitySwapIdentityMatrix d).map (starRingEnd ℂ) = identitySwapIdentityMatrix d := by
  ext ⟨⟨a, b⟩, ⟨c, e⟩⟩ ⟨⟨i, j⟩, ⟨k, l⟩⟩
  simp only [map_apply, identitySwapIdentityMatrix_apply]
  split_ifs <;> simp

private theorem map_star_swapTensorSwapMatrix :
    (swapTensorSwapMatrix d).map (starRingEnd ℂ) = swapTensorSwapMatrix d := by
  have h : (swapMatrix d).map (starRingEnd ℂ) = swapMatrix d := by
    ext ⟨a, b⟩ ⟨i, j⟩
    simp only [map_apply, swapMatrix_apply]
    split_ifs <;> simp
  rw [swapTensorSwapMatrix, map_star_kronecker, h]

private theorem map_star_reindex_shift {X : Matrix ((Fin d × Fin d) × (Fin d × Fin d))
    ((Fin d × Fin d) × (Fin d × Fin d)) ℂ} (hX : X.map (starRingEnd ℂ) = X) :
    (reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d) X).map
      (starRingEnd ℂ) = reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d) X := by
  change reindex _ _ (X.map (starRingEnd ℂ)) = _
  rw [hX]

/-! ### The two strict equivalences -/

/-- Strict equivalence under conjugation of the two-site blockings of a counterpropagating shift
`U` and of `U₁`, from blocked standard forms with gates `u = A`, `v = B` built from
`1 ⊗ 𝕊 ⊗ 1` and `𝕊 ⊗ 𝕊`. -/
private theorem strictlyEquivalent_conjugation_shiftExampleU₁_of_blocked [NeZero d]
    {D : ℕ} {U : MPOTensor (d * d) D} (hU : IsMPUCanonicalFormII U) (hstar : mapStar U = U)
    {A B : Matrix ((Fin d × Fin d) × (Fin d × Fin d)) ((Fin d × Fin d) × (Fin d × Fin d)) ℂ}
    (S : TwoSiteStandardFormData (blockTwo U)
      (reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d) A)
      (reindex (shiftTwoSitePhysicalEquiv d) (shiftTwoSitePhysicalEquiv d) B))
    (hA : A.map (starRingEnd ℂ) = A) (hB : B.map (starRingEnd ℂ) = B)
    (hAB : A.det * B.det = 1) (hAe : Even d → A.det = 1) (hBe : Even d → B.det = 1) :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (Kraus.blockPhysDim (d * d) 2))
      (blockTensor U 2) (blockTensor (shiftExampleU₁ d) 2) rfl := by
  set P := shiftTwoSitePhysicalEquiv d
  have h₁ := shiftExampleU₁CanonicalFormII d
  have S₁ := shiftExampleU₁BlockedStandardForm d
  rcases Nat.even_or_odd d with hd | hd
  · have hdd : Even (d * d) := hd.mul_right d
    refine strictlyEquivalentUnderSymmetry_conjugation_of_det_eq_of_even hU h₁ S S₁ hdd hdd
      (Or.inl ⟨map_star_reindex_shift hA, map_star_reindex_shift hB, ?_, ?_⟩)
      (Equiv.refl _) ?_ ?_
    · ext i j
      simp only [map_apply, one_apply]
      split_ifs <;> simp
    · ext i j
      simp only [map_apply, one_apply]
      split_ifs <;> simp
    · rw [det_submatrix_id, det_submatrix_id, det_mul, det_mul, det_reindex_self, hAe hd,
        det_one]
    · rw [det_submatrix_id, det_submatrix_id, det_mul, det_mul, det_reindex_self, hBe hd,
        det_one]
  · have hodd : Odd (d * d) ∨ Odd (d * d) := Or.inl (hd.mul hd)
    refine strictlyEquivalentUnderSymmetry_conjugation_of_det_mul_eq hU h₁
      (fun N _ ↦ mpo_blockTwo_map_star_of_mapStar hstar N)
      (fun N _ ↦ mpo_blockTwo_map_star_of_mapStar shiftExampleU₁_mapStar N) S S₁ hodd ?_
    rw [det_submatrix_id, det_submatrix_id, det_mul, det_mul, det_mul, det_reindex_self,
      det_reindex_self, hAB, Matrix.mul_one, det_one]

/-- **`U₂` is trivial under conjugation after blocking two sites.**

Source: arXiv:1703.09188, Proposition `prop:U2-U3-trivial-conjugation`, lines 2110--2134. -/
theorem shiftExampleU₂_strictlyEquivalentUnderSymmetry_conjugation (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (Kraus.blockPhysDim (d * d) 2))
      (blockTensor (shiftExampleU₂ d) 2) (blockTensor (shiftExampleU₁ d) 2) rfl := by
  obtain ⟨h⟩ := shiftExampleU₂_canonicalFormII d
  refine strictlyEquivalent_conjugation_shiftExampleU₁_of_blocked h shiftExampleU₂_mapStar
    (shiftExampleU₂BlockedStandardForm d) map_star_identitySwapIdentityMatrix
    (by rw [Matrix.map_mul, map_star_swapTensorSwapMatrix, map_star_identitySwapIdentityMatrix])
    ?_ (fun hd ↦ det_identitySwapIdentityMatrix_of_even hd) (fun hd ↦ ?_)
  · rw [det_mul, det_swapTensorSwapMatrix, one_mul, det_identitySwapIdentityMatrix_sq]
  · rw [det_mul, det_swapTensorSwapMatrix, one_mul, det_identitySwapIdentityMatrix_of_even hd]

/-- **`U₃` is trivial under conjugation after blocking two sites.**

Source: arXiv:1703.09188, Proposition `prop:U2-U3-trivial-conjugation`, lines 2110--2134. -/
theorem shiftExampleU₃_strictlyEquivalentUnderSymmetry_conjugation (d : ℕ) [NeZero d] :
    StrictlyEquivalentUnderSymmetry (conjugationSymmetry (Kraus.blockPhysDim (d * d) 2))
      (blockTensor (shiftExampleU₃ d) 2) (blockTensor (shiftExampleU₁ d) 2) rfl := by
  obtain ⟨h⟩ := shiftExampleU₃_canonicalFormII d
  refine strictlyEquivalent_conjugation_shiftExampleU₁_of_blocked h shiftExampleU₃_mapStar
    (shiftExampleU₃BlockedStandardForm d)
    (by rw [Matrix.map_mul, map_star_swapTensorSwapMatrix, map_star_identitySwapIdentityMatrix])
    map_star_identitySwapIdentityMatrix ?_ (fun hd ↦ ?_)
    (fun hd ↦ det_identitySwapIdentityMatrix_of_even hd)
  · rw [det_mul, det_swapTensorSwapMatrix, mul_one, det_identitySwapIdentityMatrix_sq]
  · rw [det_mul, det_swapTensorSwapMatrix, mul_one, det_identitySwapIdentityMatrix_of_even hd]

end MPOTensor
