/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MatrixFamilySupport
import TNLean.MPS.MPDO.BNTLayerOrthogonality
import TNLean.MPS.MPDO.PhysicalSectorProductRealization
import TNLean.MPS.MPDO.PhysicalSectorVirtualSpanning

/-!
# Supports of active physical-sector factors

For an injective matrix product density operator, positivity of the
neighboring operators makes the sector-coordinate tensor an injective matrix
product density operator. Its physical adjoint therefore lies in the span of
its physical slices. Restriction to one sector gives adjoint closure of the
product family
\[
  \{l_{k,\beta}\otimes r_{k,\alpha}\}_{\beta,\alpha}.
\]
For a sector in which this family is nonzero, matrix-entry functionals descend
the closure relation to the left and right factor families separately. Their
joint column supports consequently absorb the factors on both sides and have
positive-dimensional isometric parametrizations.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `Appetakhetc`, lines 1381--1450.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The family of all left-right Kronecker products in one physical sector.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable abbrev sectorProductFamily
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :=
  Matrix.familyKronecker (F.leftTensor k) (F.rightTensor k)

/-- A physical sector is active when both of its factor families have a
nonzero member.

Equivalently, the sector contributes a nonzero block to the direct-sum
factorization in `AppUkU=rl`.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
def IsActiveSector (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) : Prop :=
  (∃ β, F.leftTensor k β ≠ 0) ∧
    ∃ α, F.rightTensor k α ≠ 0

/-- A sector is active if and only if its left-right product family has a
nonzero member. -/
theorem isActiveSector_iff_exists_sectorProductFamily_ne_zero
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :
    F.IsActiveSector k ↔ ∃ q, F.sectorProductFamily k q ≠ 0 := by
  constructor
  · rintro ⟨⟨β, hβ⟩, ⟨α, hα⟩⟩
    refine ⟨(β, α), ?_⟩
    intro hzero
    have hαentry : ∃ i j, F.rightTensor k α i j ≠ 0 := by
      by_contra h
      apply hα
      ext i j
      simpa using not_exists.mp (not_exists.mp h i) j
    obtain ⟨i, j, hij⟩ := hαentry
    apply hβ
    ext u v
    have hEntry := congrFun (congrFun hzero (u, i)) (v, j)
    simpa [sectorProductFamily, Matrix.familyKronecker,
      Matrix.kroneckerMap_apply, hij] using hEntry
  · rintro ⟨⟨β, α⟩, hβα⟩
    refine ⟨⟨β, ?_⟩, ⟨α, ?_⟩⟩
    · intro hβ
      apply hβα
      simp [sectorProductFamily, Matrix.familyKronecker, hβ]
    · intro hα
      apply hβα
      simp [sectorProductFamily, Matrix.familyKronecker, hα]

/-- Inactivity means that every left-right product in the sector vanishes. -/
theorem not_isActiveSector_iff (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) :
    ¬ F.IsActiveSector k ↔ ∀ q, F.sectorProductFamily k q = 0 := by
  constructor
  · intro hk q
    by_contra hq
    exact hk ((F.isActiveSector_iff_exists_sectorProductFamily_ne_zero k).2
      ⟨q, hq⟩)
  · intro hzero hk
    obtain ⟨q, hq⟩ :=
      (F.isActiveSector_iff_exists_sectorProductFamily_ne_zero k).1 hk
    exact hq (hzero q)

/-- A sector is inactive precisely when one of its two factor families is
identically zero. -/
theorem not_isActiveSector_iff_left_or_right_eq_zero
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :
    ¬ F.IsActiveSector k ↔
      (∀ β, F.leftTensor k β = 0) ∨
        ∀ α, F.rightTensor k α = 0 := by
  simp only [IsActiveSector, not_and_or]
  constructor
  · intro h
    rcases h with hleft | hright
    · exact Or.inl fun β ↦ not_ne_iff.mp (not_exists.mp hleft β)
    · exact Or.inr fun α ↦ not_ne_iff.mp (not_exists.mp hright α)
  · rintro (hleft | hright)
    · exact Or.inl (not_exists.mpr fun β ↦ not_ne_iff.mpr (hleft β))
    · exact Or.inr (not_exists.mpr fun α ↦ not_ne_iff.mpr (hright α))

/-- At bond dimension zero every physical sector is inactive. -/
theorem not_isActiveSector_bondDim_zero
    {K : MPOTensor d 0} (F : PhysicalSectorFactorization K)
    (k : Fin F.sectorCount) :
    ¬ F.IsActiveSector k := by
  rintro ⟨⟨β, _⟩, _⟩
  exact Fin.elim0 β

/-- Injectivity is preserved when the physical indices are expressed in
sector coordinates.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
theorem sectorCoordinateTensor_isInjective
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor) :
    MPSTensor.IsInjective F.sectorCoordinateTensor.toMPSTensor := by
  change Submodule.span ℂ (Set.range F.sectorCoordinateTensor.toMPSTensor) = ⊤
  rw [← F.sectorCoordinateMatrixFamily_span_eq_top hK]
  congr 1
  ext A
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨(q.divNat, q.modNat), rfl⟩
  · rintro ⟨⟨i, j⟩, rfl⟩
    refine ⟨finProdFinEquiv (i, j), ?_⟩
    simp [MPOTensor.toMPSTensor, sectorCoordinateMatrixFamily]

/-- Positive neighboring operators make the sector-coordinate tensor a
matrix product density operator.

Source: arXiv:1606.00608, Appendix C.2, equation `Appetakhetc`, lines
1389--1450. -/
theorem sectorCoordinateTensor_isMPDO_of_neighboringOperator_pos
    (F : PhysicalSectorFactorization K)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    IsMPDO F.sectorCoordinateTensor := by
  intro N hN
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  exact F.mpo_sectorCoordinateTensor_posSemidef hpos

/-- The full left-right product family in every sector is closed under
conjugate transpose.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. This closure is a finite-dimensional
consequence of the injective MPDO factorization stated there. -/
theorem sectorProductFamily_conjTranspose_mem_span
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (k : Fin F.sectorCount) :
    ∀ q, ∃ c : Fin D × Fin D → ℂ,
      (F.sectorProductFamily k q)ᴴ =
        ∑ r, c r • F.sectorProductFamily k r := by
  obtain ⟨X, hAdjoint⟩ :=
    exists_physicalSlice_conjTranspose_eq_sum_of_isInjective_isMPDO
      F.sectorCoordinateTensor
      (F.sectorCoordinateTensor_isInjective hK)
      (F.sectorCoordinateTensor_isMPDO_of_neighboringOperator_pos hpos)
  rintro ⟨β, α⟩
  refine ⟨fun r ↦
    X β r.1 * (X⁻¹ : Matrix (Fin D) (Fin D) ℂ) r.2 α, ?_⟩
  ext x y
  have hEntry := congrFun (congrFun (hAdjoint β α)
    (F.sectorFinEquiv.symm ⟨k, x⟩))
    (F.sectorFinEquiv.symm ⟨k, y⟩)
  rw [Finset.sum_comm] at hEntry
  simpa only [sectorProductFamily, Matrix.familyKronecker,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, physicalSlice,
    sectorCoordinateTensor_apply_same, Matrix.sum_apply, Matrix.smul_apply,
    smul_eq_mul, Fintype.sum_prod_type] using hEntry

/-- In an active sector, the left factor family is closed under conjugate
transpose.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. This is the left-factor consequence of the
product-family closure. -/
theorem leftTensor_conjTranspose_mem_span_of_isActiveSector
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {k : Fin F.sectorCount} (hk : F.IsActiveSector k) :
    ∀ β, ∃ c : Fin D → ℂ,
      (F.leftTensor k β)ᴴ = ∑ μ, c μ • F.leftTensor k μ := by
  obtain ⟨α, hα⟩ := hk.2
  have hαentry : ∃ u v, F.rightTensor k α u v ≠ 0 := by
    by_contra h
    apply hα
    ext u v
    simpa using not_exists.mp (not_exists.mp h u) v
  obtain ⟨u, v, huv⟩ := hαentry
  let z : ℂ := star (F.rightTensor k α u v)
  have hz : z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 huv
  intro β
  obtain ⟨c, hc⟩ :=
    F.sectorProductFamily_conjTranspose_mem_span hK hpos k (β, α)
  refine ⟨fun μ ↦ z⁻¹ * ∑ ν, c (μ, ν) * F.rightTensor k ν v u, ?_⟩
  ext x y
  have hEntry := congrFun (congrFun hc (x, v)) (y, u)
  simp only [sectorProductFamily, Matrix.familyKronecker,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type] at hEntry ⊢
  have hEntry' :
      star (F.leftTensor k β y x) * z =
        ∑ μ, ∑ ν,
          c (μ, ν) * (F.leftTensor k μ x y * F.rightTensor k ν v u) := by
    rw [star_mul'] at hEntry
    simpa only [z] using hEntry
  calc
    star (F.leftTensor k β y x) =
        z⁻¹ * (star (F.leftTensor k β y x) * z) := by
      field_simp
    _ = z⁻¹ * ∑ μ, ∑ ν,
        c (μ, ν) * (F.leftTensor k μ x y * F.rightTensor k ν v u) := by
      rw [hEntry']
    _ = ∑ μ,
        (z⁻¹ * ∑ ν, c (μ, ν) * F.rightTensor k ν v u) *
          F.leftTensor k μ x y := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro μ _
      apply Finset.sum_congr rfl
      intro ν _
      ring

/-- In an active sector, the right factor family is closed under conjugate
transpose.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. This is the right-factor consequence of the
product-family closure. -/
theorem rightTensor_conjTranspose_mem_span_of_isActiveSector
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {k : Fin F.sectorCount} (hk : F.IsActiveSector k) :
    ∀ α, ∃ c : Fin D → ℂ,
      (F.rightTensor k α)ᴴ = ∑ ν, c ν • F.rightTensor k ν := by
  obtain ⟨β, hβ⟩ := hk.1
  have hβentry : ∃ u v, F.leftTensor k β u v ≠ 0 := by
    by_contra h
    apply hβ
    ext u v
    simpa using not_exists.mp (not_exists.mp h u) v
  obtain ⟨u, v, huv⟩ := hβentry
  let z : ℂ := star (F.leftTensor k β u v)
  have hz : z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 huv
  intro α
  obtain ⟨c, hc⟩ :=
    F.sectorProductFamily_conjTranspose_mem_span hK hpos k (β, α)
  refine ⟨fun ν ↦ z⁻¹ * ∑ μ, c (μ, ν) * F.leftTensor k μ v u, ?_⟩
  ext x y
  have hEntry := congrFun (congrFun hc (v, x)) (u, y)
  simp only [sectorProductFamily, Matrix.familyKronecker,
    Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Fintype.sum_prod_type] at hEntry ⊢
  rw [Finset.sum_comm] at hEntry
  have hEntry' :
      z * star (F.rightTensor k α y x) =
        ∑ ν, ∑ μ,
          c (μ, ν) * (F.leftTensor k μ v u * F.rightTensor k ν x y) := by
    rw [star_mul'] at hEntry
    simpa only [z] using hEntry
  calc
    star (F.rightTensor k α y x) =
        z⁻¹ * (z * star (F.rightTensor k α y x)) := by
      field_simp
    _ = z⁻¹ * ∑ ν, ∑ μ,
        c (μ, ν) * (F.leftTensor k μ v u * F.rightTensor k ν x y) := by
      rw [hEntry']
    _ = ∑ ν,
        (z⁻¹ * ∑ μ, c (μ, ν) * F.leftTensor k μ v u) *
          F.rightTensor k ν x y := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ν _
      apply Finset.sum_congr rfl
      intro μ _
      ring

/-- The joint column support of the left factor family in a sector. -/
noncomputable abbrev leftFactorSupportProj
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :=
  Matrix.familySupportProj (F.leftTensor k)

/-- The joint column support of the right factor family in a sector. -/
noncomputable abbrev rightFactorSupportProj
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :=
  Matrix.familySupportProj (F.rightTensor k)

/-- In an active sector, the factor support projections absorb every factor
on both sides.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. The support projections give a
finite-dimensional normalization of the factors appearing there. -/
theorem activeSector_factorSupport_twoSided
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    {k : Fin F.sectorCount} (hk : F.IsActiveSector k) :
    (∀ β,
      F.leftFactorSupportProj k * F.leftTensor k β = F.leftTensor k β ∧
        F.leftTensor k β * F.leftFactorSupportProj k = F.leftTensor k β) ∧
      ∀ α,
        F.rightFactorSupportProj k * F.rightTensor k α = F.rightTensor k α ∧
          F.rightTensor k α * F.rightFactorSupportProj k =
            F.rightTensor k α := by
  constructor
  · intro β
    exact ⟨Matrix.familySupportProj_mul (F.leftTensor k) β,
      Matrix.mul_familySupportProj_of_conjTranspose_mem_span
        (F.leftTensor k)
        (F.leftTensor_conjTranspose_mem_span_of_isActiveSector hK hpos hk) β⟩
  · intro α
    exact ⟨Matrix.familySupportProj_mul (F.rightTensor k) α,
      Matrix.mul_familySupportProj_of_conjTranspose_mem_span
        (F.rightTensor k)
        (F.rightTensor_conjTranspose_mem_span_of_isActiveSector hK hpos hk) α⟩

/-- The support of a sector product family is the Kronecker product of the
two factor supports.

This is the finite-dimensional support identity for the product in
`AppUkU=rl`, arXiv:1606.00608, Appendix C.2, lines 1381--1388. -/
theorem sectorProductFamily_supportProj
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :
    Matrix.familySupportProj (F.sectorProductFamily k) =
      F.leftFactorSupportProj k ⊗ₖ F.rightFactorSupportProj k :=
  Matrix.familySupportProj_kronecker (F.leftTensor k) (F.rightTensor k)

/-- An active sector has positive-dimensional isometric parametrizations of
both factor supports.

These isometries give a finite-dimensional normalization of the factors in
`AppUkU=rl`, arXiv:1606.00608, Appendix C.2, lines 1381--1450. -/
theorem exists_activeSector_factorSupportIsometries
    (F : PhysicalSectorFactorization K)
    {k : Fin F.sectorCount} (hk : F.IsActiveSector k) :
    ∃ (l r : ℕ)
      (VL : Matrix (Fin (F.leftDim k)) (Fin l) ℂ)
      (VR : Matrix (Fin (F.rightDim k)) (Fin r) ℂ),
      0 < l ∧ VLᴴ * VL = 1 ∧
        VL * VLᴴ = F.leftFactorSupportProj k ∧
      0 < r ∧ VRᴴ * VR = 1 ∧
        VR * VRᴴ = F.rightFactorSupportProj k := by
  obtain ⟨l, VL, hl, hVL, hRangeL⟩ :=
    Matrix.exists_familySupport_isometry_of_exists_ne_zero
      (F.leftTensor k) hk.1
  obtain ⟨r, VR, hr, hVR, hRangeR⟩ :=
    Matrix.exists_familySupport_isometry_of_exists_ne_zero
      (F.rightTensor k) hk.2
  exact ⟨l, r, VL, VR, hl, hVL, hRangeL, hr, hVR, hRangeR⟩

end MPOTensor.PhysicalSectorFactorization
