/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.MPDO.PhysicalSectorActiveFactorSupport

/-!
# Factor-support coordinates for active physical sectors

For each active sector of a physical-sector factorization, this file chooses
isometric coordinates for the joint column supports of the left and right
factor families.  Inactive sectors receive zero-dimensional coordinate
spaces.  These data supply the support coordinates used by the canonical
physical restriction.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equation `AppUkU=rl`, lines 1381--1388.

**Scope restriction (active physical support compression):** choosing
isometries onto the joint column supports, and assigning zero-dimensional
coordinates to inactive sectors, is a project-derived auxiliary construction
between Lemma `propSN` and Proposition `prop3to4`.  It is recorded in
`docs/paper-gaps/cpsv16_active_physical_support_compression.tex`.
-/

open scoped Matrix BigOperators ComplexOrder Kronecker

namespace MPOTensor.PhysicalSectorFactorization

variable {d D : ℕ} {K : MPOTensor d D}

/-- The product-family support of an inactive sector is zero. -/
theorem sectorProductFamily_supportProj_eq_zero_of_not_isActiveSector
    (F : PhysicalSectorFactorization K) {k : Fin F.sectorCount}
    (hk : ¬ F.IsActiveSector k) :
    Matrix.familySupportProj (F.sectorProductFamily k) = 0 := by
  have hzero : ∀ q, F.sectorProductFamily k q = 0 :=
    (F.not_isActiveSector_iff k).mp hk
  have hmin := Matrix.familySupportProj_mul_eq_self_of_forall_mul_eq
    (F.sectorProductFamily k)
    (0 : Matrix (SectorIndex F k) (SectorIndex F k) ℂ)
    (fun q ↦ by simp [hzero q])
  simpa using hmin.symm

/-- Support coordinates for one physical sector.

For an active sector the two coordinate dimensions are positive and the
factor maps have the corresponding factor supports as their ranges.  For an
inactive sector both coordinate dimensions are zero.  The product range
identity is uniform in the sector.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
structure SectorActiveFactorSupportData
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) where
  /-- Dimension of the retained left factor. -/
  leftDim : ℕ
  /-- Dimension of the retained right factor. -/
  rightDim : ℕ
  /-- Isometric inclusion of the retained left factor. -/
  leftInclusion : Matrix (Fin (F.leftDim k)) (Fin leftDim) ℂ
  /-- Isometric inclusion of the retained right factor. -/
  rightInclusion : Matrix (Fin (F.rightDim k)) (Fin rightDim) ℂ
  /-- The retained left columns are orthonormal. -/
  leftInclusion_isometry : leftInclusionᴴ * leftInclusion = 1
  /-- The retained right columns are orthonormal. -/
  rightInclusion_isometry : rightInclusionᴴ * rightInclusion = 1
  /-- In an active sector, the retained left inclusion has exactly the joint
  column support of the left factor family as its range. -/
  leftInclusion_range : F.IsActiveSector k →
    leftInclusion * leftInclusionᴴ = F.leftFactorSupportProj k
  /-- In an active sector, the retained right inclusion has exactly the joint
  column support of the right factor family as its range. -/
  rightInclusion_range : F.IsActiveSector k →
    rightInclusion * rightInclusionᴴ = F.rightFactorSupportProj k
  /-- The product inclusion has exactly the joint product-family support as
  its range. -/
  product_range :
    (leftInclusion * leftInclusionᴴ) ⊗ₖ
        (rightInclusion * rightInclusionᴴ) =
      Matrix.familySupportProj (F.sectorProductFamily k)
  /-- An active left support has positive dimension. -/
  leftDim_pos_of_isActiveSector : F.IsActiveSector k → 0 < leftDim
  /-- An active right support has positive dimension. -/
  rightDim_pos_of_isActiveSector : F.IsActiveSector k → 0 < rightDim
  /-- No left coordinate is retained in an inactive sector. -/
  leftDim_eq_zero_of_not_isActiveSector :
    ¬ F.IsActiveSector k → leftDim = 0
  /-- No right coordinate is retained in an inactive sector. -/
  rightDim_eq_zero_of_not_isActiveSector :
    ¬ F.IsActiveSector k → rightDim = 0

/-- Every physical sector admits factor-support coordinates, with
zero-dimensional coordinates in the inactive case.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
theorem nonempty_sectorActiveFactorSupportData
    (F : PhysicalSectorFactorization K) (k : Fin F.sectorCount) :
    Nonempty (SectorActiveFactorSupportData F k) := by
  classical
  by_cases hk : F.IsActiveSector k
  · obtain ⟨l, r, VL, VR, hl, hVL, hRangeL, hr, hVR, hRangeR⟩ :=
      F.exists_activeSector_factorSupportIsometries hk
    exact ⟨{
      leftDim := l
      rightDim := r
      leftInclusion := VL
      rightInclusion := VR
      leftInclusion_isometry := hVL
      rightInclusion_isometry := hVR
      leftInclusion_range := fun _ ↦ hRangeL
      rightInclusion_range := fun _ ↦ hRangeR
      product_range := by
        rw [hRangeL, hRangeR, ← F.sectorProductFamily_supportProj k]
      leftDim_pos_of_isActiveSector := fun _ ↦ hl
      rightDim_pos_of_isActiveSector := fun _ ↦ hr
      leftDim_eq_zero_of_not_isActiveSector := fun h ↦ (h hk).elim
      rightDim_eq_zero_of_not_isActiveSector := fun h ↦ (h hk).elim }⟩
  · let VL : Matrix (Fin (F.leftDim k)) (Fin 0) ℂ := 0
    let VR : Matrix (Fin (F.rightDim k)) (Fin 0) ℂ := 0
    exact ⟨{
      leftDim := 0
      rightDim := 0
      leftInclusion := VL
      rightInclusion := VR
      leftInclusion_isometry := Subsingleton.elim _ _
      rightInclusion_isometry := Subsingleton.elim _ _
      leftInclusion_range := fun h ↦ (hk h).elim
      rightInclusion_range := fun h ↦ (hk h).elim
      product_range := by
        rw [F.sectorProductFamily_supportProj_eq_zero_of_not_isActiveSector hk]
        simp [VL, VR]
      leftDim_pos_of_isActiveSector := fun h ↦ (hk h).elim
      rightDim_pos_of_isActiveSector := fun h ↦ (hk h).elim
      leftDim_eq_zero_of_not_isActiveSector := fun _ ↦ rfl
      rightDim_eq_zero_of_not_isActiveSector := fun _ ↦ rfl }⟩

/-- A simultaneous choice of factor-support coordinates for all physical
sectors.

Source context: this datum supplies the factor-support coordinates used
between Lemma `propSN` (CPSV16 lines 1381--1450) and Proposition `prop3to4`.
The choice of isometries onto joint column supports per sector, with
zero-dimensional inactive sectors, is not present in the cited source
passage.  The construction is ours. -/
structure ActiveFactorSupportData (F : PhysicalSectorFactorization K) where
  /-- The chosen support coordinates in each sector. -/
  sector : (k : Fin F.sectorCount) → SectorActiveFactorSupportData F k

/-- Factor-support coordinates can be chosen simultaneously in all sectors. -/
theorem nonempty_activeFactorSupportData
    (F : PhysicalSectorFactorization K) :
    Nonempty (ActiveFactorSupportData F) := by
  classical
  exact ⟨⟨fun k ↦ Classical.choice
    (F.nonempty_sectorActiveFactorSupportData k)⟩⟩

/-- A fixed simultaneous choice of active factor-support coordinates. -/
noncomputable def activeFactorSupportData
    (F : PhysicalSectorFactorization K) : ActiveFactorSupportData F :=
  Classical.choice F.nonempty_activeFactorSupportData

end MPOTensor.PhysicalSectorFactorization
