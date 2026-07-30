/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.MPS.MPDO.PhysicalSectorActiveFactorSupport
import TNLean.MPS.MPDO.PhysicalSupportRestriction

/-!
# Canonical physical restriction from active sector factors

The physical-sector factorization
\[
  U\,\kappa_{\beta,\alpha}\,U^*
    = \bigoplus_k (l_k)_\beta\otimes(r_k)_\alpha
\]
may contain factor directions on which every product vanishes.  This file
removes precisely those directions.  In each active sector it chooses
isometries onto the joint column supports of the left and right factor
families.  Inactive sectors receive zero-dimensional coordinate spaces.
The resulting dependent block diagonal isometry has no appended complement.

Its range is the canonical joint column support of the physical slices.  The
compressed tensor therefore has the sectorwise compressed left-right
factorization, and inclusion after restriction recovers the original tensor.
The construction remains valid when there are no active sectors, in
particular at virtual dimension zero.

## References

* [Cirac--Perez-Garcia--Schuch--Verstraete 2017] arXiv:1606.00608,
  Appendix C.2, equations `AppUkU=rl` and `Appetakhetc`, lines 1381--1450.

**Scope restriction (active physical support compression):** the active
factor-support compression (isometries onto joint column supports,
zero-dimensional inactive sectors, compressed injective tensor) does not
appear in CPSV16 lines 1381--1450.  It bridges Lemma `propSN` (the block
factorization and $\eta$ construction) to Proposition `prop3to4`.  The
compression is a standard finite-dimensional construction and is
mathematically verified; it is recorded in
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
      product_range := by
        rw [F.sectorProductFamily_supportProj_eq_zero_of_not_isActiveSector hk]
        simp [VL, VR]
      leftDim_pos_of_isActiveSector := fun h ↦ (hk h).elim
      rightDim_pos_of_isActiveSector := fun h ↦ (hk h).elim
      leftDim_eq_zero_of_not_isActiveSector := fun _ ↦ rfl
      rightDim_eq_zero_of_not_isActiveSector := fun _ ↦ rfl }⟩

/-- A simultaneous choice of factor-support coordinates for all physical
sectors.

Source context: this datum bridges Lemma `propSN` (CPSV16 lines 1381--1450)
to Proposition `prop3to4`.  The choice of isometries onto joint column
supports per sector, with zero-dimensional inactive sectors, is not present
in the cited source passage.  The construction is ours. -/
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

/-- The retained physical index within one sector.  This type is empty in an
inactive sector. -/
abbrev SupportedSectorIndex (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) :=
  Fin (A.sector k).leftDim × Fin (A.sector k).rightDim

/-- The product of the two factor-support inclusions in one sector.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def sectorSupportInclusion (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) :
    Matrix (SectorIndex F k) (SupportedSectorIndex F A k) ℂ :=
  (A.sector k).leftInclusion ⊗ₖ (A.sector k).rightInclusion

/-- The product inclusion in each sector is an isometry. -/
theorem sectorSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k : Fin F.sectorCount) :
    (F.sectorSupportInclusion A k)ᴴ * F.sectorSupportInclusion A k = 1 := by
  rw [sectorSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, (A.sector k).leftInclusion_isometry,
    (A.sector k).rightInclusion_isometry]
  exact Matrix.one_kronecker_one

/-- The range of the product inclusion is the joint support of the sector
product family. -/
theorem sectorSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (k : Fin F.sectorCount) :
    F.sectorSupportInclusion A k * (F.sectorSupportInclusion A k)ᴴ =
      Matrix.familySupportProj (F.sectorProductFamily k) := by
  rw [sectorSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul]
  exact (A.sector k).product_range

/-- The dependent direct sum of all retained sector coordinates.  Its fibers
over inactive sectors are empty. -/
abbrev SupportedPhysicalIndex (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) :=
  Σ k : Fin F.sectorCount, SupportedSectorIndex F A k

/-- The blockwise inclusion of all active factor supports in sector
coordinates.  Inactive blocks have empty domains and add no complement.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def dependentSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (SupportedPhysicalIndex F A) ℂ :=
  Matrix.blockDiagonal' fun k ↦ F.sectorSupportInclusion A k

/-- The blockwise active-factor inclusion is an isometry, including when its
domain is empty. -/
theorem dependentSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (F.dependentSupportInclusion A)ᴴ * F.dependentSupportInclusion A = 1 := by
  rw [dependentSupportInclusion, Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  simp_rw [F.sectorSupportInclusion_isometry A]
  exact Matrix.blockDiagonal'_one

/-- The blockwise range projection is the direct sum of the joint supports of
the sector product families. -/
theorem dependentSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.dependentSupportInclusion A * (F.dependentSupportInclusion A)ᴴ =
      Matrix.blockDiagonal' fun k ↦
        Matrix.familySupportProj (F.sectorProductFamily k) := by
  rw [dependentSupportInclusion, Matrix.blockDiagonal'_conjTranspose,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact F.sectorSupportInclusion_range A k

/-- The direct sum of the joint product-family supports in sector
coordinates. -/
noncomputable def dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K) :
    Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (Σ k : Fin F.sectorCount, SectorIndex F k) ℂ :=
  Matrix.blockDiagonal' fun k ↦
    Matrix.familySupportProj (F.sectorProductFamily k)

/-- The range of the active-factor inclusion is the dependent physical
support projection. -/
theorem dependentSupportInclusion_range_eq_dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.dependentSupportInclusion A * (F.dependentSupportInclusion A)ᴴ =
      F.dependentPhysicalSupportProj := by
  exact F.dependentSupportInclusion_range A

/-- The dependent physical support fixes every transformed physical slice on
the left. -/
theorem dependentPhysicalSupportProj_mul_transformedPhysicalSlice
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    F.dependentPhysicalSupportProj * F.transformedPhysicalSlice β α =
      F.transformedPhysicalSlice β α := by
  rw [dependentPhysicalSupportProj, F.transformedPhysicalSlice_eq,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact Matrix.familySupportProj_mul (F.sectorProductFamily k) (β, α)

/-- Under the positivity hypotheses of `Appetakhetc`, the dependent physical
support also fixes every transformed physical slice on the right.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem transformedPhysicalSlice_mul_dependentPhysicalSupportProj
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (β α : Fin D) :
    F.transformedPhysicalSlice β α * F.dependentPhysicalSupportProj =
      F.transformedPhysicalSlice β α := by
  rw [dependentPhysicalSupportProj, F.transformedPhysicalSlice_eq,
    ← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  exact Matrix.mul_familySupportProj_of_conjTranspose_mem_span
    (F.sectorProductFamily k)
    (F.sectorProductFamily_conjTranspose_mem_span hK hpos k) (β, α)

/-- Every matrix fixing all transformed physical slices on the left also
fixes the direct sum of their sector-family supports. -/
theorem mul_dependentPhysicalSupportProj_eq_self_of_forall_mul_transformedPhysicalSlice_eq
    (F : PhysicalSectorFactorization K)
    (P : Matrix (Σ k : Fin F.sectorCount, SectorIndex F k)
      (Σ k : Fin F.sectorCount, SectorIndex F k) ℂ)
    (hP : ∀ β α, P * F.transformedPhysicalSlice β α =
      F.transformedPhysicalSlice β α) :
    P * F.dependentPhysicalSupportProj = F.dependentPhysicalSupportProj := by
  classical
  let E := fun k ↦ Matrix.sigmaBlockInclusion (SectorIndex F) k
  have hPE (k : Fin F.sectorCount) (q : Fin D × Fin D) :
      P * E k * F.sectorProductFamily k q =
        E k * F.sectorProductFamily k q := by
    dsimp only [E]
    calc
      P * Matrix.sigmaBlockInclusion (SectorIndex F) k *
            F.sectorProductFamily k q =
          P * (F.transformedPhysicalSlice q.1 q.2 *
            Matrix.sigmaBlockInclusion (SectorIndex F) k) := by
        rw [F.transformedPhysicalSlice_eq,
          Matrix.blockDiagonal'_mul_sigmaBlockInclusion]
        simp only [sectorProductFamily, Matrix.familyKronecker, Matrix.mul_assoc]
      _ = (P * F.transformedPhysicalSlice q.1 q.2) *
          Matrix.sigmaBlockInclusion (SectorIndex F) k := by
        simp only [Matrix.mul_assoc]
      _ = F.transformedPhysicalSlice q.1 q.2 *
          Matrix.sigmaBlockInclusion (SectorIndex F) k := by
        rw [hP]
      _ = Matrix.sigmaBlockInclusion (SectorIndex F) k *
          F.sectorProductFamily k q := by
        rw [F.transformedPhysicalSlice_eq,
          Matrix.blockDiagonal'_mul_sigmaBlockInclusion]
        rfl
  have hPSupport (k : Fin F.sectorCount) :
      P * E k * Matrix.familySupportProj (F.sectorProductFamily k) =
        E k * Matrix.familySupportProj (F.sectorProductFamily k) := by
    have hGram :
        P * E k * Matrix.familyColumnGram (F.sectorProductFamily k) =
          E k * Matrix.familyColumnGram (F.sectorProductFamily k) := by
      rw [Matrix.familyColumnGram_eq_sum, Matrix.mul_sum, Matrix.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [← Matrix.mul_assoc]
      rw [hPE]
    obtain ⟨W, hW⟩ :=
      (Matrix.familyColumnGram_posSemidef
        (F.sectorProductFamily k)).exists_supportProj_eq_mul
    change P * E k *
        (Matrix.familyColumnGram_posSemidef
          (F.sectorProductFamily k)).supportProj =
      E k * (Matrix.familyColumnGram_posSemidef
        (F.sectorProductFamily k)).supportProj
    rw [hW]
    calc
      P * E k *
          (Matrix.familyColumnGram (F.sectorProductFamily k) * W) =
          (P * E k * Matrix.familyColumnGram
            (F.sectorProductFamily k)) * W := by
        simp only [Matrix.mul_assoc]
      _ = (E k * Matrix.familyColumnGram
          (F.sectorProductFamily k)) * W := by rw [hGram]
      _ = E k *
          (Matrix.familyColumnGram (F.sectorProductFamily k) * W) := by
        simp only [Matrix.mul_assoc]
  rw [dependentPhysicalSupportProj,
    Matrix.blockDiagonal'_eq_sum_sigmaBlockInclusion, Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simpa only [Matrix.mul_assoc] using congrArg
    (fun X ↦ X * (E k)ᴴ) (hPSupport k)

/-- The left factor compressed to its retained support coordinates.

Source context: the compression $(V^L_k)^\dagger \, l_{k,\beta} \, V^L_k$
does not appear in CPSV16 lines 1381--1450.  It is the natural restriction
of the left factor to the active coordinate space selected by the support
isometries, bridging `propSN` to `prop3to4`.  The construction is ours. -/
noncomputable def compressedLeftTensor (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) (β : Fin D) :
    Matrix (Fin (A.sector k).leftDim) (Fin (A.sector k).leftDim) ℂ :=
  (A.sector k).leftInclusionᴴ * F.leftTensor k β *
    (A.sector k).leftInclusion

/-- The right factor compressed to its retained support coordinates. -/
noncomputable def compressedRightTensor (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) (k : Fin F.sectorCount) (α : Fin D) :
    Matrix (Fin (A.sector k).rightDim) (Fin (A.sector k).rightDim) ℂ :=
  (A.sector k).rightInclusionᴴ * F.rightTensor k α *
    (A.sector k).rightInclusion

/-- Compression by the dependent active-factor inclusion preserves the
sectorwise left-right product form exactly.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem dependentSupportInclusion_compression
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (β α : Fin D) :
    (F.dependentSupportInclusion A)ᴴ *
          F.transformedPhysicalSlice β α *
        F.dependentSupportInclusion A =
      Matrix.blockDiagonal' fun k ↦
        F.compressedLeftTensor A k β ⊗ₖ
          F.compressedRightTensor A k α := by
  rw [dependentSupportInclusion, F.transformedPhysicalSlice_eq,
    Matrix.blockDiagonal'_conjTranspose]
  rw [← Matrix.blockDiagonal'_mul]
  rw [← Matrix.blockDiagonal'_mul]
  congr 1
  funext k
  rw [sectorSupportInclusion, Matrix.conjTranspose_kronecker,
    ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  rfl

/-- The dimension of the retained physical coordinate space. -/
abbrev supportedPhysicalDim (F : PhysicalSectorFactorization K)
    (A : ActiveFactorSupportData F) :=
  Fintype.card (SupportedPhysicalIndex F A)

/-- The canonical finite encoding of the retained dependent sector sum. -/
noncomputable def supportedPhysicalFinEquiv
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Fin (F.supportedPhysicalDim A) ≃ SupportedPhysicalIndex F A :=
  (Fintype.equivFin _).symm

/-- The active-factor inclusion with both physical index spaces encoded by
finite ordinals. -/
noncomputable def sectorCoordinateSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Matrix
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)))
      (Fin (F.supportedPhysicalDim A)) ℂ :=
  Matrix.reindex F.sectorFinEquiv.symm
    (F.supportedPhysicalFinEquiv A).symm
    (F.dependentSupportInclusion A)

/-- The finite-coordinate active-factor inclusion is an isometry. -/
theorem sectorCoordinateSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (F.sectorCoordinateSupportInclusion A)ᴴ *
        F.sectorCoordinateSupportInclusion A = 1 := by
  rw [sectorCoordinateSupportInclusion, Matrix.conjTranspose_reindex]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ
        (F.supportedPhysicalFinEquiv A).symm F.sectorFinEquiv.symm)
          (F.dependentSupportInclusion A)ᴴ *
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        (F.supportedPhysicalFinEquiv A).symm)
          (F.dependentSupportInclusion A) = 1
  rw [Matrix.reindexLinearEquiv_mul,
    F.dependentSupportInclusion_isometry A,
    Matrix.reindexLinearEquiv_one]

/-- The dependent physical support projection in finite sector
coordinates. -/
noncomputable def sectorCoordinatePhysicalSupportProj
    (F : PhysicalSectorFactorization K) :
    Matrix
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)))
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k))) ℂ :=
  Matrix.reindex F.sectorFinEquiv.symm F.sectorFinEquiv.symm
    F.dependentPhysicalSupportProj

/-- The range of the finite-coordinate inclusion is the finite-coordinate
dependent physical support. -/
theorem sectorCoordinateSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.sectorCoordinateSupportInclusion A *
        (F.sectorCoordinateSupportInclusion A)ᴴ =
      F.sectorCoordinatePhysicalSupportProj := by
  rw [sectorCoordinateSupportInclusion, Matrix.conjTranspose_reindex]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        (F.supportedPhysicalFinEquiv A).symm)
          (F.dependentSupportInclusion A) *
      (Matrix.reindexLinearEquiv ℂ ℂ
        (F.supportedPhysicalFinEquiv A).symm F.sectorFinEquiv.symm)
          (F.dependentSupportInclusion A)ᴴ =
    F.sectorCoordinatePhysicalSupportProj
  rw [Matrix.reindexLinearEquiv_mul,
    F.dependentSupportInclusion_range_eq_dependentPhysicalSupportProj A]
  rfl

/-- A physical slice of the sector-coordinate tensor is the finite
reindexing of the corresponding transformed physical slice. -/
theorem physicalSlice_sectorCoordinateTensor_eq_reindex
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    physicalSlice F.sectorCoordinateTensor β α =
      Matrix.reindex F.sectorFinEquiv.symm F.sectorFinEquiv.symm
        (F.transformedPhysicalSlice β α) := by
  ext i j
  rfl

/-- The finite-coordinate dependent support fixes every sector-coordinate
physical slice on the left. -/
theorem sectorCoordinatePhysicalSupportProj_mul_physicalSlice
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    F.sectorCoordinatePhysicalSupportProj *
        physicalSlice F.sectorCoordinateTensor β α =
      physicalSlice F.sectorCoordinateTensor β α := by
  rw [F.physicalSlice_sectorCoordinateTensor_eq_reindex,
    sectorCoordinatePhysicalSupportProj]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        F.sectorFinEquiv.symm) F.dependentPhysicalSupportProj *
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        F.sectorFinEquiv.symm) (F.transformedPhysicalSlice β α) =
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
      F.sectorFinEquiv.symm) (F.transformedPhysicalSlice β α)
  rw [Matrix.reindexLinearEquiv_mul,
    F.dependentPhysicalSupportProj_mul_transformedPhysicalSlice]

/-- Under neighboring positivity, the finite-coordinate dependent support
also fixes every sector-coordinate physical slice on the right.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem physicalSlice_mul_sectorCoordinatePhysicalSupportProj
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (β α : Fin D) :
    physicalSlice F.sectorCoordinateTensor β α *
        F.sectorCoordinatePhysicalSupportProj =
      physicalSlice F.sectorCoordinateTensor β α := by
  rw [F.physicalSlice_sectorCoordinateTensor_eq_reindex,
    sectorCoordinatePhysicalSupportProj]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        F.sectorFinEquiv.symm) (F.transformedPhysicalSlice β α) *
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
        F.sectorFinEquiv.symm) F.dependentPhysicalSupportProj =
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv.symm
      F.sectorFinEquiv.symm) (F.transformedPhysicalSlice β α)
  rw [Matrix.reindexLinearEquiv_mul,
    F.transformedPhysicalSlice_mul_dependentPhysicalSupportProj hK hpos]

/-- Every matrix fixing all sector-coordinate physical slices on the left
also fixes their finite-coordinate dependent support. -/
theorem mul_sectorCoordinatePhysicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
    (F : PhysicalSectorFactorization K)
    (P : Matrix
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k)))
      (Fin (Fintype.card (Σ k : Fin F.sectorCount, SectorIndex F k))) ℂ)
    (hP : ∀ β α, P * physicalSlice F.sectorCoordinateTensor β α =
      physicalSlice F.sectorCoordinateTensor β α) :
    P * F.sectorCoordinatePhysicalSupportProj =
      F.sectorCoordinatePhysicalSupportProj := by
  let Pσ := Matrix.reindex F.sectorFinEquiv F.sectorFinEquiv P
  have hPσ : ∀ β α, Pσ * F.transformedPhysicalSlice β α =
      F.transformedPhysicalSlice β α := by
    intro β α
    dsimp only [Pσ]
    ext x y
    have hEntry := congrFun (congrFun (hP β α)
      (F.sectorFinEquiv.symm x)) (F.sectorFinEquiv.symm y)
    rw [F.physicalSlice_sectorCoordinateTensor_eq_reindex] at hEntry
    simp only [Matrix.mul_apply, Matrix.reindex_apply,
      Matrix.submatrix_apply] at hEntry ⊢
    rw [← F.sectorFinEquiv.sum_comp (fun z ↦
      P (F.sectorFinEquiv.symm x) (F.sectorFinEquiv.symm z) *
        F.transformedPhysicalSlice β α z y)]
    simpa [Pσ, Matrix.reindex_apply] using hEntry
  have hσ :=
    F.mul_dependentPhysicalSupportProj_eq_self_of_forall_mul_transformedPhysicalSlice_eq
      Pσ hPσ
  apply (Matrix.reindex F.sectorFinEquiv F.sectorFinEquiv).injective
  change
    (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv F.sectorFinEquiv)
        (P * F.sectorCoordinatePhysicalSupportProj) =
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv F.sectorFinEquiv)
        F.sectorCoordinatePhysicalSupportProj
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
    F.sectorFinEquiv F.sectorFinEquiv F.sectorFinEquiv]
  simpa [Pσ, sectorCoordinatePhysicalSupportProj, Matrix.reindex_apply]
    using hσ

/-- The physical slice in sector coordinates is obtained by conjugating the
original physical slice by the physical coordinate matrix. -/
theorem physicalSlice_sectorCoordinateTensor_eq
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    physicalSlice F.sectorCoordinateTensor β α =
      F.physicalCoordinateMatrix * physicalSlice K β α *
        F.physicalCoordinateMatrixᴴ := by
  rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]
  rfl

/-- The original physical slice is recovered from its sector-coordinate
form.

Source context: this recovery identity $K = U^\dagger K_{\mathrm{sector}} U$
uses the isometry $U$ from Lemma `propSN` (CPSV16 lines 1381--1450).  The
subsequent compression by active-factor support isometries (which would
produce $K_{\mathrm{act}} = V^\dagger K V$) is our construction bridging to
`prop3to4`. -/
theorem physicalSlice_eq_conjTranspose_mul_sectorCoordinateTensor_mul
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    physicalSlice K β α =
      F.physicalCoordinateMatrixᴴ *
          physicalSlice F.sectorCoordinateTensor β α *
        F.physicalCoordinateMatrix := by
  rw [F.physicalSlice_sectorCoordinateTensor_eq]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrixᴴ,
    F.physicalCoordinateMatrix_isometry, Matrix.one_mul]
  exact (Matrix.mul_one _).symm

/-- The active-factor support inclusion in the original physical
coordinates.

It is the dependent block inclusion from `AppUkU=rl`, transported back by the
physical isometry appearing in that equation.  No orthogonal complement is
appended.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
noncomputable def physicalSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    Matrix (Fin d) (Fin (F.supportedPhysicalDim A)) ℂ :=
  F.physicalCoordinateMatrixᴴ * F.sectorCoordinateSupportInclusion A

/-- The original-coordinate active-factor inclusion is an isometry,
including when there are no active sectors. -/
theorem physicalSupportInclusion_isometry
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    (F.physicalSupportInclusion A)ᴴ * F.physicalSupportInclusion A = 1 := by
  rw [physicalSupportInclusion, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrix,
    F.physicalCoordinateMatrix_coisometry, Matrix.one_mul,
    F.sectorCoordinateSupportInclusion_isometry A]

/-- The active-factor support projection transported to the original
physical coordinates. -/
noncomputable def activePhysicalSupportProj
    (F : PhysicalSectorFactorization K) : Matrix (Fin d) (Fin d) ℂ :=
  F.physicalCoordinateMatrixᴴ * F.sectorCoordinatePhysicalSupportProj *
    F.physicalCoordinateMatrix

/-- The range of the original-coordinate inclusion is the transported
active-factor support projection. -/
theorem physicalSupportInclusion_range
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.physicalSupportInclusion A * (F.physicalSupportInclusion A)ᴴ =
      F.activePhysicalSupportProj := by
  rw [physicalSupportInclusion, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (F.sectorCoordinateSupportInclusion A),
    F.sectorCoordinateSupportInclusion_range A]
  simp only [activePhysicalSupportProj, Matrix.mul_assoc]

/-- The transported active-factor support is an orthogonal projection. -/
theorem isOrthogonalProjection_activePhysicalSupportProj
    (F : PhysicalSectorFactorization K) :
    IsOrthogonalProjection F.activePhysicalSupportProj := by
  let A := F.activeFactorSupportData
  rw [← F.physicalSupportInclusion_range A]
  constructor
  · simp [Matrix.IsHermitian]
  · calc
      (F.physicalSupportInclusion A *
          (F.physicalSupportInclusion A)ᴴ) *
          (F.physicalSupportInclusion A *
            (F.physicalSupportInclusion A)ᴴ) =
          F.physicalSupportInclusion A *
            ((F.physicalSupportInclusion A)ᴴ *
              F.physicalSupportInclusion A) *
            (F.physicalSupportInclusion A)ᴴ := by
        simp only [Matrix.mul_assoc]
      _ = F.physicalSupportInclusion A *
          (F.physicalSupportInclusion A)ᴴ := by
        rw [F.physicalSupportInclusion_isometry A, Matrix.mul_one]

/-- The transported active-factor support fixes every original physical slice
on the left. -/
theorem activePhysicalSupportProj_mul_physicalSlice
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    F.activePhysicalSupportProj * physicalSlice K β α =
      physicalSlice K β α := by
  rw [F.physicalSlice_eq_conjTranspose_mul_sectorCoordinateTensor_mul,
    activePhysicalSupportProj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrix,
    F.physicalCoordinateMatrix_coisometry, Matrix.one_mul]
  rw [← Matrix.mul_assoc F.sectorCoordinatePhysicalSupportProj,
    F.sectorCoordinatePhysicalSupportProj_mul_physicalSlice]

/-- Under neighboring positivity, the transported active-factor support fixes
every original physical slice on the right.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem physicalSlice_mul_activePhysicalSupportProj
    (F : PhysicalSectorFactorization K)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef)
    (β α : Fin D) :
    physicalSlice K β α * F.activePhysicalSupportProj =
      physicalSlice K β α := by
  rw [F.physicalSlice_eq_conjTranspose_mul_sectorCoordinateTensor_mul,
    activePhysicalSupportProj]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc F.physicalCoordinateMatrix,
    F.physicalCoordinateMatrix_coisometry, Matrix.one_mul]
  rw [← Matrix.mul_assoc
      (physicalSlice F.sectorCoordinateTensor β α),
    F.physicalSlice_mul_sectorCoordinatePhysicalSupportProj hK hpos]

/-- The active-factor range projection is the canonical joint column support
of the original physical slices.

This is an internal finite-dimensional consequence of the block
factorization `AppUkU=rl`: the columns in distinct physical sectors are
separate, and inactive sectors contribute no columns.

Source: arXiv:1606.00608, Appendix C.2, equation `AppUkU=rl`, lines
1381--1388. -/
theorem activePhysicalSupportProj_eq_physicalSupportProj
    (F : PhysicalSectorFactorization K) :
    F.activePhysicalSupportProj = physicalSupportProj K := by
  let S := physicalSupportProj K
  let Q := F.activePhysicalSupportProj
  have hQS : Q * S = S :=
    mul_physicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq K Q
      F.activePhysicalSupportProj_mul_physicalSlice
  let C := F.physicalCoordinateMatrix
  let R := C * S * Cᴴ
  have hR : ∀ β α, R * physicalSlice F.sectorCoordinateTensor β α =
      physicalSlice F.sectorCoordinateTensor β α := by
    intro β α
    rw [F.physicalSlice_sectorCoordinateTensor_eq]
    dsimp only [R, C]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc F.physicalCoordinateMatrixᴴ,
      F.physicalCoordinateMatrix_isometry, Matrix.one_mul]
    rw [← Matrix.mul_assoc (physicalSupportProj K),
      physicalSupportProj_mul_physicalSlice]
  have hRP :
      R * F.sectorCoordinatePhysicalSupportProj =
        F.sectorCoordinatePhysicalSupportProj :=
    F.mul_sectorCoordinatePhysicalSupportProj_eq_self_of_forall_mul_physicalSlice_eq
      R hR
  have hSQ : S * Q = Q := by
    dsimp only [S, Q, activePhysicalSupportProj, R, C] at hRP ⊢
    have hSC :
        physicalSupportProj K * F.physicalCoordinateMatrixᴴ =
          F.physicalCoordinateMatrixᴴ *
            (F.physicalCoordinateMatrix * physicalSupportProj K *
              F.physicalCoordinateMatrixᴴ) := by
      symm
      calc
        F.physicalCoordinateMatrixᴴ *
            (F.physicalCoordinateMatrix * physicalSupportProj K *
              F.physicalCoordinateMatrixᴴ) =
            (F.physicalCoordinateMatrixᴴ *
              F.physicalCoordinateMatrix) *
              physicalSupportProj K *
              F.physicalCoordinateMatrixᴴ := by
          simp only [Matrix.mul_assoc]
        _ = physicalSupportProj K *
            F.physicalCoordinateMatrixᴴ := by
          rw [F.physicalCoordinateMatrix_isometry, Matrix.one_mul]
    calc
      physicalSupportProj K *
          (F.physicalCoordinateMatrixᴴ *
            F.sectorCoordinatePhysicalSupportProj *
            F.physicalCoordinateMatrix) =
          (physicalSupportProj K * F.physicalCoordinateMatrixᴴ) *
            F.sectorCoordinatePhysicalSupportProj *
              F.physicalCoordinateMatrix := by
        simp only [Matrix.mul_assoc]
      _ = F.physicalCoordinateMatrixᴴ *
          ((F.physicalCoordinateMatrix * physicalSupportProj K *
            F.physicalCoordinateMatrixᴴ) *
            F.sectorCoordinatePhysicalSupportProj) *
          F.physicalCoordinateMatrix := by
        rw [hSC]
        simp only [Matrix.mul_assoc]
      _ = F.physicalCoordinateMatrixᴴ *
          F.sectorCoordinatePhysicalSupportProj *
          F.physicalCoordinateMatrix := by rw [hRP]
  have hQHerm : Q.IsHermitian :=
    F.isOrthogonalProjection_activePhysicalSupportProj.1
  have hSHerm : S.IsHermitian :=
    (MPSTensor.isOrthogonalProjection_supportProj
      (physicalSliceColumns K * (physicalSliceColumns K)ᴴ)
      (Matrix.posSemidef_self_mul_conjTranspose
        (physicalSliceColumns K))).1
  have hQS' := congrArg Matrix.conjTranspose hSQ
  have hQSQ : Q * S = Q := by
    simpa [Matrix.conjTranspose_mul, hQHerm.eq, hSHerm.eq] using hQS'
  exact hQSQ.symm.trans hQS

/-- The range of the explicit active-factor inclusion is the canonical
physical support projection. -/
theorem physicalSupportInclusion_range_eq_physicalSupportProj
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.physicalSupportInclusion A * (F.physicalSupportInclusion A)ᴴ =
      physicalSupportProj K := by
  rw [F.physicalSupportInclusion_range,
    F.activePhysicalSupportProj_eq_physicalSupportProj]

/-- The MPO tensor restricted to the active factor-support coordinates.

Source context: $K_{\mathrm{act}} = V^\dagger K V$ where $V$ is the
active-factor support inclusion isometry.  This restriction is not present
in CPSV16 lines 1381--1450; it bridges Lemma `propSN` to
Proposition `prop3to4` by removing inactive dimensions that the source
passage does not address.  The construction is ours. -/
noncomputable def activePhysicalSupportRestriction
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    MPOTensor (F.supportedPhysicalDim A) D :=
  changePhysicalBasis (F.physicalSupportInclusion A)ᴴ K

/-- Restriction in the original physical coordinates agrees with restriction
of the sector-coordinate tensor by the finite block inclusion. -/
theorem activePhysicalSupportRestriction_eq_sectorCoordinateRestriction
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
    F.activePhysicalSupportRestriction A =
      changePhysicalBasis (F.sectorCoordinateSupportInclusion A)ᴴ
        F.sectorCoordinateTensor := by
  rw [activePhysicalSupportRestriction, physicalSupportInclusion,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    changePhysicalBasis
        ((F.sectorCoordinateSupportInclusion A)ᴴ *
          F.physicalCoordinateMatrix) K =
        changePhysicalBasis (F.sectorCoordinateSupportInclusion A)ᴴ
          (changePhysicalBasis F.physicalCoordinateMatrix K) :=
      (changePhysicalBasis_changePhysicalBasis _ _ _).symm
    _ = changePhysicalBasis (F.sectorCoordinateSupportInclusion A)ᴴ
        F.sectorCoordinateTensor := by
      rw [F.sectorCoordinateTensor_eq_changePhysicalBasis]

/-- Reindexing the finite block inclusion back to dependent sector
coordinates recovers the original dependent block diagonal. -/
theorem reindex_sectorCoordinateSupportInclusion
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F) :
  Matrix.reindex F.sectorFinEquiv (F.supportedPhysicalFinEquiv A)
        (F.sectorCoordinateSupportInclusion A) =
      F.dependentSupportInclusion A := by
  ext x y
  simp [sectorCoordinateSupportInclusion, Matrix.reindex_apply]

/-- Reindexing a finite sector-coordinate physical slice back to its
dependent coordinates recovers the transformed physical slice. -/
theorem reindex_physicalSlice_sectorCoordinateTensor
    (F : PhysicalSectorFactorization K) (β α : Fin D) :
    Matrix.reindex F.sectorFinEquiv F.sectorFinEquiv
        (physicalSlice F.sectorCoordinateTensor β α) =
      F.transformedPhysicalSlice β α := by
  rw [F.physicalSlice_sectorCoordinateTensor_eq_reindex]
  ext x y
  simp [Matrix.reindex_apply]

/-- Every physical slice of the restricted tensor has the sectorwise
compressed left-right factorization.

Inactive sectors have empty coordinate fibers, so the displayed direct sum
contains neither an identity fallback nor an appended zero complement.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem reindex_physicalSlice_activePhysicalSupportRestriction
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (β α : Fin D) :
    Matrix.reindex (F.supportedPhysicalFinEquiv A)
        (F.supportedPhysicalFinEquiv A)
        (physicalSlice (F.activePhysicalSupportRestriction A) β α) =
      Matrix.blockDiagonal' fun k ↦
        F.compressedLeftTensor A k β ⊗ₖ
          F.compressedRightTensor A k α := by
  rw [F.activePhysicalSupportRestriction_eq_sectorCoordinateRestriction A]
  have hslice :
      physicalSlice
          (changePhysicalBasis (F.sectorCoordinateSupportInclusion A)ᴴ
            F.sectorCoordinateTensor) β α =
        (F.sectorCoordinateSupportInclusion A)ᴴ *
            physicalSlice F.sectorCoordinateTensor β α *
          F.sectorCoordinateSupportInclusion A := by
    ext i j
    simp [physicalSlice, changePhysicalBasis]
  rw [hslice]
  change
    (Matrix.reindexLinearEquiv ℂ ℂ (F.supportedPhysicalFinEquiv A)
      (F.supportedPhysicalFinEquiv A))
        ((F.sectorCoordinateSupportInclusion A)ᴴ *
            physicalSlice F.sectorCoordinateTensor β α *
          F.sectorCoordinateSupportInclusion A) =
      Matrix.blockDiagonal' fun k ↦
        F.compressedLeftTensor A k β ⊗ₖ
          F.compressedRightTensor A k α
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
    (F.supportedPhysicalFinEquiv A) F.sectorFinEquiv
    (F.supportedPhysicalFinEquiv A)]
  rw [← Matrix.reindexLinearEquiv_mul ℂ ℂ
    (F.supportedPhysicalFinEquiv A) F.sectorFinEquiv F.sectorFinEquiv]
  have hW := F.reindex_sectorCoordinateSupportInclusion A
  have hWstar := congrArg Matrix.conjTranspose hW
  rw [Matrix.conjTranspose_reindex] at hWstar
  have hW' :
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv
        (F.supportedPhysicalFinEquiv A))
          (F.sectorCoordinateSupportInclusion A) =
        F.dependentSupportInclusion A :=
    hW
  have hWstar' :
      (Matrix.reindexLinearEquiv ℂ ℂ
        (F.supportedPhysicalFinEquiv A) F.sectorFinEquiv)
          (F.sectorCoordinateSupportInclusion A)ᴴ =
        (F.dependentSupportInclusion A)ᴴ :=
    hWstar
  have hB' :
      (Matrix.reindexLinearEquiv ℂ ℂ F.sectorFinEquiv F.sectorFinEquiv)
          (physicalSlice F.sectorCoordinateTensor β α) =
        F.transformedPhysicalSlice β α :=
    F.reindex_physicalSlice_sectorCoordinateTensor β α
  rw [hWstar', hW', hB',
    F.dependentSupportInclusion_compression]

/-- Inclusion after active-factor restriction recovers the original MPO
tensor exactly.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
theorem changePhysicalBasis_physicalSupportInclusion_activePhysicalSupportRestriction
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    changePhysicalBasis (F.physicalSupportInclusion A)
        (F.activePhysicalSupportRestriction A) = K := by
  rw [activePhysicalSupportRestriction,
    changePhysicalBasis_changePhysicalBasis,
    F.physicalSupportInclusion_range]
  exact changePhysicalBasis_eq_self_of_twoSided_physicalSlice
    F.activePhysicalSupportProj K
    F.isOrthogonalProjection_activePhysicalSupportProj
    (fun β α ↦ ⟨F.activePhysicalSupportProj_mul_physicalSlice β α,
      F.physicalSlice_mul_activePhysicalSupportProj hK hpos β α⟩)

/-- The active-factor restriction of an injective tensor is injective.

Source context: injectivity of the compressed tensor $V^\dagger K V$ follows
from injectivity of $K$ because $V$ is an isometry and $VV^\dagger$ absorbs
every physical slice.  This is a standard finite-dimensional argument that
does not appear in CPSV16 lines 1381--1450; it is the key property enabling
the bridge from `propSN` to `prop3to4`.  The construction is ours. -/
theorem activePhysicalSupportRestriction_isInjective
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    MPSTensor.IsInjective (F.activePhysicalSupportRestriction A).toMPSTensor :=
  isInjective_of_eq_changePhysicalBasis
    (F.physicalSupportInclusion A)
    (F.activePhysicalSupportRestriction A) K
    (F.changePhysicalBasis_physicalSupportInclusion_activePhysicalSupportRestriction
      A hK hpos).symm hK

/-- The explicitly assembled active-factor inclusion gives the canonical
physical support restriction data.

Unlike an arbitrary range-isometry construction, this datum retains the
left-right sector coordinates of `AppUkU=rl`.

Source: arXiv:1606.00608, Appendix C.2, equations `AppUkU=rl` and
`Appetakhetc`, lines 1381--1450. -/
noncomputable def activePhysicalSupportRestrictionData
    (F : PhysicalSectorFactorization K) (A : ActiveFactorSupportData F)
    (hK : MPSTensor.IsInjective K.toMPSTensor)
    (hpos : ∀ k h, (F.neighboringOperator k h).PosSemidef) :
    PhysicalSupportRestrictionData (physicalSupportProj K) K where
  supportDim := F.supportedPhysicalDim A
  inclusion := F.physicalSupportInclusion A
  inclusion_isometry := F.physicalSupportInclusion_isometry A
  inclusion_range := by
    rw [F.physicalSupportInclusion_range,
      F.activePhysicalSupportProj_eq_physicalSupportProj]
  restricted_injective :=
    F.activePhysicalSupportRestriction_isInjective A hK hpos
  reembed :=
    F.changePhysicalBasis_physicalSupportInclusion_activePhysicalSupportRestriction
      A hK hpos

end MPOTensor.PhysicalSectorFactorization
