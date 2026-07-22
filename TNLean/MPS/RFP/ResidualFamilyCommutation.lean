/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.DependentBlockDiagonal
import TNLean.MPS.RFP.AppendixBChainCommutation
import TNLean.MPS.RFP.ResidualFamilySupport

/-!
# Commutation for a residual-isometry family

This file constructs the equal-sector virtual bond projector for the disjoint
union of the residual-pair spaces of a BNT family.  Its adjacent placements
commute sectorwise, while mixed-sector products vanish by orthogonality of the
canonical summand inclusions.  Transport by the common physical isometry then
gives the adjacent commutation relation for the canonical two-site support of
the multiplicity-one direct sum.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, lines
543--555, equations (3.16)--(3.18), lines 549--578, and Appendix B, lines
1305--1307.
-/

open scoped Matrix BigOperators Kronecker

namespace MPSTensor

variable {d r : ℕ} {dim : Fin r → ℕ}

namespace ResidualFamilyAppendixBData

variable {B : (j : Fin r) → MPSTensor d (dim j)}

/-- The canonical inclusion of one sector's residual-pair space into the
common disjoint union of residual-pair spaces.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
noncomputable abbrev sectorPairInclusion
    (j : Fin r) : Matrix (BlockEntryIndex dim) (Fin (dim j) × Fin (dim j)) ℂ :=
  Matrix.sigmaBlockInclusion (fun k ↦ Fin (dim k) × Fin (dim k)) j

/-- The rank-one bond projector of a sector, in its two residual-pair
coordinates.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def sectorVirtualBondMatrix
    (h : ResidualFamilyAppendixBData B) (j : Fin r) :
    Matrix ((Fin (dim j) × Fin (dim j)) × (Fin (dim j) × Fin (dim j)))
      ((Fin (dim j) × Fin (dim j)) × (Fin (dim j) × Fin (dim j))) ℂ :=
  Matrix.reindex (finTwoArrowEquiv (Fin (dim j) × Fin (dim j)))
    (finTwoArrowEquiv (Fin (dim j) × Fin (dim j)))
    (LinearMap.toMatrix' (h.sector j).twoSiteVirtualBondProjection)

/-- Extend one sector's virtual bond projector by zero to the common
residual-pair square.

Source: arXiv:1606.00608, equations (3.17)--(3.18), lines 564--578. -/
noncomputable def embeddedSectorVirtualBondMatrix
    (h : ResidualFamilyAppendixBData B) (j : Fin r) :
    Matrix (BlockEntryIndex dim × BlockEntryIndex dim)
      (BlockEntryIndex dim × BlockEntryIndex dim) ℂ :=
  let E := sectorPairInclusion (dim := dim) j
  ((E ⊗ₖ E) * h.sectorVirtualBondMatrix j) * (Eᴴ ⊗ₖ Eᴴ)

/-- The equal-sector virtual bond projector on the common residual-pair
space.  Cross-sector two-site pairs are absent from its range.

Source: arXiv:1606.00608, equations `eq:III_isometry` and (3.17)--(3.18),
lines 549--578. -/
noncomputable def virtualBondMatrix
    (h : ResidualFamilyAppendixBData B) :
    Matrix (BlockEntryIndex dim × BlockEntryIndex dim)
      (BlockEntryIndex dim × BlockEntryIndex dim) ℂ :=
  ∑ j : Fin r, h.embeddedSectorVirtualBondMatrix j

/-- The two adjacent placements of the equal-sector virtual bond projector
commute.  The equal-sector terms are the single-sector Appendix B
calculation; unequal-sector terms vanish by orthogonality of the canonical
summand inclusions.

Source: arXiv:1606.00608, equations `eq:III_isometry` and (3.17)--(3.18),
lines 549--578. -/
theorem virtualPairMatrices_comm
    (h : ResidualFamilyAppendixBData B) :
    appendixBLeftPairMatrix h.virtualBondMatrix *
        appendixBRightPairMatrix h.virtualBondMatrix =
      appendixBRightPairMatrix h.virtualBondMatrix *
        appendixBLeftPairMatrix h.virtualBondMatrix := by
  classical
  rw [virtualBondMatrix, appendixBLeftPairMatrix_sum,
    appendixBRightPairMatrix_sum, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : j = k
  · subst k
    exact appendixB_transportedPairMatrices_comm
      (sectorPairInclusion (dim := dim) j) (h.sectorVirtualBondMatrix j)
      (Matrix.sigmaBlockInclusion_isometry
        (fun k ↦ Fin (dim k) × Fin (dim k)) j)
      (h.sector j).virtualPairMatrices_comm
  · have horth :
        (sectorPairInclusion (dim := dim) j)ᴴ *
            sectorPairInclusion (dim := dim) k = 0 :=
      Matrix.sigmaBlockInclusion_conjTranspose_mul_of_ne
        (fun l ↦ Fin (dim l) × Fin (dim l)) hjk
    simp only [embeddedSectorVirtualBondMatrix]
    rw [appendixB_leftTransportedPairMatrix_mul_right_eq_zero_of_orthogonal
      (sectorPairInclusion (dim := dim) j)
      (sectorPairInclusion (dim := dim) k)
      (h.sectorVirtualBondMatrix j) (h.sectorVirtualBondMatrix k) horth]
    have h_reverse_product :
        appendixBRightPairMatrix (h.embeddedSectorVirtualBondMatrix j) *
            appendixBLeftPairMatrix (h.embeddedSectorVirtualBondMatrix k) = 0 := by
      simp only [embeddedSectorVirtualBondMatrix]
      exact appendixB_rightTransportedPairMatrix_mul_left_eq_zero_of_orthogonal
        (sectorPairInclusion (dim := dim) j)
        (sectorPairInclusion (dim := dim) k)
        (h.sectorVirtualBondMatrix j) (h.sectorVirtualBondMatrix k) horth
    simpa only [embeddedSectorVirtualBondMatrix] using h_reverse_product.symm

/-- The common physical isometry belonging to simultaneous Appendix B data.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
noncomputable abbrev physicalIsometryMatrix
    (h : ResidualFamilyAppendixBData B) :
    Matrix (Fin d) (BlockEntryIndex dim) ℂ :=
  residualFamilyPhysicalIsometryMatrix (fun j ↦ (h.sector j).U)

/-- Restricting the common physical isometry to one canonical summand gives
that sector's physical isometry.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
theorem physicalIsometryMatrix_mul_sectorPairInclusion
    (h : ResidualFamilyAppendixBData B) (j : Fin r) :
    h.physicalIsometryMatrix * sectorPairInclusion (dim := dim) j =
      (h.sector j).physicalIsometryMatrix := by
  classical
  ext i p
  simp [physicalIsometryMatrix, residualFamilyPhysicalIsometryMatrix,
    sectorPairInclusion, Matrix.sigmaBlockInclusion, Matrix.mul_apply,
    AppendixBStructuralData.physicalIsometryMatrix]

/-- Distinct sectors have orthogonal one-site physical isometry ranges.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554. -/
theorem sectorPhysicalIsometryMatrix_orthogonal
    (h : ResidualFamilyAppendixBData B) {j k : Fin r} (hjk : j ≠ k) :
    (h.sector j).physicalIsometryMatrixᴴ *
        (h.sector k).physicalIsometryMatrix = 0 := by
  let V := h.physicalIsometryMatrix
  let E := sectorPairInclusion (dim := dim) j
  let F := sectorPairInclusion (dim := dim) k
  have hVE : V * E = (h.sector j).physicalIsometryMatrix :=
    h.physicalIsometryMatrix_mul_sectorPairInclusion j
  have hVF : V * F = (h.sector k).physicalIsometryMatrix :=
    h.physicalIsometryMatrix_mul_sectorPairInclusion k
  have hV : Vᴴ * V = 1 :=
    h.residual.residualFamilyPhysicalIsometryMatrix_isometry
  have hEF : Eᴴ * F = 0 :=
    Matrix.sigmaBlockInclusion_conjTranspose_mul_of_ne
      (fun l ↦ Fin (dim l) × Fin (dim l)) hjk
  rw [← hVE, ← hVF, Matrix.conjTranspose_mul]
  rw [Matrix.mul_assoc Eᴴ Vᴴ (V * F)]
  rw [← Matrix.mul_assoc Vᴴ V F]
  rw [hV, Matrix.one_mul, hEF]

/-- Transporting one embedded sector bond by the common physical isometry is
the same as transporting it by that sector's physical isometry.

Source: arXiv:1606.00608, equations `eq:III_isometry` and (3.16)--(3.18),
lines 549--578. -/
theorem transport_embeddedSectorVirtualBondMatrix
    (h : ResidualFamilyAppendixBData B) (j : Fin r) :
    ((h.physicalIsometryMatrix ⊗ₖ h.physicalIsometryMatrix) *
        h.embeddedSectorVirtualBondMatrix j) *
          (h.physicalIsometryMatrixᴴ ⊗ₖ h.physicalIsometryMatrixᴴ) =
      (((h.sector j).physicalIsometryMatrix ⊗ₖ
          (h.sector j).physicalIsometryMatrix) * h.sectorVirtualBondMatrix j) *
        ((h.sector j).physicalIsometryMatrixᴴ ⊗ₖ
          (h.sector j).physicalIsometryMatrixᴴ) := by
  let V := h.physicalIsometryMatrix
  let E := sectorPairInclusion (dim := dim) j
  let U := (h.sector j).physicalIsometryMatrix
  have hVE : V * E = U := h.physicalIsometryMatrix_mul_sectorPairInclusion j
  have hEV : Eᴴ * Vᴴ = Uᴴ := by
    simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose hVE
  simp only [embeddedSectorVirtualBondMatrix, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V ⊗ₖ V) (E ⊗ₖ E)]
  rw [← Matrix.mul_kronecker_mul, hVE]
  rw [← Matrix.mul_kronecker_mul, hEV]

/-- The matrix of a sector's canonical two-site support is its transported
rank-one virtual bond matrix.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
theorem sectorSupportProjection_matrix
    (h : ResidualFamilyAppendixBData B) (j : Fin r) :
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' (h.sector j).twoSiteBasicSupportProjection) =
      (((h.sector j).physicalIsometryMatrix ⊗ₖ
          (h.sector j).physicalIsometryMatrix) * h.sectorVirtualBondMatrix j) *
        ((h.sector j).physicalIsometryMatrixᴴ ⊗ₖ
          (h.sector j).physicalIsometryMatrixᴴ) := by
  rw [← (h.sector j).transportedTwoSiteBondProjection_eq_support]
  exact (h.sector j).transportedTwoSiteBondProjection_matrix

/-- Canonical two-site support projectors of distinct residual sectors have
orthogonal ranges.

Source: arXiv:1606.00608, equation `eq:III_isometry`, lines 549--554, and
equations (3.16)--(3.18), lines 549--578. -/
theorem sectorSupportProjection_mul_eq_zero
    (h : ResidualFamilyAppendixBData B) {j k : Fin r} (hjk : j ≠ k) :
    (h.sector j).twoSiteBasicSupportProjection *
        (h.sector k).twoSiteBasicSupportProjection = 0 := by
  apply LinearMap.toMatrix'.injective
  apply (Matrix.reindexLinearEquiv ℂ ℂ (finTwoArrowEquiv (Fin d))
    (finTwoArrowEquiv (Fin d))).injective
  simp only [LinearMap.toMatrix'_mul, map_zero,
    Matrix.coe_reindexLinearEquiv]
  have horth := h.sectorPhysicalIsometryMatrix_orthogonal hjk
  calc
    Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' (h.sector j).twoSiteBasicSupportProjection *
          LinearMap.toMatrix' (h.sector k).twoSiteBasicSupportProjection) =
      Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (h.sector j).twoSiteBasicSupportProjection) *
        Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (h.sector k).twoSiteBasicSupportProjection) := by
      symm
      exact Matrix.reindexLinearEquiv_mul ℂ ℂ
        (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (finTwoArrowEquiv (Fin d)) _ _
    _ = 0 := by
      rw [h.sectorSupportProjection_matrix j, h.sectorSupportProjection_matrix k]
      let U := (h.sector j).physicalIsometryMatrix
      let V := (h.sector k).physicalIsometryMatrix
      let Q := h.sectorVirtualBondMatrix j
      let R := h.sectorVirtualBondMatrix k
      have hkron : (Uᴴ ⊗ₖ Uᴴ) * (V ⊗ₖ V) = 0 := by
        rw [← Matrix.mul_kronecker_mul]
        change ((h.sector j).physicalIsometryMatrixᴴ *
            (h.sector k).physicalIsometryMatrix) ⊗ₖ
          ((h.sector j).physicalIsometryMatrixᴴ *
            (h.sector k).physicalIsometryMatrix) = 0
        rw [horth]
        simp
      change (((U ⊗ₖ U) * Q) * (Uᴴ ⊗ₖ Uᴴ)) *
          (((V ⊗ₖ V) * R) * (Vᴴ ⊗ₖ Vᴴ)) = 0
      calc
        _ = (U ⊗ₖ U) * Q * ((Uᴴ ⊗ₖ Uᴴ) * (V ⊗ₖ V)) *
            R * (Vᴴ ⊗ₖ Vᴴ) := by
          simp only [Matrix.mul_assoc]
        _ = 0 := by rw [hkron]; simp

/-- The sum of the canonical two-site support projectors of the sectors.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
noncomputable def sectorSupportSum
    (h : ResidualFamilyAppendixBData B) :
    NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2 :=
  ∑ j : Fin r, (h.sector j).twoSiteBasicSupportProjection

/-- The sector support sum is idempotent.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
theorem sectorSupportSum_idempotent
    (h : ResidualFamilyAppendixBData B) :
    h.sectorSupportSum * h.sectorSupportSum = h.sectorSupportSum := by
  classical
  rw [sectorSupportSum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single j]
  · exact (h.sector j).twoSiteBasicSupportProjection_idempotent
  · intro k _ hkj
    exact h.sectorSupportProjection_mul_eq_zero hkj.symm
  · simp

/-- The range of the sector support sum is the linear sum of the sector
two-site ground spaces.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.17)--(3.18), lines
543--578. -/
theorem sectorSupportSum_range
    (h : ResidualFamilyAppendixBData B) :
    LinearMap.range h.sectorSupportSum =
      ⨆ j : Fin r, groundSpace (B j) 2 := by
  classical
  apply le_antisymm
  · rintro ψ ⟨v, rfl⟩
    rw [sectorSupportSum, LinearMap.sum_apply]
    apply Submodule.sum_mem
    intro j _
    apply Submodule.mem_iSup_of_mem j
    rw [(h.sector j).groundSpace_eq_coreTensor]
    change (h.sector j).twoSiteBasicSupportProjection v ∈
      (h.sector j).twoSiteBasicSpace
    rw [← (h.sector j).twoSiteBasicSupportProjection_range]
    exact ⟨v, rfl⟩
  · refine iSup_le fun j ↦ ?_
    intro ψ hψ
    rw [(h.sector j).groundSpace_eq_coreTensor] at hψ
    have hψRange : ψ ∈ LinearMap.range
        (h.sector j).twoSiteBasicSupportProjection := by
      rw [(h.sector j).twoSiteBasicSupportProjection_range]
      exact hψ
    obtain ⟨v, rfl⟩ := hψRange
    refine ⟨(h.sector j).twoSiteBasicSupportProjection v, ?_⟩
    rw [sectorSupportSum, LinearMap.sum_apply, Finset.sum_eq_single j]
    · exact LinearMap.congr_fun
        (h.sector j).twoSiteBasicSupportProjection_idempotent v
    · intro k _ hkj
      have hzero := LinearMap.congr_fun
        (h.sectorSupportProjection_mul_eq_zero hkj)
        v
      simpa only [Module.End.mul_apply, LinearMap.zero_apply] using hzero
    · simp

/-- Conjugate a coefficient-space endomorphism by the standard Euclidean
coordinate equivalence.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
private noncomputable def coefficientEuclideanEnd
    (T : NSiteSpace d 2 →ₗ[ℂ] NSiteSpace d 2) :
    EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm.toLinearMap.comp
    (T.comp (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).toLinearMap)

/-- The Euclidean form of the sector support sum.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
private noncomputable def sectorSupportSumES
    (h : ResidualFamilyAppendixBData B) :
    EuclideanSpace ℂ (Cfg d 2) →ₗ[ℂ] EuclideanSpace ℂ (Cfg d 2) :=
  coefficientEuclideanEnd h.sectorSupportSum

/-- In Euclidean coordinates the sector support sum is the sum of the
orthogonal projections onto the sector ground spaces.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
private theorem sectorSupportSumES_eq
    (h : ResidualFamilyAppendixBData B) :
    h.sectorSupportSumES =
      ∑ j : Fin r, (groundSpaceES (h.sector j).coreTensor 2).starProjection.toLinearMap := by
  classical
  apply LinearMap.ext
  intro v
  simp [sectorSupportSumES, coefficientEuclideanEnd, sectorSupportSum,
    AppendixBStructuralData.twoSiteBasicSupportProjection]

/-- The Euclidean sector support sum is a symmetric projection.

Source: arXiv:1606.00608, equations (3.16)--(3.18), lines 549--578. -/
private theorem sectorSupportSumES_isSymmetricProjection
    (h : ResidualFamilyAppendixBData B) :
    h.sectorSupportSumES.IsSymmetricProjection where
  isIdempotentElem := by
    apply LinearMap.ext
    intro v
    simpa [sectorSupportSumES, coefficientEuclideanEnd, Module.End.mul_apply] using
      LinearMap.congr_fun h.sectorSupportSum_idempotent
        ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) v)
  isSymmetric := by
    rw [h.sectorSupportSumES_eq]
    exact Finset.sum_induction
      (fun j : Fin r ↦
        (groundSpaceES (h.sector j).coreTensor 2).starProjection.toLinearMap)
      LinearMap.IsSymmetric
      (fun _ _ ha hb ↦ ha.add hb)
      LinearMap.IsSymmetric.zero
      (fun j _ ↦ (groundSpaceES (h.sector j).coreTensor 2).starProjection_isSymmetric)

/-- The Euclidean sector support sum has the direct-sum two-site ground space
as its range.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.16)--(3.18), lines
543--578. -/
private theorem sectorSupportSumES_range
    (h : ResidualFamilyAppendixBData B) :
    LinearMap.range h.sectorSupportSumES =
      groundSpaceES (directSumTensor B) 2 := by
  ext ψ
  constructor
  · rintro ⟨v, rfl⟩
    apply (mem_groundSpaceES_iff (directSumTensor B) 2 _).2
    change h.sectorSupportSum
      ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) v) ∈
        groundSpace (directSumTensor B) 2
    rw [← h.twoSiteBondEmbedding_range_eq_directSum_groundSpace,
      h.twoSiteBondEmbedding_range, ← h.sectorSupportSum_range]
    exact ⟨_, rfl⟩
  · intro hψ
    have hraw : (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)) ψ ∈
        LinearMap.range h.sectorSupportSum := by
      rw [h.sectorSupportSum_range, ← h.twoSiteBondEmbedding_range,
        h.twoSiteBondEmbedding_range_eq_directSum_groundSpace]
      exact (mem_groundSpaceES_iff (directSumTensor B) 2 ψ).1 hψ
    obtain ⟨v, hv⟩ := hraw
    refine ⟨(WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm v, ?_⟩
    apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).injective
    simpa [sectorSupportSumES, coefficientEuclideanEnd] using hv

/-- The canonical support of the direct sum is the sum of the mutually
orthogonal sector supports.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and (3.16)--(3.18), lines
543--578. -/
theorem sectorSupportSum_eq_twoSiteBondSupportProjection
    (h : ResidualFamilyAppendixBData B) :
    h.sectorSupportSum = twoSiteBondSupportProjection B := by
  have hEq : h.sectorSupportSumES =
      (groundSpaceES (directSumTensor B) 2).starProjection.toLinearMap :=
    h.sectorSupportSumES_isSymmetricProjection.ext
      (Submodule.isSymmetricProjection_starProjection _)
      (by
        rw [Submodule.range_starProjection]
        exact h.sectorSupportSumES_range)
  apply LinearMap.ext
  intro ψ
  have hψ := LinearMap.congr_fun hEq
    ((WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm ψ)
  apply (WithLp.linearEquiv 2 ℂ (NSiteSpace d 2)).symm.injective
  simpa [sectorSupportSumES, coefficientEuclideanEnd,
    twoSiteBondSupportProjection] using hψ

/-- Transporting the equal-sector virtual bond matrix through the common
physical isometry gives the matrix of the canonical direct-sum support
projector.

Source: arXiv:1606.00608, equations `eq:III_isometry` and (3.16)--(3.18),
lines 549--578. -/
theorem transportedVirtualBondMatrix_eq_supportMatrix
    (h : ResidualFamilyAppendixBData B) :
    ((h.physicalIsometryMatrix ⊗ₖ h.physicalIsometryMatrix) *
        h.virtualBondMatrix) *
          (h.physicalIsometryMatrixᴴ ⊗ₖ h.physicalIsometryMatrixᴴ) =
      Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' (twoSiteBondSupportProjection B)) := by
  classical
  rw [← h.sectorSupportSum_eq_twoSiteBondSupportProjection]
  calc
    _ = ∑ j : Fin r,
        ((h.physicalIsometryMatrix ⊗ₖ h.physicalIsometryMatrix) *
          h.embeddedSectorVirtualBondMatrix j) *
            (h.physicalIsometryMatrixᴴ ⊗ₖ h.physicalIsometryMatrixᴴ) := by
      simp [virtualBondMatrix, Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ j : Fin r,
        Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (h.sector j).twoSiteBasicSupportProjection) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [h.transport_embeddedSectorVirtualBondMatrix j]
      exact (h.sectorSupportProjection_matrix j).symm
    _ = Matrix.reindex (finTwoArrowEquiv (Fin d)) (finTwoArrowEquiv (Fin d))
        (LinearMap.toMatrix' h.sectorSupportSum) := by
      ext x y
      simp [sectorSupportSum, Matrix.reindex_apply, Matrix.submatrix_apply,
        Matrix.sum_apply]

/-- The two adjacent lifts of the canonical support projector of the
multiplicity-one direct sum commute on three sites.

Source: arXiv:1606.00608, equations `III_CFI_RFP` and `eq:III_isometry`, lines
543--555, and Appendix B, lines 1305--1307. -/
theorem twoSiteBondSupportProjection_commute_lifts
    (h : ResidualFamilyAppendixBData B) :
    leftPairLift (twoSiteBondSupportProjection B) *
        rightPairLift (twoSiteBondSupportProjection B) =
      rightPairLift (twoSiteBondSupportProjection B) *
        leftPairLift (twoSiteBondSupportProjection B) := by
  have hMatrix :
      appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) *
        appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) =
      appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) *
        appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) := by
    rw [← h.transportedVirtualBondMatrix_eq_supportMatrix]
    exact appendixB_transportedPairMatrices_comm h.physicalIsometryMatrix
      h.virtualBondMatrix
      h.residual.residualFamilyPhysicalIsometryMatrix_isometry
      h.virtualPairMatrices_comm
  apply LinearMap.toMatrix'.injective
  simp only [LinearMap.toMatrix'_mul]
  let e := finThreeArrowEquiv (Fin d)
  apply (Matrix.reindexLinearEquiv ℂ ℂ e e).injective
  simp only [Matrix.coe_reindexLinearEquiv]
  calc
    _ = Matrix.reindex e e
          (LinearMap.toMatrix' (leftPairLift (twoSiteBondSupportProjection B))) *
        Matrix.reindex e e
          (LinearMap.toMatrix' (rightPairLift (twoSiteBondSupportProjection B))) := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        (Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' (leftPairLift (twoSiteBondSupportProjection B)))
          (LinearMap.toMatrix'
            (rightPairLift (twoSiteBondSupportProjection B)))).symm
    _ = appendixBLeftPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) *
        appendixBRightPairMatrix (Matrix.reindex (finTwoArrowEquiv (Fin d))
          (finTwoArrowEquiv (Fin d))
          (LinearMap.toMatrix' (twoSiteBondSupportProjection B))) := by
      rw [leftPairLift_toMatrix_reindex, rightPairLift_toMatrix_reindex]
    _ = _ := hMatrix
    _ = Matrix.reindex e e
          (LinearMap.toMatrix' (rightPairLift (twoSiteBondSupportProjection B))) *
        Matrix.reindex e e
          (LinearMap.toMatrix' (leftPairLift (twoSiteBondSupportProjection B))) := by
      rw [leftPairLift_toMatrix_reindex, rightPairLift_toMatrix_reindex]
    _ = _ := by
      simpa only [Matrix.coe_reindexLinearEquiv] using
        Matrix.reindexLinearEquiv_mul ℂ ℂ e e e
          (LinearMap.toMatrix' (rightPairLift (twoSiteBondSupportProjection B)))
          (LinearMap.toMatrix' (leftPairLift (twoSiteBondSupportProjection B)))

/-- The canonical parent interaction of the multiplicity-one direct sum has
commuting overlapping placements on three sites.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, equations
`III_CFI_RFP` and `eq:III_isometry`, lines 543--555, and Appendix B, lines
1305--1307. -/
theorem hasOverlappingTwoSiteCommutation
    (h : ResidualFamilyAppendixBData B) :
    HasOverlappingTwoSiteCommutation (d := d)
      (parentInteraction (directSumTensor B) 2)
      (parentInteraction (directSumTensor B) 2) := by
  let hSupport : HasOverlappingTwoSiteCommutation (d := d)
      (twoSiteBondSupportProjection B) (twoSiteBondSupportProjection B) :=
    { left_idempotent := twoSiteBondSupportProjection_idempotent B
      right_idempotent := twoSiteBondSupportProjection_idempotent B
      commute_lifts := h.twoSiteBondSupportProjection_commute_lifts }
  have hComplement := hSupport.complement
  simpa [twoSiteBondSupportProjection_eq_complement] using hComplement

/-- The first two translated parent interactions of the direct sum commute
on the three-site chain.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, Theorem 3.10, lines
534--541, and Appendix B, lines 1305--1307. -/
theorem localTerm_two_three_zero_one_commute
    (h : ResidualFamilyAppendixBData B) :
    localTerm (directSumTensor B) 2 3 (0 : Fin 3) *
        localTerm (directSumTensor B) 2 3 (1 : Fin 3) =
      localTerm (directSumTensor B) 2 3 (1 : Fin 3) *
        localTerm (directSumTensor B) 2 3 (0 : Fin 3) :=
  localTerm_two_three_zero_one_commute_of_overlapping_two_site_commutation
    (directSumTensor B) h.hasOverlappingTwoSiteCommutation

/-- The residual-family form gives adjacent two-site commutation on every
periodic chain of length greater than two.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, Theorem 3.10, lines
534--541, and Appendix B, lines 1305--1307. -/
theorem adjacent_twoSite_localTerms_commute
    (h : ResidualFamilyAppendixBData B) {N : ℕ} (hN : 2 < N) (i : Fin N) :
    localTerm (directSumTensor B) 2 N i *
        localTerm (directSumTensor B) 2 N (cyclicForwardSite i 1) =
      localTerm (directSumTensor B) 2 N (cyclicForwardSite i 1) *
        localTerm (directSumTensor B) 2 N i :=
  localTerm_adjacent_twoSite_commute_of_threeSite_zero_one_commute
    h.localTerm_two_three_zero_one_commute (by omega) i

/-- Simultaneous Appendix B data supplies the nearest-neighbor commuting
parent Hamiltonian on every periodic chain of length greater than two.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, Theorem 3.10, lines
534--541, and Appendix B, lines 1305--1307. -/
theorem isNNCPH
    (h : ResidualFamilyAppendixBData B) {N : ℕ} (hN : 2 < N) :
    IsNNCPH (directSumTensor B) N :=
  (HasProductPairLocalProjectors.of_adjacent_twoSite_commute (by omega)
    (h.adjacent_twoSite_localTerms_commute hN)).isNNCPH

end ResidualFamilyAppendixBData

namespace IsBNTCanonicalForm

variable {P : SectorDecomposition d}

/-- A multiplicity-one direct sum of the distinct sectors of an RFP BNT
canonical form has commuting nearest-neighbor parent interactions on every
periodic chain of length greater than two.

Source: arXiv:1606.00608, Definition 3.9, lines 517--524, Theorem 3.10, lines
534--541, equations `III_CFI_RFP` and `eq:III_isometry`, lines 543--555, and
Appendix B, lines 1305--1307.

**Scope restriction (multiplicity-one distinct sectors):** the theorem treats
the direct sum of the BNT basis tensors, with one copy of each distinct
sector. Repeated copies and arbitrary raw sector weights remain outside this
statement; see `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex`. -/
theorem rfp_implies_nncph_basisDirectSum
    (hCF : IsBNTCanonicalForm P)
    (hRFP : IsTransferIdempotent (directSumTensor P.basis))
    (N : ℕ) (hN : 2 < N) :
    IsNNCPH (directSumTensor P.basis) N := by
  obtain ⟨h⟩ := hCF.exists_residualFamilyAppendixBData hRFP
  exact h.isNNCPH hN

end IsBNTCanonicalForm

end MPSTensor
