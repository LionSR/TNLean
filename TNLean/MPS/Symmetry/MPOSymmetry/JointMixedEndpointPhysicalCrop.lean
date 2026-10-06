/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointEdgeProjectors
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointReducingSectors
import TNLean.MPS.ParentHamiltonian.Martingale.ReducingParentCompression

/-!
# Physical zero-phase cropping of the actual joint edge

The neighboring bulk site is restricted to the entire shared first
physical alphabet. The two resulting coordinate isometries have range
projections equal to the corresponding products of row and column phase
selectors. The actual phase reduction therefore proves their commutation
with the local parent interaction. Their adjoints recover exactly the
cropped coefficient maps used by the joint boundary normalization.

The full support need not lie in either cropped coordinate range.
No positive dimension or nonempty label hypothesis is used.
Source: GLM23, arXiv:2203.12563, Section 5, lines 1695–1777.
-/

open scoped Matrix BigOperators InnerProductSpace

namespace MPSTensor.MPOSymmetry

noncomputable section

variable {d₀ d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}

private theorem firstPhysical_injective :
    Function.Injective (jointMixedFirstPhysicalIndex (d₀ := d₀) d₁ D₀ D₁) := by
  intro i j h
  exact Sum.inl.inj ((Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).injective h)

/-- Encode a full first site and one shared first-alphabet bulk letter.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgePhysicalEmbedding :
    Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀ ↪
      Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 where
  toFun p := ![p.1, jointMixedFirstPhysicalIndex d₁ D₀ D₁ p.2]
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    exact Prod.ext (by simpa using h₀) (firstPhysical_injective (by simpa using h₁))

/-- Encode one shared first-alphabet bulk letter and a full last site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgePhysicalEmbedding :
    Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) ↪
      Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2 where
  toFun p := ![jointMixedFirstPhysicalIndex d₁ D₀ D₁ p.1, p.2]
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h₀ := congrFun h 0
    have h₁ := congrFun h 1
    exact Prod.ext (firstPhysical_injective (by simpa using h₀)) (by simpa using h₁)

private def cropCoordinateLin {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    EuclideanSpace ℂ ι →ₗ[ℂ] EuclideanSpace ℂ κ := by
  classical
  exact Matrix.toEuclideanLin (Matrix.coordinateInclusion f)

private theorem cropCoordinateLin_adjoint_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ)
    (v : EuclideanSpace ℂ κ) (i : ι) :
    (cropCoordinateLin f).adjoint v i = v (f i) := by
  classical
  rw [cropCoordinateLin, ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  simp [Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, Matrix.coordinateInclusion]

private theorem cropCoordinateLin_apply_image
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ)
    (v : EuclideanSpace ℂ ι) (i : ι) :
    cropCoordinateLin f v (f i) = v i := by
  classical
  simp [cropCoordinateLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Matrix.coordinateInclusion, f.injective.eq_iff]

private theorem cropCoordinateLin_apply_outside
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ)
    (v : EuclideanSpace ℂ ι) (j : κ) (hj : j ∉ Set.range f) :
    cropCoordinateLin f v j = 0 := by
  classical
  have hne : ∀ i, j ≠ f i := fun i h => hj ⟨i, h.symm⟩
  simp [cropCoordinateLin, Matrix.toEuclideanLin, Matrix.toLpLin_apply, Matrix.mulVec,
    dotProduct, Matrix.coordinateInclusion, hne]

private theorem cropCoordinateLin_adjoint_comp
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    (cropCoordinateLin f).adjoint ∘ₗ cropCoordinateLin f = LinearMap.id := by
  ext v i
  rw [LinearMap.comp_apply, cropCoordinateLin_adjoint_apply, cropCoordinateLin_apply_image]
  rfl

private def cropCoordinateIsometry
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ) :
    EuclideanSpace ℂ ι →ₗᵢ[ℂ] EuclideanSpace ℂ κ :=
  (cropCoordinateLin f).isometryOfInner fun v w => by
    rw [← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
      cropCoordinateLin_adjoint_comp, LinearMap.id_apply]

open Classical in
private theorem cropCoordinateLin_projection_apply
    {ι κ : Type*} [Fintype ι] [Fintype κ] (f : ι ↪ κ)
    (v : EuclideanSpace ℂ κ) (j : κ) :
    (cropCoordinateLin f ∘ₗ (cropCoordinateLin f).adjoint) v j =
      if j ∈ Set.range f then v j else 0 := by
  classical
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i, rfl⟩ := hj
    simp [LinearMap.comp_apply, cropCoordinateLin_apply_image, cropCoordinateLin_adjoint_apply]
  · simp [LinearMap.comp_apply, cropCoordinateLin_apply_outside f _ j hj, hj]

/-- The first-edge physical crop as a genuine coordinate isometry.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgePhysicalIsometry :
    EuclideanSpace ℂ (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  cropCoordinateIsometry jointMixedFirstEdgePhysicalEmbedding

/-- The reflected last-edge physical crop as a coordinate isometry.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgePhysicalIsometry :
    EuclideanSpace ℂ (Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) →ₗᵢ[ℂ]
      EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :=
  cropCoordinateIsometry jointMixedLastEdgePhysicalEmbedding

/-- The first adjoint reads the full first-site coefficient and the
specified shared physical letter at the second site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgePhysicalIsometry_adjoint_apply
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2))
    (i : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) (j : Fin d₀) :
    jointMixedFirstEdgePhysicalIsometry.toLinearMap.adjoint v (i, j) =
      v ![i, jointMixedFirstPhysicalIndex d₁ D₀ D₁ j] :=
  cropCoordinateLin_adjoint_apply _ _ _

/-- The last adjoint has the reflected coefficient formula.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgePhysicalIsometry_adjoint_apply
    (v : EuclideanSpace ℂ (Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2))
    (i : Fin d₀) (j : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    jointMixedLastEdgePhysicalIsometry.toLinearMap.adjoint v (i, j) =
      v ![jointMixedFirstPhysicalIndex d₁ D₀ D₁ i, j] :=
  cropCoordinateLin_adjoint_apply _ _ _

private theorem firstPhysical_mem_range_iff
    (p : Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁)) :
    p ∈ Set.range (jointMixedFirstPhysicalIndex d₁ D₀ D₁) ↔
      jointMixedRowWeight p = 1 ∧ jointMixedColumnWeight p = 1 := by
  rw [jointMixedRowColumnWeight_eq_one_iff]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, by simp [jointMixedFirstPhysicalIndex]⟩
  · rintro ⟨i, hi⟩
    refine ⟨i, ?_⟩
    apply (Fintype.equivFin (JointMixedPhysical d₀ d₁ D₀ D₁)).symm.injective
    simpa [jointMixedFirstPhysicalIndex] using hi.symm

private theorem firstEdge_mem_range_iff
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :
    σ ∈ Set.range jointMixedFirstEdgePhysicalEmbedding ↔
      jointMixedRowWeight (σ 1) = 1 ∧ jointMixedColumnWeight (σ 1) = 1 := by
  rw [← firstPhysical_mem_range_iff]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨j, rfl⟩
  · rintro ⟨j, hj⟩
    refine ⟨(σ 0, j), ?_⟩
    funext k
    fin_cases k <;> simp [jointMixedFirstEdgePhysicalEmbedding, hj]

private theorem lastEdge_mem_range_iff
    (σ : Cfg (jointMixedPhysicalDim d₀ d₁ D₀ D₁) 2) :
    σ ∈ Set.range jointMixedLastEdgePhysicalEmbedding ↔
      jointMixedRowWeight (σ 0) = 1 ∧ jointMixedColumnWeight (σ 0) = 1 := by
  rw [← firstPhysical_mem_range_iff]
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, hi⟩
    refine ⟨(i, σ 1), ?_⟩
    funext k
    fin_cases k <;> simp [jointMixedLastEdgePhysicalEmbedding, hi]

/-- The first physical crop projects onto the full physical-00 sector at
the neighboring site, including unused first-alphabet directions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgePhysicalIsometry_comp_adjoint :
    jointMixedFirstEdgePhysicalIsometry.toLinearMap ∘ₗ
        jointMixedFirstEdgePhysicalIsometry.toLinearMap.adjoint =
      jointMixedRowSector d₀ d₁ D₀ D₁ (1 : Fin 2) *
        jointMixedColumnSector d₀ d₁ D₀ D₁ (1 : Fin 2) := by
  ext v σ
  change (cropCoordinateLin jointMixedFirstEdgePhysicalEmbedding ∘ₗ
    (cropCoordinateLin jointMixedFirstEdgePhysicalEmbedding).adjoint) v σ = _
  rw [cropCoordinateLin_projection_apply, firstEdge_mem_range_iff]
  simp only [Module.End.mul_apply, jointMixedRowSector_apply, jointMixedColumnSector_apply]
  rcases jointMixedRowWeight_eq_zero_or_one (σ 1) with hR | hR <;>
    rcases jointMixedColumnWeight_eq_zero_or_one (σ 1) with hC | hC <;> simp [hR, hC]

/-- The reflected crop is the physical-00 projection at the first site.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgePhysicalIsometry_comp_adjoint :
    jointMixedLastEdgePhysicalIsometry.toLinearMap ∘ₗ
        jointMixedLastEdgePhysicalIsometry.toLinearMap.adjoint =
      jointMixedRowSector d₀ d₁ D₀ D₁ (0 : Fin 2) *
        jointMixedColumnSector d₀ d₁ D₀ D₁ (0 : Fin 2) := by
  ext v σ
  change (cropCoordinateLin jointMixedLastEdgePhysicalEmbedding ∘ₗ
    (cropCoordinateLin jointMixedLastEdgePhysicalEmbedding).adjoint) v σ = _
  rw [cropCoordinateLin_projection_apply, lastEdge_mem_range_iff]
  simp only [Module.End.mul_apply, jointMixedRowSector_apply, jointMixedColumnSector_apply]
  rcases jointMixedRowWeight_eq_zero_or_one (σ 0) with hR | hR <;>
    rcases jointMixedColumnWeight_eq_zero_or_one (σ 0) with hC | hC <;> simp [hR, hC]

/-- The first crop reduces the actual support projector, by the proved
row and column phase commutators rather than a support-containment premise.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstEdgePhysicalIsometry_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedFirstEdgePhysicalIsometry.toLinearMap ∘ₗ
      jointMixedFirstEdgePhysicalIsometry.toLinearMap.adjoint)
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0)
          2).range.starProjection.toLinearMap) := by
  rw [jointMixedFirstEdgePhysicalIsometry_comp_adjoint]
  exact (Commute.one_right _).sub_right
    ((jointMixedRowSector_commute_extendedSupport_starProjection A₀ A₁ 1).mul_left
      (jointMixedColumnSector_commute_extendedSupport_starProjection A₀ A₁ 1))

/-- The last crop likewise reduces the actual endpoint interaction.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastEdgePhysicalIsometry_commute_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Commute (jointMixedLastEdgePhysicalIsometry.toLinearMap ∘ₗ
      jointMixedLastEdgePhysicalIsometry.toLinearMap.adjoint)
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0)
          2).range.starProjection.toLinearMap) := by
  rw [jointMixedLastEdgePhysicalIsometry_comp_adjoint]
  exact (Commute.one_right _).sub_right
    ((jointMixedRowSector_commute_extendedSupport_starProjection A₀ A₁ 0).mul_left
      (jointMixedColumnSector_commute_extendedSupport_starProjection A₀ A₁ 0))

/-- The actual first cropped support in Euclidean physical coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedFirstEdgeCroppedSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀)) :=
  (jointMixedFirstEdgeBoundaryMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ
      (Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) × Fin d₀ → ℂ)).symm.toLinearMap

/-- The actual last cropped support in Euclidean physical coordinates.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
def jointMixedLastEdgeCroppedSupportES
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    Submodule ℂ (EuclideanSpace ℂ (Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁))) :=
  (jointMixedLastEdgeBoundaryMap A₀ A₁).range.map
    (WithLp.linearEquiv 2 ℂ
      (Fin d₀ × Fin (jointMixedPhysicalDim d₀ d₁ D₀ D₁) → ℂ)).symm.toLinearMap

/-- Cropping the actual first-edge support by the true Hilbert adjoint
gives exactly the coefficient support, in both directions.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedSupport_firstPhysicalAdjoint
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.map
        jointMixedFirstEdgePhysicalIsometry.toLinearMap.adjoint =
      jointMixedFirstEdgeCroppedSupportES A₀ A₁ := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨_, ⟨blockBoundaryEquiv w, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, j⟩
    rw [jointMixedFirstEdgePhysicalIsometry_adjoint_apply]
    rfl
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨_, ⟨blockBoundaryEquiv.symm X, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, j⟩
    rw [jointMixedFirstEdgePhysicalIsometry_adjoint_apply]
    change blockInsertedGroundSpaceMap _ _ 2 (blockBoundaryEquiv (blockBoundaryEquiv.symm X)) _ = _
    rw [blockBoundaryEquiv.apply_symm_apply]
    rfl

/-- The reflected Hilbert-adjoint image is exactly the last coefficient
support, without assuming that the uncropped support is contained in it.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem map_jointMixedSupport_lastPhysicalAdjoint
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.map
        jointMixedLastEdgePhysicalIsometry.toLinearMap.adjoint =
      jointMixedLastEdgeCroppedSupportES A₀ A₁ := by
  ext v
  constructor
  · rintro ⟨_, ⟨w, rfl⟩, rfl⟩
    refine ⟨_, ⟨blockBoundaryEquiv w, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, j⟩
    rw [jointMixedLastEdgePhysicalIsometry_adjoint_apply]
    rfl
  · rintro ⟨_, ⟨X, rfl⟩, rfl⟩
    refine ⟨_, ⟨blockBoundaryEquiv.symm X, rfl⟩, ?_⟩
    apply PiLp.ext
    rintro ⟨i, j⟩
    rw [jointMixedLastEdgePhysicalIsometry_adjoint_apply]
    change blockInsertedGroundSpaceMap _ _ 2 (blockBoundaryEquiv (blockBoundaryEquiv.symm X)) _ = _
    rw [blockBoundaryEquiv.apply_symm_apply]
    rfl

/-- The actual first interaction compressed to the neighboring physical-00
alphabet is the parent projection of the cropped coefficient support.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedFirstPhysical_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedFirstEdgePhysicalIsometry.compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap) =
      1 - (jointMixedFirstEdgeCroppedSupportES A₀ A₁).starProjection.toLinearMap := by
  rw [LinearIsometry.compression_one_sub_starProjection_of_commute _ _
    (jointMixedFirstEdgePhysicalIsometry_commute_parentInteraction A₀ A₁),
    map_jointMixedSupport_firstPhysicalAdjoint]

/-- The reflected actual compression is the last cropped parent projection.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem jointMixedLastPhysical_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    jointMixedLastEdgePhysicalIsometry.compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap) =
      1 - (jointMixedLastEdgeCroppedSupportES A₀ A₁).starProjection.toLinearMap := by
  rw [LinearIsometry.compression_one_sub_starProjection_of_commute _ _
    (jointMixedLastEdgePhysicalIsometry_commute_parentInteraction A₀ A₁),
    map_jointMixedSupport_lastPhysicalAdjoint]

/-- The first physical compression has exactly the actual cropped support
as kernel; no containment of the full support in the crop is asserted.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_jointMixedFirstPhysical_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    LinearMap.ker (jointMixedFirstEdgePhysicalIsometry.compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      jointMixedFirstEdgeCroppedSupportES A₀ A₁ := by
  rw [LinearIsometry.ker_compression_one_sub_starProjection_of_commute _ _
    (jointMixedFirstEdgePhysicalIsometry_commute_parentInteraction A₀ A₁),
    map_jointMixedSupport_firstPhysicalAdjoint]

/-- The last physical compression has the reflected cropped coefficient
support as its kernel, also for empty alphabets or virtual sectors.
Source: arXiv:2203.12563, Section 5, lines 1695–1777. -/
theorem ker_jointMixedLastPhysical_compression_parentInteraction
    (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    LinearMap.ker (jointMixedLastEdgePhysicalIsometry.compression
        (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
          (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      jointMixedLastEdgeCroppedSupportES A₀ A₁ := by
  rw [LinearIsometry.ker_compression_one_sub_starProjection_of_commute _ _
    (jointMixedLastEdgePhysicalIsometry_commute_parentInteraction A₀ A₁),
    map_jointMixedSupport_lastPhysicalAdjoint]

end

end MPSTensor.MPOSymmetry
