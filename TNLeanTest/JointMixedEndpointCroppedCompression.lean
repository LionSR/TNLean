import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointCroppedCompression
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFrameReduction

/-! Regressions for actual cropped edge kernels, retaining overlapping
labels, unused bulk directions, empty labels and zero-dimensional crops.
The generic crop test deliberately has support outside the crop range. -/

open scoped Matrix BigOperators Kronecker
open MPSTensor MPSTensor.MPOSymmetry

private def overlappingCropEndpoint : Fin 2 → MPSTensor 3 1 :=
  fun x i => if i = 0 then 1 else if i = 1 ∧ x = 1 then 1 else 0

private theorem overlappingCropEndpoint_span :
    WordTupleSpanTop overlappingCropEndpoint 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingCropEndpoint x 0) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingCropEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingCropEndpoint x 1) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingCropEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp [overlappingCropEndpoint]

-- Both endpoint families have overlapping physical labels, and both
-- virtual sectors are nonzero. The full physical crop is therefore a
-- genuine phase restriction, while the adjacent third letter remains.
example :
    ((jointMixedFirstBoundaryColumns overlappingCropEndpoint overlappingCropEndpoint)ᴴ *
      jointMixedFirstBoundaryColumns overlappingCropEndpoint overlappingCropEndpoint)
        ⟨0, Fin.castAdd 1 0, 0⟩ ⟨1, Fin.castAdd 1 0, 0⟩ = 1 := by
  rw [jointMixedFirstBoundaryColumns_gram_firstSector]
  norm_num [Fin.sum_univ_three, overlappingCropEndpoint]

example :
    let U := jointMixedFirstEdgeIsometry overlappingCropEndpoint overlappingCropEndpoint
      overlappingCropEndpoint_span overlappingCropEndpoint_span
    let S := (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingCropEndpoint overlappingCropEndpoint)
      (fun _ => bondInterpolationMatrix 1 1 0) 2).range
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      jointMixedFirstEdgeCompressedSupportES overlappingCropEndpoint overlappingCropEndpoint :=
  ker_jointMixedFirstEdge_compression_parentInteraction _ _
    overlappingCropEndpoint_span overlappingCropEndpoint_span

example :
    let U := jointMixedLastEdgeIsometry overlappingCropEndpoint overlappingCropEndpoint
      overlappingCropEndpoint_span overlappingCropEndpoint_span
    let e := jointMixedLastEdgeNormalizationEquivES
      overlappingCropEndpoint overlappingCropEndpoint
      overlappingCropEndpoint_span overlappingCropEndpoint_span
    let S := (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingCropEndpoint overlappingCropEndpoint)
      (fun _ => bondInterpolationMatrix 1 1 0) 2).range
    e.symm.deformedConstraintProjection (U.compression (1 - S.starProjection.toLinearMap)) =
      (jointEndpointLastEdgeCoreSupportES overlappingCropEndpoint
        (fun _ => 1 + 1))ᗮ.starProjection.toLinearMap :=
  jointMixedLastEdge_normalize_compression_parentInteraction _ _
    overlappingCropEndpoint_span overlappingCropEndpoint_span

private def zeroSecondCropEndpoint : Fin 2 → MPSTensor 0 0 := fun _ i => Fin.elim0 i

private theorem zeroSecondCropEndpoint_span : WordTupleSpanTop zeroSecondCropEndpoint 1 := by
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hM : M = 0 := Subsingleton.elim _ _
  simp [hM]

-- Vanishing second virtual fibers still give genuine joint polar
-- isometries and the exact compressed kernel.
example :
    let U := jointMixedFirstEdgeIsometry overlappingCropEndpoint zeroSecondCropEndpoint
      overlappingCropEndpoint_span zeroSecondCropEndpoint_span
    let S := (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingCropEndpoint zeroSecondCropEndpoint)
      (fun _ => bondInterpolationMatrix 1 0 0) 2).range
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      jointMixedFirstEdgeCompressedSupportES overlappingCropEndpoint zeroSecondCropEndpoint :=
  ker_jointMixedFirstEdge_compression_parentInteraction _ _
    overlappingCropEndpoint_span zeroSecondCropEndpoint_span

-- Empty labels do not require an inhabitant or a hidden positive dimension.
example {d₀ d₁ : ℕ} {D₀ D₁ : Fin 0 → ℕ}
    (A₀ : (x : Fin 0) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin 0) → MPSTensor d₁ (D₁ x)) :
    LinearMap.ker (jointMixedFirstEdgePhysicalIsometry.compression
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      jointMixedFirstEdgeCroppedSupportES A₀ A₁ :=
  ker_jointMixedFirstPhysical_compression_parentInteraction A₀ A₁

-- An empty first physical alphabet makes the crop domain zero-dimensional.
example {d₁ r : ℕ} {D₀ D₁ : Fin r → ℕ}
    (A₀ : (x : Fin r) → MPSTensor 0 (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    LinearMap.ker (jointMixedFirstEdgePhysicalIsometry.compression
      (1 - (blockInsertedBoundaryMap (jointMixedEndpointBase A₀ A₁)
        (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2).range.starProjection.toLinearMap)) =
      ⊥ := Subsingleton.elim _ _

-- At N = 2 there is one actual interaction. Both boundary polar changes
-- act on that one term; first and last cropped terms are not added.
example :
    let U := jointMixedTwoSitePolarIsometry overlappingCropEndpoint overlappingCropEndpoint
      overlappingCropEndpoint_span overlappingCropEndpoint_span
    let S := (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingCropEndpoint overlappingCropEndpoint)
      (fun _ => bondInterpolationMatrix 1 1 0) 2).range
    U.compression (1 - S.starProjection.toLinearMap) =
      1 - (S.map U.toLinearMap.adjoint).starProjection.toLinearMap :=
  jointMixedTwoSitePolar_compression_parentInteraction _ _
    overlappingCropEndpoint_span overlappingCropEndpoint_span

private def properCrop : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := PiLp.single 2 0 z
  map_add' z w := PiLp.single_add 2 0
  map_smul' z w := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  norm_map' z := PiLp.norm_single 2 (fun _ : Fin 2 => ℂ) 0 z

-- The support in the next regression is genuinely not contained in the
-- crop: the second ambient basis vector has no preimage.
example : ¬ (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) ≤
    LinearMap.range properCrop.toLinearMap := by
  intro h
  obtain ⟨z, hz⟩ := h (show PiLp.single 2 (1 : Fin 2) (1 : ℂ) ∈
    (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))) from trivial)
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hz
  simp [properCrop] at this

example :
    LinearMap.ker (properCrop.compression
      (1 - (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).starProjection.toLinearMap)) =
      (⊤ : Submodule ℂ (EuclideanSpace ℂ (Fin 2))).map properCrop.toLinearMap.adjoint := by
  apply properCrop.ker_compression_one_sub_starProjection_of_commute
  simpa only [Submodule.starProjection_top, ContinuousLinearMap.coe_id, sub_self] using
    (Commute.zero_right (properCrop.toLinearMap ∘ₗ properCrop.toLinearMap.adjoint))

section AxiomGuards
set_option linter.hashCommand false

/--
info: 'LinearIsometry.compression_one_sub_starProjection_of_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearIsometry.compression_one_sub_starProjection_of_commute

/--
info: 'MPSTensor.MPOSymmetry.jointMixedFirstEdgePhysicalIsometry_commute_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedFirstEdgePhysicalIsometry_commute_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.ker_jointMixedFirstEdge_compression_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.ker_jointMixedFirstEdge_compression_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.ker_jointMixedLastEdge_compression_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.ker_jointMixedLastEdge_compression_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.jointMixedFirstEdge_normalize_compression_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedFirstEdge_normalize_compression_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.jointMixedLastEdge_normalize_compression_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedLastEdge_normalize_compression_parentInteraction

end AxiomGuards
