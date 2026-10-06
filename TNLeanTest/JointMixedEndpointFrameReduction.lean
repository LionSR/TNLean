import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointFrameReduction

/-! Regressions for the full actual two-site support and its rectangular
boundary-frame reduction. Labels overlap physically; the second endpoint
fibers may vanish; empty labels and zero first fibers give the zero actual
coefficient map. No kernel-identification premise is supplied. -/

set_option linter.hashCommand false

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open MPSTensor MPSTensor.MPOSymmetry

private def overlappingFrameEndpoint : Fin 2 → MPSTensor 3 1 :=
  fun x i => if i = 0 then 1 else if i = 1 ∧ x = 1 then 1 else 0

private def zeroSecondFrameEndpoint : Fin 2 → MPSTensor 0 0 :=
  fun _ i => Fin.elim0 i

private theorem overlappingFrameEndpoint_span :
    WordTupleSpanTop overlappingFrameEndpoint 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingFrameEndpoint x 0) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingFrameEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingFrameEndpoint x 1) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingFrameEndpoint x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp [overlappingFrameEndpoint]

private theorem zeroSecondFrameEndpoint_span :
    WordTupleSpanTop zeroSecondFrameEndpoint 1 := by
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hM : M = 0 := Subsingleton.elim _ _
  simp [hM]

-- The physical alphabet has a genuinely unused third direction, while
-- both scalar block labels contribute to the same first direction.
example : jointMixedPhysicalDim 3 0 (fun _ : Fin 2 => 1) (fun _ => 0) = 3 := by
  simp [jointMixedPhysicalDim]

example : overlappingFrameEndpoint 0 0 = overlappingFrameEndpoint 1 0 := by
  simp [overlappingFrameEndpoint]

example (x : Fin 2) : overlappingFrameEndpoint x 2 = 0 := by
  simp [overlappingFrameEndpoint]

-- The full trace factorization retains both coherent labels and the
-- original three-letter physical alphabet, with all second fibers zero.
example (X : (x : Fin 2) → Matrix (Fin (1 + 0)) (Fin (1 + 0)) ℂ) :
    blockInsertedGroundSpaceMap
        (jointMixedEndpointBase overlappingFrameEndpoint zeroSecondFrameEndpoint)
        (fun _ => bondInterpolationMatrix 1 0 0) 2 X =
      jointMixedTwoSiteBoundaryColumns overlappingFrameEndpoint zeroSecondFrameEndpoint *ᵥ
        jointMixedTwoSiteBoundaryCoefficients X :=
  blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns _ _ X

-- The support and reducing projection are derived for these actual
-- overlapping tensors, without an orthogonality or commutator premise.
example :
    Commute (jointMixedTwoSiteFrameProjection overlappingFrameEndpoint zeroSecondFrameEndpoint)
      (1 - (blockInsertedBoundaryMap
        (jointMixedEndpointBase overlappingFrameEndpoint zeroSecondFrameEndpoint)
        (fun _ => bondInterpolationMatrix 1 0 0) 2).range.starProjection.toLinearMap) :=
  jointMixedTwoSiteFrameProjection_commute_parentInteraction _ _

example :
    1 - jointMixedTwoSiteFrameProjection overlappingFrameEndpoint zeroSecondFrameEndpoint ≤
      1 - (blockInsertedBoundaryMap
        (jointMixedEndpointBase overlappingFrameEndpoint zeroSecondFrameEndpoint)
        (fun _ => bondInterpolationMatrix 1 0 0) 2).range.starProjection.toLinearMap :=
  one_sub_jointMixedTwoSiteFrameProjection_le_parentInteraction _ _

-- Both boundary changes act on one two-site term. Its actual compressed
-- kernel follows from the support factorization and proved one-site span.
example :
    let U := jointMixedTwoSitePolarIsometry overlappingFrameEndpoint zeroSecondFrameEndpoint
      overlappingFrameEndpoint_span zeroSecondFrameEndpoint_span
    let S := (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingFrameEndpoint zeroSecondFrameEndpoint)
      (fun _ => bondInterpolationMatrix 1 0 0) 2).range
    LinearMap.ker (U.compression (1 - S.starProjection.toLinearMap)) =
      S.map U.toLinearMap.adjoint :=
  ker_jointMixedTwoSitePolar_compression_parentInteraction _ _
    overlappingFrameEndpoint_span zeroSecondFrameEndpoint_span

-- With no block labels, the newly exposed coefficient vector vanishes,
-- so the actual full two-site map is zero on every physical alphabet.
example {d₀ d₁ : ℕ} {D₀ D₁ : Fin 0 → ℕ}
    (A₀ : (x : Fin 0) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin 0) → MPSTensor d₁ (D₁ x)) :
    blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 = 0 := by
  apply LinearMap.ext
  intro X
  change blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) 0) 2 X = 0
  rw [blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns]
  simp [jointMixedTwoSiteBoundaryCoefficients]

-- Zero first fibers kill the contracted bond even if second fibers and
-- both physical alphabets remain arbitrary and nonempty.
example {d₀ d₁ r : ℕ} {D₁ : Fin r → ℕ}
    (A₀ : Fin r → MPSTensor d₀ 0)
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) :
    blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix 0 (D₁ x) 0) 2 = 0 := by
  apply LinearMap.ext
  intro X
  change blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
    (fun x => bondInterpolationMatrix 0 (D₁ x) 0) 2 X = 0
  rw [blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns]
  simp [jointMixedTwoSiteBoundaryCoefficients]

private def properFrame : ℂ →ₗᵢ[ℂ] EuclideanSpace ℂ (Fin 2) where
  toFun z := PiLp.single 2 0 z
  map_add' z w := PiLp.single_add 2 0
  map_smul' z w := by
    apply PiLp.ext
    intro i
    fin_cases i <;> simp
  norm_map' z := PiLp.norm_single 2 (fun _ : Fin 2 => ℂ) 0 z

example : ¬ Function.Surjective properFrame := by
  intro h
  obtain ⟨z, hz⟩ := h (PiLp.single 2 (1 : Fin 2) (1 : ℂ))
  have := congrArg (fun v : EuclideanSpace ℂ (Fin 2) => v 1) hz
  simp [properFrame] at this

-- Compressing the complementary projection of a proper frame gives
-- the zero operator, even though that projection is nonzero physically.
example :
    properFrame.compression
      (1 - (LinearMap.range properFrame.toLinearMap).starProjection.toLinearMap) = 0 := by
  rw [properFrame.compression_one_sub_starProjection_of_le_range _ le_rfl]
  have hmap : (LinearMap.range properFrame.toLinearMap).map
      properFrame.toLinearMap.adjoint = ⊤ := by
    apply top_unique
    intro z _
    exact ⟨properFrame z, ⟨z, rfl⟩, LinearMap.congr_fun properFrame.adjoint_comp_self' z⟩
  simp only [hmap, Submodule.starProjection_top, ContinuousLinearMap.coe_id]
  change (1 : Module.End ℂ ℂ) - 1 = 0
  exact sub_self _

-- A zero-dimensional frame needs neither an inhabitant of a coordinate
-- type nor a surjectivity premise. Its compressed kernel is derived.
example :
    LinearMap.ker ((⊥ : Submodule ℂ ℂ).subtypeₗᵢ.compression (1 : Module.End ℂ ℂ)) =
      (⊥ : Submodule ℂ (⊥ : Submodule ℂ ℂ)) := by
  simpa only [Submodule.starProjection_bot, ContinuousLinearMap.toLinearMap_zero,
    sub_zero, Submodule.map_bot] using
    (⊥ : Submodule ℂ ℂ).subtypeₗᵢ.ker_compression_one_sub_starProjection_of_le_range
      (⊥ : Submodule ℂ ℂ) bot_le

/--
info: 'MPSTensor.MPOSymmetry.blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.blockInsertedGroundSpaceMap_jointMixed_eq_boundaryColumns

/--
info: 'MPSTensor.MPOSymmetry.jointMixedTwoSiteFrameProjection_commute_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedTwoSiteFrameProjection_commute_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.one_sub_jointMixedTwoSiteFrameProjection_le_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.one_sub_jointMixedTwoSiteFrameProjection_le_parentInteraction

/--
info: 'MPSTensor.MPOSymmetry.ker_jointMixedTwoSitePolar_compression_parentInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.ker_jointMixedTwoSitePolar_compression_parentInteraction
