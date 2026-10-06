import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointOpenSectorPenalty

/-! Regressions for the actual joint open active projection. The two scalar
labels overlap physically, the second endpoint fibers vanish, and the first
physical alphabet has an unused direction. Separate instances retain empty
labels and zero first dimensions. No support, commutator, sector-penalty,
or spectral-gap premise is supplied. -/

open scoped Matrix ComplexOrder
open MPSTensor MPSTensor.MPOSymmetry

private def overlappingEndpoint : Fin 2 → MPSTensor 3 1 :=
  fun x i => if i = 0 then 1 else if i = 1 ∧ x = 1 then 1 else 0

private def zeroSecondEndpoint : Fin 2 → MPSTensor 0 0 :=
  fun _ i => Fin.elim0 i

example : overlappingEndpoint 0 0 = overlappingEndpoint 1 0 := by
  simp [overlappingEndpoint]

example (x : Fin 2) : overlappingEndpoint x 2 = 0 := by
  simp [overlappingEndpoint]

-- The shortest longer-chain case has one shared physical interior site.
example :
    (jointMixedOpenActiveProjection overlappingEndpoint zeroSecondEndpoint 0).IsSymmetricProjection :=
  jointMixedOpenActiveProjection_isSymmetricProjection _ _ 0

example :
    Commute (jointMixedOpenActiveProjection overlappingEndpoint zeroSecondEndpoint 0)
      (openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction overlappingEndpoint zeroSecondEndpoint 0).toLinearMap 3) :=
  jointMixedOpenActiveProjection_commute_openInteraction _ _ 0

example (n : ℕ) :
    1 - jointMixedOpenActiveProjection overlappingEndpoint zeroSecondEndpoint n ≤
      openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction overlappingEndpoint zeroSecondEndpoint 0).toLinearMap
          (n + 3) :=
  one_sub_jointMixedOpenActiveProjection_le_openInteraction _ _ n

-- The active interior retains all three original physical directions,
-- including the unused one. It is not replaced by the one-site MPS span.
example (v : EuclideanSpace ℂ
    (Cfg (jointMixedPhysicalDim 3 0 (fun _ : Fin 2 => 1) (fun _ => 0)) 4)) :
    v ∈ LinearMap.range (jointMixedOpenActiveProjection overlappingEndpoint zeroSecondEndpoint 1) ↔
      siteMatrixES (jointMixedFirstFrameProjectionMatrix overlappingEndpoint zeroSecondEndpoint)
        (0 : Fin 4) v = v ∧
      siteMatrixES (jointMixedLastFrameProjectionMatrix overlappingEndpoint zeroSecondEndpoint)
        (Fin.last 3) v = v ∧
      ∀ k : Fin 2,
        jointMixedRowSector 3 0 (fun _ : Fin 2 => 1) (fun _ => 0) k.succ.castSucc v = v ∧
        jointMixedColumnSector 3 0 (fun _ : Fin 2 => 1) (fun _ => 0) k.succ.castSucc v = v :=
  mem_range_jointMixedOpenActiveProjection_iff _ _ 1 v

-- With no labels, the same construction and penalty are still defined.
example {d₀ d₁ : ℕ} {D₀ D₁ : Fin 0 → ℕ}
    (A₀ : (x : Fin 0) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin 0) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    1 - jointMixedOpenActiveProjection A₀ A₁ n ≤
      (2 : ℂ) • openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3) :=
  one_sub_jointMixedOpenActiveProjection_le_twice_openInteraction A₀ A₁ n

-- Zero first fibers are allowed even with nonzero second endpoint fibers.
example {d₀ d₁ r : ℕ} {D₁ : Fin r → ℕ}
    (A₀ : Fin r → MPSTensor d₀ 0)
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x)) (n : ℕ) :
    Commute (jointMixedOpenActiveProjection A₀ A₁ n)
      (openInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A₀ A₁ 0).toLinearMap (n + 3)) :=
  jointMixedOpenActiveProjection_commute_openInteraction A₀ A₁ n

-- The two-site chain is a single full-frame term.
example :
    Commute (jointMixedTwoSiteFrameProjection overlappingEndpoint zeroSecondEndpoint)
        (openInteractionHamiltonianES
          (jointMixedEndpointParentInteraction overlappingEndpoint zeroSecondEndpoint 0).toLinearMap 2) ∧
      1 - jointMixedTwoSiteFrameProjection overlappingEndpoint zeroSecondEndpoint ≤
        openInteractionHamiltonianES
          (jointMixedEndpointParentInteraction overlappingEndpoint zeroSecondEndpoint 0).toLinearMap 2 :=
  jointMixedTwoSiteFrameProjection_openInteraction_reduction _ _

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'MPSTensor.periodicLocalInteractionES_eq_embedOp'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.periodicLocalInteractionES_eq_embedOp

/--
info: 'MPSTensor.MPOSymmetry.range_blockInsertedBoundaryMap_jointMixed_le_firstOneSidedProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.range_blockInsertedBoundaryMap_jointMixed_le_firstOneSidedProjection

/--
info: 'MPSTensor.MPOSymmetry.range_blockInsertedBoundaryMap_jointMixed_le_lastOneSidedProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.range_blockInsertedBoundaryMap_jointMixed_le_lastOneSidedProjection

/--
info: 'MPSTensor.MPOSymmetry.jointMixedOpenBondProjection_commute'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedOpenBondProjection_commute

/--
info: 'MPSTensor.MPOSymmetry.jointMixedOpenActiveProjection_isSymmetricProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedOpenActiveProjection_isSymmetricProjection

/--
info: 'MPSTensor.MPOSymmetry.mem_range_jointMixedOpenActiveProjection_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mem_range_jointMixedOpenActiveProjection_iff

/--
info: 'MPSTensor.MPOSymmetry.one_sub_jointMixedOpenActiveProjection_le_openInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.one_sub_jointMixedOpenActiveProjection_le_openInteraction

/--
info: 'MPSTensor.MPOSymmetry.jointMixedOpenActiveProjection_commute_openInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedOpenActiveProjection_commute_openInteraction

/--
info: 'MPSTensor.MPOSymmetry.one_sub_jointMixedOpenActiveProjection_le_twice_openInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.one_sub_jointMixedOpenActiveProjection_le_twice_openInteraction

/--
info: 'MPSTensor.MPOSymmetry.jointMixedTwoSiteFrameProjection_openInteraction_reduction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedTwoSiteFrameProjection_openInteraction_reduction

end AxiomChecks
