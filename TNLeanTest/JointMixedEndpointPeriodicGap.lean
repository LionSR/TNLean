import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointPeriodicGap
import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointOrthogonalCorners

/-!
Regression tests for the actual degenerate periodic endpoint. The two
endpoint blocks overlap on their physical alphabet; the shortest ring
retains both directed interactions. Empty block and physical families are
also included. Axiom guards allow only Lean's standard axioms.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open MPSTensor MPSTensor.MPOSymmetry

namespace TNLeanTest.JointMixedEndpointPeriodicGap

private def overlappingEndpoints : Fin 2 → MPSTensor 2 1 :=
  fun x i => if i = 0 then 1 else if x = 1 then 1 else 0

private theorem overlappingEndpoints_span : WordTupleSpanTop overlappingEndpoints 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingEndpoints x 0) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEndpoints x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingEndpoints x 1) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEndpoints x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp [overlappingEndpoints]

-- Both block labels occupy the same physical letter, with nonzero overlap.
example : (∑ i : Fin 2, star (overlappingEndpoints 0 i 0 0) *
    overlappingEndpoints 1 i 0 0) = 1 := by
  norm_num [Fin.sum_univ_two, overlappingEndpoints]

-- Phase corners are orthogonal even though their block columns overlap.
example : Pairwise fun p q : Bool × Bool =>
    (jointMixedEndpointCornerSupport overlappingEndpoints overlappingEndpoints p).IsOrtho
      (jointMixedEndpointCornerSupport overlappingEndpoints overlappingEndpoints q) :=
  jointMixedEndpointCornerSupport_pairwise_isOrtho _ _

-- The canonical comparison is the joint parent of both overlapping blocks.
example :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap 2) =
        (blockPeriodicMpvMapES (jointMixedEndpointLeftTensor overlappingEndpoints 2
          (fun _ => 1)) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_eq _ _ overlappingEndpoints_span
    overlappingEndpoints_span (fun _ => by decide) (by decide)

-- The same kernel is stated directly on the actual enlarged path tensors.
example :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap 2) =
        (blockPeriodicMpvMapES
          (jointMixedEndpointInterpolation overlappingEndpoints overlappingEndpoints 0) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_eq_actual _ _ overlappingEndpoints_span
    overlappingEndpoints_span (fun _ => by decide) (by decide)

-- A common intrinsic gap is derived without supplying individual block gaps.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap N))ᗮ,
      δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap N v‖ :=
  exists_uniform_jointMixedEndpoint_periodic_gap _ _ overlappingEndpoints_span
    overlappingEndpoints_span (fun _ => by decide)

private noncomputable def firstLetter :
    Fin (jointMixedPhysicalDim 2 2 (fun _ : Fin 2 => 1) (fun _ => 1)) :=
  Fintype.equivFin (JointMixedPhysical 2 2 (fun _ : Fin 2 => 1) (fun _ => 1))
    (Sum.inl (0 : Fin 2))

private noncomputable def crossLetter :
    Fin (jointMixedPhysicalDim 2 2 (fun _ : Fin 2 => 1) (fun _ => 1)) :=
  Fintype.equivFin (JointMixedPhysical 2 2 (fun _ : Fin 2 => 1) (fun _ => 1))
    (Sum.inr (Sum.inl ⟨0, ((0 : Fin 1), (0 : Fin 1))⟩))

-- One 01 phase on a two-site ring violates exactly its column constraint.
example : jointMixedPeriodicViolationCount 2 2 (fun _ : Fin 2 => 1) (fun _ => 1) 2
    ![crossLetter, firstLetter] = 1 := by
  norm_num [jointMixedPeriodicViolationCount, Fin.sum_univ_two, jointMixedRowWeight,
    jointMixedColumnWeight, firstLetter, crossLetter]

-- Both directed edges supply the phase penalty even at N = 2.
example : jointMixedPeriodicPhasePenalty 2 2 (fun _ : Fin 2 => 1) (fun _ => 1) 2 ≤
    (2 : ℂ) • periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap 2 :=
  jointMixedPeriodicPhasePenalty_le_twice _ _ (by decide)

-- The exact active operator identity retains every overlap within phase 00.
example :
    periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction overlappingEndpoints
        overlappingEndpoints 0).toLinearMap 2 *
      jointMixedPeriodicActiveProjection 2 2 (fun _ : Fin 2 => 1) (fun _ => 1) 2 =
    parentHamiltonianES (toTensorFromBlocks (μ := fun _ => 1)
      (jointMixedEndpointLeftTensor overlappingEndpoints 2 (fun _ => 1))) 2 2 *
      jointMixedPeriodicActiveProjection 2 2 (fun _ : Fin 2 => 1) (fun _ => 1) 2 :=
  jointMixedEndpoint_periodic_mul_activeProjection _ _ (by decide)

private theorem empty_span {d : ℕ} (A : (x : Fin 0) → MPSTensor d (Fin.elim0 x)) :
    WordTupleSpanTop A 1 := by
  unfold WordTupleSpanTop
  apply top_unique
  intro X _
  have hX : X = 0 := funext fun x => x.elim0
  rw [hX]
  exact Submodule.zero_mem _

-- No nonempty physical alphabet is introduced as a new source assumption.
example (A : (x : Fin 0) → MPSTensor 0 (Fin.elim0 x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction A A 0).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction A A 0).toLinearMap N v‖ :=
  exists_uniform_jointMixedEndpoint_periodic_gap A A (empty_span A) (empty_span A)
    (fun x => x.elim0)

-- Empty labels with a nonempty physical alphabet are covered separately.
example (A : (x : Fin 0) → MPSTensor 1 (Fin.elim0 x)) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A A 0).toLinearMap 2) =
        (blockPeriodicMpvMapES (jointMixedEndpointLeftTensor A 1 Fin.elim0) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_eq A A (empty_span A) (empty_span A)
    (fun x => x.elim0) (by decide)

end TNLeanTest.JointMixedEndpointPeriodicGap

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_eq_iSup_corners'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_eq_iSup_corners
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpointCornerSupport_pairwise_isOrtho'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpointCornerSupport_pairwise_isOrtho
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_ker_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_ker_eq
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_outerCorner_eq_groundSpaceES
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpointLeftTensor_starProjection_eq_outerCorner'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpointLeftTensor_starProjection_eq_outerCorner
/--
info: 'MPSTensor.MPOSymmetry.one_sub_jointMixedPeriodicActiveProjection_le_twice'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.one_sub_jointMixedPeriodicActiveProjection_le_twice
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_mul_activeProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_mul_activeProjection
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_eq
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_eq_actual'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_eq_actual
/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_gap
/--
info: 'LinearMap.IsPositive.norm_gap_of_reducing_projection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearMap.IsPositive.norm_gap_of_reducing_projection

end AxiomChecks
