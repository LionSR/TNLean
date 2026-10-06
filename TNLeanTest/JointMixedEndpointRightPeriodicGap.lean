import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointRightPeriodicGap

/-!
Strict regression for the second joint periodic endpoint. The endpoint
alphabets have different sizes, their block vectors overlap, and the
rectangular swap retains the order of unequal virtual coordinates.
The terminal statements include two-site rings and empty dimensions.
-/

open scoped Matrix BigOperators InnerProductSpace ComplexOrder
open MPSTensor MPSTensor.MPOSymmetry

namespace TNLeanTest.JointMixedEndpointRightPeriodicGap

private def overlappingEndpoints (d : ℕ) : Fin 2 → MPSTensor d 1 :=
  fun x i => if i.val = 1 then if x = 1 then 1 else 0 else 1

private theorem overlappingEndpoints_span {d : ℕ} (hd : 2 ≤ d) :
    WordTupleSpanTop (overlappingEndpoints d) 1 := by
  classical
  rw [wordTupleSpanTop_one_iff]
  apply top_unique
  intro M _
  have hzero : (fun x => overlappingEndpoints d x ⟨0, by omega⟩) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEndpoints d x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hone : (fun x => overlappingEndpoints d x ⟨1, by omega⟩) ∈
      Submodule.span ℂ (Set.range fun i => fun x => overlappingEndpoints d x i) :=
    Submodule.subset_span (Set.mem_range_self _)
  have hcomb := Submodule.add_mem _
    (Submodule.smul_mem _ (M 0 0 0) hzero)
    (Submodule.smul_mem _ (M 1 0 0 - M 0 0 0) hone)
  convert hcomb using 1
  funext x a b
  fin_cases x <;> fin_cases a <;> fin_cases b <;> simp [overlappingEndpoints]

-- Both endpoint families overlap physically; the extra third letter is nonzero.
example : (∑ i : Fin 2, star (overlappingEndpoints 2 0 i 0 0) *
    overlappingEndpoints 2 1 i 0 0) = 1 := by
  norm_num [Fin.sum_univ_two, overlappingEndpoints]

example : (∑ i : Fin 3, star (overlappingEndpoints 3 0 i 0 0) *
    overlappingEndpoints 3 1 i 0 0) = 2 := by
  norm_num [Fin.sum_univ_three, overlappingEndpoints]

-- A rectangular 01 letter becomes 10 with the same ordered tuple (0,1).
example : jointMixedPhysicalSwap 2 3 (fun _ : Fin 2 => 1) (fun _ => 2)
    (Sum.inr (Sum.inl ⟨0, ((0 : Fin 1), (1 : Fin 2))⟩)) =
      Sum.inr (Sum.inr (Sum.inl ⟨0, ((0 : Fin 1), (1 : Fin 2))⟩)) := rfl

-- Unequal virtual dimensions require the genuine summand permutation.
example (A₀ : Fin 2 → MPSTensor 2 1) (A₁ : Fin 2 → MPSTensor 3 2)
    (x : Fin 2)
    (p : Fin (jointMixedPhysicalDim 2 3 (fun _ : Fin 2 => 1) (fun _ => 2))) :
    jointMixedEndpointBase A₁ A₀ x
        (jointMixedEndpointPhysicalSwap 2 3 (fun _ : Fin 2 => 1) (fun _ => 2) p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap 1 2)
        (jointMixedEndpointBase A₀ A₁ x p) :=
  jointMixedEndpointBase_swap A₀ A₁ x p

-- Parameter reflection is valid without injectivity or interval hypotheses.
example (A₀ : Fin 2 → MPSTensor 2 1) (A₁ : Fin 2 → MPSTensor 3 2)
    (γ : ℝ) (x : Fin 2)
    (p : Fin (jointMixedPhysicalDim 2 3 (fun _ : Fin 2 => 1) (fun _ => 2))) :
    jointMixedEndpointInterpolation A₁ A₀ (1 - γ) x
        (jointMixedEndpointPhysicalSwap 2 3 (fun _ : Fin 2 => 1) (fun _ => 2) p) =
      Matrix.reindexAlgEquiv ℂ ℂ (mixedEndpointBondSwap 1 2)
        (jointMixedEndpointInterpolation A₀ A₁ γ x p) :=
  jointMixedEndpointInterpolation_reflect_swap A₀ A₁ γ x p

-- Conjugacy preserves the full two-site periodic sum at any real parameter.
example (γ : ℝ) :
    periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
        (overlappingEndpoints 3) γ).toLinearMap 2 =
      (physicalReindexLinearIsometryEquiv
        (jointMixedEndpointPhysicalSwap 2 3 (fun _ : Fin 2 => 1) (fun _ => 1))
          2).toLinearEquiv.conj
        (periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction (overlappingEndpoints 3)
            (overlappingEndpoints 2) (1 - γ)).toLinearMap 2) :=
  jointMixedEndpoint_periodic_eq_conj_reflect_swap _ _ γ 2

-- The shortest ring has exactly the actual second-endpoint component span.
example :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
        (overlappingEndpoints 3) 1).toLinearMap 2) =
      (blockPeriodicMpvMapES
        (jointMixedEndpointInterpolation (overlappingEndpoints 2)
          (overlappingEndpoints 3) 1) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_one_eq_actual _ _
    (overlappingEndpoints_span (by decide : 2 ≤ 2))
    (overlappingEndpoints_span (by decide : 2 ≤ 3))
    (fun _ => by decide) (by decide)

-- The combined kernel theorem has the same actual component family at each endpoint.
example (γ : ℝ) (hγ : γ = 0 ∨ γ = 1) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
        (overlappingEndpoints 3) γ).toLinearMap 2) =
      (blockPeriodicMpvMapES
        (jointMixedEndpointInterpolation (overlappingEndpoints 2)
          (overlappingEndpoints 3) γ) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_endpoints_eq_actual _ _
    (overlappingEndpoints_span (by decide : 2 ≤ 2))
    (overlappingEndpoints_span (by decide : 2 ≤ 3))
    (fun _ => by decide) (fun _ => by decide) γ hγ (by decide)

-- The second-endpoint gap is intrinsic and uniform over every ring N≥2.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ N : ℕ, 2 ≤ N →
    ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
        (overlappingEndpoints 3) 1).toLinearMap N))ᗮ,
      δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
          (overlappingEndpoints 3) 1).toLinearMap N v‖ :=
  exists_uniform_jointMixedEndpoint_periodic_one_gap _ _
    (overlappingEndpoints_span (by decide : 2 ≤ 2))
    (overlappingEndpoints_span (by decide : 2 ≤ 3)) (fun _ => by decide)

-- One constant covers both actual periodic endpoints of this joint family.
example : ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ, γ = 0 ∨ γ = 1 →
    ∀ N : ℕ, 2 ≤ N →
      ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
        (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
          (overlappingEndpoints 3) γ).toLinearMap N))ᗮ,
        δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction (overlappingEndpoints 2)
            (overlappingEndpoints 3) γ).toLinearMap N v‖ :=
  exists_uniform_jointMixedEndpoint_periodic_endpoints_gap _ _
    (overlappingEndpoints_span (by decide : 2 ≤ 2))
    (overlappingEndpoints_span (by decide : 2 ≤ 3))
    (fun _ => by decide) (fun _ => by decide)

private theorem zeroBond_span {d r : ℕ} (A : Fin r → MPSTensor d 0) :
    WordTupleSpanTop A 1 := by
  unfold WordTupleSpanTop
  apply top_unique
  intro X _
  have hX : X = 0 := by
    funext x a
    exact a.elim0
  rw [hX]
  exact Submodule.zero_mem _

-- Endpoint one requires positivity only of D₁, allowing D₀=0 and d₀=0.
example (A₀ : Fin 2 → MPSTensor 0 0) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₀ (overlappingEndpoints 3) 1).toLinearMap 2) =
      (blockPeriodicMpvMapES
        (jointMixedEndpointInterpolation A₀ (overlappingEndpoints 3) 1) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_one_eq_actual A₀ _ (zeroBond_span A₀)
    (overlappingEndpoints_span (by decide : 2 ≤ 3)) (fun _ => by decide) (by decide)

private theorem empty_span {d : ℕ} (A : (x : Fin 0) → MPSTensor d (Fin.elim0 x)) :
    WordTupleSpanTop A 1 := by
  unfold WordTupleSpanTop
  apply top_unique
  intro X _
  have hX : X = 0 := funext fun x => x.elim0
  rw [hX]
  exact Submodule.zero_mem _

-- Empty labels remain valid with two different nonempty physical alphabets.
example (A₀ : (x : Fin 0) → MPSTensor 1 (Fin.elim0 x))
    (A₁ : (x : Fin 0) → MPSTensor 2 (Fin.elim0 x)) :
    LinearMap.ker (periodicInteractionHamiltonianES
      (jointMixedEndpointParentInteraction A₀ A₁ 1).toLinearMap 2) =
      (blockPeriodicMpvMapES (jointMixedEndpointInterpolation A₀ A₁ 1) 2).range :=
  jointMixedEndpoint_periodic_groundSpace_one_eq_actual A₀ A₁
    (empty_span A₀) (empty_span A₁) (fun x => x.elim0) (by decide)

-- No nonempty physical alphabet assumption is introduced by the conjugacy.
example (A : (x : Fin 0) → MPSTensor 0 (Fin.elim0 x)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ γ : ℝ, γ = 0 ∨ γ = 1 →
      ∀ N : ℕ, 2 ≤ N →
        ∀ v ∈ (LinearMap.ker (periodicInteractionHamiltonianES
          (jointMixedEndpointParentInteraction A A γ).toLinearMap N))ᗮ,
          δ * ‖v‖ ≤ ‖periodicInteractionHamiltonianES
            (jointMixedEndpointParentInteraction A A γ).toLinearMap N v‖ :=
  exists_uniform_jointMixedEndpoint_periodic_endpoints_gap A A (empty_span A) (empty_span A)
    (fun x => x.elim0) (fun x => x.elim0)

end TNLeanTest.JointMixedEndpointRightPeriodicGap

section AxiomChecks

set_option linter.hashCommand false

/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpointBase_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpointBase_swap
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpointInterpolation_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpointInterpolation_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.blockInsertedBoundaryMap_jointMixed_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.blockInsertedBoundaryMap_jointMixed_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_eq_map_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedSupport_eq_map_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpointParentInteraction_eq_conj_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpointParentInteraction_eq_conj_reflect_swap
/--
info: 'MPSTensor.periodicInteractionHamiltonianES_physicalReindex_conj'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.periodicInteractionHamiltonianES_physicalReindex_conj
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_eq_conj_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_eq_conj_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.mpv_jointMixedEndpointInterpolation_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mpv_jointMixedEndpointInterpolation_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.blockPeriodicMpvMapES_jointMixed_reflect_swap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.blockPeriodicMpvMapES_jointMixed_reflect_swap
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_one_eq_actual'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_one_eq_actual
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_endpoints_eq_actual'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_periodic_groundSpace_endpoints_eq_actual
/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_one_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_one_gap
/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_endpoints_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_jointMixedEndpoint_periodic_endpoints_gap
/--
info: 'LinearIsometryEquiv.norm_gap_iff_of_conj'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearIsometryEquiv.norm_gap_iff_of_conj

end AxiomChecks
