import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSupport

/-! Regressions for the actual mixed family with shared endpoint alphabets.
The two scalar endpoint columns below overlap physically while jointly spanning.
The physical dimension counts each endpoint alphabet once, and the two singular
parameters retain the full joint extended support. -/

set_option linter.hashCommand false

open scoped Matrix BigOperators
open MPSTensor MPSTensor.MPOSymmetry

variable {d₀ d₁ r N : ℕ} {D₀ D₁ : Fin r → ℕ}

example (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1) :
    WordTupleSpanTop (jointMixedEndpointBase A₀ A₁) 1 :=
  wordTupleSpanTop_jointMixedEndpointBase A₀ A₁ h₀ h₁

example (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    (h₀ : WordTupleSpanTop A₀ 1) (h₁ : WordTupleSpanTop A₁ 1)
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    WordTupleSpanTop (jointMixedEndpointInterpolation A₀ A₁ γ) 1 :=
  wordTupleSpanTop_jointMixedEndpointInterpolation A₀ A₁ h₀ h₁ hγ

example (A₀ : (x : Fin r) → MPSTensor d₀ (D₀ x))
    (A₁ : (x : Fin r) → MPSTensor d₁ (D₁ x))
    {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) (hN : 0 < N) :
    (blockInsertedGroundSpaceMap (jointMixedEndpointBase A₀ A₁)
      (fun x => bondInterpolationMatrix (D₀ x) (D₁ x) γ) N).range =
        ⨆ x, groundSpace (jointMixedEndpointInterpolation A₀ A₁ γ x) N :=
  jointMixedEndpoint_extendedGroundSpace_eq_iSup A₀ A₁ hγ hN

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

-- Two shared two-letter endpoint alphabets plus four cross-corner letters.
example : jointMixedPhysicalDim 2 2 (fun _ : Fin 2 => 1) (fun _ => 1) = 8 := by
  rw [jointMixedPhysicalDim_eq]
  decide

-- The same 00 physical letter is nonzero in both distinct block labels.
example :
    jointMixedEndpointLetter overlappingEndpoints overlappingEndpoints (.inl 0)
      0 (.inl 0) (.inl 0) = 1 ∧
    jointMixedEndpointLetter overlappingEndpoints overlappingEndpoints (.inl 0)
      1 (.inl 0) (.inl 0) = 1 := by
  simp [jointMixedEndpointLetter, overlappingEndpoints, Matrix.fromBlocks]

-- The shared endpoint physical columns are not orthogonal.
example : (∑ i : Fin 2, star (overlappingEndpoints 0 i 0 0) *
    overlappingEndpoints 1 i 0 0) = 1 := by
  norm_num [Fin.sum_univ_two, overlappingEndpoints]

example : WordTupleSpanTop
    (jointMixedEndpointBase overlappingEndpoints overlappingEndpoints) 1 :=
  wordTupleSpanTop_jointMixedEndpointBase _ _ overlappingEndpoints_span overlappingEndpoints_span

-- The zero endpoint insertion is singular, with its second diagonal entry zero.
example : bondInterpolationMatrix 1 1 0
    (finSumFinEquiv (.inr 0)) (finSumFinEquiv (.inr 0)) = 0 := by simp

example (γ : ℝ) (hN : 0 < N) :
    Module.finrank ℂ (blockInsertedBoundaryMap
      (jointMixedEndpointBase overlappingEndpoints overlappingEndpoints)
      (fun _ => bondInterpolationMatrix 1 1 γ) N).range = 8 := by
  simpa using finrank_jointMixedEndpoint_extendedBoundarySupport
    overlappingEndpoints overlappingEndpoints overlappingEndpoints_span overlappingEndpoints_span
    (fun _ => by decide) (fun _ => by decide) γ hN

example (hN : 2 ≤ N) :
    LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap
        (jointMixedEndpointBase overlappingEndpoints overlappingEndpoints)
        (fun _ => bondInterpolationMatrix 1 1 0) 2).range.starProjection).toLinearMap N) =
      (blockInsertedBoundaryMap
        (jointMixedEndpointBase overlappingEndpoints overlappingEndpoints)
        (fun _ => bondInterpolationMatrix 1 1 0) N).range :=
  ker_openInteractionHamiltonianES_jointMixedEndpoint_eq _ _
    overlappingEndpoints_span overlappingEndpoints_span (fun _ => by decide)
    (fun _ => by decide) 0 hN

example (hN : 2 ≤ N) :
    Continuous fun γ : ℝ => (LinearMap.ker (openInteractionHamiltonianES
      (1 - (blockInsertedBoundaryMap
        (jointMixedEndpointBase overlappingEndpoints overlappingEndpoints)
        (fun _ => bondInterpolationMatrix 1 1 γ) 2).range.starProjection).toLinearMap
          N)).starProjection :=
  continuous_ker_openInteractionHamiltonianES_jointMixedEndpoint_starProjection _ _
    overlappingEndpoints_span overlappingEndpoints_span (fun _ => by decide)
    (fun _ => by decide) hN

/--
info: 'MPSTensor.wordTupleSpanTop_one_of_rectangular_compression'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.wordTupleSpanTop_one_of_rectangular_compression
/--
info: 'MPSTensor.MPOSymmetry.wordTupleSpanTop_jointMixedEndpointBase'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.wordTupleSpanTop_jointMixedEndpointBase
/--
info: 'MPSTensor.MPOSymmetry.wordTupleSpanTop_jointMixedEndpointInterpolation'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.wordTupleSpanTop_jointMixedEndpointInterpolation
/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_blockInsertedBoundaryMap_injective'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_blockInsertedBoundaryMap_injective
/--
info: 'MPSTensor.MPOSymmetry.ker_openInteractionHamiltonianES_jointMixedEndpoint_eq'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.ker_openInteractionHamiltonianES_jointMixedEndpoint_eq
/--
info: 'MPSTensor.MPOSymmetry.continuous_ker_openInteractionHamiltonianES_jointMixedEndpoint_starProjection'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.continuous_ker_openInteractionHamiltonianES_jointMixedEndpoint_starProjection

/--
info: 'MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedGroundSpace_eq_iSup'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointMixedEndpoint_extendedGroundSpace_eq_iSup
