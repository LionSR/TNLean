import TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointCoreHamiltonian

/-! Regression coverage for all ordered pairs, arbitrary exterior
multiplicities, original joint bulk, empty labels, and vanishing fibers. -/

set_option linter.hashCommand false

open MPSTensor MPSTensor.MPOSymmetry ContinuousLinearMap

private def overlapEndpoint : Fin 2 → MPSTensor 3 1 :=
  fun x i ↦ if i = 0 then 1 else if i = 1 ∧ x = 1 then 1 else 0

-- The two labels are physically overlapping, and the physical alphabet
-- has a direction unused by both labels. Unequal exterior dimensions are allowed.
example (σ : Cfg 3 1) :
    jointEndpointChainSpectatorEquiv 3 1 (fun _ : Fin 2 ↦ 1)
        (fun x ↦ if x = 0 then 2 else 3) (fun x ↦ if x = 0 then 4 else 5)
        (⟨0, 0, 0⟩, σ, ⟨1, 0, 0⟩) =
      ⟨(0, 1), (0, σ, 0), (0, 0)⟩ := rfl

-- An off-diagonal ordered pair survives the exact operator identity.
example (n : ℕ)
    (v : EuclideanSpace ℂ (JointEndpointChainCfg 3 (n + 1) (fun _ : Fin 2 ↦ 1)
      (fun _ ↦ 2) (fun _ ↦ 3)))
    (κ : JointEndpointCoreCfg 3 (n + 1) (fun _ : Fin 2 ↦ 1) (0, 1)) :
    jointEndpointNormalizedSum overlapEndpoint (fun _ ↦ 2) (fun _ ↦ 3) n v
        (⟨0, 0, κ.1⟩, κ.2.1, ⟨1, κ.2.2, 0⟩) =
      jointEndpointCoreHamiltonian overlapEndpoint n (0, 1)
        (jointEndpointExteriorFiber v (0, 1) (0, 0)) κ :=
  jointEndpointNormalizedSum_apply_fiber overlapEndpoint (fun _ ↦ 2) (fun _ ↦ 3)
    n v (0, 1) (0, 0) κ

-- At the minimum supported total length three, there are two boundary
-- terms and no middle edge. This does not make a two-site doubled-edge claim.
example (A : Fin 2 → MPSTensor 3 1) :
    jointEndpointNormalizedSum A (fun _ ↦ 2) (fun _ ↦ 3) 0 =
      jointEndpointNormalizedFirstTerm A (fun _ ↦ 2) (fun _ ↦ 3) 0 +
        jointEndpointNormalizedLastTerm A (fun _ ↦ 2) (fun _ ↦ 3) 0 := by
  simp [jointEndpointNormalizedSum, jointEndpointNormalizedBulkTerm_one_eq_zero]

-- A zero exterior multiplicity does not require choosing a spectator.
example (n : ℕ) :
    (jointEndpointChainSpectatorIsometry 3 (n + 1) (fun _ : Fin 2 ↦ 1)
      (fun _ ↦ 0) (fun _ ↦ 3)).toLinearEquiv.conj
        (jointEndpointNormalizedSum overlapEndpoint (fun _ ↦ 0) (fun _ ↦ 3) n) =
      (dependentRightFiberwiseMap
        (S := fun _ : Fin 2 × Fin 2 ↦ Fin 0 × Fin 3)
        (fun q ↦
          (jointEndpointCoreHamiltonian overlapEndpoint n q).toContinuousLinearMap)).toLinearMap :=
  jointEndpointNormalizedSum_conj_coreSpectators overlapEndpoint (fun _ ↦ 0) (fun _ ↦ 3) n

-- An empty label family has no ordered-pair fibers and needs no chosen label.
example (d n : ℕ) (D E F : Fin 0 → ℕ) (A : (x : Fin 0) → MPSTensor d (D x)) :
    (jointEndpointChainSpectatorIsometry d (n + 1) D E F).toLinearEquiv.conj
        (jointEndpointNormalizedSum A E F n) =
      (dependentRightFiberwiseMap (S := fun q : Fin 0 × Fin 0 ↦ Fin (E q.1) × Fin (F q.2))
        (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap)).toLinearMap :=
  jointEndpointNormalizedSum_conj_coreSpectators A E F n

-- Vanishing virtual core dimensions and physical alphabet are permitted.
example (n : ℕ) (A : Fin 2 → MPSTensor 0 0) :
    (jointEndpointChainSpectatorIsometry 0 (n + 1) (fun _ : Fin 2 ↦ 0)
      (fun _ ↦ 2) (fun _ ↦ 3)).toLinearEquiv.conj
        (jointEndpointNormalizedSum A (fun _ ↦ 2) (fun _ ↦ 3) n) =
      (dependentRightFiberwiseMap (S := fun _ : Fin 2 × Fin 2 ↦ Fin 2 × Fin 3)
        (fun q ↦ (jointEndpointCoreHamiltonian A n q).toContinuousLinearMap)).toLinearMap :=
  jointEndpointNormalizedSum_conj_coreSpectators A (fun _ ↦ 2) (fun _ ↦ 3) n

-- The consumer compares the two concrete normalized sums, deriving the
-- common core and operator identification rather than assuming either.
example {r d n : ℕ} (D₀ D₁ : Fin r → ℕ) (hD₀ : ∀ x, 0 < D₀ x)
    (A : (x : Fin r) → MPSTensor d (D₀ x)) {δ : ℝ} (hδ : 0 ≤ δ) :
    (∀ v ∈ (LinearMap.ker (jointEndpointNormalizedSum A D₀ D₀ n))ᗮ,
      δ * ‖v‖ ≤ ‖jointEndpointNormalizedSum A D₀ D₀ n v‖) ↔
      ∀ v ∈ (LinearMap.ker (jointEndpointNormalizedSum A
          (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n))ᗮ,
        δ * ‖v‖ ≤ ‖jointEndpointNormalizedSum A
          (fun x ↦ D₀ x + D₁ x) (fun x ↦ D₀ x + D₁ x) n v‖ :=
  jointEndpointNormalizedSum_norm_gap_iff_enlarged D₀ D₁ hD₀ A n hδ

/--
info: 'LinearIsometryEquiv.conj_eq_dependentRightFiberwiseMap_of_ker_iff'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms LinearIsometryEquiv.conj_eq_dependentRightFiberwiseMap_of_ker_iff

/--
info: 'MPSTensor.MPOSymmetry.jointEndpointFirstEdgeCoreConstraint_conj_spectators'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointEndpointFirstEdgeCoreConstraint_conj_spectators

/--
info: 'MPSTensor.MPOSymmetry.jointEndpointLastEdgeCoreConstraint_conj_spectators'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointEndpointLastEdgeCoreConstraint_conj_spectators

/--
info: 'MPSTensor.MPOSymmetry.jointEndpointNormalizedSum_conj_coreSpectators'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointEndpointNormalizedSum_conj_coreSpectators

/--
info: 'MPSTensor.MPOSymmetry.jointEndpointNormalizedSum_norm_gap_iff_enlarged'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.jointEndpointNormalizedSum_norm_gap_iff_enlarged
