import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalEndpointAttachment

/-! The attachment regressions retain arbitrary original physical dimensions.
Only positive bond dimensions and one-site injectivity are hypotheses. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open MPSTensor MPSTensor.MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ} [NeZero D₀] [NeZero D₁]
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)

example : arbitraryPhysicalMixedInteraction A₀ A₁ 0 ≤
    LinearMap.toMatrix' (parentInteraction
      (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2) :=
  arbitraryPhysicalMixedInteraction_zero_le_parent A₀ A₁ h₀

example : arbitraryPhysicalMixedInteraction A₀ A₁ 1 ≤
    LinearMap.toMatrix' (parentInteraction
      (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2) :=
  arbitraryPhysicalMixedInteraction_one_le_parent A₀ A₁ h₁

example : arbitraryPhysicalEndpointAttachment A₀ A₁ false 0 =
    arbitraryPhysicalMixedInteraction A₀ A₁ 0 := by simp

example : arbitraryPhysicalEndpointAttachment A₀ A₁ true 0 =
    arbitraryPhysicalMixedInteraction A₀ A₁ 1 := by simp

example : arbitraryPhysicalEndpointAttachment A₀ A₁ false 1 =
    LinearMap.toMatrix' (parentInteraction
      (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) 2) := by
  simp [arbitraryPhysicalEndpointParentInteraction]

example : arbitraryPhysicalEndpointAttachment A₀ A₁ true 1 =
    LinearMap.toMatrix' (parentInteraction
      (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) 2) := by
  simp [arbitraryPhysicalEndpointParentInteraction]

example (right : Bool) : Continuous (arbitraryPhysicalEndpointAttachment A₀ A₁ right) :=
  continuous_arbitraryPhysicalEndpointAttachment A₀ A₁ right

example (right : Bool) (t : unitInterval) :
    (arbitraryPhysicalEndpointAttachment A₀ A₁ right t).PosSemidef :=
  arbitraryPhysicalEndpointAttachment_posSemidef A₀ A₁ h₀ h₁ right t.property.1

example (right : Bool) (t : unitInterval) :
    ‖arbitraryPhysicalEndpointAttachment A₀ A₁ right t‖ ≤ 1 :=
  arbitraryPhysicalEndpointAttachment_norm_le_one A₀ A₁ h₀ h₁ right t.property

-- No division by N - 2 or exclusion of the two-site periodic chain is introduced.
example (right : Bool) (t : unitInterval) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) (by omega : 2 ≤ 2)))) = 1 :=
  arbitraryPhysicalEndpointAttachment_groundSpace_finrank
    A₀ A₁ h₀ h₁ right t.property.1 (by omega)

-- The exact original first tensor is the constant ground representative.
example (t : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ false t) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := N)
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀)))} := by
  simpa only [Bool.false_eq_true, if_false] using
    arbitraryPhysicalEndpointAttachment_groundSpace_eq_span_mpv
      A₀ A₁ h₀ h₁ false t.property.1 hN

-- The exact original second tensor is the constant ground representative.
example (t : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ true t) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := N)
        (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁)))} := by
  simpa only [if_true] using
    arbitraryPhysicalEndpointAttachment_groundSpace_eq_span_mpv
      A₀ A₁ h₀ h₁ true t.property.1 hN

example : ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ right : Bool, ∀ t : unitInterval,
    ∀ N : ℕ, ∀ hN : 2 ≤ N,
    ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN)))ᗮ,
      δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin (interactionHamiltonian
        (arbitraryPhysicalEndpointAttachment A₀ A₁ right t) hN) v‖ :=
  exists_uniform_arbitraryPhysicalEndpointAttachment_gap A₀ A₁ h₀ h₁

/--
info: 'MPSTensor.interactionHamiltonian_affine_norm_gap_of_order'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.interactionHamiltonian_affine_norm_gap_of_order

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_zero_le_parent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_zero_le_parent

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_one_le_parent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_one_le_parent

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_endpoint_ker_eq_parent

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_norm_le_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_norm_le_one

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_groundSpace_eq_span_mpv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_groundSpace_eq_span_mpv

/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_groundSpace_finrank'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalEndpointAttachment_groundSpace_finrank

/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_arbitraryPhysicalEndpointAttachment_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_arbitraryPhysicalEndpointAttachment_gap
