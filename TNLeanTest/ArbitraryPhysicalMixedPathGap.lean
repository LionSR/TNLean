import TNLean.MPS.Symmetry.MPOSymmetry.ArbitraryPhysicalMixedPathGap

/-! Regressions for the actual GLM mixed path with arbitrary original physical
alphabets. Only positive bond dimensions and one-site injectivity are inputs;
no gap, kernel, continuity, commuting-term, or square-alphabet input is added. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open scoped Matrix MatrixOrder ComplexOrder
open MPSTensor MPSTensor.MPOSymmetry

variable {d₀ d₁ D₀ D₁ N : ℕ} [NeZero D₀] [NeZero D₁]
  (A₀ : MPSTensor d₀ D₀) (A₁ : MPSTensor d₁ D₁)
  (h₀ : Kraus.IsInjective A₀) (h₁ : Kraus.IsInjective A₁)

example : Kraus.IsInjective (polarPosTensor A₀) := isInjective_polarPosTensor h₀

example : (commonPhysicalEmbeddingLeft d₁ D₁ A₀)ᴴ *
    commonPhysicalEmbeddingLeft d₁ D₁ A₀ = 1 :=
  commonPhysicalEmbeddingLeft_isometry d₁ D₁ h₀

example : (commonPhysicalEmbeddingRight d₀ D₀ A₁)ᴴ *
    commonPhysicalEmbeddingRight d₀ D₀ A₁ = 1 :=
  commonPhysicalEmbeddingRight_isometry d₀ D₀ h₁

example : (commonPhysicalEmbeddingLeft d₁ D₁ A₀)ᴴ *
    commonPhysicalEmbeddingRight d₀ D₀ A₁ = 0 :=
  commonPhysicalEmbeddingLeft_conjTranspose_mul_right_eq_zero A₀ A₁

example : Continuous (arbitraryPhysicalMixedInterpolation A₀ A₁) :=
  continuous_arbitraryPhysicalMixedInterpolation A₀ A₁

example : Continuous (arbitraryPhysicalMixedInteraction A₀ A₁) :=
  continuous_arbitraryPhysicalMixedInteraction A₀ A₁ h₀ h₁

example (hN : 0 < N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 0) :
      NSiteSpace ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) N) =
      mpv (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀) :=
  mpv_arbitraryPhysicalMixedInterpolation_zero A₀ A₁ h₀ hN

example (hN : 0 < N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ 1) :
      NSiteSpace ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) N) =
      mpv (rotatePhysical (commonPhysicalEmbeddingRight d₀ D₀ A₁) A₁) :=
  mpv_arbitraryPhysicalMixedInterpolation_one A₀ A₁ h₁ hN

example {γ : ℝ} (hγ : γ ∈ Set.Ioo (0 : ℝ) 1) :
    arbitraryPhysicalMixedInteraction A₀ A₁ γ =
      LinearMap.toMatrix'
        (parentInteraction (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) 2) :=
  arbitraryPhysicalMixedInteraction_eq_parent_of_mem_Ioo A₀ A₁ hγ

example (γ : unitInterval) (hN : 2 ≤ N) :
    (mpv (arbitraryPhysicalMixedInterpolation A₀ A₁ γ) :
      NSiteSpace ((((D₀ + D₁) * (D₀ + D₁)) + d₀) + d₁) N) ≠ 0 :=
  mpv_arbitraryPhysicalMixedInterpolation_ne_zero A₀ A₁ h₀ h₁ γ hN

example (γ : unitInterval) (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN)) =
      Submodule.span ℂ {(WithLp.toLp 2
        (mpv (N := N) (arbitraryPhysicalMixedInterpolation A₀ A₁ γ)))} :=
  arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv A₀ A₁ h₀ h₁ γ hN

example (γ : unitInterval) (hN : 2 ≤ N) :
    Module.finrank ℂ (LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN))) = 1 :=
  arbitraryPhysicalMixedInteraction_groundSpace_finrank A₀ A₁ h₀ h₁ γ hN

-- The smallest ring and the singular first endpoint are covered together.
example :
    LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian
      (arbitraryPhysicalMixedInteraction A₀ A₁ 0) (by omega : 2 ≤ 2))) =
      Submodule.span ℂ {(WithLp.toLp 2 (mpv (N := 2)
        (rotatePhysical (commonPhysicalEmbeddingLeft d₁ D₁ A₀) A₀)))} := by
  simpa only [Set.Icc.coe_zero,
    mpv_arbitraryPhysicalMixedInterpolation_zero (N := 2) A₀ A₁ h₀ (by omega)] using
    arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv (N := 2) A₀ A₁ h₀ h₁
      (0 : unitInterval) (by omega)

example :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ γ : unitInterval, ∀ N : ℕ, ∀ hN : 2 ≤ N,
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN)))ᗮ,
        δ * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (interactionHamiltonian (arbitraryPhysicalMixedInteraction A₀ A₁ γ) hN) v‖ :=
  exists_uniform_arbitraryPhysicalMixed_periodic_path_gap A₀ A₁ h₀ h₁

/--
info: 'MPSTensor.periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.periodicInteractionHamiltonianES_eq_toEuclideanLin_interactionHamiltonian
/--
info: 'MPSTensor.MPOSymmetry.mpv_arbitraryPhysicalMixedInterpolation_zero'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mpv_arbitraryPhysicalMixedInterpolation_zero
/--
info: 'MPSTensor.MPOSymmetry.mpv_arbitraryPhysicalMixedInterpolation_one'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.mpv_arbitraryPhysicalMixedInterpolation_one
/--
info: 'MPSTensor.MPOSymmetry.continuous_arbitraryPhysicalMixedInteraction'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.continuous_arbitraryPhysicalMixedInteraction
/--
info: 'MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.arbitraryPhysicalMixedInteraction_groundSpace_eq_span_mpv
/--
info: 'MPSTensor.MPOSymmetry.exists_uniform_arbitraryPhysicalMixed_periodic_path_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.MPOSymmetry.exists_uniform_arbitraryPhysicalMixed_periodic_path_gap
