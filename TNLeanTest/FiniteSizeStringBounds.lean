import TNLean.MPS.Symmetry.PhysicalStringBounds
import TNLean.MPS.Symmetry.PeriodicStringBounds
import TNLean.MPS.Examples.StringOrderScalarPhase

/-!
# Finite-size String Order regression checks

The canonical example supplies all spectral assumptions. The periodic bound
admits arbitrary fixed supports and non-Hermitian matrices. The symmetry
bound is checked at the nonreal scalar phase `i`, without replacing it by one.
-/

open scoped Matrix BigOperators ComplexOrder MatrixOrder TNOperatorSpace InnerProductSpace

namespace MPSTensor

/-- The geometric expectation theorem applies to every fixed observable of
an actual canonical tensor, without a supplied error bound or normalization. -/
example : ∃ r : ℝ, 0 < r ∧ r < 1 ∧
    ∀ (k : ℕ) (O : Matrix (Fin k → Fin 4) (Fin k → Fin 4) ℂ),
      ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n →
        ‖mpvExpectation stringPhaseTensor (k + n) (appendObservable O
            (1 : Matrix (Fin n → Fin 4) (Fin n → Fin 4) ℂ)) -
          Matrix.trace (((1 / 2 : ℂ) • 1) *
            physicalObservableTransfer stringPhaseTensor k O 1)‖ ≤ C * r ^ n := by
  obtain ⟨C₀, r, hC₀, hr, hr1, N₀, hN₀, hnorm, hbound⟩ :=
    pureCanonical_periodic_expectations_le_geometric stringPhaseTensor
      ((1 / 2 : ℂ) • 1) stringPhaseTensor_canonical.1
      stringPhaseTensor_canonical.2.1 stringPhaseTensor_canonical.2.2
      stringPhaseTensor_unital stringPhaseTensor_pure
  refine ⟨r, hr, hr1, fun k O => ?_⟩
  obtain ⟨C, hC, hCbound⟩ := hbound k O
  exact ⟨C, hC, N₀, hCbound⟩

/-- The phase-adjusted estimate retains a nonreal unit phase at every positive
middle length, while its common rate is independent of the endpoints. -/
example : ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ x y : Matrix (Fin 4) (Fin 4) ℂ,
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖(Complex.I ^ N)⁻¹ * physicalStringOrderParam stringPhaseTensor
          ((1 / 2 : ℂ) • 1) x y (Complex.I • 1) N -
        Matrix.trace (((1 / 2 : ℂ) • 1) * twistedTransferMap stringPhaseTensor y 1) *
          Matrix.trace (((1 / 2 : ℂ) • 1) * twistedTransferMap stringPhaseTensor x 1)‖ ≤
            C * r ^ N := by
  obtain ⟨hIrr, hPrim⟩ := pureCanonical_isIrreducibleMap_and_isPrimitive
    stringPhaseTensor ((1 / 2 : ℂ) • 1) stringPhaseTensor_canonical.1
    stringPhaseTensor_canonical.2.2 stringPhaseTensor_unital stringPhaseTensor_pure
  have h := physicalStringOrderParam_phase_adjusted_le_geometric
    stringPhaseTensor hIrr hPrim ((1 / 2 : ℂ) • 1)
    stringPhaseTensor_canonical.1 stringPhaseTensor_canonical.2.1
    stringPhaseTensor_canonical.2.2 stringPhaseTensor_unital
    (Complex.I • 1) 1 Complex.I (by simp) (by simp) (fun i => by
      simp [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, ite_smul])
  simpa only [Matrix.conjTranspose_one, Matrix.mul_one] using h

end MPSTensor

section AxiomChecks
set_option linter.hashCommand false

/--
info: 'MPSTensor.canonical_transfer_pow_sub_stationary_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.canonical_transfer_pow_sub_stationary_le_geometric

/--
info: 'MPSTensor.physicalStringOrderParam_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.physicalStringOrderParam_le_geometric

/--
info: 'MPSTensor.physicalStringOrderParam_phase_adjusted_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.physicalStringOrderParam_phase_adjusted_le_geometric

/--
info: 'MPSTensor.canonical_trace_mul_transfer_pow_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.canonical_trace_mul_transfer_pow_le_geometric

/--
info: 'MPSTensor.pureCanonical_periodic_expectations_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_periodic_expectations_le_geometric

/--
info: 'MPSTensor.pureCanonical_mpvExpectation_fullRing_le_geometric'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.pureCanonical_mpvExpectation_fullRing_le_geometric

end AxiomChecks
