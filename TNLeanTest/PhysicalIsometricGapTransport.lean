import TNLean.MPS.Symmetry.PhysicalIsometricGapTransport

/-! Regression checks for arbitrary positive, possibly noncommuting local
interactions. The original interaction need not be a projection. -/

-- These regression files intentionally audit axioms with guarded #print commands.
set_option linter.hashCommand false

open scoped Matrix ComplexOrder InnerProductSpace
open MPSTensor

variable {d m N : ℕ} (E : Matrix (Fin m) (Fin d) ℂ) (hE : Eᴴ * E = 1)
  (A : MPOTensor.ChainOperator d 2) (hA : A.PosSemidef)

example (hN : 2 ≤ N) :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) hN)) =
      (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN))).map
        (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E N)) :=
  isometricInteractionExtension_ker_eq_map_of_posSemidef E hE hA hN

-- The smallest permitted periodic chain is covered with the same hypotheses.
example :
    LinearMap.ker (Matrix.toEuclideanLin
      (interactionHamiltonian (isometricInteractionExtension E A) (by omega : 2 ≤ 2))) =
      (LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian A (by omega : 2 ≤ 2)))).map
          (Matrix.toEuclideanLin (MPOTensor.sitewisePhysicalMatrix E 2)) :=
  isometricInteractionExtension_ker_eq_map_of_posSemidef E hE hA (by omega)

example {δ : ℝ} (hδ : 0 < δ)
    (hGap : ∀ N (hN : 2 ≤ N),
      ∀ x ∈ (LinearMap.ker (Matrix.toEuclideanLin (interactionHamiltonian A hN)))ᗮ,
        δ * ‖x‖ ≤ ‖Matrix.toEuclideanLin (interactionHamiltonian A hN) x‖) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N (hN : 2 ≤ N),
      ∀ v ∈ (LinearMap.ker (Matrix.toEuclideanLin
        (interactionHamiltonian (isometricInteractionExtension E A) hN)))ᗮ,
        ε * ‖v‖ ≤ ‖Matrix.toEuclideanLin
          (interactionHamiltonian (isometricInteractionExtension E A) hN) v‖ := by
  refine ⟨min δ 1, lt_min hδ zero_lt_one, ?_⟩
  intro N hN
  exact isometricInteractionExtension_norm_gap E hE hA hN hδ.le (hGap N hN)

example (hN : 2 ≤ N) {δ : ℝ}
    (hGap : ∀ z ∈ spectrum ℂ (interactionHamiltonian A hN), z.re = 0 ∨ δ ≤ z.re) :
    ∀ z ∈ spectrum ℂ (interactionHamiltonian (isometricInteractionExtension E A) hN),
      0 ≤ z.re ∧ (z.re = 0 ∨ min δ 1 ≤ z.re) :=
  isometricInteractionExtension_spectrum_gap E hE hA hN hGap

/--
info: 'MPSTensor.isometricInteractionExtension_ker_eq_map_of_posSemidef'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.isometricInteractionExtension_ker_eq_map_of_posSemidef
/--
info: 'MPSTensor.isometricInteractionExtension_norm_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.isometricInteractionExtension_norm_gap
/--
info: 'MPSTensor.isometricInteractionExtension_spectrum_gap'
depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MPSTensor.isometricInteractionExtension_spectrum_gap
