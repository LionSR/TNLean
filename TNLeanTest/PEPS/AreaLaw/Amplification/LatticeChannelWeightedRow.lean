/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelWeightedRow

/-! Concrete lattice counts and the boundary filter exponent consume the wrapper. -/

open QuantumCircuit SpectralFilter Matrix TNLean.PEPS.AreaLaw
open scoped BigOperators Matrix.Norms.L2Operator MatrixOrder ComplexOrder

namespace LatticeChannelWeightedRowTest

-- The geometric coefficient is the literal lattice constant K = 2.
theorem ballCount {Λ : Finset (ℤ × ℤ)} (x : Site Λ) (l : ℕ) :
    ((graphBall (domainGraph Λ) x l).card : ℝ) ≤ 2 * ((l : ℝ) + 1) ^ 2 :=
  card_graphBall_domainGraph_le x l

-- Multiplicity counts support labels and uses exactly the natural-power cast.
theorem anchorMultiplicity {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    (a : AdmissibleSupport Λ R → Site Λ) (ha : ∀ X, a X ∈ X.1) (x : Site Λ) :
    ((Finset.univ.filter fun X => a X = x).card : ℝ) ≤
      ((2 ^ ((1 + 2 * R * (R + 1)) - 1) : ℕ) : ℝ) := by
  exact_mod_cast card_anchor_fiber_le a ha x

-- At interaction range zero this exact multiplicity is one.
theorem radiusZeroMultiplicity {Λ : Finset (ℤ × ℤ)}
    (a : AdmissibleSupport Λ 0 → Site Λ) (ha : ∀ X, a X ∈ X.1) (x : Site Λ) :
    ((Finset.univ.filter fun X => a X = x).card : ℝ) ≤ 1 := by
  simpa using anchorMultiplicity a ha x

-- The p = 1 endpoint gives α = 1/2; all scalar witnesses still precede q,
-- the domain, Hamiltonian, anchors, ground vector, spectator and cutoff.
theorem halfExponent_actualBounds (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c v : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (N : ℕ),
        (∀ i, Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N) →
        let α : ℝ := 1 / 2
        let k := fun i => positiveConstraint (positiveNormalization 1 (Δ / 2) J)
          (centeredFilter 1 (Δ / 2) h.operator Ω (h.term i))
        let D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))
        (∀ y, (∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * ((domainGraph Λ).dist y z : ℝ) ^ α)) ≤ v) ∧
        (∀ (y : Site Λ)
            (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
            siteOscillation q y B)) ≤
          ∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
            siteOscillation q z B) := by
  simpa only [kernelExponent_one] using
    exists_latticeChannelEventKernel_bounds (p := 1) (by decide) R hJ hΔ

-- A lattice hole or disconnected domain cannot create an off-component entry.
theorem disconnected {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    (a : AdmissibleSupport Λ R → Site Λ) (D b α : ℝ) (N : ℕ) (y z : Site Λ)
    (hyz : ¬ (domainGraph Λ).Reachable y z) :
    graphChannelEventKernel (domainGraph Λ) a D b α N y z = 0 :=
  graphChannelEventKernel_eq_zero_of_not_reachable (domainGraph Λ) a D b α N y z hyz

end LatticeChannelWeightedRowTest

/--
info: 'TNLean.PEPS.AreaLaw.exists_latticeChannelEventKernel_bounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms exists_latticeChannelEventKernel_bounds

/--
info: 'LatticeChannelWeightedRowTest.ballCount'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.ballCount

/--
info: 'LatticeChannelWeightedRowTest.anchorMultiplicity'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.anchorMultiplicity

/--
info: 'LatticeChannelWeightedRowTest.radiusZeroMultiplicity'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.radiusZeroMultiplicity

/--
info: 'LatticeChannelWeightedRowTest.halfExponent_actualBounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.halfExponent_actualBounds

/--
info: 'LatticeChannelWeightedRowTest.disconnected'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.disconnected
