/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.Amplification.LatticeChannelWeightedRow
import TNLean.PEPS.AreaLaw.Amplification.ChannelWordObservables

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

private theorem sum_true {κ M : Type*} [Fintype κ] [AddCommMonoid M]
    (f : {_i : κ // True} → M) :
    (∑ i, f i) = ∑ i, f ⟨i, trivial⟩ :=
  Fintype.sum_equiv (Equiv.subtypeUnivEquiv (fun _ => trivial)) f _ (fun _ => rfl)

-- The all-retained kernel really is the original kernel on the original labels.
theorem retainedAll_kernel {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (G : SimpleGraph ι) (a : κ → ι) (D b α : ℝ) (N : ℕ) (y z : ι) :
    graphChannelEventKernel G (fun i : {_i : κ // True} => a i) D b α N y z =
      graphChannelEventKernel G a D b α N y z := by
  classical
  simp only [graphChannelEventKernel, Finset.natCast_card_filter, sum_true]

-- Recover the original complete signature with the witnesses obtained once
-- from the retained theorem. Both kernel cardinalities and sums are identified.
theorem fullFamily_actualBounds {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c v : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (N : ℕ),
        (∀ i, Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N) →
        let α := kernelExponent p
        let k := fun i => positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        let D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))
        (∀ y, (∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * ((domainGraph Λ).dist y z : ℝ) ^ α)) ≤ v) ∧
        (∀ (y : Site Λ)
            (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∑ i, (siteOscillation q y (spectatorRootChannel (k i) B) -
            siteOscillation q y B)) ≤
          ∑ z, graphChannelEventKernel (domainGraph Λ) a D (c / 2) α N y z *
            siteOscillation q z B) := by
  obtain ⟨C, c, v, hC, hc, hv, hbounds⟩ := exists_latticeChannelEventKernel_bounds hp R hJ hΔ
  refine ⟨C, c, v, hC, hc, hv, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs Aux _ _ N hN
  simpa only [retainedAll_kernel, sum_true] using
    hbounds Λ h a ha E₀ Ω hgs (fun _ => True) Aux N (fun i => hN i)

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
    fullFamily_actualBounds (p := 1) (by decide) R hJ hΔ

-- A lattice hole or disconnected domain cannot create an off-component entry.
theorem disconnected {Λ : Finset (ℤ × ℤ)} {R : ℕ}
    (a : AdmissibleSupport Λ R → Site Λ) (D b α : ℝ) (N : ℕ) (y z : Site Λ)
    (hyz : ¬ (domainGraph Λ).Reachable y z) :
    graphChannelEventKernel (domainGraph Λ) a D b α N y z = 0 :=
  graphChannelEventKernel_eq_zero_of_not_reachable (domainGraph Λ) a D b α N y z hyz

-- No nonempty-retained-family hypothesis is needed, and no channel fires.
theorem retainedNone {q : ℕ} {ι κ Aux : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [Fintype Aux] [DecidableEq Aux]
    (G : SimpleGraph ι) (a : κ → ι) (k : κ → Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (w : List {_i : κ // False}) (y : ι)
    (B : Matrix ((ι → Fin q) × Aux) ((ι → Fin q) × Aux) ℂ) (D b α : ℝ) (N : ℕ) :
    spectatorRootChannelWord k (w.map Subtype.val) B = B ∧
      (∑ z, graphChannelEventKernel G (fun i : {_i : κ // False} => a i) D b α N y z *
        siteOscillation q z B) = 0 ∧
      (∑ i : {_i : κ // False}, (siteOscillation q y (spectatorRootChannel (k i) B) -
        siteOscillation q y B)) = 0 := by
  cases w with
  | nil => simp [graphChannelEventKernel]
  | cons i _ => exact i.property.elim

-- Retaining two of three coincident labels strictly changes the count from
-- three to two, rather than collapsing both retained labels to their anchor.
theorem retainedPair_kernel {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : SimpleGraph ι) (x : ι) (D b : ℝ) {α : ℝ} (hα : 0 < α) :
    graphChannelEventKernel G (fun _ : {i : Fin 3 // i < 2} => x) D b α 0 x x = 2 * D ∧
      graphChannelEventKernel G (fun _ : Fin 3 => x) D b α 0 x x = 3 * D := by
  classical
  have hcard : Fintype.card {i : Fin 3 // i < 2} = 2 := by decide
  simp [graphChannelEventKernel, mem_graphBall, Real.zero_rpow hα.ne', hcard, mul_comm]

-- The lattice producer controls the literal observable after every retained
-- word, evaluated through the original label type. The same C,c,v precede P.
theorem retainedWord_actualBounds {p : ℕ} (hp : 1 ≤ p)
    (R : ℕ) {J Δ : ℝ} (hJ : 0 ≤ J) (hΔ : 0 < Δ) :
    ∃ C c v : ℝ, 0 ≤ C ∧ 0 < c ∧ 0 ≤ v ∧
      ∀ {q : ℕ} [NeZero q] (Λ : Finset (ℤ × ℤ)) (h : LocalHamiltonian Λ q R J)
        (a : AdmissibleSupport Λ R → Site Λ), (∀ X, a X ∈ X.1) →
        ∀ (E₀ : ℝ) (Ω : StateSpace Λ q), IsGappedGroundState Λ q h.operator E₀ Ω Δ →
        ∀ (P : AdmissibleSupport Λ R → Prop) [DecidablePred P]
          (Aux : Type*) [Fintype Aux] [DecidableEq Aux] (N : ℕ),
        (∀ i : {i // P i}, Finset.univ.sup ((domainGraph Λ).dist (a i)) ≤ N) →
        let α := kernelExponent p
        let aP := fun i : {i // P i} => a i
        let k := fun i : AdmissibleSupport Λ R =>
          positiveConstraint (positiveNormalization p (Δ / 2) J)
          (centeredFilter p (Δ / 2) h.operator Ω (h.term i))
        let D := 2 * (2 + 8 * Real.sqrt C * Real.exp (c / 2))
        (∀ y, (∑ z, graphChannelEventKernel (domainGraph Λ) aP D (c / 2) α N y z *
          Real.exp (c / (4 * (2 : ℝ) ^ α) * ((domainGraph Λ).dist y z : ℝ) ^ α)) ≤ v) ∧
        (∀ (w : List {i // P i}) (y : Site Λ)
            (B : Matrix (Configuration Λ q × Aux) (Configuration Λ q × Aux) ℂ),
          (∑ i : {i // P i},
            (siteOscillation q y (spectatorRootChannelWord k ((w ++ [i]).map Subtype.val) B) -
              siteOscillation q y (spectatorRootChannelWord k (w.map Subtype.val) B))) ≤
          ∑ z, graphChannelEventKernel (domainGraph Λ) aP D (c / 2) α N y z *
            siteOscillation q z (spectatorRootChannelWord k (w.map Subtype.val) B)) := by
  obtain ⟨C, c, v, hC, hc, hv, hbounds⟩ := exists_latticeChannelEventKernel_bounds hp R hJ hΔ
  refine ⟨C, c, v, hC, hc, hv, ?_⟩
  intro q _ Λ h a ha E₀ Ω hgs P _ Aux _ _ N hN α aP k D
  obtain ⟨hrows, hincrements⟩ := hbounds Λ h a ha E₀ Ω hgs P Aux N hN
  refine ⟨hrows, ?_⟩
  intro w y B
  simpa only [spectatorRootChannelWord_map, spectatorRootChannelWord_append_singleton,
    Function.comp_apply] using
    hincrements y (spectatorRootChannelWord (k ∘ Subtype.val) w B)

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

/--
info: 'TNLean.PEPS.AreaLaw.card_anchor_fiber_subtype_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.card_anchor_fiber_subtype_le

/--
info: 'TNLean.PEPS.AreaLaw.spectatorRootChannelWord_map'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.PEPS.AreaLaw.spectatorRootChannelWord_map

/--
info: 'LatticeChannelWeightedRowTest.retainedAll_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.retainedAll_kernel

/--
info: 'LatticeChannelWeightedRowTest.fullFamily_actualBounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.fullFamily_actualBounds

/--
info: 'LatticeChannelWeightedRowTest.retainedNone'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.retainedNone

/--
info: 'LatticeChannelWeightedRowTest.retainedPair_kernel'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.retainedPair_kernel

/--
info: 'LatticeChannelWeightedRowTest.retainedWord_actualBounds'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms LatticeChannelWeightedRowTest.retainedWord_actualBounds
