/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.Examples.QuantumDoubleLatticeBlocking

/-! Full-space and nonabelian checks of the periodic quantum-double Hamiltonian. -/

open scoped Matrix BigOperators
open TNLean.PEPS

-- This regression intentionally inspects axiom dependencies.
set_option linter.hashCommand false

namespace QuantumDoubleLatticeTest

section GeneralFiniteGroup

variable {width height : ℕ} [NeZero width] [NeZero height]
variable [Fact (2 < width)] [Fact (2 < height)]
local instance : Fact (1 < width) := ⟨by have := Fact.out (p := 2 < width); omega⟩
local instance : Fact (1 < height) := ⟨by have := Fact.out (p := 2 < height); omega⟩
variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
local notation "X" => TorusVertex width height
local notation "E" => Edge (torusGraph width height)
local notation "C" => QuantumDoubleKLatticeConfig width height G

-- All ambient commutators are available without a support or state assumption.
theorem all_terms_commute (j k : (X ⊕ X) ⊕ E) :
    Commute (quantumDoubleKLatticeTerm (G := G) j) (quantumDoubleKLatticeTerm k) :=
  quantumDoubleKLatticeTerm_commute j k

-- The source's actual eight-spin east-west action is the restriction of placement.
example (u : G) (x : C) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusRightEdge v) u x (v.1 + 1, v.2) =
      quantumDoubleKBondRight u (x (v.1 + 1, v.2)) :=
  quantumDoubleKLatticeBondPermutation_right_at_right u x v

-- Vertical placement has the correct two opposite corner multiplications.
example (u : G) (x : C) (v : X) :
    quantumDoubleKLatticeBondPermutation (torusUpEdge v) u x (v.1, v.2 + 1) =
      ((x (v.1, v.2 + 1)).1, (x (v.1, v.2 + 1)).2.1 * u⁻¹,
        u * (x (v.1, v.2 + 1)).2.2.1, (x (v.1, v.2 + 1)).2.2.2) :=
  quantumDoubleKLatticeBondPermutation_up_at_top u x v

-- The full periodic kernel uses contractible flatness, not trivial torus holonomy.
theorem flat_invariant_kernel (ψ : C → ℂ) :
    quantumDoubleKLatticeHamiltonian *ᵥ ψ = 0 ↔
      (∀ x, ¬IsQuantumDoubleKLatticeFlat x → ψ x = 0) ∧
        ∀ u : E → G, ∀ x, ψ (quantumDoubleKLatticeGauge u x) = ψ x :=
  quantumDoubleKLatticeHamiltonian_mulVec_eq_zero_iff_flat_invariant ψ

-- Exact orbit sums are actual inserted native PEPS vectors, with no range assumption.
theorem flat_orbit_in_closureSpan (x : C) (hx : IsQuantumDoubleKLatticeFlat x) :
    quantumDoubleKLatticeOrbitSum x ∈ quantumDoubleKCommutingClosureSpan := by
  rw [quantumDoubleKLatticeOrbitSum_eq_twistedState x (fun v => hx (.inl v))]
  exact quantumDoubleKRegularTwistedState_mem_closureSpan _
    (quantumDoubleKHalfEdgeOfPhysical_flat x hx)

-- Literal source K has the same regional image after virtual inversion, for every region.
example (R : Finset X) :
    regionGroundSpace (quantumDoubleKRegularPEPS (G := G)) R =
      regionGroundSpace (quantumDoubleKPEPS (G := G)) R :=
  regionGroundSpace_quantumDoubleKRegularPEPS R

-- Native left-regular seams are explicitly transported to right-regular
-- seams on the literal source K tensor, with the same labels.
example (g h : G) :
    quantumDoubleKClosure (width := width) (height := height) g h =
      torusGClosure (rightRegularMatrix G) (quantumDoubleKTensor G) g h :=
  quantumDoubleKClosure_eq_source g h

-- No G-injectivity hypothesis is supplied for the exact source tensor.
example : IsGInjective (torusLegRep (leftRegularMatrix G))
    (siteMap (quantumDoubleKRegularTensor (G := G))) :=
  isGInjective_quantumDoubleKRegularTensor

-- The kernel dimension is the complete commuting-pair sector count.
theorem full_sector_count : Module.finrank ℂ (Matrix.mulVecLin
    (quantumDoubleKLatticeHamiltonian (width := width) (height := height) (G := G))).ker =
      Nat.card (CommutingPairConjugacyClass G) :=
  finrank_ker_quantumDoubleKLatticeHamiltonian

theorem full_closure_span :
    LinearMap.ker (Matrix.mulVecLin
      (quantumDoubleKLatticeHamiltonian (width := width) (height := height) (G := G))) =
        quantumDoubleKCommutingClosureSpan :=
  ker_quantumDoubleKLatticeHamiltonian_eq_commutingClosureSpan

theorem source_parent_kernel
    (P : (v : X) → Matrix
      (RegionPhysicalConfig (d := Fintype.card (G × G × G × G)) (torusPlaquetteRegion v))
      (RegionPhysicalConfig (d := Fintype.card (G × G × G × G)) (torusPlaquetteRegion v)) ℂ)
    (hP : ∀ v, IsRegionParentInteraction (quantumDoubleKPEPS (G := G))
      (torusPlaquetteRegion v) (P v)) :
    (Matrix.mulVecLin (regionParentHamiltonian torusPlaquetteRegion P)).ker =
      (Matrix.mulVecLin (quantumDoubleKLatticeHamiltonian (G := G))).ker.map
        quantumDoubleKPhysicalEquiv.toLinearMap :=
  ker_quantumDoubleK_sourceParent_eq_latticeKernel P hP

-- The original T contraction is killed by each actual physical pullback term.
theorem elementary_network_ground_state (j : (X ⊕ X) ⊕ E) :
    quantumDoubleKLatticeUnblockedTerm (G := G) j *ᵥ
      (fun σ => torusBondNetwork (quantumDoublePeriodicElementarySite σ) 1 1) = 0 :=
  quantumDoubleKLatticeUnblockedTerm_checkerboard j

-- A direct nonzero witness for the genuine untwisted contraction.
example : quantumDoubleKLatticeContraction
    (width := width) (height := height) (fun _ => (1 : G × G × G × G)) =
      (Fintype.card G : ℂ) := by
  rw [quantumDoubleKLatticeContraction_eq_card]
  simp only [quantumDoubleDualToK, Equiv.coe_fn_symm_mk]
  apply ite_eq_left
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro v
    simp
  · intro v
    simp
  · simp [IsQuantumDoubleTrivialHolonomy, quantumDoubleDualRowTransport,
      quantumDoubleDualColumnTransport, zmodTransport]

end GeneralFiniteGroup

local instance : Fact (2 < 3) := ⟨by decide⟩
local instance : Fact (1 < 3) := ⟨by decide⟩

namespace NonabelianChecks

private abbrev S₃ := Equiv.Perm (Fin 3)
private def s : S₃ := Equiv.swap 0 1
private def t : S₃ := Equiv.swap 1 2
private def x : QuantumDoubleKLatticeConfig 3 3 S₃ := fun _ => (t, 1, 1, 1)

example : s * t ≠ t * s := by decide

-- Gauge transformations preserve the identity indicator, not arbitrary holonomy itself.
example : quantumDoubleKHolonomy
    (quantumDoubleKLatticeGauge (fun _ => s) x (0, 0)) ≠
      quantumDoubleKHolonomy (x (0, 0)) := by
  rw [quantumDoubleKHolonomy_latticeGauge]
  change s * t * s⁻¹ ≠ t
  decide

-- Adjacent distinct bonds still commute for two noncommuting group labels.
example : Commute
    (quantumDoubleKLatticeBondPermutation (torusRightEdge (0 : TorusVertex 3 3)) s)
    (quantumDoubleKLatticeBondPermutation (torusUpEdge (0 : TorusVertex 3 3)) t) :=
  quantumDoubleKLatticeBondPermutation_commute (torusRightEdge_ne_torusUpEdge _ _) s t

end NonabelianChecks

-- The full toric-code ground space on the first native torus has four sectors.
example : Module.finrank ℂ (Matrix.mulVecLin
    (quantumDoubleKLatticeHamiltonian (width := 3) (height := 3)
      (G := Multiplicative (ZMod 2)))).ker = 4 := by
  rw [finrank_ker_quantumDoubleKLatticeHamiltonian, card_commutingPairConjugacyClass_of_commGroup]
  norm_num [Nat.card_eq_fintype_card]


/--
info: 'QuantumDoubleLatticeTest.all_terms_commute' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.all_terms_commute

/--
info: 'QuantumDoubleLatticeTest.flat_invariant_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.flat_invariant_kernel

/--
info: 'QuantumDoubleLatticeTest.flat_orbit_in_closureSpan' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.flat_orbit_in_closureSpan

/--
info: 'QuantumDoubleLatticeTest.full_closure_span' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.full_closure_span

/--
info: 'QuantumDoubleLatticeTest.source_parent_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.source_parent_kernel

/--
info: 'QuantumDoubleLatticeTest.full_sector_count' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.full_sector_count

/--
info: 'QuantumDoubleLatticeTest.elementary_network_ground_state' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumDoubleLatticeTest.elementary_network_ground_state

end QuantumDoubleLatticeTest
