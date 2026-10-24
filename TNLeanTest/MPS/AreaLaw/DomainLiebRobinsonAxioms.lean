/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.MPS.AreaLaw.DomainLiebRobinson
import TNLean.Circuit.LiebRobinson.GraphLocalization

/-!
# Axiom checks for finite-domain propagation and infinite-distance commutation

These declarations use only the three standard axioms of Lean.
-/

/--
info: 'QuantumCircuit.heisenberg_commutator_eq_zero_of_forall_edist_eq_top'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenberg_commutator_eq_zero_of_forall_edist_eq_top

/--
info: 'QuantumCircuit.heisenberg_commutator_eq_zero_of_edist_eq_top'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenberg_commutator_eq_zero_of_edist_eq_top

/--
info: 'QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_heisenberg_sub_siteExpectation_graphNeighborhood_le

/--
info: 'TNLean.MPS.AreaLaw.norm_heisenberg_commutator_le_domainDistance'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms TNLean.MPS.AreaLaw.norm_heisenberg_commutator_le_domainDistance
