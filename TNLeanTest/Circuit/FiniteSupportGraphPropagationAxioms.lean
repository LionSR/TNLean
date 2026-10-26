import TNLean.Circuit.LiebRobinson.GraphPropagation
import TNLean.Circuit.SiteEmbedding

/-! Axiom checks for finite-support graph propagation and its restricted-norm estimate. -/

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset

/--
info: 'QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finset_numeric

/--
info: 'QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset_numeric

open scoped Matrix.Norms.L2Operator

-- A zero interaction budget and arbitrary real time are admitted, even with no terms.
example (S : Finset Unit)
    (A B : Matrix (Unit → Fin 2) (Unit → Fin 2) ℂ)
    (hA : A ∈ QuantumCircuit.supportedOperators 2 (S : Set Unit)) (t : ℝ) :
    ‖QuantumCircuit.heisenbergEvolution 0 t A * B -
      B * QuantumCircuit.heisenbergEvolution 0 t A‖ ≤
      4 * (S.card : ℝ) * ‖A‖ * ‖B‖ := by
  have hB : B ∈ QuantumCircuit.supportedOperators 2 ({()} : Set Unit) := by
    have hset : ({()} : Set Unit) = Set.univ := by
      ext x
      cases x
      simp
    rw [hset]
    exact QuantumCircuit.mem_supportedOperators_univ B
  have h := QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finset_numeric
    (q := 2) (κ := Fin 0) (⊥ : SimpleGraph Unit) (fun _ => ∅) (fun _ => ())
    (fun k => Fin.elim0 k) (fun _ => 0) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) 0 (fun k => Fin.elim0 k) 1 (by decide)
    (fun k => Fin.elim0 k) 0 (by simp) S hA () hB 1 (by norm_num)
    0 (by simp) t
  simpa using h
