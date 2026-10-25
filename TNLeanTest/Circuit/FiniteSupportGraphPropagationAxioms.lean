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
  have h := QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finsets_numeric
    (q := 2) (κ := Fin 0) (⊥ : SimpleGraph Unit) (fun _ => ∅) (fun _ => ())
    (fun k => Fin.elim0 k) (fun _ => 0) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) 0 (fun k => Fin.elim0 k) 1 (by decide)
    (fun k => Fin.elim0 k) 0 (by simp) S hA {()}
    (by simpa only [Finset.coe_singleton] using hB) 1 (by norm_num) 0 (by simp) t
  simpa using h

/--
info: 'QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finsets_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finsets_numeric

/--
info: 'QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finsets_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finsets_numeric

-- Both supports are arbitrary, including empty; zero budget and every real time are allowed.
example (S Y : Finset Bool)
    (A B : Matrix (Bool → Fin 2) (Bool → Fin 2) ℂ)
    (hA : A ∈ QuantumCircuit.supportedOperators 2 (S : Set Bool))
    (hB : B ∈ QuantumCircuit.supportedOperators 2 (Y : Set Bool)) (t : ℝ) :
    ‖QuantumCircuit.heisenbergEvolution 0 t A * B -
      B * QuantumCircuit.heisenbergEvolution 0 t A‖ ≤
      4 * (S.card : ℝ) * ‖A‖ * ‖B‖ := by
  have h := QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finsets_numeric
    (q := 2) (κ := Fin 0) (⊥ : SimpleGraph Bool) (fun _ => ∅) (fun _ => false)
    (fun k => Fin.elim0 k) (fun _ => 0) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) 0 (fun k => Fin.elim0 k) 1 (by decide)
    (fun k => Fin.elim0 k) 0 (by simp) S hA Y hB 1 (by norm_num)
    0 (by simp) t
  simpa using h

-- Empty ambient type: a negative vacuous budget and every local dimension are admitted.
example {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι] (q : ℕ)
    (B : Matrix (ι → Fin q) (ι → Fin q) ℂ)
    (hB : B ∈ QuantumCircuit.supportedOperators q (∅ : Set ι)) (t : ℝ) :
    QuantumCircuit.heisenbergCommutatorNorm 0 B (∅ : Set ι) t ≤ 0 := by
  have h := QuantumCircuit.heisenbergCommutatorNorm_le_graphDistance_finsets_numeric
    (q := q) (κ := Fin 0) (⊥ : SimpleGraph ι) (fun _ => ∅) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) (fun _ => 0) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) 0 (fun k => Fin.elim0 k) 1 (by decide)
    (fun k => Fin.elim0 k) (-1) (fun x => isEmptyElim x) B ∅
    (by simpa only [Finset.coe_empty] using hB) ∅ 1 (by norm_num)
    1 (by simp) t
  simpa only [Finset.sum_const_zero, Finset.coe_empty, Finset.card_empty,
    Nat.cast_zero, mul_zero, zero_mul] using h

-- An observed two-site region can be disconnected from the initial site at every finite scale.
example (A B : Matrix (Fin 3 → Fin 2) (Fin 3 → Fin 2) ℂ)
    (hA : A ∈ QuantumCircuit.supportedOperators 2 ({0} : Set (Fin 3)))
    (hB : B ∈ QuantumCircuit.supportedOperators 2 ({1, 2} : Set (Fin 3)))
    (n : ℕ) (t : ℝ) :
    ‖QuantumCircuit.heisenbergEvolution 0 t A * B -
      B * QuantumCircuit.heisenbergEvolution 0 t A‖ ≤
      4 * ‖A‖ * ‖B‖ * Real.exp (-(n : ℝ)) := by
  have h := QuantumCircuit.norm_heisenberg_commutator_le_graphDistance_finsets_numeric
    (q := 2) (κ := Fin 0) (⊥ : SimpleGraph (Fin 3)) (fun _ => ∅) (fun _ => 0)
    (fun k => Fin.elim0 k) (fun _ => 0) (fun k => Fin.elim0 k)
    (fun k => Fin.elim0 k) 0 (fun k => Fin.elim0 k) 1 (by decide)
    (fun k => Fin.elim0 k) 0 (by simp) {0} (by simpa using hA)
    {1, 2} (by simpa using hB) 1 (by norm_num) n
    (by simp [SimpleGraph.edist_bot]) t
  simpa using h
