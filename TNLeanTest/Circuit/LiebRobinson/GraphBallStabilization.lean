import TNLean.Circuit.LiebRobinson.GraphBallStabilization

/-! Boundary consumers for exact graph-ball component stabilization. -/

open QuantumCircuit

variable {ι : Type*} [Fintype ι]

-- The finite cutoff is valid without a connectedness assumption.
example (G : SimpleGraph ι) (a : ι) :
    (graphBall G a (Finset.univ.sup (G.dist a)) : Set ι) = {x | G.Reachable a x} :=
  coe_graphBall_eq_reachable_of_sup_dist_le G a le_rfl

-- Radius zero is the anchor alone, including in disconnected graphs.
example (G : SimpleGraph ι) (a x : ι) : x ∈ graphBall G a 0 ↔ a = x := by
  simp [mem_graphBall]

-- Infinite-distance sites are excluded at every finite radius.
example (G : SimpleGraph ι) (a y : ι) (hy : ¬G.Reachable a y) (n : ℕ) :
    y ∉ graphBall G a n :=
  notMem_graphBall_of_edist_eq_top (G.edist_eq_top_of_not_reachable hy) n

-- The two isolated vertices never enter each other's balls.
example (n : ℕ) : (1 : Fin 2) ∉ graphBall (⊥ : SimpleGraph (Fin 2)) 0 n := by
  apply notMem_graphBall_of_edist_eq_top
  apply SimpleGraph.edist_eq_top_of_not_reachable
  simp

/--
info: 'QuantumCircuit.graphBall_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.graphBall_mono

/--
info: 'QuantumCircuit.notMem_graphBall_of_edist_eq_top' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.notMem_graphBall_of_edist_eq_top

/--
info: 'QuantumCircuit.coe_graphBall_eq_reachable_of_sup_dist_le' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.coe_graphBall_eq_reachable_of_sup_dist_le

/--
info: 'QuantumCircuit.exists_graphBall_eq_reachable' depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms QuantumCircuit.exists_graphBall_eq_reachable
