/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.GraphExtendedMetric
import TNLean.PEPS.AreaLaw.Amplification.GraphChannelWeightedRow

/-! Boundary consumers for the graph pseudo-emetric and actual event kernel. -/

open QuantumCircuit TNLean.PEPS.AreaLaw
open scoped BigOperators

namespace GraphExtendedMetricTest

-- The standard metric laws are available without finiteness or connectivity.
example {ι : Type*} (G : SimpleGraph ι) (x y z : ι) :
    letI := graphPseudoEMetricSpace G
    edist x x = 0 ∧ edist x y = edist y x ∧
      edist x z ≤ edist x y + edist y z := by
  let := graphPseudoEMetricSpace G
  exact ⟨edist_self x, edist_comm x y, edist_triangle x y z⟩

-- Unreachable vertices remain infinitely far apart, despite the toReal convention.
example :
    letI := graphPseudoEMetricSpace (⊥ : SimpleGraph (Fin 2))
    edist (0 : Fin 2) 1 = ⊤ ∧ (edist (0 : Fin 2) 1).toReal = 0 := by
  simp [graphPseudoEMetricSpace_edist, SimpleGraph.edist_bot]

-- An edge has the expected finite distance.
example :
    letI := graphPseudoEMetricSpace (⊤ : SimpleGraph (Fin 2))
    edist (0 : Fin 2) 1 = 1 := by
  simp [graphPseudoEMetricSpace_edist, SimpleGraph.edist_top]

-- The empty graph's pseudo-emetric needs no inhabitedness assumption.
noncomputable example : PseudoEMetricSpace (Fin 0) := graphPseudoEMetricSpace ⊥

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

-- Exactly the nonnegativity and support assumptions of extended-metric kernel
-- theorems follow for the actual kernel on arbitrary disconnected graphs.
theorem actualKernelSupport (G : SimpleGraph ι) (a : κ → ι)
    {D : ℝ} (hD : 0 ≤ D) (b α : ℝ) (N : ℕ) :
    letI := graphPseudoEMetricSpace G
    (∀ y z, 0 ≤ graphChannelEventKernel G a D b α N y z) ∧
      ∀ y z, edist y z = ⊤ → graphChannelEventKernel G a D b α N y z = 0 := by
  let := graphPseudoEMetricSpace G
  refine ⟨fun y z => graphChannelEventKernel_nonneg G a hD b α N y z, ?_⟩
  intro y z hyz
  exact graphChannelEventKernel_eq_zero_of_not_reachable G a D b α N y z
    ((graphPseudoEMetricSpace_edist_eq_top G y z).mp hyz)

-- A natural-distance weighted row is the extended-metric row verbatim.
theorem actualKernelRow (G : SimpleGraph ι) (a : κ → ι) (D b α R : ℝ) (N : ℕ)
    (hrow : ∀ y, (∑ z, graphChannelEventKernel G a D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (G.dist y z : ℝ) ^ α)) ≤ R) :
    letI := graphPseudoEMetricSpace G
    ∀ y, (∑ z, graphChannelEventKernel G a D b α N y z *
      Real.exp (b / (2 * (2 : ℝ) ^ α) * (edist y z).toReal ^ α)) ≤ R := by
  simpa only [graphPseudoEMetricSpace_edist_toReal] using hrow

end GraphExtendedMetricTest

/--
info: 'TNLean.PEPS.AreaLaw.graphPseudoEMetricSpace'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphPseudoEMetricSpace

/--
info: 'TNLean.PEPS.AreaLaw.graphPseudoEMetricSpace_edist'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphPseudoEMetricSpace_edist

/--
info: 'TNLean.PEPS.AreaLaw.graphPseudoEMetricSpace_edist_ne_top'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphPseudoEMetricSpace_edist_ne_top

/--
info: 'TNLean.PEPS.AreaLaw.graphPseudoEMetricSpace_edist_eq_top'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphPseudoEMetricSpace_edist_eq_top

/--
info: 'TNLean.PEPS.AreaLaw.graphPseudoEMetricSpace_edist_toReal'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphPseudoEMetricSpace_edist_toReal

/--
info: 'TNLean.PEPS.AreaLaw.graphChannelEventKernel_nonneg'
depends on axioms: [propext, Classical.choice, Quot.sound]
---
info: `#`-commands, such as '#print', are not allowed in 'Mathlib' [linter.hashCommand]
-/
#guard_msgs (whitespace := lax) in
#print axioms graphChannelEventKernel_nonneg
