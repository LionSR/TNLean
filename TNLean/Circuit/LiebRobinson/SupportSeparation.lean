/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Circuit.LiebRobinson.GraphLocalization
import QICLean.Entropy.SupportedMarginalTails

/-!
# Graph neighborhoods of crossing supports avoid interior cores

Let two outer regions be disjoint. If every ball of radius `ℓ + R` about
either core lies in its outer region, then the radius-`ℓ` neighborhood of
the exterior and the supports crossing the first region avoids both cores.
Only the graph diameter bound `R` on interaction supports is used.

This is the geometric argument of the TNLean one-dimensional note,
`part2a_mps_information.tex`, lines 419–425, on an arbitrary finite graph.
It is an auxiliary support statement, without a quantum-state assumption.
-/

set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
set_option linter.mathlibStandardSet true

namespace QuantumCircuit

/-- A strict real distance margin contains every closed ball whose natural radius
is at most that margin.
Disconnected vertices impose no finite-distance condition.
TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–425. -/
lemma graphBall_subset_of_finite_distance_margin
    {ι : Type*} [Fintype ι]
    (G : SimpleGraph ι) (D : Finset ι) (x : ι) (w : ℝ) (m : ℕ)
    (hm : (m : ℝ) ≤ w)
    (hmargin : ∀ y : ι, y ∉ D → ∀ d : ℕ,
      G.edist x y = (d : ℕ∞) → w < (d : ℝ)) :
    graphBall G x m ⊆ D := by
  classical
  intro y hy
  by_contra hyD
  have hxy := mem_graphBall.mp hy
  obtain ⟨d, hd⟩ := ENat.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ENat.natCast_ne_top m) hxy)
  have hdm : d ≤ m := ENat.natCast_le_natCast.mp (hd ▸ hxy)
  exact (not_lt_of_ge ((Nat.cast_le.mpr hdm).trans hm)) (hmargin y hyD d hd.symm)

/-- The radius-`ℓ` neighborhood of the exterior and crossing supports avoids
both cores when their radius-`ℓ + R` balls lie in disjoint outer regions.
TNLean one-dimensional note, `part2a_mps_information.tex`, lines 419–425. -/
theorem reset_graphNeighborhood_disjoint_cores
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    (G : SimpleGraph ι) (X : κ → Finset ι) (R ℓ : ℕ)
    (hDiam : ∀ k, ∀ x ∈ X k, ∀ y ∈ X k, G.edist x y ≤ (R : ℕ∞))
    (D C R₀ C₀ : Finset ι) (hDC : Disjoint D C)
    (hR : ∀ r ∈ R₀, graphBall G r (ℓ + R) ⊆ D)
    (hC : ∀ c ∈ C₀, graphBall G c (ℓ + R) ⊆ C) :
    let Q := (D ∪ C)ᶜ
    let crossing := Entropy.crossingTerms X D
    let Z := crossing.biUnion X
    Disjoint ((Q ∪ Z).biUnion fun z ↦ graphBall G z ℓ) (R₀ ∪ C₀) := by
  classical
  intro Q crossing Z
  apply Finset.disjoint_left.mpr
  intro a ha hcore
  obtain ⟨z, hz, hza⟩ := Finset.mem_biUnion.mp ha
  have haz : G.edist a z ≤ (ℓ : ℕ∞) := by
    simpa only [SimpleGraph.edist_comm] using (mem_graphBall.mp hza)
  have hNear (y : ι) (hzy : G.edist z y ≤ (R : ℕ∞)) :
      y ∈ graphBall G a (ℓ + R) := mem_graphBall.mpr (by
    simpa only [Nat.cast_add] using
      (G.edist_triangle (u := a) (v := z) (w := y)).trans (add_le_add haz hzy))
  rcases Finset.mem_union.mp hz with hQ | hZ
  · rcases Finset.mem_union.mp hcore with haR | haC
    · exact Finset.mem_compl.mp hQ
        (Finset.mem_union_left C (hR a haR (hNear z (by simp))))
    · exact Finset.mem_compl.mp hQ
        (Finset.mem_union_right D (hC a haC (hNear z (by simp))))
  · obtain ⟨k, hk, hzX⟩ := Finset.mem_biUnion.mp hZ
    obtain ⟨⟨x, hx, hxD⟩, y, hy, hyD⟩ :
        (∃ x ∈ X k, x ∈ D) ∧ ∃ y ∈ X k, y ∉ D := by
      simpa only [crossing, Entropy.crossingTerms, Finset.mem_filter,
        Finset.mem_univ, true_and] using hk
    rcases Finset.mem_union.mp hcore with haR | haC
    · exact hyD (hR a haR (hNear y (hDiam k z hzX y hy)))
    · exact Finset.disjoint_left.mp hDC hxD
        (hC a haC (hNear x (hDiam k z hzX x hx)))

end QuantumCircuit
