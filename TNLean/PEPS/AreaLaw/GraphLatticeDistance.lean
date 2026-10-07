/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Int.NatAbs

/-!
# Ambient lattice distance along graph walks

The integer lattice distance is the sum of coordinate displacements. It satisfies the triangle
inequality, and a graph whose edges have ambient displacement at most one has walk displacement
at most the walk length. Finite extended graph distance therefore bounds ambient displacement,
including for graphs with holes or disconnected components.

This distance infrastructure supports the exact ambient count in `GraphLatticeDiamond` and
the interaction bounds derived from it. It introduces no finite-domain or Hamiltonian model.

## Provenance

The proofs are independently written from the ambient displacement argument preceding
`eq:ball-count` in OpenAI, *A two-dimensional area law from a global spectral gap*,
`01-preliminaries.tex`, lines 81–87, at commit `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
No upstream Lean proof text is copied or adapted.

## References

* <https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex#L81-L87>
-/

/-!
## Declaration provenance

Provenance-ID: 8745-tnlean.peps.arealaw.latticel1distance
Downstream declaration: TNLean.PEPS.AreaLaw.latticeL1Distance
Provenance-ID: 8745-tnlean.peps.arealaw.latticel1distance_self
Downstream declaration: TNLean.PEPS.AreaLaw.latticeL1Distance_self
Provenance-ID: 8745-tnlean.peps.arealaw.latticel1distance_triangle
Downstream declaration: TNLean.PEPS.AreaLaw.latticeL1Distance_triangle
Provenance-ID: 8745-tnlean.peps.arealaw.latticel1distance_le_walk_length
Downstream declaration: TNLean.PEPS.AreaLaw.latticeL1Distance_le_walk_length
Provenance-ID: 8745-tnlean.peps.arealaw.latticel1distance_le_of_edist_le
Downstream declaration: TNLean.PEPS.AreaLaw.latticeL1Distance_le_of_edist_le
Source: September 24, 2026.
https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-two-dimensional-area-law-from-a-global-spectral-gap-September-24-2026/build/sections/01-preliminaries.tex
Labels: eq:ball-count.
Independently formalized; no upstream Lean proof text reused.
These are auxiliary graph and counting results, not the complete propagation or area-law theorem.
-/

namespace TNLean.PEPS.AreaLaw

/-- The ambient integer lattice distance, measured by the sum of coordinate displacements.
Source: the ambient displacement comparison preceding `eq:ball-count` in the pinned paper. -/
def latticeL1Distance (a b : ℤ × ℤ) : ℕ :=
  (a.1 - b.1).natAbs + (a.2 - b.2).natAbs

/-- Ambient lattice distance vanishes at a site. -/
@[simp]
theorem latticeL1Distance_self (a : ℤ × ℤ) : latticeL1Distance a a = 0 := by
  simp [latticeL1Distance]

/-- Ambient lattice distance satisfies the triangle inequality. -/
theorem latticeL1Distance_triangle (a b c : ℤ × ℤ) :
    latticeL1Distance a c ≤ latticeL1Distance a b + latticeL1Distance b c := by
  have hx : (a.1 - c.1).natAbs ≤ (a.1 - b.1).natAbs + (b.1 - c.1).natAbs := by
    have he : a.1 - c.1 = (a.1 - b.1) + (b.1 - c.1) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  have hy : (a.2 - c.2).natAbs ≤ (a.2 - b.2).natAbs + (b.2 - c.2).natAbs := by
    have he : a.2 - c.2 = (a.2 - b.2) + (b.2 - c.2) := by omega
    rw [he]
    exact Int.natAbs_add_le _ _
  dsimp only [latticeL1Distance]
  omega

variable {V : Type*} {G : SimpleGraph V} (coord : V → ℤ × ℤ)

/-- A walk has ambient displacement at most its length when each edge has displacement at most
one. Walks are in the full given graph, without any restriction to an interaction support.
Source: `01-preliminaries.tex`, lines 81–84, preceding `eq:ball-count`. -/
theorem latticeL1Distance_le_walk_length
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} (p : G.Walk a b) : latticeL1Distance (coord a) (coord b) ≤ p.length := by
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
      calc
        latticeL1Distance (coord a) (coord c) ≤
            latticeL1Distance (coord a) (coord b) +
              latticeL1Distance (coord b) (coord c) :=
          latticeL1Distance_triangle _ _ _
        _ ≤ 1 + p.length := Nat.add_le_add (hstep hab) ih
        _ = (SimpleGraph.Walk.cons hab p).length := by simp [Nat.add_comm]

/-- A finite upper bound on extended graph distance also bounds ambient displacement.
The extended distance retains the value `⊤` between different graph components.
Source: the displacement comparison preceding `eq:ball-count` in the pinned paper. -/
theorem latticeL1Distance_le_of_edist_le
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    {a b : V} {R : ℕ} (hdist : G.edist a b ≤ (R : ℕ∞)) :
    latticeL1Distance (coord a) (coord b) ≤ R := by
  have hfinite : G.edist a b < ⊤ := lt_of_le_of_lt hdist (by simp)
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top (ne_of_lt hfinite)
  have hlength : p.length ≤ R := by
    exact ENat.natCast_le_natCast.mp (hp.le.trans hdist)
  exact (latticeL1Distance_le_walk_length coord hstep p).trans hlength

end TNLean.PEPS.AreaLaw
