/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.Group.Abs

/-!
# Ambient counting for graphs embedded in the square lattice

An edge with ambient integer coordinate displacement at most one gives the same bound for the
displacement of a walk, with its length in place of one. An injective coordinate map then bounds
every finite set reached in at most `R` steps by the containing square of size `(2 * R + 1)^2`.
The graph may have holes or disconnected components. Walks remain in the given graph throughout.

**Auxiliary alternative bound:** The square bound here is a conservative replacement for the
diamond count `v_R = 1 + 2 * R * (R + 1)` in the paper. It is not the paper's exact constant.
This file establishes only geometric counting ingredients, not graph-distance propagation or
an area law. It introduces no finite-domain or Hamiltonian model.

## Provenance

All declarations are independently written from the mathematical argument in OpenAI,
*A two-dimensional area law from a global spectral gap*, `01-preliminaries.tex`,
`eq:ball-count`, lines 81–87, and `03-quasilocal.tex`, lines 122–126, at commit
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. No upstream Lean proof text is copied or adapted.

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
Provenance-ID: 8745-tnlean.peps.arealaw.card_le_square_of_latticel1distance_le
Downstream declaration: TNLean.PEPS.AreaLaw.card_le_square_of_latticeL1Distance_le
Provenance-ID: 8745-tnlean.peps.arealaw.card_le_square_of_walks
Downstream declaration: TNLean.PEPS.AreaLaw.card_le_square_of_walks
Provenance-ID: 8745-tnlean.peps.arealaw.card_le_square_of_edist_le
Downstream declaration: TNLean.PEPS.AreaLaw.card_le_square_of_edist_le
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

/-- A finite set embedded injectively into the integer lattice and contained in an ambient
distance ball has at most `(2 * R + 1)^2` elements.
This is the explicitly auxiliary square bound, rather than the paper's exact diamond count. -/
theorem card_le_square_of_latticeL1Distance_le (s : Finset V)
    (hcoord : Function.Injective coord) (a : V) (R : ℕ)
    (hs : ∀ x ∈ s, latticeL1Distance (coord a) (coord x) ≤ R) :
    s.card ≤ (2 * R + 1) ^ 2 := by
  classical
  let sx := Finset.Icc ((coord a).1 - (R : ℤ)) ((coord a).1 + (R : ℤ))
  let sy := Finset.Icc ((coord a).2 - (R : ℤ)) ((coord a).2 + (R : ℤ))
  have hmaps : Set.MapsTo coord (s : Set V) (↑(sx ×ˢ sy) : Set (ℤ × ℤ)) := by
    intro x hx
    have hd := hs x hx
    have hxabs : |(coord a).1 - (coord x).1| ≤ (R : ℤ) := by
      rw [← Int.natCast_natAbs]
      have hnat : ((coord a).1 - (coord x).1).natAbs ≤ R := by
        dsimp only [latticeL1Distance] at hd
        omega
      exact Int.ofNat_le.mpr hnat
    have hyabs : |(coord a).2 - (coord x).2| ≤ (R : ℤ) := by
      rw [← Int.natCast_natAbs]
      have hnat : ((coord a).2 - (coord x).2).natAbs ≤ R := by
        dsimp only [latticeL1Distance] at hd
        omega
      exact Int.ofNat_le.mpr hnat
    have hxle := abs_le.mp hxabs
    have hyle := abs_le.mp hyabs
    change coord x ∈ sx ×ˢ sy
    simp only [Finset.mem_product, Finset.mem_Icc, sx, sy]
    constructor <;> constructor <;> omega
  have hxcard : sx.card = 2 * R + 1 := by
    dsimp only [sx]
    rw [Int.card_Icc]
    omega
  have hycard : sy.card = 2 * R + 1 := by
    dsimp only [sy]
    rw [Int.card_Icc]
    omega
  calc
    s.card ≤ (sx ×ˢ sy).card :=
      Finset.card_le_card_of_injOn coord hmaps (fun _ _ _ _ h ↦ hcoord h)
    _ = (2 * R + 1) ^ 2 := by rw [Finset.card_product, hxcard, hycard, pow_two]

/-- A finite collection of vertices reached from an anchor by walks of length at most `R`
obeys the auxiliary square count. No connectivity assumption on the whole graph is needed.
Source: the walk comparison used for `eq:ball-count` in the pinned paper. -/
theorem card_le_square_of_walks (s : Finset V) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) (R : ℕ) (hs : ∀ x ∈ s, ∃ p : G.Walk a x, p.length ≤ R) :
    s.card ≤ (2 * R + 1) ^ 2 := by
  apply card_le_square_of_latticeL1Distance_le coord s hcoord a R
  intro x hx
  obtain ⟨p, hp⟩ := hs x hx
  exact (latticeL1Distance_le_walk_length coord hstep p).trans hp

/-- Every finite set in a closed graph ball obeys the auxiliary square count, with a constant
independent of domain cardinality. Disconnected sites cannot satisfy its distance hypothesis.
Source: the ambient inclusion argument for `eq:ball-count` in the pinned paper. -/
theorem card_le_square_of_edist_le (s : Finset V) (hcoord : Function.Injective coord)
    (hstep : ∀ ⦃x y : V⦄, G.Adj x y → latticeL1Distance (coord x) (coord y) ≤ 1)
    (a : V) (R : ℕ) (hs : ∀ x ∈ s, G.edist a x ≤ (R : ℕ∞)) :
    s.card ≤ (2 * R + 1) ^ 2 := by
  apply card_le_square_of_latticeL1Distance_le coord s hcoord a R
  intro x hx
  exact latticeL1Distance_le_of_edist_le coord hstep (hs x hx)

end TNLean.PEPS.AreaLaw
