import TNLean.PEPS.Defs
import TNLean.PEPS.InjectiveRegion

/-!
# One-edge blocking data for the normal PEPS proof

This file records the one-edge red/blue/complement datum used before the
normal square-lattice construction is translated around every edge.

## References

* [Molnár, Garre-Rubio, Pérez-García, Schuch, Cirac, *Normal projected
  entangled pair states generating the same state*, arXiv:1804.04964,
  Section 3, Theorem 3]
-/

namespace TNLean
namespace PEPS

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable (ι : RegionInjectivityData V)

/-- Red, blue, and complementary blocking data for one fixed edge.

This is the one-edge form of `NormalEdgeBlockingHypotheses`, used before the
normalized edge construction is translated around the full lattice.

Source: arXiv:1804.04964, Section 3, proof of Theorem 3, lines 1475--1500. -/
structure NormalEdgeBlockingData (G : SimpleGraph V) (e : Edge G) where
  red : Finset V
  blue : Finset V
  complement : Finset V
  left_mem_red : e.1.1 ∈ red
  right_mem_blue : e.1.2 ∈ blue
  red_injective : ι.IsInjective red
  blue_injective : ι.IsInjective blue
  complement_injective : ι.IsInjective complement
  red_disjoint_blue : Disjoint red blue
  red_disjoint_complement : Disjoint red complement
  blue_disjoint_complement : Disjoint blue complement
  cover_univ : red ∪ blue ∪ complement = Finset.univ

end PEPS
end TNLean
