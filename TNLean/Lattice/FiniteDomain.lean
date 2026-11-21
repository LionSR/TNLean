/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import QICLean.ManyBody.Sites.Lattice.Plane
import Mathlib.Logic.Equiv.Fintype

/-!
# Finite induced square-lattice domains

A domain is an arbitrary finite subset of the integer lattice. Interaction
range is measured by walks that remain in the domain.
Neither connectedness nor the absence of holes is assumed. The induced nearest-neighbor graph
`ManyBody.planeDomainGraph`, the admissible supports `ManyBody.IsAdmissibleSupport` and the
ambient dilation `ManyBody.ambientDilation` are QICLean's, as are the graph neighborhood
`ManyBody.graphNeighborhood`, the edge boundary `ManyBody.edgeBoundary` and the splitting
`ManyBody.cutEquiv` of a configuration along a region, applied here to `planeDomainGraph Λ`.

## Main definitions

* `Site`: the sites of a finite domain.
* `Configuration`: the configurations of a domain with local dimension `q`.

## References

* OpenAI, *A two-dimensional area law from a global spectral gap*,
  September 24, 2026, Theorem 1.1, `eq:hamiltonian`, and Section 2.
  Source revision: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

Independently formalized from the manuscript; no upstream Lean proof text is reused.
-/

namespace TNLean.Lattice

/-- Sites of a finite induced domain. Source: area-law Theorem 1.1. -/
abbrev Site (Λ : Finset (ℤ × ℤ)) := ↥Λ

/-- Configurations of a domain with local dimension `q`.
Source: area-law Section 1, the tensor product of the site spaces. -/
abbrev Configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) := Site Λ → Fin q

/-- The number of configurations is exactly the tensor-product dimension.
Source: area-law Section 1, the site Hilbert spaces. -/
@[simp] theorem card_configuration (Λ : Finset (ℤ × ℤ)) (q : ℕ) :
    Fintype.card (Configuration Λ q) = q ^ Λ.card := by
  simp [Configuration, Site]

end TNLean.Lattice
