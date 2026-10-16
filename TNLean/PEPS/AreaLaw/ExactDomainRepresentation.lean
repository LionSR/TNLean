/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.PEPS.AreaLaw.RectangularDomain
import TNLean.PEPS.Approximation.ExactTreeRepresentation
import TNLean.PEPS.Approximation.SquareLatticeConnectivity

/-!
# Exact PEPS representations on finite lattice domains

The exact spanning-tree construction represents every vector on a connected
finite induced domain of the integer lattice, the domains of the area-law
model, as a native PEPS on the induced nearest-neighbor graph with bond
dimensions at most the number of configurations. Rectangular domains with
positive sides are connected, so the open square is included in its
area-law coordinates.

The site order is a parameter, as in the edge-crossing budget: the native edge
type orients each edge by a linear order of the vertices, and the integer
lattice carries no canonical linear order.

The domain-general statement is a generalization made in this library of the
square case of *Polynomial PEPS approximation of gapped square-grid ground
states*, September 24, 2026, `07-assembly.tex`, lines 203–214; the domains are
those of *A two-dimensional area law from a global spectral gap*, Section 1.
Both at immutable manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
-/

namespace TNLean.PEPS.AreaLaw

variable {Λ : Finset (ℤ × ℤ)} [LinearOrder (Site Λ)]

/-- Every vector on a connected finite domain is the exact contraction of a
native PEPS on the induced lattice graph, with positive bond dimensions bounded
by the number `q ^ |Λ|` of configurations. Source: polynomial-PEPS
`07-assembly.tex`, lines 203–214, with the induced domain graph in place of the
open square. -/
theorem exists_exact_domain_tensor (hΛ : (domainGraph Λ).Connected) {q : ℕ} (hq : 0 < q)
    (ψ : Configuration Λ q → ℂ) :
    ∃ A : Tensor (domainGraph Λ) q, (∀ e, 0 < A.bondDim e) ∧
      (∀ e, A.bondDim e ≤ q ^ Λ.card) ∧ stateCoeff A = ψ := by
  simpa only [Fintype.card_coe] using
    ExactTreeRepresentation.exists_exact_tensor q hΛ hq ψ

/-- The integer domain of a rectangle with positive sides is connected: its
induced graph is isomorphic to the open rectangular grid. Source: area-law
Corollary 1.2 and polynomial-PEPS Section 1. -/
theorem domainGraph_rectangularDomain_connected {width height : ℕ} (hwidth : 0 < width)
    (hheight : 0 < height) : (domainGraph (rectangularDomain width height)).Connected :=
  (SimpleGraph.Iso.connected_iff (rectangleGraphIso width height)).mp
    (squareLatticeGraph_connected hwidth hheight)

end TNLean.PEPS.AreaLaw
