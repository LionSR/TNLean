# Nearest-neighbor crossing budget

Private source preparation on historical accepted TNLean base
`3d4fdd50a1` with the unchanged accepted QIC revision
`7d9e0688a55a64474707c5f5b260163e11b30128`.
The private native energy tree uses a later QIC revision; no integration or
pin update is performed here.

## Mathematical contract

For arbitrary finite induced domain Λ, arbitrary cuts Aⱼ and weights aⱼ,
the interaction index is the existing on-site vertices plus the existing
`TNLean.PEPS.Edge (domainGraph Λ)` type. Each edge has one normalized
endpoint order; no ordered-edge double count or replacement graph is added.
Any linear order on the finite sites can be used to instantiate that existing
representation. The result is independent of that choice.

A crossing edge has exactly one endpoint inside. Thus its inside
configuration cardinality is q, including q = 0 and q = 1. On-site terms
never cross. The exact generic sum

    Σⱼ aⱼ² Σᵢ∈crossingTerms |inside configurationsᵢⱼ|² J

is

    q² J Σⱼ aⱼ² |edgeBoundary Λ Aⱼ|.

No sign conditions on J or the weights are needed for this identity. There
is no Hamiltonian, norm bound, state, minimum, or energy premise. The
subsequent energy application, choice of positive κ when J = 0, and the
coefficient 36 are outside this file.

## Source and ownership

Mathematical source: OpenAI polynomial PEPS manuscript at revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`, `03-patches.tex`, lines 302–336:
one inside endpoint, its q² matrix units, and the boundary-weighted sum.
All proofs are independently written; no upstream Lean proof text is copied.

The issue 8767 ownership comments were reread on 2026-10-08. Existing
geometry ownership covers square radii, nesting, crossing uniqueness, and
the scalar 36. No crossingTerms-to-edgeBoundary adapter claim was found.
No held geometry file or PR is imported, merged, or copied. The sole geometry
import is the existing `FiniteDomain`.

Current-main GitHub blob hashes checked after selecting the historical base:

- `TNLean/PEPS/Defs.lean`: `6ab572358d4cbe7df130e04b0dfd5b5a41a386c5`
- `TNLean/PEPS/AreaLaw/FiniteDomain.lean`: `d32935c393c2d3a4938635b610a087f36e017d42`

Both match this base exactly. Default-branch search for crossingTerms plus
edgeBoundary returned no result. This is supplementary to the ownership
check, not a proof about every unpublished branch.

## Simplification review

Reuse the existing Edge, Edge.ofAdj and its endpoint theorem, Sym2,
FiniteDomain.edgeBoundary, Entropy.crossingTerms, and Finset.card_bij.
The combined support is one function on a sum, not a new Hamiltonian or
interaction structure. The combinatorial helper proves the singleton before
the dimension calculation; it does not square the full two-site dimension.
Explicit witnesses avoid unrestricted simplification over concrete lattice
subtypes. No general tactic or parallel boundary API is added.

## Validation status

Focused validation and source-bound evidence are recorded separately.
No root build, hosted CI, blueprint acceptance, glossary publication, or
native energy integration is claimed by this source-preparation note.

Final focused checks used one compiler process under the shared serial lock,
package linter options, warnings as errors, and a 90-second hard cap:

- Production: 19.71 seconds, passed.
- Dimension/degenerate regressions: 14.65 seconds, passed.
- Concrete one-edge boundary count and exact budget: 7.52 seconds, passed.
- Nine kernel dependency reports: 5.47 seconds, stock axioms only.

Earlier failed attempts remain in the validation record, including the
78.91-second run exceeding the 50-second failure threshold. Accordingly the
cumulative timing gate remains failed; later fast passes do not erase it.
The source-level repair replaced unrestricted concrete-subtype simplification
with explicit witnesses and fixed a conflicting inherited preorder by explicitly
selecting the chosen Edge order in strict-order asymmetry.
