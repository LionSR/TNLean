# Fixed-representation G-injective parent transport

## Source scope

SCP10, arXiv:1001.3807v3, Definition 5.1 and Theorems 5.5–5.7 use
site inverses on the invariant virtual subspaces. The new results apply
that argument to the actual finite-graph regional contractions. They allow
arbitrary finite-group virtual representations, including semi-regular
ones, without requiring injectivity on the whole virtual space or equal
ambient physical dimensions.

This is **fixed-representation transport**, not a proof that regular and
semi-regular virtual representations have the same canonical plaquette
parent kernels. The virtual bond spaces and representations are kept fixed.

## Exact statements

`ParentHamiltonian/RangePhysicalParentTransport.lean` proves:

- Physical maps injective only on each site's physical range admit linear
  inverses on those ranges.
- The product maps are inverse on every genuine open-region range, for
  arbitrary virtual boundary conditions.
- If the parent regions cover every vertex, their product identifies the
  entire common parent ground spaces and preserves their dimensions.
- Arbitrary positive interactions with those genuine regional kernels have
  full Hamiltonian kernels related by the same product map. No particular
  closed vector or ground-space spanning hypothesis is used.

`ParentHamiltonian/GInjectiveParentTransport.lean` derives the physical
comparison from the G-injective left-inverse identities themselves. Its
main result is
`exists_ker_regionParentHamiltonian_transport_of_isGInjective`.
The result includes injectivity on the complete source kernel and equality
of the kernel dimensions. It does not assume the kernel transport being
proved. Local positivity and exact local parent kernels are the ordinary
parent-Hamiltonian hypotheses.

The existing `globalPhysicalMap_comp` now accepts rectangular matrices;
its square-matrix uses remain specializations.

## Why vertex coverage is explicit

An unused physical subspace at an uncovered vertex produces additional
common ground vectors. Hence site-range-injective maps need not preserve
the parent dimension without vertex coverage. The regression file checks
both physical dimension growth under coverage and unequal one-vertex
parent dimensions when the region family is empty.

## Remaining semi-regular step

Section 7's isometry acts jointly on physical endpoints on neighboring
vertices. It therefore crosses the boundary of a parent region. Equality
of closed inserted states, even simultaneously for all insertions, does
not by itself identify the genuine local ranges.

`GraphOpenAveragingBondState` provides the correct starting point: internal
bonds carry Θ²V(q_head q_tail⁻¹), while crossing bonds retain ΘV(q_tail⁻¹)
or V(q_head)Θ and an arbitrary virtual boundary label. A canonical-parent
comparison must preserve those retained boundary factors. A useful next
step is deriving internal-bond support for all open-region vectors and
then global bond support from edge-covering parent regions. Bare global
Hamiltonian compression does not replace that local comparison.

## Validation

The changed composition lemma, its affected regional dependencies, both
new modules, and `TNLeanTest/GInjectiveParentTransport.lean` were compiled
using the repository's Lean options, with read-only shared dependency
artifacts and isolated output. Dependencies use the manifest's QICLean
revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`.
The new modules and regression tests emit no linter warnings.
Axiom inspection of the main kernel-transport theorem, regional inverse,
and common-ground-space equivalence reports only `propext`,
`Classical.choice`, and `Quot.sound`. A root-library build is an integration
check; this change does not regenerate the common root imports.
