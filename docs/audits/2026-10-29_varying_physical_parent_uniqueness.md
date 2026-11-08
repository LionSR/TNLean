# The actual varying-physical-alphabet open parent ground line

This final source component removes the common-physical-alphabet restriction
from the adjacent open-chain result supporting PGVWC07 Theorem 9. The input is
the original finite family of rectangular site matrices, with arbitrary natural
physical dimensions, varying bond dimensions, singleton endpoint bonds,
sitewise canonical row identities and full rectangular spans. The chain length
is explicitly at least two. No state, embedded-state membership, local sections,
Hamiltonian comparison, canonicalization or ground-kernel supplier is assumed.

The common alphabet is the derived sum of the actual physical dimensions.
`commonPhysicalSiteFamily` extends each original site family by zero and puts
zero outside the finite chain. It uses the existing rectangular products and
scalar-endpoint state, without a second chain record or product recursion.
`varyingPhysicalScalarState` reads that actual state on the original embedded
configurations. At each actual letter the extended matrix equals the original
matrix, so these are the original rectangular product coefficients.

The existing physical-extension lemmas preserve both the canonical row sums
and full rectangular spans. Canonical normalization first proves the actual
common-alphabet state has norm one. If that alphabet were empty, every full
configuration would be impossible at the first site; its state would be zero.
This contradiction derives physical nonemptiness internally, with no additional
premise. The actual common-alphabet parent equation and the proved support
extraction then give Omega = E(pullback Omega). Isometry proves the actual
original-space state has norm one.

For any original-space vector, the existing actual Hamiltonian intertwining
and uniform old/new parent comparison identify its original kernel equation
with the old common-alphabet kernel equation of its extension. The proved
uniform scalar reconstruction gives E(psi)=c E(Omega); injectivity yields the
original scalar multiple. Conversely the represented common-alphabet state is
annihilated by its actual parent; derived transport gives the original parent
equation. Thus the actual dependent-physical-space parent kernel is precisely
the represented state line, and its dimension is one by derived nonvanishing.
Positivity of that actual parent is already proved without tensor assumptions.

Independent source/API reviews by the parent and the physical-transport owner
found no concrete mismatch. The six public declarations have separate
scope-faithful notready Blueprint entries. The source-domain note now records
that the physical-alphabet restriction has been removed; the N >= 2 domain,
scalar phase freedom, hosted proof acceptance and integration remain explicit.
This is not an unrestricted source-theorem completion claim.

Native import, Blueprint, roles, prose, TeX, width and integrity checks are
recorded in the draft PR. No local Lean, Lake, elaboration or build was run.
