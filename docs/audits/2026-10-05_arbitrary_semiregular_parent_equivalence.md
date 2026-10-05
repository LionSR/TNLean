# Arbitrary semi-regular canonical parent equivalence

## Result

`nonempty_semiRegularGInjectiveParentEquiv` identifies the entire genuine
regional-parent ground space of an arbitrary physical G-injective tensor with
the canonical regular-representation parent space. The virtual representation
is an arbitrary finite-dimensional unitary semi-regular `U`; neither its
irreducible decomposition nor its multiplicities are supplied as hypotheses.
The kernel corollary applies to arbitrary positive local interactions whose
kernels are the actual regional PEPS ranges.

## Mathematical chain

1. `exists_minimalSemiRegular_matrix` derives positive dimensions and actual
   positive copy multiplicities, distinct irreducible unitary blocks, and a
   unitary coordinate intertwiner from `U`. Single-copy semi-regularity follows
   from linear independence of the original representation matrices.
2. `GraphOpenCopyTransport` proves actual all-boundary contraction covariance
   and adjoint covariance for independent dimension and copy families `d,m`.
   One virtual endpoint uses `m_i^(1/4)`, so an internal bond supplies `sqrt m_i`.
   The normalized copy map cancels this against its inverse-square-root factor.
   Crossing-boundary factors retain exactly one fourth-root weight.
3. `CopyCanonicalParentTransport` lifts literal exterior matrix blocks to
   regional constraints. Every common-parent vector has the necessary source
   matching-sector support and target product-range support, derived from
   internal-edge coverage and actual internal slices. These support statements
   prove both inverse identities; no parent identity is assumed.
4. `CopyWeightPhysicalTransport` proves equality of actual weighted tensors
   with a sitewise invertible physical deformation of unweighted tensors.
   Therefore `canonicalMultiplicityChangeParentEquiv` compares arbitrary
   positive copy families, not only `m_i=1` or `m_i=d_i`.
5. `exists_isometry_multiplicityRestored_leftRegular` derives the regular
   character from the complete irreducible family and constructs a normalized
   Fourier matrix. This supplies the genuine regular coordinate intertwiner
   needed by the already validated all-boundary Fourier transport packet.
6. `GraphAveragingGInjective` proves that the canonical tensor is the average
   of the actual oriented incident representation: head `U(g)`, tail
   `transpose(U(g^-1))`. Its numbered local tensor map is G-injective, without
   unitarity or semi-regularity assumptions at this step.
7. The existing fixed-representation physical transport compares arbitrary
   physical G-injective tensors to this canonical tensor. Composing gives
   `nonempty_semiRegularGInjectiveParentEquiv`, the dimension identity, and
   `nonempty_ker_regionParentHamiltonian_semiRegularGInjective_equiv`.

## Exact hypotheses and source boundary

- Finite simple graph, with endpoint orientation determined by vertex order.
- One representation `U` used uniformly on edges. Unitarity is part of the
  source's semi-regular definition (paper lines 1010–1013), not an extra
  restriction on that definition.
- Constant incidence count supplies a common numbered physical alphabet at
  intermediate stages. Original physical tensors may have another dimension.
- Every edge is internal to at least one parent region. The arbitrary physical
  tensor comparison additionally needs every vertex covered by a region.
- Source-faithful local G-injectivity is stated for the explicit oriented
  incident action; no range/kernel equivalence is assumed.

This is not yet a native-torus closure-spanning theorem. Remaining integration:

1. Match the actual torus plaquette family, coordinate enumeration, and ordered
   endpoint convention to the native right/up torus model.
2. Identify the transported spanning vectors with the original named commuting
   pair closures, rather than only identifying equivalent spaces/dimensions.
3. The paper explicitly allows link-dependent representations (lines 1310–1316).
   This packet uses a uniform `U`. Reversing a native oriented edge replaces its
   representation by the contragredient; arbitrary multiplicities need not be
   dual-symmetric. Thus a link-dependent or arbitrary-orientation extension is
   needed for a fully automatic native orientation specialization.
4. Small-period tori that collapse parallel bonds remain a separate graph-model
   issue; constant incidence four is not automatic for those simple graphs.

The existing multiplicity-one public APIs remain intact as specializations of
independent `d,m` results. Generic coordinate/factor definitions were extracted
into shared modules to avoid duplicated proofs. The prior Fourier packet is
unchanged.

## Validation

The changed TNLean dependency closure, all new modules, and existing
multiplicity/Fourier regression modules compile with package lint options.
New regression uses block dimension 2 and copy counts 3 and 1 on an actual
two-vertex graph, so the generalized multiplicities are exercised concretely.
Principal theorem axiom audits list only `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, new axiom, or target-kernel premise was introduced.
Shared dependency sources/artifacts were not changed; exact QIC pin is
`2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`. No Mathlib rebuild was performed.
