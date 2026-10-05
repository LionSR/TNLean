# SCP10 Theorem 5.5: dimension-independent four-block closure

## Result

The source-faithful capstone is:

`TNLean.PEPS.DependentTorus.fourCutSpace_eq_commutingClosureSpan`

in `TNLean/PEPS/DependentTorusClosureTheorem.lean`.

It proves that the intersection of the four literal edge-cut ranges equals
the span of the actual commuting closure vectors for four arbitrary
G-injective blocks. Every one of the eight bonds may have its own finite
virtual alphabet and its own matching semi-regular representation. Every one
of the four sites may have its own physical alphabet and tensor.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807, Theorem 5.5,
`Papers/1001.3807/paper_v3.tex`, lines 1421–1513. The representation matching
convention is Definition 5.1 and lines 1310–1316. Coefficient extraction uses
Lemma 4.6, lines 1015–1029.

## Signature-to-source comparison

- **Finite group:** the finite-group context of the source is retained.
- **Separate bond spaces:** `D : Bond → Type*`, with a finite type on each
  bond; no equal-dimension or common-alphabet assumption remains.
- **Separate physical spaces:** `Phys : Vertex → Type*`, finite at each site;
  no common physical dimension is imposed.
- **Matching representations:** each oriented bond has one representation
  on its own alphabet. Its head reads the representation and its tail reads
  the inverse transpose. The two incident tensors therefore use precisely
  the same representation on that link, as required by the source.
- **Semi-regularity:** assumed independently on all eight actual bonds,
  not merely on a four-leg product representation.
- **Unitarity:** the source's unitary convention is not needed by the algebraic
  proof. Omitting it generalizes the result; it adds no hypothesis to the
  source's statement.
- **G-injectivity:** assumed separately for every physical tensor and its
  actual incident representation. No G-isometry or normalization is added.
- **Boundary data:** each of the four ranges permits one arbitrary joint
  tensor on all cut endpoints. No factorization or initial boundary-invariance
  hypothesis is imposed.
- **Conclusion:** the intersection of those four actual ranges is exactly
  the span of the same four tensors closed with commuting group labels.
  Neither side is defined using the other.

There is no period-at-least-three assumption, no homogeneous tensor or uniform
representation assumption, no extra graph-region hypothesis, no assumed
parent-kernel identity, and no supplied closure-spanning premise.

## Exact geometry

The vertex type is the two-by-two torus. A labelled bond is a vertex paired
with a direction flag: horizontal bonds point right, vertical bonds point
down. A second, independent flag identifies the head or tail endpoint.
Consequently, the opposite bonds joining the same two vertices remain distinct.
No simple-graph adjacency quotient is used for the contraction or the cuts.

`TorusLabelledBondGeometry` proves:

- four vertices and eight independently labelled bonds;
- four distinct endpoint incidences at every vertex;
- four cut bonds and eight distinct cut endpoints for each seam pair;
- every bond is uncut in at least one of the four cuts;
- the uncut relative labels satisfy the appropriate plaquette relation.

The matrix convention is consistently head-row, tail-column. Actual coefficient
contraction sums over all independent endpoint assignments. The cut tensor
uses identities on uncut edges and one arbitrary joint function of the cut
endpoints. Fixed endpoint columns are proved equal to the actual networks
with matrix units on cut edges. The tests include correlated boundaries that
cannot factor into independent edge matrices.

## Proof route

1. The generic dependent network and cut maps retain every endpoint and its
   own alphabet. Site-incidence regrouping and edge-pair regrouping are actual
   equivalences, not supplied coordinate identities.
2. The local invariant projectors are the actual averages of the incident
   representations. Expanding their contraction yields a coherent sum over
   vertex group labels, with the factor `|G|⁻⁴` retained on the four-block torus.
3. In every cut, a one-bond slice on an uncut edge lies in that edge's
   representation-matrix span. The four cuts cover all bonds by such uncut
   edges. The dependent product-range theorem therefore derives the complete
   coherent bond-product expansion.
4. The trace-dual pairing extracts coefficients from that expansion. A nonzero
   coefficient in a cut range must admit one vertex-label assignment realizing
   its labels simultaneously on every uncut edge. The four uncut plaquette
   edges then satisfy the nonabelian flatness equation. Thus all nonflat
   coefficients vanish in the four-cut intersection.
5. Flat assignments on the actual labelled torus are vertex-gauge equivalent
   to two commuting seams. This is the rooted-tree group calculation at period
   two, retaining all parallel bonds.
6. The product of local invariant projectors fixes every canonical cut vector.
   It maps each bare bond product to its actual canonical network. Canonical
   vertex-gauge invariance then identifies every surviving flat term with an
   actual commuting closure. This proves the reverse inclusion.
7. A pure group-valued seam gauge moves each commuting closure to any of the
   four cuts. The resulting representation matrices are explicit boundary
   witnesses, proving the forward inclusion.
8. Genuine local G-injective inverses, with each site's own physical dimension,
   give one common product map for all cuts. Its recovery map identifies the
   intersection with the image of the canonical intersection and recovers the
   actual commuting closure span. This proves the theorem for the original
   independent physical tensors.

The argument is noncircular. In particular, coherent bond support is derived
before coefficient comparison, and no termwise inference is made on a sum
before applying the trace-dual functionals.

## Validation and regressions

All new source modules are checked using the pinned Lean toolchain with
`autoImplicit=false`, `relaxedAutoImplicit=false`, `maxSynthPendingDepth=3`,
Mathlib's full standard linter set, and warnings as errors. No Mathlib rebuild
or package update is used. The combined validation compiles all new modules
in import order, followed by every new regression module.

The capstone regression `TNLeanTest/PEPS/DependentTorusClosure.lean` checks the
full unrestricted signature and a concrete example with one dimension-two
bond and seven dimension-one bonds. Its physical site spaces have different
dimensions as well. The dimension-two bond carries two trivial copies and is
therefore genuinely nonregular. The example supplies actual canonical local
G-injectivity and invokes the full physical-tensor capstone.

Supporting regressions cover virtual dimensions two and three, physical
dimensions five and seven where no injectivity is requested, parallel edges,
self edges, empty alphabets/edge sets, nonfactorizable correlated boundaries,
heterogeneous matrix ranks, noncommuting S3 seam labels, and the explicit
native gauge/holonomy formulas. Guarded axiom reports for the full capstone,
nonflat-coefficient elimination, and common local-inverse intersection contain
only `propext`, `Classical.choice`, and `Quot.sound`.

## Integration notes

This result removes the dimensional restriction documented in
`2026-10-05_scp10_four_cut_closure_reconstruction.md`. The earlier uniform and
common-alphabet results remain valid specializations. The dependent support
module has a Mathlib-only import graph. The common-alphabet site-dependent
product helpers now specialize it directly, removing their repeated slice and
retraction proofs. The pre-existing constant-matrix support module is outside
this packet's new-file scope and remains a later integration consolidation target.

Shared import routers, blueprint source labels, and the paper-gap note are
left to the integrator. The source-labelled Theorem 5.5 should cite the full
`DependentTorus` capstone above, not the preceding common-alphabet theorem.
The generic dependent infrastructure may be reused for other source targets;
this audit makes no claim about Theorem 5.4 or the geometric reblocking target.
