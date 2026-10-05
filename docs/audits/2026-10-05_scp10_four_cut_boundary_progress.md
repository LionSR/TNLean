# SCP10 four-block cut spaces: foundation-stage scope

This records the foundation stage at commit `6b1ffc2b1`. The subsequent
common-alphabet reverse inclusion and closure equality are proved in
[the reconstruction audit](2026-10-05_scp10_four_cut_closure_reconstruction.md).
The gaps listed below describe that earlier foundation stage.

Source: Schuch, Cirac, Pérez-García, arXiv:1001.3807,
Theorem 5.5, `Papers/1001.3807/paper_v3.tex`, lines 1421–1513.

## Literal geometry, not a parent-kernel substitute

The model uses the native edge-labelled two-by-two torus. Its four horizontal
and four vertical bonds are distinct, including parallel bonds between the
same adjacent vertices. A cut `(c,r)` opens the horizontal bonds with head
column `c` and vertical bonds with upper row `r`. Its four uncut bonds carry
identity pairings. There are eight independent open endpoints.

`TorusCutBoundaryConfig 2 2 V` is the full endpoint configuration type, and
`torusCutMap a c r` accepts any complex-valued function on that type. In
particular, a boundary can correlate all eight endpoints. The product boundary
`torusCutBondBoundary` is one class of allowed boundary tensors, not the
definition of the space. The actual four-cut space is the intersection of
the four ranges. It is not a simple-graph region range, a parent kernel, or an
abstract subspace supplied together with the desired closure classification.

## Proved in this packet

- `TorusCutBoundary`: actual linear contractions, coefficient/range membership,
  fixed-endpoint spanning, the full boundary cardinality, and the exact bridge
  from product boundary matrices to the original native bond network.
- `TorusCutClosureMembership`: actual site-dependent commuting closures lie in
  every cut range, with explicit witnesses. This forward inclusion uses one
  uniform matching representation and only each site's virtual invariance.
  No injectivity or isometry is assumed.
- `TorusMatchedBondRepresentation`: different horizontal and vertical
  representations on all eight labelled bonds, with the same representation
  read at its two endpoints. Incoming legs use the representation and outgoing
  legs its inverse transpose. Unitarity and algebraic semi-regularity are
  separately explicit predicates on every bond.
- `TorusCutPhysicalMap`: distinct rectangular physical maps commute with every
  actual cut contraction and with the actual native closure contraction.
- `TorusCutLocalInverse`: actual local G-injective inverses preserve the entire
  boundary tensor. A common product inverse works for every cut. Consequently,
  the physical four-cut intersection is exactly the image of the canonical
  averaging-tensor intersection. This reduction allows different matched bond
  actions and independent site tensors; it does not assume closure spanning.
- `TorusCutProjectorExpansion`: the canonical contraction is the normalized
  sum over four independent vertex group labels, retaining the original joint
  boundary tensor. The normalization is the fourth power of the inverse group
  order on the two-by-two torus.
- `TorusCutCoefficientExtraction`: the source's trace-dual pairing on each
  actual semi-regular bond extracts one coefficient from any coherent
  bond-product sum. The bond-product family is linearly independent and equality
  of coherent sums is equality of coefficients. Different bond representations
  are allowed. The nonabelian relative-label compatibility identity and its
  commutation consequence are also proved.

## What is still missing

The reverse inclusion of Theorem 5.5 is not proved. In particular, this packet
does not establish that an arbitrary canonical four-cut vector lies in the
bond-product span. Coefficient uniqueness is used only for vectors explicitly
expressed as such sums, and is not silently used to supply that expression.

The next geometric step is to derive a base-cut block inverse by the source's
three link concatenations and the remaining connected-block leg contraction.
Apply it to opposite-cut membership to obtain relative labels
`h₁=b⁻¹a`, `h₂=d⁻¹c`, `v₁=c⁻¹a`, `v₂=d⁻¹b` and their compatibility
`v₂h₁=h₂v₁`. Compare with the horizontally and vertically shifted cuts, using
trace-dual extraction on coherent sums, to force `h₁=h₂` and `v₁=v₂` on the
coefficient support. Only then infer commutation and reconstruct the closure.
The existing concatenation and leg-contraction inverse theorems may be reused;
their identifications with this concrete four-block boundary map remain work.

The forward closure-membership theorem currently uses a uniform bond
representation. The matching-bond data, canonical reduction, and coherent
coefficient extraction already support independent bond representations, but
nonuniform seam deformation is not proved in this packet. All coordinate
alphabets currently have the same finite type `V`; arbitrary bond dimensions
and site-dependent physical alphabets remain extensions. The tensors
`a v` themselves are fully site-dependent.

No theorem in this packet should replace the source-labelled Theorem 5.5 or
mark it formalized. No global parent classification is used in any proof.

## Validation and integration

The seven new modules and `TNLeanTest/PEPS/FourTorusCut.lean` are checked with
the pinned Lean toolchain, strict implicit arguments, Mathlib's standard
linters, and warnings as errors. The test checks the 256 endpoint and bond-label
configurations for a two-element alphabet, an explicit correlated boundary
that cannot factor into independent bond matrices, site-dependent hypotheses, matched
nonuniform local actions, and coherent coefficient uniqueness. Axiom inspection
of the main results is included. All results use only the standard Lean axioms.

The packet adds only new Lean, regression-test, and audit files. Shared import
routers, blueprint labels, and paper-gap claims are intentionally left to the
integrator; the source theorem must remain open there.

The finite-sum/product permutation proof used by sitewise physical-map
transport also occurs in `TorusPhysicalMap`. This is a candidate for a future
finite-site contraction lemma; no general contraction infrastructure is
replaced by the present patch.
