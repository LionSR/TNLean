# Joint boundary compression and normalization

Source: GLM23v3, `Papers/2203.12563/REsubmission.tex`, lines 1695–1777.
Base: `5ff8b1f986d702da458392d71413355c7411b210`, the checked joint-column
and dependent-spectator checkpoint. The dependency manifest is unchanged.

## Mathematical content

`JointMixedEndpointEdgeFactors.lean` defines the actual first and last
two-site coefficient maps by evaluating `blockInsertedGroundSpaceMap` at
`(i, ι₀(j))` and `(ι₀(i), j)`. The adjacent site uses the entire original
shared alphabet of dimension `d₀`. Expanding the actual mixed letters gives

```
B_L(X) = (L ⊗ I_d₀) Φ_L((V_x† X_x)_x),
B_R(X) = (I_d₀ ⊗ R) Φ_R((X_x V_x)_x),
Φ_L(Y)[x,a,b;j] = (Aₓ⁰(j) Yₓ)[b,a],
Φ_R(Z)[i;x,c,e] = (Zₓ Aₓ⁰(i))[e,c].
```

The exterior dimensions in both core maps are arbitrary. The intended
canonical choice is `E_x = D₀ x`; the extended choice is
`E_x = D₀ x + D₁ x`. Padding with `V_x Y_x` or `Z_x V_x†` proves that the
virtual rectangular extraction maps are onto, with no positive-dimension
assumption.

`JointMixedEndpointEdgeNormalization.lean` compresses the actual maps with
`U_L† ⊗ I_d₀` and `I_d₀ ⊗ U_R†`. Simultaneous one-site spanning, already
among the source hypotheses, gives `U_L† L = P_L` and `U_R† R = P_R`.
The resulting maps have exactly the joint boundary weights `P_L` and `P_R`.
Their inverse weights give exact image-of-range equalities with the full
one-sided core supports. All factors act jointly on the block labels.

`JointMixedEndpointEdgeProjectors.lean` constructs the inverse-weight
changes as Euclidean linear equivalences and derives their exact support
images. For each support image `e(S) = T`, it proves both orientations

```
e.symm.deformedConstraintProjection Π_(S⊥) = Π_(T⊥),
e.deformedConstraintProjection Π_(T⊥) = Π_(S⊥).
```

These statements use orthogonal projections onto transported kernels,
not similarity conjugation. Neither the adjacent physical letter nor any
interior tensor is normalized.

`IsometricCompressionGap.lean` separately proves that a rectangular
isometry `U` whose range projection commutes with `H` satisfies
`H U = U (U† H U)` and `(U† H U) U† = U† H`. It identifies the compressed
kernel and its orthogonal complement, then restricts every norm-gap bound
without changing its constant. It does not assume ambient surjectivity,
positive dimensions, positivity, or self-adjointness. The physical
application must establish reduction.

## Exact remaining obligations

The coefficient maps above are actual cropped maps. Their compressed
ranges have not yet been identified with kernels of compressed actual
Hamiltonian terms. That requires the reducing range projections, using
the actual joint phase support identities and the joint polar frame
range. No such identification is assumed in any theorem in this package.

The full canonical and extended chain operators still need to be proved
equal, after boundary-only deformation and reindexing, to the dependent
spectator extensions of one common family indexed by all ordered pairs
`(x,y)`. In particular, the off-diagonal cases `x ≠ y` cannot be omitted.
This package introduces no chain operator or edge sum.

At length two, the first and last edge are the same edge. Both changes
must be applied to its one kernel, and the term must be counted once.
For separate first/last terms, require total length at least three.
The eventual unbounded canonical gap subsequence permits this threshold.

The uniform boundary norm bounds, the full inactive-sector lower bound,
and the canonical-to-extended chain comparison also remain open. No
endpoint-gap premise, blockwise physical orthogonality hypothesis,
per-block minimum of gaps, or uniform-gap conclusion is added here.

## Validation status

The individual-module proof gate passes on the exact public head
`7b6bbfab322bb2dbd2571606d4f4f11db060ceac` of PR #8724. GitHub Actions
[run 37443744958, build job 112204012969](https://github.com/LionSR/TNLean/actions/runs/37443744958/job/112204012969)
compiled all four production modules, ran the strict regression and all four
standard guards, and passed compiled declaration, style, and timing checks.
The tested merge checkout was `be05ad5dae147f1474b22f85ef912f8acc4a289a`;
its tree `79a28916888ebbd8fa56aa790fc496291c1e2bb0` is identical to the
authored source checkpoint `d8f74705c00cf21e4ad4cc083b7dd2af9ddb799c`.
Production compilation times were 2.6 seconds for the isometric restriction,
8.2 seconds for the edge coefficients, 2.9 seconds for normalization, and
5.8 seconds for the projection constraints. Each standard guard retained
exactly `propext`, `Classical.choice`, and `Quot.sound`.

This checked-documentation batch changes neither production nor regression
sources. Its blueprint adds 23 statement/proof markers for the 35 public
declarations. The exact proof-tested source hashes and CI identifiers are
recorded in the companion validation report. CI on the later documentation
head is separate and remains pending until publication and completion.
The proof-tested head's full blueprint job was still finishing its page
checks when the individual-module result was recorded; it is not represented
here as a completed full-documentation check.

Earlier local evidence is preserved separately: the exact edge-coefficient
file passed strict read-only Lean in 15 seconds, and the full real-source
bundle passed all four production leaves, both missing dependency sources,
the focused regression, and its four guards in 40 seconds with an empty log.
Those concatenation checks were not substitutes for individual module or
import-boundary validation. No cache or compiled Lean artifact was written
by the bounded probes, and no proof was replaced by a stub.

The unchanged base PR #8721 had already passed all eight checks at source
head `5ff8b1f986d702da458392d71413355c7411b210`, including its full blueprint,
browser checks, and strict regression guards. That is inherited evidence,
separate from the later #8724 proof gate and this documentation update.

Focused checks of the checked leaf pass with pinned latexindent 3.24.7.
All 35 public declarations have exactly one blueprint owner; global source
synchronization, scoped reverse coverage, reader-facing prose, forbidden
token, generated-import, and whitespace checks pass. The focused native PDF
has ten pages. Physical pages 4–7, containing all new checked mathematics,
and page 8, containing the inherited tensor diagram, were inspected without
clipping or overflow. There are no undefined-reference or missing-character
warnings. HTML contains all 22 labels of the new and preceding boundary
leaves, with no missing local anchors, duplicate IDs, or rendering sentinels.
The inherited Tenkz picture has a valid six-path SVG and passes the native
audit with zero hard errors and zero advisories; its expected source-wrapper
`tex-unlinked` note is recorded. This focused PDF/HTML verification is
separate from the full-book CI and does not claim browser inspection.

The focused regression retains two physically overlapping scalar labels
in a three-letter alphabet, so the canonical columns are rectangular.
It also covers the unused third physical direction, zero second dimensions,
empty labels, zero first fibers, a nonsurjective frame, and a zero-dimensional
compressed space with a nontrivial physical complement.

The generated imports, chapter include, and existing strict CI regression
loop were extended additively. No resource limit, dependency pin, existing
theorem hypothesis, or unrelated source file is changed.
