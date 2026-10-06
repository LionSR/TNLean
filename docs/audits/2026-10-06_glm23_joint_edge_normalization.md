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

The unchanged base PR #8721 passed all eight checks on exact source head
`5ff8b1f986d702da458392d71413355c7411b210`, including the full blueprint
and browser checks and the strict regression guards. Its test merge
`b31d1af` had the identical tree `bcdc61aa`. These inherited checks do
not validate the new edge leaves.

The generic isometric-compression leaf passed a strict one-thread Lean
elaboration probe, with all package strictness and linter options enabled,
before its integration. The exact complete `JointMixedEndpointEdgeFactors.lean`
file now passes a strict one-thread read-only elaboration check in 15 seconds,
with an empty log. A later strict source-bundle check also passes all four
production leaves and the complete focused regression, including all four
standard guards, in 40 seconds with an empty log. It includes the complete real
sources of the two missing dependency leaves, replaces only their internal
imports, and isolates each source body in a section. No definition or proof
is replaced by a stub. This is not an individual Lake-target or module-import
check; those remain pending. The first authorized
read-only probe timed out at the external 60-second wall limit with no
diagnostics; exit 124 is inconclusive, not a successful check. It wrote no
Lean artifact or cache. The shared heavy-build slot is reserved for this
package after the current owner releases it.

The new blueprint leaf deliberately has no `leanok` markers, including
for the generic isometry assertions, until the coherent package passes
individual native module checks. The strict standard guards have executed
successfully in the exact-source bundle. The scoped source and
render checks are recorded separately from native proof validation.

Static validation passes: forbidden proof-token checking, generated-import
synchronization, file-size and changed non-comment line-length checks,
reader-facing prose, and the pinned latexindent 3.24.7 byte comparison.
Global blueprint/source synchronization and reverse coverage find all 35
new public declarations with no missing or duplicate owners. The source
checker reads manifest-identical QICLean sources from the canonical
validation checkout, without creating a source-worktree Lake cache.

The focused PDF has ten pages. All four pages containing the new leaf
(physical pages 4–7) were inspected after the final render. There are no
overflow, undefined-reference, or missing-character warnings. The HTML
has all 22 labels of the new and preceding boundary leaves, no broken
local anchors, duplicate IDs, or rendering sentinels. The inherited
Tenkz picture rendered to a six-path SVG. This is focused PDF and HTML
validation, not browser inspection or a whole-book build. Detailed render
evidence is in the companion validation report.

The focused regression covers two physically overlapping scalar labels
in a three-letter alphabet, so the canonical columns are rectangular.
It also covers zero second endpoint dimensions, empty labels, zero
first fibers, a nonsurjective isometry, and a zero-dimensional compressed
space with a nontrivial ambient space. Four strict guards expect exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The generated module imports, chapter include, and existing strict CI
regression loop are extended additively. No resource limit, dependency pin,
existing theorem hypothesis, or unrelated source file is changed.
