# GLM23: the actual mixed block family

## Source and scope

The source is GLM23 v3, `Papers/2203.12563/REsubmission.tex`, lines
1695–1777. The mixed block tensor and bond weight occur at lines
1695–1704. The joint finite-volume boundary results used here are in
`JointInsertedBoundary`, `JointInsertedIntersection`, and
`JointInsertedOpenKernel`. Those modules are not changed by this addition.
The source SHA-256 is
`c820b20187584d441c1a40ef80fdccbc8a2aad819ac6673464c6b913c28fa58c`.

This step constructs the actual mixed family and derives its simultaneous
one-site span from the simultaneous one-site spans of the two supplied
endpoint families. It then applies the existing joint boundary and open-kernel
results to that constructed family. The endpoint span assumptions are explicit;
separate injectivity of each endpoint block does not replace them.

The blueprint leaf is
`blueprint/src/chapter/ch30_mpo_joint_mixed_family.tex`. It is included immediately after the generic joint inserted-boundary leaf.
The generated import frontier includes all three production modules, and the
existing mixed-interaction regression loop includes the seven-guard test.
The checked markers cover the compiled construction and finite-volume results
listed below; they make no spectral-gap or MPO-symmetry claim.

## Physical and virtual coordinates

There is one common block label set and two shared physical endpoint alphabets.
The physical alphabet is

```
Fin d0 ⊕ ((Σ x, Fin (D0 x) × Fin (D1 x)) ⊕
  ((Σ x, Fin (D1 x) × Fin (D0 x)) ⊕ Fin d1))
```

The two endpoint alphabets occur exactly once. A diagonal physical letter
acts by the corresponding original endpoint matrix in every block. Each
cross letter contains its block label and produces its rectangular matrix
unit in that block only. Its value in every other block is zero. This gives
physical dimension `d0 + d1 + 2 * Σ x, D0 x * D1 x` and bond dimension
`D0 x + D1 x` in block `x`.

Writing the unweighted family as `C`, the actual path is
`A_x(γ) = C_x W_x(γ)`, where
`W_x(γ) = (1−γ) I_(D0 x) ⊕ γ I_(D1 x)`. The weight is on the outgoing
virtual bond. The attached Tenkz equality has one internal virtual
contraction and the same two virtual and one physical open legs on both
sides. The block label is a fixed parameter in this equality, not an
additional tensor leg or a physical label on the diagonal sectors.

## Span and finite-volume conclusions

1. For a target tuple of mixed matrices, decompose each matrix into four
   corners. Simultaneous endpoint spanning gives common coefficients across
   all blocks for each diagonal corner. The explicitly block-labelled cross
   letters supply every off-diagonal entry. Thus the mixed family has
   simultaneous one-site span without a new span assumption about the result.
2. For `0 < γ < 1`, right multiplication by every `W_x(γ)` is invertible.
   The same simultaneous span holds for the path family. The path letters
   depend continuously on the real parameter.
3. First-corner compression of the actual base recovers the original first
   family, extended by zero outside its single endpoint physical alphabet.
   Rectangular compression by an inverse pair preserves the simultaneous
   span. The proof applies this to the derived mixed span.
4. The final weight omitted from the inserted word is absorbed into the
   boundary: `Γ_N(CW)(X) = Γ′_N(C,W)(WX)`. Invertible blockwise boundary
   reparametrization identifies the actual interior extended support with
   the sum of the actual canonical block supports at every positive length.
   This identity needs no span hypothesis. It is the joint form of the
   paper's support identification at lines 1690–1692.
5. When both endpoint bond dimensions are positive in every block,
   `W_x(γ) ≠ 0` for all real `γ`. The joint inserted boundary map is therefore
   injective at every positive length, including the singular values `γ = 0`
   and `γ = 1`. Its rank is `Σ x, (D0 x + D1 x)^2`.
6. For every `N ≥ 2`, the actual sum of the `N−1` nonwrapping two-site
   extended parent terms has kernel equal to that joint boundary range and
   the same dimension. Its orthogonal projector varies continuously at each
   fixed length. The generic inserted results supply these consequences once
   the actual mixed span and nonzero weights are established.

## Boundaries of this result

The paper's line 317 concerns thermodynamic orthogonality of distinct blocks.
It supplies no exact one-site orthogonality of their physical columns. The
separating inverse at lines 1332–1349 is represented here by an explicit
simultaneous span hypothesis, retaining arbitrary overlaps of the original
columns. No per-block orthogonality or independent physical copy of an
endpoint alphabet is introduced.

The open boundary domain is the product of the mixed block matrix algebras,
of dimension `Σ x, (D0 x + D1 x)^2`. It is neither the full matrix algebra
of the summed bond space nor the smaller embedded endpoint boundary domain.
In particular, the singular values of the insertion do not justify deleting
open boundary coordinates.

This addition proves no volume-independent spectral gap, boundary-completion
comparison, periodic endpoint kernel identification, fixed-MPO commutation,
or degenerate phase classification. Those obligations are unchanged. A
minimum of separate block gaps and fixed-volume projector continuity do not
supply the missing joint endpoint spectral comparison.

## Validation

The final checked source checkpoint is
`06075cb0a7a63b9131434ee622248124ecf8bde5`. The production proof sources are
unchanged from `fc1c7f8baa355c1d80bb0220d79eb2246491374c`; the final checkpoint
shortens one regression command through an already-open namespace to satisfy
the strict line-length linter. It retains the original theorem names in the
expected guard output and introduces no alias or warning suppression.
The build used Lean 4.35.0-rc3, commit
`470d5ce1400764999581fd26d5d72b00d990b0f4`. Machine-readable native evidence is
`/workspace/shared/glm23-recovery/joint-mixed-native-validation.json`.

The verified SHA-256 values are:

| File | SHA-256 |
| --- | --- |
| `TNLean/MPS/SharedInfra/JointOneSiteSpan.lean` | `7f7034c5c4139faf4e74a5e17ed2f8ddec380aaec73205f6b820920ceaa883ac` |
| `TNLean/MPS/Symmetry/MPOSymmetry/JointMixedEndpointFamily.lean` | `ea08244da6a35eb6fb7db74fdfc64d953041ee0dc43209c77fc41addb622d89d` |
| `TNLean/MPS/Symmetry/MPOSymmetry/JointMixedEndpointSupport.lean` | `d8eb09afda3f5eb42424d7829f903c82744b5f9f0c5a2240fe1a12be8dd67f0d` |
| `TNLeanTest/JointMixedEndpointFamily.lean` | `b2f45fb65f21349a2fa7892ce4c9585574373cbf38f4d660b854aa8313f91831` |

The native production command was:

```sh
source /workspace/shared/glm23-env.sh
LEAN_NUM_THREADS=2 lake build TNLean.MPS.Symmetry.MPOSymmetry.JointMixedEndpointSupport
```

It exited zero after 9,299 jobs; the final support-module build took 101
seconds locally. None of the three changed production modules emitted a
warning. Lake replayed inherited deprecation warnings from Gametheory and
QICLean dependencies. The log is
`/workspace/shared/glm23-recovery/joint-mixed-build-final.log`.

The strict regression command was:

```sh
LEAN_NUM_THREADS=2 lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false -Dpp.unicode.fun=true -DmaxSynthPendingDepth=3 -Dlinter.mathlibStandardSet=true -DwarningAsError=true TNLeanTest/JointMixedEndpointFamily.lean
```

It exited zero, and
`/workspace/shared/glm23-recovery/joint-mixed-regression-checked.log` is empty.
All seven original theorem guards passed with exactly `propext`,
`Classical.choice`, and `Quot.sound`. The regression retains two overlapping
endpoint columns `(1,0)` and `(1,1)` with inner product one, checks physical
dimension eight, and covers the joint support rank, singular endpoint,
canonical interior support, exact open kernel, and projector continuity.

All 27 public declarations have exactly one owner in the blueprint leaf.
Six statement markers and five proof markers record the completed checks;
the separate extended-support notation definition has no new declaration
owner and remains unmarked. The four canonical-support declarations
`insertedEvalWord_mul_right`, `blockGroundSpaceMap_rightMul_eq_inserted`,
`range_blockInsertedGroundSpaceMap_eq_of_isUnit`, and
`jointMixedEndpoint_extendedGroundSpace_eq_iSup` are included in that coverage.
Every dependency and reference label resolves uniquely.

The full repository source-synchronization check passes with the exact
pinned QICLean source revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`
visible through a local source symlink: zero missing declarations, zero
duplicate owners, and zero stale declaration records. The generated-import
check covers 2,722 production modules with 71 aggregators. The only CI edit
is one added regression name in the existing mixed-interaction loop.

The leaf was formatted with the repository's checksum-verified
`latexindent` 3.24.7 and passed its one-file CI formatting check. The three
previously missing HTML anchors were repaired without changing their
mathematics: the alphabet label is on the first row, and the cross-corner
and boundary-map identities each have their own labelled display.

The exact native Tenkz picture body was compiled in an ordinary equation
wrapper and a `tenkzeq` boundary-signature check; both two-panel forms passed
with zero hard errors and advisories. The rasterized ordinary PDF was
visually inspected: the two virtual legs and single physical leg agree,
the internal virtual connection is visible, and the labels do not overlap.
Native evidence remains under
`/workspace/shared/glm23-blueprint-validation/joint-mixed-native/`.

The final checked-marker focused fixture under
`/workspace/shared/glm23-blueprint-validation/joint-mixed-checked/`
compiled to 11 PDF pages, four HTML files, and six SVGs. The three changed
mathematical pages, physical PDF pages 3–5, were rasterized and visually
inspected after adding the markers. They have no overflow, clipping,
unresolved references, or overlapping labels. Context and bibliography
pages 6–11 are byte-identical to the previously inspected raster images.
All three repaired HTML anchors occur exactly once, every leaf label has a
static HTML anchor, and there are no missing images or unresolved citation
sentinels. The pinned `texra-blueprint bbl` generated the web bibliography.
Three PDF overflow warnings and the missing `eq:mpo_mixed_letters` HTML
anchor belong to unchanged extracted context. The detailed report is
`review.json`; outputs are `blueprint/src/print.pdf` and
`blueprint/web/ch-mpo_symmetry_basics.html` beneath the same fixture path.

Cloud-browser visual inspection remains unavailable: the authorized same-call
retry rejected the local `file:` URL because the browser permits only HTTP
and HTTPS. No further browser retry or route workaround was attempted.
The HTML evidence is static inspection, not a claimed browser pass. No
Lean/Lake command, cache mutation, or dependency change was performed by the
documentation task. The production and strict-regression evidence above comes
from the task holding the single build slot. Later documentation changes do
not reattribute a previous commit's results to a later source tree; affected
remote CI and timing checks remain separate.
