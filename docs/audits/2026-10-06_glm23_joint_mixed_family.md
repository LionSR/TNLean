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
No new checked markers are attached without compile evidence for the
corresponding exact source.

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

Source-only coverage matches all 27 public declarations from
`SharedInfra/JointOneSiteSpan.lean`, `MPOSymmetry/JointMixedEndpointFamily.lean`,
and `MPOSymmetry/JointMixedEndpointSupport.lean` to exactly one owner in the
new leaf. This includes the four canonical-support bridge declarations
`insertedEvalWord_mul_right`, `blockGroundSpaceMap_rightMul_eq_inserted`,
`range_blockInsertedGroundSpaceMap_eq_of_isUnit`, and
`jointMixedEndpoint_extendedGroundSpace_eq_iSup`. Every referenced label
resolves uniquely in the blueprint source. No checked markers are present.

The full repository source-synchronization check also passes with the exact
pinned QICLean source revision `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`
visible through a local source symlink: zero missing declarations, zero
duplicate owners, and zero stale declaration records. The generated-import
check covers 2,722 production modules with 71 aggregators. The only CI edit
is one added regression name in the existing mixed-interaction loop.

The exact native Tenkz picture body was compiled with the restored pinned
documentation environment, both in its ordinary equation wrapper and in a
`tenkzeq` boundary-signature check. Both two-panel forms passed the Tenkz
audit with zero hard errors and zero advisories. The ordinary PDF was
rasterized and visually inspected: the two virtual legs and single physical
leg agree, the internal virtual connection is visible, and the labels do not
overlap. The harness explicitly loads the existing Computer Modern font maps
because the restored environment lacks a generated default font map.

Local render and source-check evidence is in
`/workspace/shared/glm23-blueprint-validation/joint-mixed-native/`:
`joint-mixed-wrapper.pdf`, `joint-mixed-wrapper.png`,
`joint-mixed-signature.pdf`, their TeX/log files, and
`source-validation.json`. These are documentation-only checks, not Lean
verification or a full blueprint web build.

The source regression retains two overlapping endpoint columns `(1,0)` and
`(1,1)` with inner product one, checks physical dimension eight, and states
the joint support-rank and singular-endpoint consequences. Its compilation
and guarded axiom reports are still pending. No Lean/Lake command or cache
change was run for this documentation task. All new Lean declarations remain
uncompiled at this checkpoint; the parent task owns the first compile. No
success from a previous commit is attributed to the current source tree.
