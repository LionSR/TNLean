# Actual joint open-chain active projection

This source extension addresses the inactive sector of the zero-parameter
open interaction in GLM23, arXiv:2203.12563v3, Section 5, lines 1695–1777.
It does not establish the full endpoint gap.

## Mathematical content

Write `L` and `R` for the orthogonal projections onto the full joint polar
boundary ranges, and `row₀`, `column₀` for the physical phase selectors.
The actual support is contained in each of

- `ran(L ⊗ row₀)`;
- `ran(column₀ ⊗ R)`;
- `ran(column₀ ⊗ row₀)`.

These inclusions come from the existing full joint frame factorization and
the actual inner phase-fixing identities. They are not supplied as premises.
All joint Gram entries, shared physical directions, empty labels, and zero
dimensions remain present.

For `N = n + 3`, the `n + 2` nonwrapping bond constraints use the first
one-sided product on the first bond, the last one-sided product on the last
bond, and the inner product elsewhere. Their only overlaps are row and
column selectors on interior sites. Their product `Q` is therefore an
orthogonal projection. Its range is characterized by the full first frame,
the full last frame, and both zero-phase selectors at each of the `n + 1`
interior sites. The interior alphabet is the entire original shared
physical `00` space, including unused physical directions.

The source derives `Commute Q H` and `1 - Q ≤ H`, hence `1 - Q ≤ 2 • H`.
The coefficient-one estimate is an auxiliary strengthening from the chosen
commuting constraints, not a constant attributed to the paper. The actual
Hamiltonian terms are not assumed to commute. The two-site chain is handled
separately by its one full-frame term.

## Source ownership and validation

- `Martingale/SiteProjectionEmbedding.lean` identifies the existing local
  Euclidean extension with the existing circuit matrix embedding. It gives
  multiplicativity, projection transport, one-site placement, and disjoint
  support commutation. It does not introduce another embedding definition
  for multi-site operators.
- `JointMixedEndpointOneSidedSupport.lean` derives the full one-sided support
  and the separate first/last frame commutators and local penalties.
- `JointMixedEndpointInnerConstraints.lean` combines the actual inner phase
  constraints and transports all phase commutators to the open chain.
- `JointMixedEndpointOpenSectorPenalty.lean` constructs the actual active
  projection, identifies its range, and proves the reducing commutator and
  inactive penalty.
- `TNLeanTest/JointMixedEndpointOpenSectorPenalty.lean` includes overlapping
  physical labels, an unused physical direction, zero second fibers, zero
  first fibers, empty labels, `N = 3`, and the separate `N = 2` term. Ten
  standard-axiom guards cover the main statements and the embedding bridge.

The first source checkpoint covered 16 of the 69 added/promoted public
declarations in its blueprint leaf; the repository reverse-coverage checker
found 53 missing owners. This was incomplete reverse coverage, despite every
existing tag resolving. The documentation completion assigns all 69 declarations
exactly one mathematical owner across three focused leaves: 14 embedding and
binary-diagonal declarations, 32 one-sided-support declarations, and 23 inner
and open-chain declarations. There are 23 coherent mathematical owning entries,
with no checked markers. Private helpers are excluded.

The repository reverse-coverage checker now reports zero missing declarations
for the actual four-leaf source diff from `d4b97308` through `4870c749`, plus
its promoted public binary-diagonal declaration. The focused source-sync check
also passes with duplicate ownership treated as an error: all 69 tags resolve.
The complete ownership inventory, source hashes, rendered-artifact hashes,
and validation limits are in
`2026-10-06_glm23_joint_open_sector_blueprint_validation.json`.

The focused PDF has 11 pages. Final pages 3–9, including the tensor-product
diagram, were inspected as raster images. The PDF log has no warnings,
overfull boxes, or underfull boxes. The focused web build succeeds; all 69
owner links render, every target label and local anchor resolves, all image
resources exist, and raw-HTML reader checks pass for six generated pages.
The review repaired missing anchors on multi-line displays and prepared the
numbered bibliography in the temporary web fixture. The Tenkz event audit
reports two new pictures in one display, zero hard findings, and zero
advisories. This is a presentational equation row: no hard `tenkzeq` group
check ran. The fallback SVG converter is the restored
XeLaTeX/PDF/pdftocairo route because `dvisvgm` is unavailable.

Browser inspection is **unverified**. Chromium failed before opening a page
because creating its process-singleton Unix socket returned
`Operation not permitted`. No alternate browser route or sandbox change was
attempted. Browser layout and dynamic MathJax checks therefore remain pending.

The pinned `latexindent` 3.24.7 byte-comparison check passes for all three
leaves, as do the changed reader-facing prose and whitespace checks.
No Lean compiler, Lake build, or Lean cache operation ran; native elaboration
and the ten actual axiom-guard outputs remain unverified. Completion markers
remain absent from every newly owned statement and proof.

Root imports, shared workflow lists, the common blueprint input list, and
shared `blueprint/lean_decls` remain unchanged. The three new leaves should
be integrated after the full-frame reduction, in this order:

1. `ch30_mpo_joint_site_projection_embedding.tex`
2. `ch30_mpo_joint_one_sided_support.tex`
3. `ch30_mpo_joint_open_sector_penalty.tex`

No MPU or PEPS source was changed. Publication is handled separately by the
parent task; this completion is preserved locally as a clean source commit,
a patch against the already preserved checkpoint, and a source/render archive.

## Remaining endpoint argument

This package does not identify or gap the active compressed Hamiltonian.
The subsequent argument must connect its actual boundary-normalized
constraints to the unchanged joint `A₀` bulk and the common ordered-pair
core family, and derive the needed uniform comparison. No per-block gap
minimum, blockwise physical orthogonality, or interior normalization is
introduced here.
