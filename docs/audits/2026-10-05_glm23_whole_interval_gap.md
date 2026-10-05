# GLM23 whole-interval gap: source and validation checkpoint

Checkpoint: 5 October 2026. This records a draft continuation and its exact
local evidence; it is not a full-paper completion claim.

## Source assumptions and conclusion

Source context: Garre-Rubio–Lootens–Molnár, arXiv:2203.12563v3,
`Papers/2203.12563/REsubmission.tex`, Section 5, lines 1687–1692;
the finite-window compactness argument follows arXiv:1010.3732, Appendix A.

The candidate declaration
`MPSTensor.MPOSymmetry.exists_uniform_mixedEndpoint_periodic_path_gap`
takes positive natural bond dimensions D₀,D₁ and the actual given tensors
Aₚ : MPSTensor (Dₚ * Dₚ) Dₚ, each one-site injective. Its conclusion is one
δ>0 such that δ‖v‖≤‖H′γ,N v‖ on the actual periodic kernel complement,
for every γ∈[0,1] and every N≥2. The constant may depend on the endpoints.
The square physical alphabets are assumptions, not an unstated reduction
from arbitrary original alphabets. No fixed-point, supplied gap, kernel
identity, or projector-continuity premise is added.

The proof derives endpoint open gaps by bounded changes at the two boundary
sites and free-exterior-register comparison. Strict windows persist locally;
Knabe is used only in the injective interior, with m+1 sites and N≥2m.
Separate endpoint periodic bounds cover the ends. Compactness gives a
uniform large-volume bound, and the continuous actual periodic ground line
handles the finitely many shorter rings. Full MPO covariance along the path
and the resulting symmetric-phase classification remain separate.

## Immutable compiler checkpoint

Of 26 additional production modules, the following eight exact repaired
versions have local canonical targeted-build passes. The other 18, including
`MixedEndpointUniformPathGap`, and both new strict regression files remain
pending at this checkpoint. Earlier frozen or warning-bearing versions do
not inherit the passes below. Later CI results must identify their own tree
and bytes rather than retrospectively changing this checkpoint.

| Module | Checked SHA-256 |
| --- | --- |
| `SquarePhysicalCoordinates` | `4bc2d69d57bfad4df4b506573347d7c30bcba9e2dec702ba61ab22d5811b6ddd` |
| `MixedEndpointBoundaryFactors` | `27434b4dccd7fda6d432bcd3d6564e1b5a01afaacc3e86e698f7abbf13b7a582` |
| `MixedEndpointBoundaryCoordinates` | `7fc0e92d26f6f6323bb709be2d7fd0b2d3a3bcf7f6c4d984b285664b4c11c2f6` |
| `BoundedCongruenceGap` | `81bb3e0de99f02a78e3bff75f24aec74975fed68aad791e1cdfb150567192fcd` |
| `LocalEquivalenceBounds` | `e88204615c1b2f56ee327338f0a8bf9320383e4b5c463194b1f4855d5353ab58` |
| `MixedEndpointOpenSectors` | `a17c56a7b281421019ad9146ea2de8d84d08c1b736d110ebc0ea447d2773eb6d` |
| `BoundedProjectionDeformation` | `e3bcc360a3e46c1a74568277709792806aaa105986e94496013749104c45db99` |
| `MixedEndpointActiveBoundaryTransport` | `9dc053fbf4f0e9180b5eab15af24d656e0b22ba6851ec389d9b07cd5ac93a88e` |

The final assembly source under review has SHA-256
`aa71b0ea4c35a480230ec594525a5225063494ee8b72feacff9a901d138fe1ed`.
It has no compiler pass credited here. `TNLeanTest/MixedEndpointOpenGap.lean`
and `TNLeanTest/MixedEndpointUniformPathGap.lean`, including their guarded
axiom expectations, have not passed the new strict-regression checkpoint.
Expected guard messages are not observed axiom-audit results.

## Review and documentation evidence

Independent mathematical review of the exact assembly and separate review
of its continuity prerequisites found no mathematical or hypothesis leak.
Earlier endpoint-chain reviews checked the boundary deformation directions,
volume-independent norm bounds, exact local projections, and spectator
comparison. These are source reviews, not Lean elaboration evidence.

The two continuation leaves now uniquely own all 378 named top-level public
declarations in the 26-module cone. Their original 369 owners and labels
are preserved; seven coordinate aliases and two edge-index types fill the
nine missing owners. Both leaves remain without `leanok` markers.

The actual pinned texra-blueprint 0.3.8 strict web CLI passes with exit 0.
Generated-source/HTML checks, all references, 378 main declaration links,
and pinned latexindent idempotence pass. A 28-page focused PDF includes the
two leaves and exact supporting excerpts. All affected main-text pages were
visually inspected; the final log has no warnings or overflow. A preview-only
2em emergency line-stretch setting fixes an unchanged appendix heading;
no shared preamble changed. Interactive browser checks are not claimed.

Frozen leaf hashes:

- `ch30_mpo_mixed_open_gap.tex`:
  `fdc36ddd9413c6eb51ef78def0ada97131fedff035162020912efc7cfae548ca`
- `ch30_mpo_mixed_uniform_path_gap.tex`:
  `c4557da78356973dbedf047baa15ad9500bd3b2069d9f7edb2518d6f0de6634e`

This documentation work adds no compiler credit and changes no Lean source,
router, workflow, dependency, or verification marker. Publication of a draft
does not establish the pending theorem cone or the full phase classification.

## Publication structure

The publication snapshot separates the active-edge coordinate/placement
results from the boundary-normalization and deformed-sum identities.
`MixedEndpointActiveEdgePlacement` now imports only the prerequisites for
its 457-line coordinate development; the new 664-line
`MixedEndpointActiveEdgeNormalization` imports it and owns the normalization
results. The two consumers import the latter module. Declaration names and
proof bodies are preserved, and all 378 public owners remain unchanged.
The draft therefore has 27 production modules: the eight checked hashes
above and nineteen modules still requiring validation. No compilation
credit is inferred from this source-only structural split.

## Subsequent compiler checkpoint: 2026-10-05 22:36 UTC

The published `7d39eed` head's workflow did not reach Lean compilation:
its starting job was cancelled during the GitHub Actions incident. Those
cancellations are not evidence of a mathematical or compiler failure.

Local validation subsequently compiled the repaired
`MixedEndpointActiveEdgePlacement` (SHA-256
`faf560f28f995057a24521a7a527c0e25df5c75c2a16133aa05e935d7392af31`),
plus `MixedEndpointRightComparison` and `RingEndpointRightComparison`.
The first full check of `MixedEndpointActiveEdgeNormalization` found
coordinate-projection argument, definitional-coercion, and explicit-argument
errors. This batch repairs those proof terms without changing its theorem
statements. Its strict follow-up check lost the executor connection without
a terminal result; no compilation pass is credited to that repair.
The final normalization hash under review is
`548d6e29cf4de5e0f28e7596c5b5fe322b9daf4be3e2920585254c132bd0079d`.
The downstream open-gap and whole-path conclusions remain unverified until
fresh exact-head CI succeeds, including both guarded regression files.

This batch also narrows the imports of `PhysicalGibbsEmbedding` to its
actual algebraic dependencies and makes `TopologicalPhysicalGibbs` import
its domain-specific prerequisite explicitly. The former's unchanged body
passed a strict check and a targeted build. The exposed scalar-inner-product
proof in `BondProductSpectralGap` is repaired using explicit inner-product
identities; its statement is unchanged and its strict check and targeted
build passed. No toolchain or dependency pin changes are included.
