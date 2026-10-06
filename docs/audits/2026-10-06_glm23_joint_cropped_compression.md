# Actual joint cropped interaction audit

Source: GLM23v3, `REsubmission.tex`, lines 1695–1777. This is the next local Hamiltonian bridge after the joint boundary normalization and full-frame packages.

## Exact scope

The new proof source derives the missing local statement: compressing the actual zero-parameter parent interaction by the first joint polar frame and the neighboring full physical-00 inclusion gives exactly the orthogonal-complement projector of the compressed coefficient support. The last edge has the reflected identity. Boundary-only canonical normalization then yields the original-tensor one-sided core constraint. This is not yet the chain Hamiltonian identification or a uniform endpoint gap.

The proof has two stages. First, a coordinate isometry restricts the adjacent physical site to the entire shared first alphabet. Its range projection is the product of the checked row and column phase selectors at that site. Their actual commutators with the support projector give reduction. The generic reducing-isometry kernel theorem identifies the compressed kernel with the adjoint image of the actual support, which is proved equal to the cropped coefficient support by explicit boundary witnesses. The full support is not assumed to be contained in this phase crop.

Second, the trace-derived coefficient factorization writes that cropped support in the range of the joint polar frame tensored with the identity on the neighboring first alphabet. Supported-parent compression therefore applies at this stage. The exact adjoint image is the already defined compressed support from the boundary normalization package. Composition of the two actual isometries closes the local Hamiltonian identity. The inverse positive factor changes the kernel; no similarity-conjugation formula for an orthogonal projector is asserted.

## Source and dependencies

The checked frame/core integration base is authored commit `3b4ff7c1fe616fcb9be7325675e66e1635246ec4`. Four phase leaves are copied byte-for-byte from checked #8722 source `7526a088de379402132b015c8186ec879e07fa42`: `JointMixedEndpointSectors`, `JointMixedEndpointCornerSupport`, `JointMixedEndpointReducingSectors`, and `ReducingProjectionGap`. They are reused dependencies, not new results in this package. Source hashes are in the companion validation JSON.

Three new production leaves contain 36 public declarations:

- `ReducingParentCompression`: symmetric-projection compression under a derived reducing commutator, the exact support kernel, canonical parent projection, and composition of compressions.
- `JointMixedEndpointPhysicalCrop`: both coordinate embeddings/isometries, exact physical-00 range projections, actual reduction, adjoint support images, and physically cropped operator/kernel identities.
- `JointMixedEndpointCroppedCompression`: both boundary polar isometries, derived support containment, exact adjoint images, composite physical inclusions, actual edge projector/kernel identities, and normalized core constraints.

All 36 declarations have direct mathematical blueprint owners. The focused blueprint contains one tensor-network diagram of joint polar reconstruction. New source files remain unregistered in shared import routers and workflows pending parent-controlled integration.

## Hypotheses and degeneracies

Physical phase cropping uses no injectivity or span hypothesis. Polar isometries use exactly simultaneous one-letter spanning of each endpoint family. The matrices and positive factors act jointly across block labels; no off-diagonal label Gram entries are dropped and no blockwise physical orthogonality is assumed. The neighboring physical alphabet is unchanged and may contain unused directions. Empty labels and zero-dimensional physical or virtual fibers require no chosen inhabitants.

The two-site open chain has a single interaction. Its two boundary changes use the existing full product frame theorem once. The first and last cropped local identities are not added at this length.

The regression includes overlapping block labels with nonzero second virtual fibers, an unused third bulk letter, both actual compression orientations, vanishing second virtual fibers, empty labels, an empty first alphabet, the single two-site full-frame term, and a rectangular example whose full support is explicitly not contained in the crop. Six dependency guards require only `propext`, `Classical.choice`, and `Quot.sound`.

## Validation and recovery

The original `/workspace/shared` tree disappeared before any bridge compiler command ran. The first 326-line physical-crop draft was preserved in the surviving task directory with SHA256 `19a68d120fb87da6222a1739cfa2a514d6dcfbc0fa40d2779cfe1226537581bf`, then restored on the remotely preserved frame/core base. The new source was checkpointed before continuing. No bridge proof or guard has yet been accepted by Lean. The parent owns restoration of the official pinned toolchain and prebuilt cache; no duplicate build or cache mutation was started here.

Whitespace and the source-only forbidden-token/resource-override scans pass. These checks are not elaboration evidence. Native module validation, strict regression guards, and compiled declaration checks remain pending. Accordingly, the new blueprint has no checked markers.

The focused six-page PDF and HTML now render successfully. The mathematical pages 3–5 and the joint polar diagram were visually inspected; the final native log has no overfull boxes, undefined references, or missing characters. All 14 source labels have HTML anchors, with no duplicate IDs or unresolved-reference text. Both current tensor panels contain nonempty SVG paths (10 and 6), and the linked Tenkz audit reports zero hard errors and zero advisories. The pinned formatter 3.24.7 passes.

Independent source review found no mathematical blocker and corrected a private matrix-coordinate helper to include the decidable equality required by the upstream Euclidean matrix map. The source/blueprint synchronization checker finds no new-leaf issues and the manual reverse-ownership check covers all 36 public declarations. The global synchronization result remains incomplete because this separate worktree has no restored QIC source link; inherited QIC references are reported missing. None of these checks is a Lean elaboration pass.

## Remaining chain work

The package closes individual cropped local interactions only. Assembly at every chain length, spectator multiplicities, and transfer of a uniform gap to the actual open Hamiltonian remain separate tasks.

For the later inactive-sector penalty, the stronger inclusions `S ⊂ ran(U_L) ⊗ row₀` and `S ⊂ column₀ ⊗ ran(U_R)` follow by intersecting the full-frame support inclusion with the existing row/column support-fixing identities. This package does not yet expose those combined inclusion statements or the chain inequality `I − Q ≤ 2H`.
