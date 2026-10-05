# GLM23: actual multiplicity mixed pentagon

## Scope and baseline

This additive source package follows the boundary L-matrix package at published
head `c708e9119275d0015e7430a92b16a0fa362a9c85`, exact tree
`4e8d709a172965b110739dc5b4b82087e394899b`. The local source-only worktree starts
from commit `e6a935cd3049eadec80ebedb0c45e5d019c43e46` with that same tree.
No existing production theorem, router, workflow, dependency pin, or source
correction note is changed.

The source is Garre-Rubio--Lootens--Molnár, arXiv:2203.12563v3,
`REsubmission.tex`: `algcond`, `eq:compatible`, `Fsymbolsdef`, `eq:F_symbol2`,
`1Fsymbol`, `coupledpent` (lines 554–562), and Appendix A. The reused ordinary
fusion comparison/pentagon APIs cite arXiv:1511.08090; their opposite F
orientation is identified explicitly rather than silently attributed to GLM23.

## Actual conclusions and premises

`MPOTensor.actionLMatrix_mixed_pentagon` takes the original exact biorthogonal
fusion/action maps, individual injectivity of the operator and state blocks,
positive virtual dimensions, and no scalar-gauge duplicates within each
family. It concludes the mixed pentagon for `actionLMatrix` and `fusionFMatrix`
computed from those same unblocked maps.

`MPOTensor.IsBoundaryCompatible.exists_exact_mixed_pentagon` additionally
derives the exact maps from arbitrary-boundary operator closedness and
operator/state compatibility of the assembled unweighted block tensors. Its
premises contain neither simultaneous word spanning nor coherence. In both
boundary hypotheses, one output boundary is chosen before quantifying all
positive chain lengths; length-by-length closure alone is not substituted.

No ambient support identity, positivity/star closure, categorical unit,
duality, scalar multiplicity assumption, or entrywise nonzero L assumption is
introduced. Finite multiplicity spaces may be empty. Gauge covariance and
the separate group/coset specialization are outside this package.

## Construction and orientation

1. Embed operator letters in the upper-left physical corner of size `d+1`
   and state letters in its upper-right column. Products encode the original
   operator product and action exactly. Every state-left product is zero.
2. The auxiliary labels are `Fin r ⊕ Fin s`. Only operator/operator-to-operator
   and operator/state-to-state channels are populated. All other channels are
   empty; there is no zero-tensor label. Original V/W matrices are unchanged.
3. Physical padding preserves individual injectivity and within-kind gauge
   separation; the disjoint physical supports imply cross-kind separation.
   Relabel only the common-inverse argument through `finSumFinEquiv`. Derive a
   positive common blocking and return its inverse rows to the Sum labels.
   The blocked physical dimension is `(d+1)^L`, not `d^L+1`.
4. Exact reconstruction gives the complete zipper equations. The existing
   ordinary pentagon supplies `C B A = E D`; the proved lifted inverse
   `A Q = I` gives `E D Q = C B`. No coherence field is assumed.
5. The comparison entries are identified with actual contractions. Auxiliary
   `P[⟨z,j,i⟩,⟨c,mu,k⟩]` equals the original
   `actionLMatrix[⟨z,i,j⟩,⟨c,k,mu⟩]`, since both are normalized traces of
   sequential analysis followed by fusion-then-action synthesis.
6. `fusionFMatrix` is the normalized trace of left fusion analysis followed by
   right fusion synthesis. It equals the reused API's `inversePrintedFMatrix`
   for the original exact fusion family and for the auxiliary operator-only
   sector. Thus the remaining inverse edge is the actual GLM F coefficient.

The five fourfold spaces for input `(a,b,c,x)` and final state `y` are:

- `S0 = (((ab)c)x)`: `(d,e,eta,chi,m)`
- `S1 = ((a(bc))x)`: `(f,e,mu,nu,m)`
- `S2 = a((bc)x)`: `(f,z,mu,l,i)`
- `S3 = (ab)(cx)`: `(d,t,eta,k,n)`
- `S4 = a(b(cx))`: `(t,z,k,j,i)`

The result therefore uses F row `(d,eta,chi)` and column `(f,mu,nu)`.
This is the typed local correction to both reversed multiplicity pairs in
the source coupled pentagon. The correction is already documented in
`docs/paper-gaps/glm23_multiplicity_l_indices.tex`.

## Dependency and validation boundary

The elementary padding, exact-decomposition transport, and scalar-gauge
restriction adapters import no phase-gap modules. The ordinary mixed
orientation/entry identities use only the existing complete zipper pentagon
cone. The normalized-trace F bridge uses only its ordinary inverse APIs.

The actual P=L adapter imports the already checked `BoundaryActionLMatrix`
cone. The common-blocking source constructor imports `BoundaryZipperBlocked`
and its source simultaneous-span cone. These heavier imports are confined to
the adapters that actually use them.

At the integration checkpoint on 5 October 2026, the exact source files
`TriangularPhysicalPadding`, `TriangularPaddingDecomposition`,
`CompleteZipperFusionMixedOrientation`, and `BoundaryActionTreeEntries`
passed canonical builds. Strict standalone elaboration also passed
`CompleteZipperFusionTrace`, `CompleteZipperFusionMixedEntries`, and the
explicitly typed `TriangularBoundaryDecomposition` repair. These checks do
not establish the remaining capstone dependency chain or the new regression
files; both remain pending. No `leanok` marker is asserted yet.

The five ownership leaves cover all 55 public declarations exactly once.
Their combined nineteen-page PDF was rendered and visually inspected, and
the actual pinned strict web renderer passed a focused combined document.
Source/reverse declaration synchronization, generated imports, module-size,
proof-token, YAML, formatting and whitespace checks passed. Full exact-head
repository CI and final review remain required.

The exact checked production hashes are:

- `TriangularPhysicalPadding`: `6271d149c032e6eb3f183867d495f170aede884e0453fce88a5c727dc954564f`
- `TriangularPaddingDecomposition`: `c623cf26d708f4517408b65c0bf2ac809a0223e7284203d64f0224426157cf75`
- `CompleteZipperFusionMixedOrientation`: `68d2694c238ddc86af1106278b9ee5bc15be81beea3f6f3d288d84fe9aa17ee2`
- `BoundaryActionTreeEntries`: `c3d6b9152ed27068b74a54a0b1bcbc8862028ed8d263c5e69cd32fe241beb151`
- `CompleteZipperFusionTrace`: `0b649703cea2b27b8419a22491a558d659e65e27664fda16835ea470b2c9985c`
- `CompleteZipperFusionMixedEntries`: `0b616e0c11c959e2aa518f1d36253064ae20ddb72a64246a17e1afd3d27f4cd4`
- `TriangularBoundaryDecomposition`: `033ce5352b9286137a48355b978b203006bc25c1ee2bac2f7cfb58b7c72b8950`

All Lean checking uses the one canonical cloud checkout. Source worktrees
perform no independent cache mutation. The PR remains a draft while the
source-derived capstone and its guarded axiom reports are unverified.
