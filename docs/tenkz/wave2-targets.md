# Wave-2 author-figure target inventory

This inventory fixes the wave-2 source scope before any manifest target is added.
It covers every labelled TikZ block in the four author files for Sections II–V,
classifies ownership by the current RMP manifest, and names the language demand
created by each unowned block.

## Inventory rule

A labelled block starts at a line inside a `tikzpicture` whose first non-space
characters are `%%` or `%%%`, followed by nonempty text that is not a commented
TeX command. It ends immediately before the next labelled block in the same
picture, or immediately before that picture ends. This rule excludes empty
separators and commented drawing commands while retaining author labels such as
`(a)`, `Eq50`, and `Rtensor`.

A block is **owned** when its closed line interval overlaps an `author_lines`
interval in `tests/tenkz/rmp/manifest.toml` for the same `author_source`.
Otherwise it is **unowned**. The scan finds 107 labelled blocks: 90 owned and
17 unowned.

### `ImagesReview Section II/ImagesReview Section II.tex`

| Author label | Lines | Ownership |
|---|---:|---|
| `AL` | 192–198 | owned: `rmp-ii-canonical-left` |
| `AR` | 199–207 | owned: `rmp-ii-canonical-right` |
| `PT(A)` | 208–236 | owned: `rmp-ii-tangent-projector`, `rmp-workbench-ii-projector-on-pta` |
| `PEPS construction Fig1` | 237–248 | owned: `rmp-ii-peps-projection` |
| `PEPS construction Fig2 fiducial states` | 249–257 | owned: `rmp-ii-peps-projection` |
| `Fig 3 three vertex tensor` | 258–268 | owned: `rmp-ii-triangle-network` |
| `Fig 4 MPS and PEPS with their marginals` | 269–269 | owned: `rmp-ii-mps-marginal` |
| `MPS` | 270–286 | owned: `rmp-ii-mps-marginal` |
| `PEPS` | 287–304 | owned: `rmp-ii-peps-marginal` |
| `Figure 5: MPO and PEPO` | 305–316 | owned: `rmp-ii-mpo-sheet`, `rmp-ii-pepo-sheet` |
| `Figure 6 TI MPO positive` | 317–337 | owned: `rmp-ii-local-purification`, `rmp-workbench-ii-positive-mpo-old` |
| `Figure 7` | 338–338 | owned: `rmp-ii-local-purification` |
| `From thesis:` | 339–357 | owned: `rmp-ii-mpu-normal-form` |
| `from 1 to 3` | 358–373 | owned: `rmp-workbench-ii-peps-gauge-old` |
| `from 2 to 2` | 374–392 | owned: `rmp-workbench-ii-peps-gauge-without-a` |
| `Figure 8` | 393–393 | owned: `rmp-ii-mpu-unitarity` |
| `(a1)` | 394–404 | owned: `rmp-ii-mpu-unitarity` |
| `(a2)` | 405–432 | owned: `rmp-ii-mpu-blocking` |
| `(b1)` | 433–449 | owned: `rmp-ii-mpu-splitting` |
| `(b2)` | 450–464 | owned: `rmp-ii-mpu-brickwork` |
| `Figure 9` | 465–465 | owned: `rmp-ii-mpu-wrap` |
| `(a)` | 466–472 | owned: `rmp-ii-mpu-wrap` |
| `(b)` | 473–483 | owned: `rmp-ii-mpu-two-shift`, `rmp-workbench-ii-mpu-wrap-second` |
| `Figure 10 TN of reduced density matrix` | 484–534 | owned: `rmp-ii-reduced-density`, `rmp-ii-spectrum-fixed-points`, `rmp-ii-spectrum-rho`, `rmp-ii-spectrum-transfer` |
| `Figure 11 (old)` | 535–540 | owned: `rmp-ii-blocking` |
| `(a2)` | 541–546 | owned: `rmp-ii-staircase` |
| `(b)` | 547–571 | owned: `rmp-ii-circuit` |
| `Fig11 new (tangent space)` | 572–589 | **unowned** |
| `Def of V tensor` | 590–597 | owned: `rmp-ii-boundary-region`, `rmp-workbench-ii-boundary-a-old`, `rmp-workbench-ii-v-tensor-definition` |
| `(a)` | 598–617 | owned: `rmp-ii-boundary-region`, `rmp-workbench-ii-boundary-a-old` |
| `(b)` | 618–649 | owned: `rmp-ii-boundary-lasso`, `rmp-workbench-ii-boundary-b-old` |
| `(c)` | 650–684 | owned: `rmp-ii-boundary-state` |
| `AA=UA` | 685–701 | owned: `rmp-ii-rfp-isometry` |
| `Fig:ZCL-MPDO` | 702–713 | owned: `rmp-ii-zcl-mpdo` |
| `Fig: TandS` | 714–727 | owned: `rmp-ii-channels-ts` |
| `Fig:MPDO-O_L` | 728–741 | owned: `rmp-ii-mpdo-ol` |
| `Fig14` | 742–800 | owned: `rmp-ii-peps-rg`, `rmp-workbench-ii-peps-fine-graining`, `rmp-workbench-ii-peps-rg-workbench` |
| `Fig 15` | 801–832 | owned: `rmp-ii-inverse-renormalization`, `rmp-workbench-ii-historical-composite` |

### `ImagesReview Section III/ImagesReview Section III.tex`

| Author label | Lines | Ownership |
|---|---:|---|
| `S_alpha,g` | 114–132 | owned: `rmp-iii-a-symmetry-sector` |
| `Eq50` | 133–135 | owned: `rmp-workbench-iii-eq50` |
| `Eq51` | 136–143 | owned: `rmp-iii-a-boundary-algebra-n`, `rmp-workbench-iii-eq51` |
| `Eq52` | 144–149 | owned: `rmp-iii-a-boundary-algebra`, `rmp-workbench-iii-eq52` |
| `Diagram1` | 150–163 | owned: `rmp-iii-a-coproduct`, `rmp-workbench-iii-diagram-one` |
| `Diagram2` | 164–169 | owned: `rmp-workbench-iii-diagram-two` |
| `Diagram3` | 170–197 | owned: `rmp-workbench-iii-diagram-three`, `rmp-workbench-iii-historical-composite` |
| `Diagram4` | 198–210 | owned: `rmp-workbench-iii-diagram-four` |
| `Eq new52` | 211–219 | owned: `rmp-workbench-iii-eq50-reduced` |
| `Eq intertwiner` | 220–304 | owned: `rmp-iii-a-commuting-hamiltonian`, `rmp-iii-a-f-symbol`, `rmp-workbench-iii-dual-reduced`, `rmp-workbench-iii-f-symbol-simplified-a`, `rmp-workbench-iii-f-tensor`, `rmp-workbench-iii-mpo-representation` |
| `Eq 59now56` | 305–328 | owned: `rmp-iii-a-g-injective-projector`, `rmp-workbench-iii-eq59-now` |
| `diagram of clusterstate` | 329–356 | owned: `rmp-iii-a-ghz-state`, `rmp-workbench-iii-ghz-state-workbench` |
| `ghzupdownmatrix` | 357–362 | owned: `rmp-iii-a-ghz-tensor`, `rmp-iii-a-hadamard`, `rmp-workbench-iii-ghz-up` |
| `Frank's proof of MPS invariant under MPO` | 363–363 | owned: `rmp-iii-a-proof-one` |
| `proof1` | 364–375 | owned: `rmp-iii-a-proof-one` |
| `proof2` | 376–385 | owned: `rmp-iii-a-proof-two` |
| `proof3` | 386–413 | owned: `rmp-iii-a-proof-three` |
| `eq55now (Fig8previously draw)` | 414–447 | owned: `rmp-iii-a-pulling-through`, `rmp-iii-a-spt-mpo` |
| `Dia. intertwiner for SPT` | 448–467 | owned: `rmp-iii-a-spt-intertwiner`, `rmp-workbench-iii-intertwining-mpo` |
| `pullingthroughtforGinjective (Fig8previously draw)` | 468–500 | owned: `rmp-workbench-iii-g-injective-pull` |
| `veryold` | 501–520 | owned: `rmp-workbench-iii-mpo-injective-white` |
| `Explaining the MPO-injective PEPS` | 521–537 | owned: `rmp-iii-a-mpo-injective`, `rmp-workbench-iii-mpo-on-peps-definition` |
| `Eq.60now57` | 538–552 | owned: `rmp-iii-a-mpo-action`, `rmp-workbench-iii-eq60-now` |
| `Eq63now59` | 553–562 | owned: `rmp-iii-a-torus-two`, `rmp-workbench-iii-enlarged-mpo-black` |
| `Ed58now ->Torus` | 563–571 | owned: `rmp-iii-a-torus-one`, `rmp-workbench-iii-eq59` |
| `Eq62 (now 60)` | 572–603 | owned: `rmp-iii-a-torus-three`, `rmp-workbench-iii-eq59` |
| `4MPO` | 604–621 | owned: `rmp-workbench-iii-g-injective-mpo` |
| `PEPS4` | 622–630 | owned: `rmp-workbench-iii-peps-renormalization-one` |
| `PEPS4 renorm` | 631–643 | owned: `rmp-workbench-iii-peps-renormalization-two` |
| `Anyon` | 644–660 | owned: `rmp-iii-b-anyon-pair` |
| `Idempotent` | 661–687 | owned: `rmp-iii-b-idempotent` |
| `Dyon for GInj` | 688–703 | owned: `rmp-iii-b-dyon` |
| `Selfbraiding` | 704–738 | owned: `rmp-iii-b-self-braiding` |
| `Definition of R tensor` | 739–740 | owned: `rmp-iii-b-r-tensor-left` |
| `Part1` | 741–772 | owned: `rmp-iii-b-r-tensor-left` |
| `Part2` | 773–798 | owned: `rmp-iii-b-r-tensor-right` |
| `Braiding` | 799–799 | owned: `rmp-iii-b-braid-one` |
| `Part1` | 800–825 | owned: `rmp-iii-b-braid-one` |
| `Part2` | 826–957 | owned: `rmp-iii-b-braid-four`, `rmp-iii-b-braid-three`, `rmp-iii-b-braid-two`, `rmp-iii-b-condensation` |

### `ImagesReview Section IV/ImagesReview Section IV.tex`

| Author label | Lines | Ownership |
|---|---:|---|
| `GS subspace 1D` | 46–54 | owned: `rmp-iv-ground-space-1d` |
| `GS subspace 2D` | 55–70 | owned: `rmp-iv-ground-space-2d` |
| `Rtensor` | 71–78 | owned: `rmp-iv-intersection-rhs-one` |
| `Ltensor` | 79–86 | owned: `rmp-iv-intersection-lhs-one` |
| `Rtensor2` | 87–94 | owned: `rmp-iv-intersection-rhs-two` |
| `Ltensor2` | 95–102 | owned: `rmp-iv-intersection-lhs-two` |
| `Ltensor3` | 103–111 | owned: `rmp-iv-intersection-lhs-three` |
| `Rtensor3` | 112–121 | owned: `rmp-iv-intersection-rhs-three` |
| `Rtensor4` | 122–133 | owned: `rmp-iv-intersection-rhs-four` |
| `Ltensor4` | 134–141 | owned: `rmp-iv-intersection-lhs-four` |
| `Ltensor5` | 142–147 | owned: `rmp-iv-intersection-lhs-five` |
| `Rtensor5` | 148–155 | owned: `rmp-iv-intersection-rhs-five` |
| `Inverting and growing back R` | 156–172 | owned: `rmp-iv-intersection-lhs-six` |
| `Inverting and growing back L` | 173–190 | owned: `rmp-iv-intersection-rhs-six` |

### `ImagesReview Section V/ImagesReview Section V.tex`

| Author label | Lines | Ownership |
|---|---:|---|
| `4MPO` | 238–255 | **unowned** |
| `PEPS4` | 256–264 | **unowned** |
| `PEPS4 renorm` | 265–277 | **unowned** |
| `Fsymbols` | 278–280 | **unowned** |
| `Rtensor` | 281–288 | **unowned** |
| `Ltensor` | 289–296 | **unowned** |
| `Rtensor2` | 297–304 | **unowned** |
| `Ltensor2` | 305–312 | **unowned** |
| `Ltensor3` | 313–321 | **unowned** |
| `Rtensor3` | 322–331 | **unowned** |
| `Rtensor4` | 332–343 | **unowned** |
| `Ltensor4` | 344–351 | **unowned** |
| `Ltensor5` | 352–357 | **unowned** |
| `Rtensor5` | 358–365 | **unowned** |
| `Inverting and growing back R` | 366–383 | **unowned** |
| `Inverting and growing back L` | 384–402 | **unowned** |

## Proposed targets for unowned blocks

The descriptions follow the author TikZ rather than a rendered-asset guess. The
capability names come exclusively from the language concepts in
`docs/tenkz/LANGUAGE-1.0.md` Sections 5–6 or from capability names already used
by the RMP manifest.

| Proposed target | Author source and lines | Description | Capabilities |
|---|---|---|---|
| `rmp-w2-tangent-space-projector` | Section II, 572–589 | The tangent-space projector sums paired left and right ket-bra environments with boundary weights. | `grid`, `free-graph`, `typed-ports`, `equation-composition` |
| `rmp-w2-four-mpo-plaquette` | Section V, 238–255 | Four local MPO tensors meet at one plaquette with eight sector-labelled boundary legs. | `free-graph`, `four-site-plaquette`, `sector-labels` |
| `rmp-w2-four-peps-plaquette` | Section V, 256–264 | Four PEPS tensors occupy the edges of one renormalization plaquette. | `free-graph`, `four-site-plaquette`, `renormalization` |
| `rmp-w2-peps-block-renormalization` | Section V, 265–277 | A two-by-two PEPS block renormalizes to one effective four-leg tensor. | `lattice`, `blocking`, `equation-composition` |
| `rmp-w2-f-symbol-tensor` | Section V, 278–280 | One F-symbol tensor carries the trivalent fusion data and its labelled legs. | `coherence`, `fusion-tree` |
| `rmp-w2-right-intersection-word` | Section V, 281–288 | The right word joins boundary tensor R to tensors B and C and closes both virtual ends into R. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-left-intersection-word` | Section V, 289–296 | The left word joins tensors A and B to boundary tensor L and closes both virtual ends into L. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-right-intersection-after-inverse` | Section V, 297–304 | Applying the inverse of B leaves R, one exposed site, and C. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-left-intersection-after-inverse` | Section V, 305–312 | Applying the inverse of B leaves A, one exposed site, and L. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-left-intersection-regrown` | Section V, 313–321 | Growing B back gives A joined to B, one exposed site, and boundary tensor L. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-right-intersection-regrown` | Section V, 322–331 | Growing B back gives boundary tensor R, B, one exposed site, and C. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-right-intersection-with-s` | Section V, 332–343 | S acts on the right word formed by an uncovered wire, B, and C inside boundary tensor R. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-left-intersection-after-s-inverse` | Section V, 344–351 | The inverse of S removes the jointly injective A–B pair from the L side. | `free-graph`, `typed-ports` |
| `rmp-w2-left-boundary-two-indices` | Section V, 352–357 | After inversion, boundary tensor L retains two open indices. | `grid`, `typed-ports` |
| `rmp-w2-right-boundary-x` | Section V, 358–365 | The right boundary reduces to X attached to tensor C inside boundary tensor R. | `free-graph`, `closure`, `typed-ports` |
| `rmp-w2-right-boundary-window` | Section V, 366–383 | A two-dimensional R-boundary window surrounds its retained B–C interior. | `lattice`, `regions`, `typed-ports` |
| `rmp-w2-left-boundary-window` | Section V, 384–402 | A two-dimensional L-boundary window surrounds its retained B–A interior. | `lattice`, `regions`, `typed-ports` |

## Capability demand

The existing column counts blocked targets whose `missing` list names the
capability in `tests/tenkz/rmp/verdicts.toml`. The wave-2 column counts proposed
consumers above. The combined column is their sum; it is the demand to use when
ordering language work. These are deliberately different populations: the sum
combines planned source-block consumers with current blocked targets, not all
current manifest consumers. A repeated figure block remains a separate proposed
consumer because this inventory assigns coverage to each author-source
occurrence; the table does not deduplicate mathematically equivalent blocks.

| Capability | Wave-2 proposed consumers | Existing blocked targets | Combined demand |
|---|---:|---:|---:|
| `blocking` | 1 | 0 | 1 |
| `braid-resolver` | 0 | 3 | 3 |
| `closure` | 8 | 0 | 8 |
| `cluster-groups` | 0 | 1 | 1 |
| `coherence` | 1 | 0 | 1 |
| `crossing-order` | 0 | 9 | 9 |
| `enclosure-marks` | 0 | 10 | 10 |
| `equation-composition` | 2 | 2 | 4 |
| `four-site-plaquette` | 2 | 0 | 2 |
| `free-graph` | 12 | 0 | 12 |
| `fusion-tree` | 1 | 0 | 1 |
| `grid` | 2 | 0 | 2 |
| `group-average` | 0 | 2 | 2 |
| `kernel` | 0 | 0 | 0 |
| `lattice` | 3 | 0 | 3 |
| `marked-region` | 0 | 1 | 1 |
| `multi-strand-braid` | 0 | 2 | 2 |
| `open-string` | 0 | 1 | 1 |
| `pulling-through` | 0 | 3 | 3 |
| `regions` | 2 | 0 | 2 |
| `renormalization` | 1 | 0 | 1 |
| `ring-closure` | 0 | 2 | 2 |
| `rotated-action` | 0 | 5 | 5 |
| `sector-labels` | 1 | 0 | 1 |
| `staggered-sites` | 0 | 1 | 1 |
| `string-slide` | 0 | 1 | 1 |
| `strings` | 0 | 7 | 7 |
| `torus-cycle` | 0 | 4 | 4 |
| `typed-ports` | 13 | 0 | 13 |

`kernel` is listed to distinguish kernel-reachable pictures from 0.7 surface
pictures, but it is not missing language demand. Its twelve current consumers
are accepted targets recorded in the RMP manifest, so they do not enter either
demand column.

The `enclosure-marks` row is an audit exception rather than language demand.
Its ten existing blockers are stale Section IV intersection verdicts: their
manifest capabilities and cases use boundary atoms, in agreement with
`docs/tenkz/LANGUAGE-1.0.md` Section 14. Treat the semantic demand for
`enclosure-marks` as zero. Reclassifying those verdicts is separate work and is
deliberately outside this inventory-only change.
