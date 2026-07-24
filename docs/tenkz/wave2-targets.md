# Wave-2 RMP author targets

This inventory records every drawing block headed by a nonempty `%%`,
`%%%`, or `%%%%` label in the Section II--V author files. A block starts at
its outermost consecutive label and ends at the last source line before the
next labelled drawing. Consecutive heading and panel labels, such as
`Figure 8` and `(a1)`, form one block; doubled-percent picture-style setup
between them does not split the block. TeX commands commented with doubled
percent signs and empty separator comments are not labels.

Ownership means that at least one `author_lines` interval in
`tests/tenkz/rmp/manifest.toml` intersects the block in the same
`author_source` file. It does not identify a visually similar block in a
different author file. Under that rule, 17 labelled blocks are unowned.

## Mechanical inventory

### Section II

| Lines | Author label | Ownership |
|---|---|---|
| 192--198 | `AL` | owned: `rmp-ii-canonical-left` |
| 199--207 | `AR` | owned: `rmp-ii-canonical-right` |
| 208--236 | `PT(A)` | owned: `rmp-ii-tangent-projector`, `rmp-workbench-ii-projector-on-pta` |
| 237--248 | `PEPS construction Fig1` | owned: `rmp-ii-peps-projection` |
| 249--257 | `PEPS construction Fig2 fiducial states` | owned: `rmp-ii-peps-projection` |
| 258--268 | `Fig 3 three vertex tensor` | owned: `rmp-ii-triangle-network` |
| 269--286 | `Fig 4 MPS and PEPS with their marginals` / `MPS` | owned: `rmp-ii-mps-marginal` |
| 287--304 | `PEPS` | owned: `rmp-ii-peps-marginal` |
| 305--316 | `Figure 5: MPO and PEPO` | owned: `rmp-ii-mpo-sheet`, `rmp-ii-pepo-sheet` |
| 317--337 | `Figure 6 TI MPO positive` | owned: `rmp-ii-local-purification`, `rmp-workbench-ii-positive-mpo-old` |
| 338--357 | `Figure 7` / `From thesis:` | owned: `rmp-ii-local-purification`, `rmp-ii-mpu-normal-form` |
| 358--373 | `from 1 to 3` | owned: `rmp-workbench-ii-peps-gauge-old` |
| 374--389 | `from 2 to 2` | owned: `rmp-workbench-ii-peps-gauge-without-a` |
| 393--404 | `Figure 8` / `(a1)` | owned: `rmp-ii-mpu-unitarity` |
| 405--432 | `(a2)` | owned: `rmp-ii-mpu-blocking` |
| 433--449 | `(b1)` | owned: `rmp-ii-mpu-splitting` |
| 450--464 | `(b2)` | owned: `rmp-ii-mpu-brickwork` |
| 465--472 | `Figure 9` / `(a)` | owned: `rmp-ii-mpu-wrap` |
| 473--483 | `(b)` | owned: `rmp-ii-mpu-two-shift`, `rmp-workbench-ii-mpu-wrap-second` |
| 484--534 | `Figure 10 TN of reduced density matrix` | owned: `rmp-ii-reduced-density`, `rmp-ii-spectrum-rho`, `rmp-ii-spectrum-transfer`, `rmp-ii-spectrum-fixed-points` |
| 535--540 | `Figure 11 (old)` | owned: `rmp-ii-blocking` |
| 541--546 | `(a2)` | owned: `rmp-ii-staircase` |
| 547--571 | `(b)` | owned: `rmp-ii-circuit` |
| 572--589 | `Fig11 new (tangent space)` | **unowned** |
| 590--597 | `Def of V tensor` | owned: `rmp-ii-boundary-region`, `rmp-workbench-ii-boundary-a-old`, `rmp-workbench-ii-v-tensor-definition` |
| 598--617 | `(a)` | owned: `rmp-ii-boundary-region`, `rmp-workbench-ii-boundary-a-old` |
| 618--649 | `(b)` | owned: `rmp-ii-boundary-lasso`, `rmp-workbench-ii-boundary-b-old` |
| 650--684 | `(c)` | owned: `rmp-ii-boundary-state` |
| 685--701 | `AA=UA` | owned: `rmp-ii-rfp-isometry` |
| 702--713 | `Fig:ZCL-MPDO` | owned: `rmp-ii-zcl-mpdo` |
| 714--727 | `Fig: TandS` | owned: `rmp-ii-channels-ts` |
| 728--741 | `Fig:MPDO-O_L` | owned: `rmp-ii-mpdo-ol` |
| 742--800 | `Fig14` | owned: `rmp-ii-peps-rg`, `rmp-workbench-ii-peps-fine-graining`, `rmp-workbench-ii-peps-rg-workbench` |
| 801--831 | `Fig 15` | owned: `rmp-ii-inverse-renormalization`, `rmp-workbench-ii-historical-composite` |

### Section III

| Lines | Author label | Ownership |
|---|---|---|
| 114--132 | `S_alpha,g` | owned: `rmp-iii-a-symmetry-sector` |
| 133--135 | `Eq50` | owned: `rmp-workbench-iii-eq50` |
| 136--143 | `Eq51` | owned: `rmp-iii-a-boundary-algebra-n`, `rmp-workbench-iii-eq51` |
| 144--149 | `Eq52` | owned: `rmp-iii-a-boundary-algebra`, `rmp-workbench-iii-eq52` |
| 150--163 | `Diagram1` | owned: `rmp-iii-a-coproduct`, `rmp-workbench-iii-diagram-one` |
| 164--169 | `Diagram2` | owned: `rmp-workbench-iii-diagram-two` |
| 170--197 | `Diagram3` | owned: `rmp-workbench-iii-diagram-three`, `rmp-workbench-iii-historical-composite` |
| 198--210 | `Diagram4` | owned: `rmp-workbench-iii-diagram-four` |
| 211--219 | `Eq new52` | owned: `rmp-workbench-iii-eq50-reduced` |
| 220--304 | `Eq intertwiner` | owned: `rmp-iii-a-f-symbol`, `rmp-iii-a-commuting-hamiltonian` and four workbench targets |
| 305--328 | `Eq 59now56` | owned: `rmp-workbench-iii-eq59-now` |
| 329--356 | `diagram of clusterstate` | owned: `rmp-iii-a-ghz-state`, `rmp-workbench-iii-ghz-state-workbench` |
| 357--362 | `ghzupdownmatrix` | owned: `rmp-iii-a-ghz-tensor`, `rmp-iii-a-hadamard`, `rmp-workbench-iii-ghz-up` |
| 363--375 | `Frank's proof of MPS invariant under MPO` / `proof1` | owned: `rmp-iii-a-proof-one` |
| 376--385 | `proof2` | owned: `rmp-iii-a-proof-two` |
| 386--413 | `proof3` | owned: `rmp-iii-a-proof-three` |
| 414--447 | `eq55now (Fig8previously draw)` | owned: `rmp-iii-a-pulling-through`, `rmp-iii-a-spt-mpo`, `rmp-workbench-iii-g-injective-pull` |
| 448--467 | `Dia. intertwiner for SPT` | owned: `rmp-iii-a-spt-intertwiner`, `rmp-workbench-iii-intertwining-mpo` |
| 468--500 | `pullingthroughtforGinjective (Fig8previously draw)` | owned: `rmp-iii-a-g-injective-projector` |
| 501--520 | `veryold` | owned: `rmp-iii-a-g-injective-projector`, `rmp-workbench-iii-mpo-injective-white` |
| 521--537 | `Explaining the MPO-injective PEPS` | owned: `rmp-iii-a-mpo-injective`, `rmp-workbench-iii-mpo-on-peps-definition` |
| 538--552 | `Eq.60now57` | owned: `rmp-iii-a-mpo-action`, `rmp-workbench-iii-eq60-now` |
| 553--562 | `Eq63now59` | owned: `rmp-iii-a-torus-one`, `rmp-workbench-iii-enlarged-mpo-black` |
| 563--571 | `Ed58now ->Torus` | owned: `rmp-iii-a-torus-three`, `rmp-workbench-iii-eq59` |
| 572--603 | `Eq62 (now 60)` | owned: `rmp-iii-a-torus-two`, `rmp-workbench-iii-eq59` |
| 604--621 | `4MPO` | owned: `rmp-workbench-iii-g-injective-mpo` |
| 622--630 | `PEPS4` | owned: `rmp-workbench-iii-peps-renormalization-one` |
| 631--643 | `PEPS4 renorm` | owned: `rmp-workbench-iii-peps-renormalization-two` |
| 644--660 | `Anyon` | owned: `rmp-iii-b-anyon-pair` |
| 661--687 | `Idempotent` | owned: `rmp-iii-b-idempotent` |
| 688--703 | `Dyon for GInj` | owned: `rmp-iii-b-dyon` |
| 704--738 | `Selfbraiding` | owned: `rmp-iii-b-self-braiding` |
| 739--772 | `Definition of R tensor` / `Part1` | owned: `rmp-iii-b-r-tensor-left` |
| 773--798 | `Part2` | owned: `rmp-iii-b-r-tensor-right` |
| 799--825 | `Braiding` / `Part1` | owned: `rmp-iii-b-braid-one` |
| 826--953 | `Part2` and its unlabelled continuations | owned: `rmp-iii-b-braid-two`, `rmp-iii-b-braid-three`, `rmp-iii-b-braid-four`, `rmp-iii-b-condensation` |

### Section IV

| Lines | Author label | Ownership |
|---|---|---|
| 46--54 | `GS subspace 1D` | owned: `rmp-iv-ground-space-1d` |
| 55--70 | `GS subspace 2D` | owned: `rmp-iv-ground-space-2d` |
| 71--78 | `Rtensor` | owned: `rmp-iv-intersection-rhs-one` |
| 79--86 | `Ltensor` | owned: `rmp-iv-intersection-lhs-one` |
| 87--94 | `Rtensor2` | owned: `rmp-iv-intersection-rhs-two` |
| 95--102 | `Ltensor2` | owned: `rmp-iv-intersection-lhs-two` |
| 103--111 | `Ltensor3` | owned: `rmp-iv-intersection-lhs-three` |
| 112--121 | `Rtensor3` | owned: `rmp-iv-intersection-rhs-three` |
| 122--133 | `Rtensor4` | owned: `rmp-iv-intersection-rhs-four` |
| 134--141 | `Ltensor4` | owned: `rmp-iv-intersection-lhs-four` |
| 142--147 | `Ltensor5` | owned: `rmp-iv-intersection-lhs-five` |
| 148--155 | `Rtensor5` | owned: `rmp-iv-intersection-rhs-five` |
| 156--172 | `Inverting and growing back R` | owned: `rmp-iv-intersection-lhs-six` |
| 173--190 | `Inverting and growing back L` | owned: `rmp-iv-intersection-rhs-six` |

### Section V

The unlabelled CZX block at lines 147--219 is already owned by
`rmp-app-czx-state`; it is outside this labelled-block inventory.

| Lines | Author label | Ownership |
|---|---|---|
| 238--255 | `4MPO` | **unowned** |
| 256--264 | `PEPS4` | **unowned** |
| 265--277 | `PEPS4 renorm` | **unowned** |
| 278--280 | `Fsymbols` | **unowned** |
| 281--288 | `Rtensor` | **unowned** |
| 289--296 | `Ltensor` | **unowned** |
| 297--304 | `Rtensor2` | **unowned** |
| 305--312 | `Ltensor2` | **unowned** |
| 313--321 | `Ltensor3` | **unowned** |
| 322--331 | `Rtensor3` | **unowned** |
| 332--343 | `Rtensor4` | **unowned** |
| 344--351 | `Ltensor4` | **unowned** |
| 352--357 | `Ltensor5` | **unowned** |
| 358--365 | `Rtensor5` | **unowned** |
| 366--383 | `Inverting and growing back R` | **unowned** |
| 384--402 | `Inverting and growing back L` | **unowned** |

## Proposed targets

Descriptions state the visible mathematical object. Capabilities use the
language of `LANGUAGE-1.0.md` Sections 5--6 and the capability words already
present in the benchmark manifest or blocked-verdict ledger.

| Proposed target | Drawn object | Author lines | Required capabilities |
|---|---|---|---|
| `rmp-w2-ii-tangent-space-projector` | A tangent-space projector summand with ket--bra chains, left and right closures, and square-root fixed-point insertions. | II:572-589 | `grid`, `typed-ports`, `closure`, `equation-composition` |
| `rmp-w2-v-four-mpo-plaquette` | A cyclic square of four MPO atoms with two labelled virtual indices at each corner. | V:238-255 | `four-site-plaquette`, `ring-closure`, `typed-ports` |
| `rmp-w2-v-four-peps-plaquette` | A square PEPS plaquette with one outward physical leg on each side. | V:256-264 | `four-site-plaquette`, `lattice`, `typed-ports` |
| `rmp-w2-v-peps-plaquette-renormalization` | Four decorated PEPS sites grouped into one decorated effective site. | V:265-277 | `lattice`, `cluster-groups`, `renormalization`, `typed-ports` |
| `rmp-w2-v-f-tensor` | One \(F\)-labelled fusion-map atom with a split input boundary and one output leg. | V:278-280 | `free-graph`, `fusion-map`, `typed-ports` |
| `rmp-w2-v-r-boundary-three-site` | An \(R\) enclosure around a three-site right boundary word. | V:281-288 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-boundary-three-site` | An \(L\) enclosure around a three-site left boundary word. | V:289-296 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-r-boundary-exposed-site` | An \(R\) enclosure with one retained atom and one exposed site. | V:297-304 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-boundary-exposed-site` | An \(L\) enclosure with one retained atom and one exposed site. | V:305-312 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-boundary-grown` | An \(L\) enclosure after two boundary atoms are grown back. | V:313-321 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-r-boundary-grown` | An \(R\) enclosure after two boundary atoms are grown back. | V:322-331 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-r-boundary-inverse` | An \(R\) enclosure below an \(S\)-labelled inverse acting on two open legs. | V:332-343 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-boundary-inverse` | An \(L\) enclosure with an inverse cup above its retained boundary legs. | V:344-351 | `free-graph`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-open-boundary` | An \(L\) boundary enclosure retaining two open indices. | V:352-357 | `grid`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-r-x-boundary` | An \(R\) boundary enclosure attached to an \(X\)-labelled atom. | V:358-365 | `free-graph`, `closure`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-r-boundary-window` | A two-dimensional \(R\) boundary window surrounding two interior atoms. | V:366-383 | `lattice`, `regions`, `enclosure-marks`, `typed-ports` |
| `rmp-w2-v-l-boundary-window` | A two-dimensional \(L\) boundary window surrounding two interior atoms. | V:384-402 | `lattice`, `regions`, `enclosure-marks`, `typed-ports` |

The Section V boundary sequence resembles the owned Section IV sequence, but
it changes atom labels, contour details, and in one case whether the source
ink is active. The manifest identifies ownership by source path and line
range, so these are distinct author blocks and distinct redraw consumers.

## Capability demand

The blocked column counts targets whose `status = "blocked"` verdict names
the capability in `missing`. The wave-2 column counts proposed targets above.
The total is the redraw demand after admitting these targets.

| Capability | Existing blocked | Wave-2 proposed | Total demand |
|---|---:|---:|---:|
| `braid-resolver` | 3 | 0 | 3 |
| `closure` | 0 | 9 | 9 |
| `cluster-groups` | 1 | 1 | 2 |
| `crossing-order` | 9 | 0 | 9 |
| `enclosure-marks` | 10 | 12 | 22 |
| `equation-composition` | 2 | 1 | 3 |
| `four-site-plaquette` | 0 | 2 | 2 |
| `free-graph` | 0 | 10 | 10 |
| `fusion-map` | 0 | 1 | 1 |
| `grid` | 0 | 2 | 2 |
| `group-average` | 2 | 0 | 2 |
| `lattice` | 0 | 4 | 4 |
| `marked-region` | 1 | 0 | 1 |
| `multi-strand-braid` | 2 | 0 | 2 |
| `open-string` | 1 | 0 | 1 |
| `pulling-through` | 3 | 0 | 3 |
| `regions` | 0 | 2 | 2 |
| `renormalization` | 0 | 1 | 1 |
| `ring-closure` | 2 | 1 | 3 |
| `rotated-action` | 5 | 0 | 5 |
| `staggered-sites` | 1 | 0 | 1 |
| `string-slide` | 1 | 0 | 1 |
| `strings` | 7 | 0 | 7 |
| `torus-cycle` | 4 | 0 | 4 |
| `typed-ports` | 0 | 17 | 17 |

## Range verification

The verifier reads the proposed-target table, resolves each section to its
author file, checks the source line count, and rejects overlap with every
same-file manifest interval:

```console
$ python3 scripts/verify_tenkz_wave2_targets.py
verified 17 exhaustive wave-2 ranges: in-bounds, unique, and unowned; capability demand matches verdicts
```

The author source drop is local and untracked. A checkout without it must pass
its location explicitly:

```console
$ python3 scripts/verify_tenkz_wave2_targets.py --source-root /path/to/RMP_TIKZ_SOURCE_CODE
```
