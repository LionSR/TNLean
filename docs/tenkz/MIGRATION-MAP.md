# tenkz migration map — old TN catalogue → tenkz (Phase-1 shim blueprint)

Generated 2026-07-17. READ-ONLY analysis of:

- `tex/tn/tn_catalogue.tex` — all 114 `\TNDeclareDiagram` entries (every entry has ≥1 chapter call site; no chapter uses a non-catalogue `\TN` macro).
- Call sites: `grep -rn '\\TN[A-Z]' blueprint/src/chapter/` (140 macro occurrences on 140 lines).
- tenkz surface: `docs/tenkz/USAGE.md` (Phase-0, from the tenkz/06-manual stack worktree) + `docs/tenkz/WHATS-NEW-0.5.md` (0.5 additions + §Gaps = the 0.6 list).

Spelling note: the tenkz bodies sketched below were written against the
0.5 surface and predate the 0.6 rename sweep — read `close west/east` as
`west=cup` / `east={cup=$m$}`, `plane=` as `frame=`, and so on
(CHANGES-0.6.md has the full table). The sketches are Phase-1 input, not
user documentation; the shim PRs will spell them 0.6.

Chapter names below are relative to `blueprint/src/chapter/`, `.tex` dropped. Classes:

| class | migration action |
|---|---|
| empty-equation | delete wrapper, keep the `\ensuremath` formula as plain display math |
| drawn-single-use | inline a `tenkz`/`\tnpic` grid body at the call site |
| multi-use | `\tndefine` candidate (survives as a plain preamble macro; spec PR 1c) |
| cd genre | `tenkzcd` (polygon mode) and/or `\tntree` in math |
| region genre | `tenkzlattice` cell-set regions |
| channel/free genre | sandwich/cups channel spellings, or `tenkzfree` for irregular graphs/stars |

## Class counts

| class | entries | of the 140 macro occurrences |
|---|---:|---:|
| empty-equation → plain display math | **33** | 33 |
| drawn-single-use → inline tenkz grid body | **38** | 38 |
| multi-use → `\tndefine` candidate | **12** | 38 |
| cd genre → tenkzcd / `\tntree` | **5** | 5 |
| region genre → tenkzlattice | **10** | 10 |
| channel/free genre → sandwich-cups / tenkzfree | **16** | 16 |
| **total** | **114** | **140** |

Recount note: the review report (and DESIGN §5/§6) first quoted **34**
empty-equation entries; the measured recount over the catalogue — an
entry is empty iff its body calls no drawing macro at all — finds
exactly **33**, and the review-side counts have been corrected to match.
This table is the authoritative census.

The 12 multi-use entries account for 38 occurrences (10+5+3+3+3+2×7); every other entry is single-use. Two multi-use entries (`TNPEPSNormalRegionsRS`, `TNPEPSNormalRegionT`) have region-genre bodies; three (`TNPEPSEdgeGaugeOrientation`, `TNPEPSGaugeVertexAction`, `TNPEPSVertexInjectivityMap`) have free-genre bodies — they are counted once, under multi-use.

## Needs-new-key list (cross-checked against the 0.6 gap list)

The WHATS-NEW-0.5 §Gaps (0.6 backlog) is: *per-side boundary control, bare identity-wire atom, `combined=` on `wires=k` glyphs, inter-sheet closures, directed signatures, mirrored `tri=` closures.* **Almost none of the keys the catalogue migration needs are on that list** — the 0.6 backlog is RMP-reproduction-driven, not migration-driven. Keys needed, none of which exist in 0.5:

| key (proposed) | blocked entries | on 0.6 list? | fallback without the key |
|---|---|---|---|
| K1 `\tnspan[box]` — dashed group-fit box over a cell range (blocked-tensor box) | TNBlocking, TNMPDOTwoSiteBlocking, TNMPDOBlockedRFPChannels, TNPEPSEdgeBlockingReduction, TNPEPSNormalEdgeBlockingReduction (blocked-row halves) | **no** | redesign the grouping as `\tnspan[brace below]` |
| K2 `periodic=physical` — vertical trace closure of a stacked op-row column (multi-row analogue of per-glyph `trace=physical`) | TNMPDOBNTOperatorTraceClosure (`O_L(M_α)` vertical word) | **no** | none faithful; demote to `O_L(M_α)=\tr_v(M_α^{⊗v L})`-style plain math |
| K3 lattice `physical stubs` — per-site physical leg (diagonal stub) on tenkzlattice vertices | TNPEPSLatticeState, TNPEPSTorusGeometry | **no** | draw the patch in tenkzfree with `ports={north east:physical}` per site (verbose) |
| K4 lattice `torus`/identification marks (opposite-boundary gluing) | TNPEPSTorusGeometry | **no** (but anticipated by the final spec's manual plan, ch5 "torus/cylinder marks") | annotation arrows outside the picture |
| K5 `pair label=` / plain (dot-free) label on a cup apex or paired internal leg | TNMPOLocalPurification ($k$ on the ancilla cup) | **no** | drop the $k$ label (the sole closed ancilla pair makes the contraction unambiguous), or accept the `close east={…}` fixed-point-dot styling |
| K6 `\tnedge[insert=$X$]` — on-edge insertion glyph in the lattice tier | TNPEPSEdgeInsertedCoeff, TNPEPSThreeSiteInsertionComparison, TNPEPSPhysicalToVirtualInsertion (lattice-strip route) | **no** | tenkzfree: the insertion is its own `\tnput` node with two `\tnjoin`s — expressible today |
| K7 free-tier region highlight — hull/slot fill over a set of `\tnput` nodes | TNPEPSEdgeBlockingReduction + TNPEPSEdgeInsertionEquality (pentagon patch with region overlays), TNAppendixB* grouping regions | **no** | hand-drawn dashed box in tenkzfree (violates "no raw styling at call sites") |

Tangential 0.6 overlap: the *bare identity-wire atom* gap would let TNChoiMatrix's `id` layer be a plain wire instead of a boxed `\tn{\mathrm{id}}` (cosmetic, not blocking); *bond dir* for TNPEPSEdgeGaugeOrientation's oriented edge already shipped in 0.5. **No catalogue entry needs** per-side boundary control, `combined=` on `wires=k`, inter-sheet closures, directed signatures, or mirrored `tri=`.

Recommendation for Phase-1 sequencing: K1 and K5 are one-day keys that unblock 8 entries; K2–K4 unblock 3 pedagogical PEPS/MPDO figures and can land with the lattice batch; K6/K7 are optional (free-tier fallbacks exist).

---

## 1. empty-equation → plain display math (33 entries, all trivial)

The wrapper (`TNEquationRow` around a single `\ensuremath`) draws nothing; Phase-1 unwraps to `\[ … \]` at the call site and deletes the entry. All **trivial**.

| entry | call site | formula wrapped |
|---|---|---|
| TNEtaSectorDecomposition | ch21_mpdo_rfp_simple_local_closed_sector_rephasing:286 | $\eta_{k,h}=r_k l_h$ |
| TNMPDOTwoSiteTraceAndShift | ch21_mpdo_rfp_simple_local_normalized_preparations:1000 | $\mathcal T_0,\ \mathcal S_2$ typed maps |
| TNMPDOThreeSiteTraceAndShift | ch21_mpdo_rfp_simple_local_normalized_preparations:1006 | $\mathcal S_0,\ \mathcal T_2$ typed maps |
| TNMPDORefinementConstruction | ch21_mpdo_rfp_simple_local_refinement_channels:150 | $\mathfrak R_2\to\cdots\to\mathfrak R_3$ chain |
| TNMPDORefinementDirection | ch21_mpdo_rfp_simple_local_refinement_channels:153 | $\mathfrak R_2(\mathcal K_2)\xrightarrow{\mathcal T}\mathfrak R_3(\mathcal K_3)$ |
| TNMPDOPhysicalIsometryTransport | ch21_mpdo_rfp_simple_local_refinement_channels:966 | $U^{\otimes4}\widehat{\mathcal T}^2(U^\dagger)^{\otimes2}=\mathcal T,\dots$ |
| TNMPDOTwoSiteClosureFactorization | ch21_mpdo_rfp_simple_local_bond_products:580 | $\mathfrak R_2(\mathcal K_2(X))_{k,h}=a_kb_hB_{k,h}(X)$ |
| TNMPDOThreeSiteClosureFactorization | ch21_mpdo_rfp_simple_local_bond_products:584 | $\mathfrak R_3(\mathcal K_3(X))_{k,l,h}=\dots$ |
| TNMPDOFixedSectorAdjacentCommutativity | ch21_mpdo_rfp_simple_local_bond_products:896 | $\eta^{(12)}\eta^{(23)}=\eta^{(23)}\eta^{(12)}$ |
| TNMPDOCyclicEtaContraction | ch21_mpdo_rfp_simple_local_closed_sector_rephasing:350 | $\tr(M_{k_0}\cdots)=\tr(\eta\otimes\cdots)$ |
| TNMPDOInverseMapThreeSiteContraction | ch21_mpdo_rfp_simple_local_markov_factorization:387 | $(\mathcal K^{-1}\otimes\Id\otimes\mathcal K^{-1})\mathcal K_3=\dots$ |
| TNMPDOHorizontalOperator | ch20_mpdo_canonical_forms:1089 | $H^{(N)}(\widetilde M)=\tr_v(\widetilde M_1\cdots\widetilde M_N)$ |
| TNMPDOFirstSiteContractions | ch20_mpdo_canonical_forms:1157 | $PH^{(N+1)},\ H^{(N+1)}P,\ PH^{(N+1)}P$ |
| TNMPDOVerticalDirectSum | ch20_mpdo_canonical_forms:171 | $U\mathcal KU^\dagger=\bigoplus_k\mu_k\otimes A_k$ |
| TNMPDOVerticalReducingSectors | ch20_mpdo_canonical_forms:2735 | $U\mathcal KU^\dagger=\bigoplus_\alpha M_\alpha$ |
| TNMPDOVerticalGaugeGramComparison | ch20_mpdo_canonical_forms:2265 | $X_\alpha^\dagger X_\alpha=Y_\alpha^\dagger Y_\alpha$ |
| TNMPDOInverseContraction | ch21_mpdo_rfp_simple_local_markov_factorization:217 | $\mathcal K^{-1}\mathcal K=\Id$ |
| TNMPDONormalizedFourSiteTail | ch21_mpdo_rfp_simple_local_markov_factorization:268 | $\tr_4(\mathcal K_4)=\sum_\alpha L_\alpha\otimes B_\alpha\otimes R_\alpha$ |
| TNMPDOSectorFactorization | ch21_mpdo_rfp_simple_local_markov_factorization:755 | $U_B\mathcal KU_B^\dagger=\bigoplus_k l_k\otimes r_k$ |
| TNMPDOLocalOrthogonality | ch21_mpdo_rfp_simple_local_primitivity:171 | $P_j\mathcal K_iP_{j'}=0$ unless $i=j=j'$ |
| TNMPSInverseContraction | ch02_mps:478 | $A^{-1}A=\Id$ |
| TNMPDOZCLIdempotence | ch21_mpdo_rfp_foundations:49 | $\mathcal T_M=\mathcal T_M^2$ |
| TNRFPKrausIsometry | ch26_mps_rfp_core:116 | $A^{i_1}A^{i_2}=\sum_jV^{i_1i_2}_jA^j$ |
| TNRFPKrausIsometryReverse | ch26_mps_rfp_core:118 | $\sum(V^\dagger)^j_{i_1i_2}A^{i_1}A^{i_2}=A^j$ |
| TNRFPIsometryCanonicalForm | ch26_mps_rfp_core:657 | $A=X\sqrt\Lambda\,U\,X^{-1}$ |
| TNRFPIsometryCanonicalFormBlocks | ch26_mps_rfp_core:736 | $A=X(\bigoplus_j\mu_j\otimes\sqrt{\Lambda_j}U_j)X^{-1}$ |
| TNMPDOFirstSiteInsertionHypothesis | ch20_mpdo_canonical_forms:971 | $YH^{(N)}=ZH^{(N)}$ |
| TNMPDOFirstSiteInsertionBlockwise | ch20_mpdo_canonical_forms:973 | $YA_k=ZA_k$ |
| TNMPDOInsertionTracePairing | ch20_mpdo_canonical_forms:1005 | $\tr(WYA_k)=\tr(WZA_k)$ |
| TNMPDOHorizontalCanonicalForm | ch20_mpdo_canonical_forms:76 | $K=X(\bigoplus_j\mathcal K_j)X^{-1}$ |
| TNMPDOBlockInjectiveInverse | ch20_mpdo_canonical_forms:276 | $K^{-1}K=\bigoplus_j\Id_j$ |
| TNMPDOInverseRecovery | ch21_mpdo_rfp_simple_local_markov_factorization:225 | $K\,K^{-1}K=K$ |
| TNMPDOProjectorAbsorption | ch21_mpdo_rfp_simple_local_structure_capstone:57 | $\mathcal K_i=P_i\mathcal K_i=\mathcal K_iP_i$ |

## 2. multi-use → `\tndefine` candidates (12 entries, 38 occurrences — spec PR 1c)

| entry | uses | call sites | tenkz spelling sketch (the `\tndefine` body) | risk |
|---|---:|---|---|---|
| TNGaugeConjugation | 10 | ch23_algebraic_ft:77,1592,1594; ch12_symmetry:155,267,399,401; ch02_mps:227; ch03_single:227; ch24_peps_ft_edge_kernel_gauges:605 | `\tnpic[physical=up]{\tnX{#1} & \tn[up=$#2$]{A} & \tnX{#3}}` | trivial |
| TNPEPSEdgeGaugeOrientation | 5 | ch24_peps_ft_balanced_edge_scalars:34,109,127,147; ch24_peps_ft_foundations:87 | tenkzfree: two 4-leg `\tnput` stars, oriented shared edge via `\tnjoin[dir]` + $Z_e$ node on the edge | needs-judgment (star pair in free tier; bond dir exists) |
| TNGroundSpaceMap | 3 | ch13_parent_hamiltonian_injective_ground_spaces:42,525,546 | `\tnpic[periodic, physical=up]{\tn[up=$#2$]{} & \tn{} & \tndots & \tn[up=$#3$]{} & \tnX{#5}}` + length label | needs-judgment (source draws $X$ on the trace return wire; respell as on-row `\tnX` under `periodic` — same contraction) |
| TNCondCOne | 3 | ch12_symmetry:757,838,1184 | `\tnpic[rows={op,ket}]{\tn{#1}\\ \tn[…]{A}} = \tnpic[physical=up]{\tnX{#2} & \tn{A} & \tnX{#2^\dagger}}` | trivial |
| TNCondCTwo | 3 | ch12_symmetry:770,798,861 | `\tnpic[sandwich]{\tnX{#1} & \tn{A}\\ \tnX{#1^\dagger} & \tn*{A}} = \tnpic[sandwich]{\tn{A} & \tnX{#1}\\ \tn*{A} & \tnX{#1^\dagger}}` | trivial |
| TNPermutationTwistLabeled | 2 | ch12_symmetry:591,593 | `\tnpic[physical=up]{\tn[up=$#1$]{A}} \xrightarrow{#3} \tnpic[physical=up]{\tn[up=$#2$]{A}}` | trivial |
| TNPEPSVertexInjectivityMap | 2 | ch24_peps_ft_foundations:224; ch24_peps_ft:43 | tenkzfree 5-leg star (`ports={…:virtual, north east:physical}`) `\longmapsto` math vector | needs-judgment (free-tier star) |
| TNPEPSNormalRegionsRS | 2 | ch24_peps_ft_normal_square:91,1213 | two `tenkzlattice` panels: `\tnregion[slot=selected, label=$R$]{…}` / `[slot=secondary, label=$S$]{…}` | trivial |
| TNPEPSNormalRegionT | 2 | ch24_peps_ft_normal_square:95,1217 | `tenkzlattice` + `\tnregion[slot=selected, label=$T$]{…}` | trivial |
| TNPEPSGaugeVertexAction | 2 | ch24_peps_ft_balanced_edge_scalars:206; ch24_peps_ft_foundations:106 | tenkzfree star with $Z_{e_i}^{\pm1}$ nodes on each leg (FourBondGaugeStar shape) | needs-judgment (free-tier star) |
| TNLocalEqualityStep | 2 | ch23_algebraic_ft:409,1646 | `\tnpic[physical=up]{\tn{}&\tnX{#1}&\tn[up=$#3$]{}} = \tnpic[physical=up]{\tn{}&\tnX{#2}&\tn[up=$#3$]{}}` | trivial |
| TNBoundaryRegrow | 2 at census; 1 before this migration | ch23_algebraic_ft:407 (migrated inline in #4403); ch13_parent_hamiltonian_injective_ground_spaces:638 (migrated here) | `[periodic, physical=up]: \tnX{X'} & \tn[up=$\sigma_1$]{A} & \tn{A} & \tndots & \tn[up=$\sigma_{L+1}$]{A}` + an `$L+1$ sites` brace | migrated inline here as the traced word defining $\Gamma_{L+1}(X')$ |

## 3. cd genre → tenkzcd / `\tntree` (5 entries)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNMPDOFixedFinalFusionBracketings | ch21_mpdo_rfp_fusion_isometries:638 | display math: `\tntree{((\alpha\,\beta)_\delta\,\gamma)_\varepsilon} \xleftrightarrow{F^{\alpha\beta\gamma}_\varepsilon} \tntree{(\alpha\,(\beta\,\gamma)_\eta)_\varepsilon}` | trivial |
| TNMPDOPrintedFMove | ch21_mpdo_rfp_fusion_isometries:1742 | `\tntree{…} = \sum_{f\lambda\sigma}(F^{abc}_d)^{f\lambda\sigma}_{e\mu\nu}\,\tntree{…}` (arXiv:1511.08090 eq. Fmove) | trivial |
| TNMPDOFixedFinalComparisonUnitary | ch21_mpdo_rfp_fusion_isometries:1523 | split into 3 displays: selector row as `\tnpic[physical=updown]{\tn[mpo]{}&\tn[mpo]{M^w_{\varepsilon'}}&\tn[mpo]{}}\longmapsto\delta…`; sector cut as `\tntree` pair; diagonal corner as plain math | needs-judgment (mixed grid + tree + plain math; no single environment) |
| TNMPDOFourfoldBondReassociationPentagon | ch21_mpdo_rfp_fusion_isometries:1913 | `tenkzcd polygon=5, radius=…` with 5 text nodes $(((A\times B)\times C)\times D)$… + `\tnarrow` $r_1..r_3, s_1, s_2$ | trivial |
| TNMPDOCompleteZipperFusionPentagon | ch21_mpdo_rfp_fusion_isometries:1809 | `tenkzcd polygon=5` + `\tntree` ×5 (four-leaf bracketings) + 5 F-move arrows — the spec's flagship example | trivial |

## 4. region genre → tenkzlattice (10 single-use entries; plus RegionsRS/RegionT under multi-use)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNPEPSEdgeBlockingReduction | ch24_peps_ft_edge_middle:215 | five-site patch (pentagon graph) with region overlays `\rightsquigarrow` blocked 3-tensor row (`\tnpic` + K1 box) | needs-judgment + K7 (region highlight on a free-tier graph), K1 |
| TNPEPSInjectiveRegionUnionProof | ch24_peps_ft_normal_union:211 | 5 `tenkzlattice` panels joined by `=`/`⊆` math, regions via `\tnregion` slots | trivial |
| TNPEPSNormalRectangleCover | ch24_peps_ft_normal_square:242 | `tenkzlattice[rows=4, cols=4]` + overlapping `\tnregion[outline]` rectangles | trivial |
| TNPEPSNormalEdgeComplementTopCollar | ch24_peps_ft_normal_square:517 | two lattice panels with `=`; complement + `slot=collar` regions | trivial |
| TNPEPSNormalOneSiteSeparation | ch24_peps_ft_normal_square:1169 | two lattice panels; `\tnsite[removed]` + region slots | trivial |
| TNPEPSNormalEdgeBlockingReduction | ch24_peps_ft_normal_square:1236 | lattice panel `\rightsquigarrow` blocked grid row | needs-judgment (mixed lattice+grid display), K1 for the blocked box |
| TNPEPSNormalEdgeBlockingHypotheses | ch24_peps_ft_normal_square:1123 | single lattice panel with hypothesis regions | trivial |
| TNPEPSNormalBlockingHypotheses | ch24_peps_ft_normal_capstone:33 | nested lattice panels (outer + two inner) with regions | trivial |
| TNPEPSLatticeState | ch24_peps_ft:15 | `tenkzlattice[rows=3, cols=3, boundary legs]` + per-site physical stubs | **needs-new-key K3** (`physical stubs`) |
| TNPEPSTorusGeometry | ch24_peps_ft_torus:7 | `tenkzlattice` patch + opposite-boundary identification marks | **needs-new-key K4** (`torus` marks) + K3 |

Note: the 7 hand-digitized region polygons inside `tn_motifs_peps.tex` all become `\tnregion` cell-set data (spec §migration table); none survive as coordinates.

## 5. channel/free genre (16 entries)

### 5a. Channel spellings (ch16 + ch14)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNKrausMap | ch16_channel_representations:467 | `[sandwich, east={cup=$\rho$}, west label=$T(\rho)$]: \tn{K_i} \\ \tn*{K_i}` | source-faithful applied channel; exact boundary `(2,0,0,0)`, no package change |
| TNStinespring | ch16_channel_representations:768 | `[sandwich, east={cup=$\rho$}, west label=$T(\rho)$]: \tn{V} \\ \tn*{V}` | migrated inline (applied channel; the house input is the east cup; the unique unlabelled pairleg traces $E$) |
| TNChoiMatrix | ch16_channel_representations:108 | `[rows={wire,wire}, east={cup=$\ketbra{\Omega}{\Omega}$}, west label=$\tau$]: \tnghost{} & \tnX[wires=2]{T\otimes\id} & \tnghost{} \\ \tnghost{} & & \tnghost{}` | applied two-wire Choi map; zero pairlegs, exact boundary `(2,0,0,0)`, no package change |
| TNTransferMapTracePairing | ch16_channel_representations:1478 | demote: `T(\rho)=\sum_{ij}t_{ij}\tr(\sigma_j\rho)\,\sigma_i` (+ optional `\tnpic[inline, periodic]{\tnX{\sigma_j}&\tnX{\rho}}` for the trace loop) | needs-judgment (candidate demotion to plain math) |
| TNTwoPointCorrelator | ch14_correlations:50 | `[sandwich, west={cup=$Y$}, east={cup=$X\rho^R$}]` with `\tnX[wires=2]{\mathcal E_A^n}` between ghost anchors | trivial (a doubled-index map between input and trace-pairing cups; not a periodic word) |

### 5b. Free tier (irregular graphs, stars, projector chains)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNPEPSStateContraction | ch24_peps_ft:34 | tenkzfree: 5 `\tnput` (pentagon + chord), typed `\tnjoin`s, physical ports open | trivial (verbose) |
| TNPEPSInjectiveRegionUnion | ch24_peps_ft_normal_union:204 | tenkzfree 4-node union schematic; or redesign as `tenkzlattice` regions $A\cup B$ | needs-judgment |
| TNPEPSLocalTensorStar | ch24_peps_ft_foundations:39 | tenkzfree: one `\tnput[ports={north:virtual, south:virtual, east:virtual, west:virtual, north east:physical}]` star | trivial |
| TNPEPSVertexScalarBalance | ch24_peps_ft_balanced_edge_scalars:8 | tenkzfree star; `\tnjoin[label=$c_{v,e}$]` per incident edge | trivial |
| TNPEPSEdgeGaugeAbsorption | ch24_peps_ft_edge_kernel_gauges:848 | tenkzfree: star $B_v$ `\longmapsto` star with $Z_{e_i}^{\pm1}$ nodes on all four legs | needs-judgment (star pair) |
| TNPEPSGaugeCancellation | ch24_peps_ft_foundations:177 | tenkzfree: two stars with $Z$, $Z^{-1}$ on the shared edge `=` two bare stars | needs-judgment |
| TNPEPSTINormalGaugeAbsorption | ch24_peps_ft_normal_square:1251 | tenkzfree: square tensor star `=` gauge-dressed star | needs-judgment |
| TNPEPSTwoInjectiveGaugeScalarReduction | ch24_peps_ft_edge_kernel_gauges:1056 | tenkzfree: three-leg fan `=` fan+$Z$ `=` fan+$U$ `=` fan+$W$ (4 panels) | needs-judgment |
| TNAppendixBAdjacentBondProjectors | ch13_parent_hamiltonian_commuting_gap:1307 | tenkzfree: 3 fusion nodes $U_0U_1U_2$ + 2 $\varphi$ sites, `\tnjoin[route=vh]`, highlighted $P_{01},P_{12}$ | needs-judgment + K7 (group highlight) |
| TNAppendixBPhysicalSupportTransport | ch13_parent_hamiltonian_commuting_gap:1459 | same body + two overlapping support regions above | needs-judgment + K7 |
| TNAppendixBChainTransport | ch13_parent_hamiltonian_commuting_gap:1718 | respell hexagon ring as `[periodic, physical=up]` 6-cell row ($h_i$, $h_{i+1}$ highlighted labels) `\xrightarrow{R^{(3)}_{i,\tau}}` 3-site open row | needs-judgment (layout redesign ring→periodic row; same contraction) |

## 6. drawn-single-use → inline tenkz grid body (38 entries)

### MPS / MPO basics (ch02, ch20, ch21)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNMPSLocal | ch02_mps:22 | `\tnpic[physical=up]{\tn[up=$i$]{A}}` | trivial |
| TNMPSWord | ch02_mps:40 | `[physical=up]: \tn[up=$i$]{A} & \tn{A} & \tndots & \tn[up=$k$]{A}` + `\tnspan[brace below]{4}{L}` | trivial |
| TNMPV | ch02_mps:152 | `[periodic, physical=up]: \tn[up=$i$]{A} & \tn{A} & \tndots & \tn[up=$k$]{A}` | trivial |
| TNBlocking | ch02_mps:733 | word row + dashed group box labelled $A$ over all cells | **needs-new-key K1** (`\tnspan[box]`; brace fallback) |
| TNMPVOverlap | ch02_mps:850 | `[rows={ket,bra}, periodic]: \tn{A}&\tndots&\tn{A}\\ \tn*{B}&\tndots&\tn*{B}` | trivial |
| TNTransferMap | ch02_mps:169 | `[sandwich, west label=$X$, east label=$\mathcal E_A(X)$]: \tn{A} \\ \tn*{A}` | trivial (K5 pair label $i$ optional) |
| TNMPOCell | ch20_mpdo_foundations:12 | `[physical=updown]: \tn[mpo, up=$i$, down=$j$]{A}` | trivial |
| TNMPOChain | ch20_mpdo_foundations:119 | `[periodic, physical=updown]: \tn[mpo, up=$i_1$, down=$j_1$]{A} & \tndots & \tn[mpo, up=$i_N$, down=$j_N$]{A}` | trivial |
| TNMPOLocalPurification | ch20_mpdo_foundations:311 | `\tnpic[physical=updown]{\tn[mpo]{M}} = \tnpic[rows={ket:nopair, bra}, close east]{\tn{A}\\ \tn*{A}}` with $k$ on the ancilla cup | needs-judgment (K5: plain cup label vs fixed-point dot) |
| TNMPORenormalizationTS | ch21_mpdo_rfp_renormalization:619 | `M_1(X)=\tnpic[physical=updown]{\tn[mpo]{M}} \xrightleftharpoons[\mathcal S]{\mathcal T} \tnpic[physical=updown]{\tn[mpo]{M}&\tn[mpo]{M}} = M_2(X)` | trivial |

### MPDO fusion / structure (ch10, ch21)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNMPDOBlockedRFPChannels | ch21_mpdo_rfp_simple_local_refinement_channels:888 | math arrows $\widehat{\mathcal T},\widehat{\mathcal S}$ between `\tnpic` factor chains (2/3/4 cells) + blocked-site boxes | **needs-new-key K1** (blocked boxes; brace fallback) |
| TNMPDOHayashiSectorComparison | ch21_mpdo_rfp_simple_local_markov_factorization:555 | `R\cdot\tnpic[physical=updown, west label=$\beta_1$, east label=$\alpha_3$]{\tn[mpo, up=…, down=…]{\widetilde\kappa^{(k)}}} = p_k\,A^{(k)}\otimes B^{(k)}` | trivial |
| TNBNTDecomposition | ch10_bnt:664 | demoted to the exact CPSV16 coefficient decomposition $A^i=X[\bigoplus_j(M_j\otimes A_j^i)]X^{-1}=\bigoplus_{j,q}\mu_{j,q}X_{j,q}A_j^iX_{j,q}^{-1}$; no diagram remains | exact plain mathematics: the paper explicitly warns that its graphical $j,q$ lines replace direct sums by tensor products and are not literal tensor-network legs |
| TNMPDOBNTFusionIdentity | ch21_mpdo_rfp_fusion_isometries:318 | `\tnfuse[combined=west]{U_{\alpha\beta}} &` stacked $M_\alpha/M_\beta$ `& \tnfuse[combined=east]{U^\dagger} = \bigoplus_\gamma` weighted block (`\tnX{\chi_{\alpha\beta\gamma}}`) | trivial (`\tnfuse` + doubled combined stub exist) |
| TNMPDOUnweightedZipperReconstruction | ch21_mpdo_rfp_fusion_isometries:499 | 3 zipper equations, each `\tnfuse` + `\tn[mpo]{H}` grids | trivial |
| TNMPDOFusionTracePower | ch21_mpdo_rfp_fusion_isometries:520 | `[rows={op,op}, periodic]` $M_\alpha$ row over $M_\beta$ row `= \sum_\gamma` `[rows={wire,op}, periodic]` $\chi$ row over $M_\gamma$ row | trivial (the right rows are disjoint; only the left rows pair physically) |
| TNMPDORecursiveStructureOperator | ch21_mpdo_rfp_fusion_isometries:813 | `tenkzfree`: degree-four $X_s$ boxes meet open $k_s,\alpha_s,\beta_s,\gamma_s$ copy rails; $\gamma_s$ and $\alpha_{s+1}$ share one open rail, and the final rail selects traced $M_{\gamma_r}$ with its physical pair open | source-faithful free-tier routing; no package change |
| TNMPDOTwoSiteBlocking | ch21_mpdo_rfp_blocked_rfp:5 | `\tnpic[physical=updown]{\tn[mpo]{M}} = \tnpic[physical=updown]{\tn[mpo]{K}&\tn[mpo]{K}}` + grouped-leg boxes | **needs-new-key K1** (or drop the grouping box) |
| TNMPDOBNTVerticalProduct | ch21_mpdo_rfp_simple_local_structure_capstone:48 | `[rows={op,op}]: \tn[mpo]{\mathcal K_y} \\ \tn[mpo]{\mathcal K_x}` `= 0\ (x\ne y)` | trivial |
| TNMPDOBlockClosureMap | ch21_mpdo_rfp_algebra_tower:63 | `M_\alpha(X)=\tnpic[physical=updown, periodic]{\tn[mpo]{M_\alpha}&\tnX{X}}` (twice, for $M_\alpha$ and $A_\alpha$) | trivial |
| TNMPDOBNTOperatorTraceClosure | ch21_mpdo_rfp_bnt_coefficients:32 | `O_L(M_\alpha)=` vertical stack of $L$ op rows, physically trace-closed top-to-bottom, horizontal legs open | **needs-new-key K2** (`periodic=physical`) |

### Symmetry / algebraic FT (ch12, ch23)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNPhysicalRealization | ch23_algebraic_ft:188 | `\tnpic[physical=up]{\tn{A}&\tnX{X}} = \tnpic[rows={op,ket}]{\tn{O_A(X)}\\ \tn{A}}` | trivial |
| TNLinearTwist | ch12_symmetry:153 | `[rows={op:none,ket}]: \tn[role=operator,up=$i$]{U(g)} \\ \tn{A}` | trivial (`op:none` is required because $U(g)$ has no virtual legs) |
| TNPermutationTwist | ch12_symmetry:549 | fold into the `\tndefine`d PermutationTwistLabeled with $\sigma_g$ | trivial |
| TNTwistedTransfer | ch12_symmetry:616 | `[rows={ket,op,bra}, west label=$X$, east label=$\mathcal E_u(X)$]: \tn{A^{(n)}} \\ \tn{u} \\ \tn*{A^{(n')}}` | trivial |
| TNStringOrderParameter | ch12_symmetry:634 | `[rows={ket,op,bra}]` word with `\tnghost` end cells in the op row, `\tndots`, length brace $L$ | trivial |
| TNInternalTraceInsertion | ch23_algebraic_ft:372 | `[periodic, physical=up]: \tn[up=$i$]{} & \tnX{X} & \tn[up=$k$]{}` | trivial |
| TNExternalTraceInsertion | ch23_algebraic_ft:377 | same contraction; source draws $Y$ on the trace return wire — respell as `[periodic]` with boundary `\tnX{Y}` | needs-judgment (return-wire fidelity vs respell; a `trace insert=` key would preserve layout) |

### PEPS equation diagrams (ch24)

| entry | call site | tenkz spelling sketch | risk |
|---|---|---|---|
| TNPEPSEdgeInsertedCoeff | ch24_peps_ft_edge_middle:120 | 3-site strip with $X$ on a bond: `tenkzlattice[rows=1, cols=3, boundary legs]` + edge insertion; or tenkzfree with $X$ as its own node | **needs-new-key K6** (`\tnedge[insert=]`; free-tier fallback exists) |
| TNPEPSThreeSiteInsertionComparison | ch24_peps_ft_edge_kernel_gauges:475 | two such strips joined by `=` ($A$-family with $X$ = $B$-family with $Y$) | **needs-new-key K6** (same; free fallback) |
| TNPEPSInsertionPhysicalRealization | ch24_peps_ft_edge_kernel_gauges:185 | site with $M$ on west bond + $\eta$ labels + south stub `=` site with $O(\cdot)$ on physical leg | needs-judgment (south virtual stub: free tier or lattice strip) |
| TNPEPSPhysicalToVirtualInsertion | ch24_peps_ft_edge_kernel_gauges:372 | three strips ($O_1$ physical, $O_2$ physical, $\Longrightarrow$ $W$ on bond) | **needs-new-key K6** / free fallback |
| TNPEPSEdgeInsertionEquality | ch24_peps_ft_edge_kernel_gauges:903 | five-site pentagon patch with $X$ on an edge, `=`, relabelled copy | needs-judgment (free-tier graph + K7 if regions kept) |
| TNPEPSTwoInjectiveTensorInsertionComparison | ch24_peps_ft_edge_kernel_gauges:1293 | two-site pair with $X$ insertion `=` $B$-copy | needs-judgment (free/lattice strip) |
| TNPEPSOneVertexComplementComparison | ch24_peps_ft_region_transfer_covariance:279 | pure 1D rows: `\tnpic[physical=up]{\tn{A_R}&\tn{A_v}} = \tnpic{\tn{A_S}} \propto \tnpic{\tn{\widetilde B_S}} = \tnpic{\tn{\widetilde B_R}&\tn{\widetilde B_v}}` | trivial |
| TNPEPSBlockedMiddleLocalGaugeFormula | ch24_peps_ft_edge_kernel_gauges:815 | gauge-dressed site equation (peps-gauge family) → tenkzfree composition | needs-judgment |
| TNPEPSLocalGaugeExtraction | ch24_peps_ft_edge_kernel_gauges:941 | gauge-extraction equation → tenkzfree composition | needs-judgment |
| TNPEPSGlobalConsistency | ch24_peps_ft_edge_kernel_gauges:975 | two-site consistency relation (EdgeGaugeOrientation shape) → reuse that `\tndefine`d free body with different scalars | needs-judgment |

---

## Phase-1 batching suggestion (from the classes)

1. **PR 1a — unwrap the 33 empty-equation entries** (pure deletion; no tenkz needed; largest single shrink of the shim).
2. **PR 1b — keys K1 + K5** (one-day keys), then the ch02/ch03 canonical MPS figures and the ch16/ch14 channel five (sets house style, per spec ordering).
3. **PR 1c — the 12 `\tndefine` names** (as ordinary preamble macros, no catalogue).
4. **PR 1d — tenkzcd batch** (5 fusion/pentagon entries in ch21_fusion_isometries).
5. **PR 1e — tenkzlattice batch** (ch24 region entries; land K3/K4 here).
6. **PR 1f — tenkzfree batch** (PEPS stars/graphs, AppendixB chains; decide K6/K7 vs fallbacks).
7. **PR 1g — MPDO drawn remainder** (ch20/ch21 grid equations; K2 for TNMPDOBNTOperatorTraceClosure or demote it).

Exit criterion (spec): `grep -r '\\TN[A-Z]' blueprint/src/chapter/` returns nothing; every shim entry deleted at zero remaining uses.
