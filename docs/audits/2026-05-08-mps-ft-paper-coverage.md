# MPS Fundamental Theorem & Quantum Wielandt — Paper-to-Code Coverage Audit

**Audit date**: 2026-05-08
**Source papers**:
- **PGVWC07**: D. Pérez-García, F. Verstraete, M.M. Wolf, J.I. Cirac, *Matrix Product State Representations*, Quantum Inf. Comput. **7**, 401–430 (2007), arXiv:quant-ph/0608197.
  Source TeX: `Papers/quant-ph_0608197/MPSarchive.tex`
- **CPSV16**: J.I. Cirac, D. Pérez-García, N. Schuch, F. Verstraete, *Matrix Product Density Operators: Renormalization Fixed Points and Boundary Theories*, Ann. Phys. **378**, 100–149 (2017), arXiv:1606.00608.
  Source TeX: `Papers/1606.00608/MPDO-22-12-17-2.tex`
- **SPGWC09** (Wielandt): M. Sanz, D. Pérez-García, M.M. Wolf, J.I. Cirac, *A quantum version of Wielandt's inequality*, IEEE Trans. Inf. Theory **56**, 4668–4673 (2010), arXiv:0909.5347.
  Source TeX: `Papers/0909.5347/main.tex`

**Leaning on** (not audited in detail):
- **CPSV21**: Cirac, Pérez-García, Schuch, Verstraete, *Matrix product states and projected entangled pair states: Concepts, symmetries, theorems*, Rev. Mod. Phys. **93**, 045003 (2021), arXiv:2011.12127 — used for the rendered numbering of the BNT and Fundamental Theorem statements.
- **DeLasCuevas2017Irreducible**: Gemma De las Cuevas, J. Ignacio Cirac,
  Norbert Schuch, David Pérez-García, *Irreducible forms of Matrix Product
  States: Theory and Applications*, arXiv:1708.00029 — used in
  `Periodic/FundamentalTheorem.lean`.

**Scope**: This audit covers the MPS and MPDO results of CPSV16, the MPS / pure-state sections of PGVWC07, and a full Wielandt source-paper crosswalk (§9). The CPSV16 crosswalk was synchronized with the complete source audit on 2026-07-28 and with the every-label audit on 2026-08-10. The latter checks 187 lexical occurrences and 183 lexical names, of which 186 occurrences and 182 names are active; see `docs/audits/2026-08-10-cpsv16-every-label-audit.md` and `docs/audits/data/cpsv16-label-dispositions.tsv`.

**Maintainer note** (from #1498, 2026-05-08): "Please please follow CPSV16". For non-periodic FT work, prioritize source-faithful CPSV16 statement/prose and avoid implementation-driven reinterpretations.

---

## 1. Current proof-integrity status

**Maintained update (2026-08-11):** This section and the PGVWC07 crosswalk
below report the post-audit repository state; the filename and audit date retain
the original 2026-05-08 date.

The May 2026 per-file `sorry` table is no longer a current description of the
repository. On 2026-08-11, an exact search for proof holes and axiom
declarations in `TNLean/MPS/` finds none. The remaining qualifications in this
audit are therefore mathematical scope distinctions: a current theorem may be
conditional, may prove only part of a source result, or may concern a different
boundary convention even though every cited Lean declaration is proved.

---

## 2. Coverage crosswalk: CPSV16 (arXiv:1606.00608)

At this revision, after the normal-tensor RFP characterization, the
trace-normalized RFP-to-ZCL-and-SAL result, the unrestricted Proposition
`prop3to4`, the fixed-bond/source-ZCL SAL theorem, the literal sharp
`propblockinj` theorem, and the literal CPSV topological-projector commuting
Gibbs theorem, the paper has 45 theorem-like occurrences and 40 distinct
results. The occurrence-level count is 25 complete, 7 partial, and 13
not-ready; the distinct-result count is 24 complete, 5 partial, and 11
not-ready. Here **not-ready** means that the printed statement is false,
ambiguous, or depends essentially on a formally refuted source lemma. It does
not mean that every printed result has been formalized. These counts predate
the 2026-08-23 reclassification; the rows below reflect the nonzero-coefficient convention adopted on 2026-08-23
(`docs/audits/2026-08-23_nonzero_coefficient_convention.md`): every
canonical-form coefficient is nonzero by the source's line-246 normalization,
and the zero-coefficient refutations recorded by earlier versions of this
audit have been withdrawn.

The distinct count is the 40 source `thm`, `prop`, `cor`, and `lem`
environments. The occurrence count adds five Appendix A/C restatements.
The following ledger makes the count reproducible from source line numbers:

- **Complete (24 distinct):** 249, 253, 342, 398, 606, 945, 1013, 1080, 1121,
  1130, 1274, 1333, 1351, 1406, 1484, 1503, 1510, 1569, 1597, 1647, 1680,
  1786, 1835, and 2221.
- **Partial (5 distinct):** 278, 801, 851, 972, and 1801.
- **Not-ready (11 distinct):** 349, 354, 500, 534, 543, 583, 777, 1155,
  1197, 1740, and 1810.
- **Additional occurrences:** the Appendix A restatements at 1137, 1167,
  and 1172 inherit partial, not-ready, and not-ready status, respectively; the
  Appendix C.3--C.4 restatements at 1863 and 1929 inherit complete and partial status.
  Thus the five restatements add one complete, two partial, and two not-ready
  occurrences, giving the displayed totals 25/7/13.

Definitions, equations, and explanatory proof-segment rows are not counted.
In particular, Eq. `II_XAX` at 1072--1077 is excluded, while the purification
equivalence is counted because it is the `thm` environment beginning at line
777.  The Appendix B rows at 1209--1244, 1246--1271, and 1305--1307 are proof
segments of Theorems 3.1 and 3.10, not additional theorem occurrences.

This theorem-like count is not the label inventory.  The source contains 187
lexical `\label{...}` occurrences and 183 lexical names, including section,
definition, equation, figure, example, and internal proof labels.  The
commented-out label `biCF` is the only inactive name, leaving 186 active
occurrences and 182 active names.  Activity is derived from the source after
stripping unescaped TeX comments and is checked occurrence by occurrence.
Every lexical label has an explicit activity, classification, and disposition in
`docs/audits/data/cpsv16-label-dispositions.tsv`, validated by
`python3 scripts/audit_cpsv16_labels.py`.  The validator also requires exactly
58 unique equation or figure labels, comprising 60 occurrences inside theorem
statements and proofs, to inherit the enclosing result's status and semantic
boundary explicitly.  The four duplicate
names are `thm1`, `II_cor2`, `eq:II_auxcor`, and `eq1:proof.IV.12`; the last is
accidental.

### 2.1 Section II — Matrix Product Vectors (pure-state canonical form)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| §II Defn (l.132) | 132–139 | MPV definition (`MPV`) | `TNLean/MPS/Defs.lean` | `leanok` |
| Prop (l.249) | 249–251 | After blocking, any tensor has a canonical-form representative with the same positive-length MPVs | `TNLean/MPS/CanonicalForm/CPSVAfterBlocking.lean` (`MPSTensor.exists_cpsvCanonicalForm_representative_after_blocking`) | **complete** |
| Prop (l.253) | 253–255 | Projector criterion for canonical form | `TNLean/MPS/CanonicalForm/ProjectorClosureSpectral.lean` (`MPSTensor.exists_normalTensor_blockDecomp_with_isometry_of_hasInvariantProjectorClosure`) | **complete**; #2634 closed |
| Prop 2.7 (l.278, `prop:char-BNT`) | 278–280 | BNT characterization: every canonical-form normal tensor is gauge-phase-equivalent to a basis element | Blueprint `thm:cpsv_bnt_characterization`; `TNLean/MPS/CanonicalForm/BNTCharacterization.lean` (`MPSTensor.isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal`) | **complete under the nonzero-coefficient local correction** — the canonical-form convention requires every coefficient to be nonzero (source line 246), so every block is determined by positive-length MPVs; see `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` |
| Defn "injective" (l.317, `defnbi`) | 317–322 | A normal tensor is injective when its matrices span the full matrix algebra; biCF is block-injective canonical form | `TNLean/MPS/Defs.lean` (`MPSTensor.IsInjective`) and the biCF development under `TNLean/MPS/MPDO/BiCFDerivation/` | `leanok` |
| Prop (l.342, `propblockinj`) | 342–345 | After blocking at most $3D^5$ spins, any canonical-form tensor becomes biCF | `TNLean/MPS/MPDO/CPSVSharpBlocking.lean` (`MPSTensor.IsCPSVCanonicalForm.exists_bnt_biCF_after_blocking_le_three_bondDim_pow_five`) | **complete** — literal canonical-form data supply an active BNT whose representative dimensions sum to at most the ambient bond dimension $D$; for $D>0$, blocking at a positive length $L\leq3D^5$ gives the simultaneous one-letter span of the full product matrix algebra |
| **Theorem 2.10** (l.349, `thm1`) | 349–352 | Fundamental theorem of MPVs, proportional case | Blueprint `thm:cpgsv_multiblock_ft_source`; `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_proportional_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **complete under the nonzero-coefficient local correction** — with every canonical-form coefficient nonzero, the BNT cardinalities agree and the Lean fundamental theorem proves the proportional statement |
| **Corollary 2.11** (l.354, `II_cor2`) | 354–361 | Equal MPVs imply conjugacy by an invertible matrix | Blueprint `thm:cpgsv_equal_case_source`; `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **complete under the nonzero-coefficient local correction** — with every canonical-form coefficient nonzero, equal MPVs determine the ambient dimension and the global conjugacy |

### 2.2 Section III — Pure States: Renormalization of MPS (RFP / ZCL / NNCPH)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem 3.1** (l.398, `thm:renormalization-flow`) | 398–405 | A tensor appears as a renormalization-flow limit iff two blocked physical sites are related to one site by an isometry | `TNLean/MPS/RFP/FlowLimit.lean` (`MPSTensor.AppearsAsRenormalizationFlowLimit`, `MPSTensor.appearsAsRenormalizationFlowLimit_iff_hasPhysicalBlockingIsometry`); `TNLean/MPS/RFP/Defs.lean` (`HasPhysicalBlockingIsometry`); `docs/paper-gaps/cpsv16_renormalization_flow_index_typo.tex` | **complete, with documented local correction** — the flow-limit predicate quantifies the initial physical dimension and tensor, fixes the bond dimension, and uses convergence of the dyadic transfer matrices in their standard finite-dimensional matrix topology. The printed blocking equation has malformed summation and output indices; the preceding renormalization equation, diagrams, and Appendix proof determine the corrected identity without changing the hypotheses or conclusion |
| Defn RFP (l.420, `defRFP`) | 420–424 | Pure-state RFP condition | `TNLean/MPS/RFP/Defs.lean` (`HasPhysicalBlockingIsometry`) | `leanok` |
| Defn CID (l.438) | 438–446 | Correlations independent of distance | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsPhysicalCID`) | `leanok` |
| **Example 3.4** (`Ex:ZCL`, l.453) | 453–464 | A permutation-invariant state has CID but is not an RFP | Blueprint Chapter 15: `def:cpsv16_example_34_tensor`, `thm:cpsv16_example_34_mpv`, `thm:cpsv16_example_34_cid`, and `thm:cpsv16_example_34_not_rfp`; `TNLean/MPS/RFP/CPSVCIDNotRFPExample.lean` (`MPSTensor.cpsvExample34Tensor`, `MPSTensor.cpsvExample34_mpv`, `MPSTensor.cpsvExample34_isPhysicalCID`, `MPSTensor.cpsvExample34_not_isTransferIdempotent`, `MPSTensor.cpsvExample34_not_hasPhysicalBlockingIsometry`) | **complete** — the formalization uses the exact printed tensor, proves the positive-length state formula, establishes physical correlation independence, and proves failure of the pure-state renormalization fixed-point equation |
| Defn LO (l.468, `DefLO`) | 468–474 | Local orthogonality | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsBNTLocallyOrthogonal`) | `leanok` |
| Defn ZCL (l.476) | 476–478 | ZCL = LO and CID | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsPhysicalBNTZCL`) | `leanok` |
| Defn transfer matrix (l.482) | 482–488 | Transfer map | `TNLean/MPS/Core/Transfer.lean` (`transferMap`) | `leanok` |
| **Theorem 3.8** (l.500, `TheoremZCLPure`) | 500–503 | ZCL iff the transfer map is idempotent | `TNLean/MPS/RFP/ZCLReverse.lean` (`IsBNTCanonicalForm.isPositiveGapBNTZCL_basisDirectSum_iff_isTransferIdempotent`); `BNTWeightCounterexample.lean`; `BellPairCIDObstruction.lean`; `docs/paper-gaps/cpsv16_pure_zcl_raw_weight_counterexample.tex`; `docs/paper-gaps/cpsv16_pure_zcl_adjacent_gap_cid_scope.tex` | **not-ready** — the multiplicity-one unit-weight representative now has a proved positive-gap biconditional, using an eigenvalue-free local correction to the false inference at line 1250. The printed theorem remains false: raw weights refute ZCL⇒idempotence, and the Bell-pair chain at zero complementary gap refutes the unrestricted reverse implication |
| Defn parent Hamiltonian (l.522) | 522–525 | Parent-Hamiltonian BNT ground-space spanning for arbitrary \(L\), with commuting and nearest-neighbor refinements | `TNLean/MPS/ParentHamiltonian/Commuting.lean` (`MPSTensor.HasParentHamiltonianGroundSpaceSpanning`, `MPSTensor.IsCommutingParentHam`, `MPSTensor.IsNNCPH`; `MPSTensor.HasNNCPHGroundSpaces` packages the \(L=2\) all-chain condition) | `leanok` |
| **Theorem 3.10** (l.534, `thm:main-MPS`) | 534–541 | RFP iff ZCL iff NNCPH | `TNLean/MPS/RFP/ZCLReverse.lean`; `MainMPSConditional.lean` (`IsBNTCanonicalForm.isPositiveGapBNTZCL_implies_hasNNCPHGroundSpaces_basisDirectSum`); `PhysicalObservableRealization.lean` | **not-ready** — positive-gap BNT ZCL now implies the all-chain NNCPH ground-space condition at the multiplicity-one unit-weight representative by the local correction to line 1250. The printed three-way equivalence remains false because it inherits the raw-weight and adjacent-gap counterexamples to Theorem 3.8 |
| **Theorem 3.11** (l.543, `thm:charact-MPS`) | 543–555 | Repeated-copy structural characterization of RFP | `TNLean/MPS/RFP/StructuralFull.lean` (`MPSTensor.rfp_nt_structural_full`); `TNLean/MPS/RFP/ResidualIsometry.lean`; Blueprint `thm:cpsv_charact_mps_status`; `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` | **not-ready** — the displayed physical isometry has no copy index, and the source supplies neither a coordinate map for the physical routing of the copy index nor a dimension hypothesis for it, so the display does not determine a coordinate-level predicate; #2598 closed as a source obstruction. The fixed-letter virtual-block reading of the display is out of scope, since the source requires the copy index to contribute to the physical direct sum as well; see `docs/audits/2026-08-24_degenerate_readings_wave_2.md` |
| Corollary 3.12 (l.583, `III_cor3`) | 583–590 | Structural form of the BNT elements of an RFP tensor | `TNLean/MPS/RFP/CPSVCanonicalForm.lean` (`CPSVCanonicalFormData.weight_norm_one_and_block_rfp`, `CPSVCanonicalFormData.BNTRefinement.exists_residualIsometryFamily_of_isTransferIdempotent`, `IsCPSVCanonicalForm.exists_bntRefinement_residualIsometryFamily_of_isTransferIdempotent`); `TNLean/MPS/RFP/ResidualIsometry.lean`; `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` | **complete for the phase-class representatives** — one representative of each phase class has a trace-normalized square-root form, and the residual tensors satisfy all diagonal and off-diagonal joint-isometry equations simultaneously; the statement is read for the canonical-form blocks, all of which carry nonzero coefficients |
| Prop (l.606) | 606–609 | Pure RFP implies saturation of the area law | `TNLean/MPS/MPDO/PureRFPSAL.lean` (`MPSTensor.isSAL_of_isTransferIdempotent`) | **complete** |

### 2.3 Section IV — Mixed States (MPDO)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn RFP (mixed) (l.658) | 658–663 | Mixed-state RFP via trace-preserving completely positive maps | `TNLean/MPS/MPDO/RFPViaTS.lean` (`MPOTensor.IsRFPViaTS`) | `leanok` |
| **Definition 4.2** (`DefinitionZCL`, l.736) | 735–739 | ZCL is literal idempotence of the physical-trace transfer | Blueprint `def:mpo_physical_trace_idempotence`; `TNLean/MPS/MPDO/ZCL.lean` (`MPOTensor.IsPhysicalTraceIdempotent`, `MPOTensor.isPhysicalTraceIdempotent_iff`) | **complete** — the named predicate is exactly $\mathcal T_M^2=\mathcal T_M$. The nonzero up-to-scalar `IsSourceZCL` relation is retained separately and is not mapped to the source label |
| Defn Puri-RFP (l.758) | 758–764 | Purification RFP | `TNLean/MPS/MPDO/PRFP.lean` (`MPOTensor.HasGlobalPurificationEquation`, `MPOTensor.HasPurificationRFPWitness`, `MPOTensor.IsPRFP`) | `leanok` for the definition; the ancillary trace-preserving refinement is recorded separately |
| **Theorem 4.4** (unlabeled theorem environment, l.777; counted) | 777–784 | Puri-RFP iff ZCL and the stated purification form | Blueprint `thm:cpsv_theorem44_printed_status` and `thm:nonzero_global_prfp_not_physical_trace_idempotence`; `TNLean/MPS/MPDO/LocalPurificationRFP.lean` (`MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isPhysicalTraceIdempotent`, the separate stronger `MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL`, and local corrected equivalences); `docs/paper-gaps/cpsv16_purification_rfp_definition.tex` | **refuted as printed** — a nonzero MPDO satisfies the positive-length global PRFP predicate but fails literal physical-trace idempotence because the equations do not detect its nilpotent hidden bond sector. The local-purification equivalences are restricted corrections, not the printed global theorem |
| Proposition 4.5 (l.801, `PropILILp1`) | 801–807 | Mutual information is monotone, bounded, and has the stated thermodynamic limit | Blueprint `thm:cpsv_prop45_printed_status` and `thm:cpsv_prop45_limit_counterexample`; `TNLean/MPS/MPDO/MutualInfoMonotone.lean` (`MPOTensor.mutualInfoChain_monotone`); `TNLean/MPS/MPDO/MutualInfoAreaLaw.lean` (`MPOTensor.mutualInfoChain_le_two_log_bondDim`, `MPOTensor.IsMPDO.mutualInfoChain_le_four_log_bondDim`); `TNLean/MPS/MPDO/ThermodynamicLimitCounterexample.lean` (`MPOTensor.ThermodynamicLimitCounterexample.proposition45_limit_counterexample`); `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex` | **refuted as printed** — the monotonicity and finite-chain bounds are proved and retained separately, including the stronger estimate $I_L\le 2\log D$ for every fixed positive MPO operator of nonzero trace. The parity tensor is an MPDO, but every fixed nonempty cut has no real mutual-information limit. Aperiodicity or convergence would be a genuine additional boundary condition, not a hypothesis of the printed proposition |
| Defn SAL (l.811, `def:area-law`) | 811–813 | Saturation of the area law | `TNLean/MPS/MPDO/AreaLaw.lean` (`MPOTensor.IsSAL`) | `leanok` |
| **Definition 4.7** (l.821) | 815–822, with standing convention 217–246 | A simple MPDO has no nilpotent element in a blocked BNT | `TNLean/MPS/MPDO/SourceSimpleTensor.lean` (`MPOTensor.IsSimple`, `MPOTensor.bnt_basis_not_isNilpotent_iff`, `MPOTensor.IsSimple.exists_mpo_ne_zero`); `BNTRefinement.lean` (`MPSTensor.IsBNTSectorPresentation`, `equiv_of_sameMPV₂Pos`); `SimpleTensor.lean` (gauge-phase invariance of doubled-transfer nilpotency); Blueprint `def:mpdo_simple_tensor`; `docs/paper-gaps/cpsv16_simple_tensor_nilpotency.tex`; `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **complete** — `IsSimple` records the nonzero canonical-block construction by existentially choosing a positive blocking and a BNT sector presentation. Every representative has a positive number of copies and all copy weights are nonzero; presentations are unique up to permutation, dimension identification, gauge, and phase, under which doubled-transfer nilpotency is invariant. Positive-length nontriviality follows from the presentation and is not a defining hypothesis. The line-246 unit-weight witness is not a clause of Definition 4.7, and there is no separate all-length nonvanishing predicate; see `docs/audits/2026-08-24_degenerate_readings_wave_2.md` |
| Defn GSNNCH (l.829) | 829–837 | Gibbs state of a nearest-neighbor commuting Hamiltonian | `TNLean/MPS/MPDO/CommutingForm.lean` (`MPOTensor.GSNNCHData`, `MPOTensor.IsGSNNCH`) | `leanok` |
| **Theorem 4.9** (l.851, `thm:main-simple`) | 851–893 | Simple-MPDO implication chain \((i)\Rightarrow(ii)\Leftrightarrow(iii)\Rightarrow(iv)\Rightarrow(v)\) | Blueprint `thm:cpsv_theorem49_printed_status`, `thm:mpdo_bond_one_physical_sector_factorization`, `thm:mpdo_sal_zcl_bnt_sector_structure_counterexample`, and `thm:mpdo_theorem49_iv_to_v_counterexample`; `TNLean/MPS/MPDO/BondOnePhysicalSectorFactorization.lean`; `TNLean/MPS/MPDO/RFPViaTSSAL.lean`; `TNLean/MPS/MPDO/CyclicActiveAreaLaw.lean`; `TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`; `TNLean/MPS/MPDO/BNTSourceSectorProjectors.lean`; `TNLean/MPS/MPDO/BNTSectorAnalyticProperties.lean`; `TNLean/MPS/MPDO/BNTSectorAreaLaw.lean`; `TNLean/MPS/MPDO/CaseIIAbsorptionCounterexample.lean`; `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean`; `TNLean/MPS/MPDO/Theorem49RepeatedCopyCounterexample.lean`; `TNLean/Analysis/EntropyMarkovForward.lean`; `TNLean/Channel/PetzProductReference.lean` | **partial and partly refuted** — implication \((i)\Rightarrow(ii)\) is complete at the explicit density-family boundary, and the HJPW/Hayashi and Petz-recovery constructions are complete. The two-sector bond-one construction refutes preservation of normality under coefficient absorption. At virtual bond dimension one, SAL and literal physical-trace idempotence do imply a normalized one-sector neighboring-trace factorization without normality. The non-Cartesian four-letter tensor shows that the inherited low-level properties do not alone imply such a factorization in arbitrary virtual dimension, but it has no ambient simple-biCF witness and therefore does not refute (ii)$\Rightarrow$(iv). Independently, the scalar one-representative tensor with raw copy weights $1,1/2$ satisfies the standing hypotheses and every clause of (iv), while that block fails Definition 4.1; thus literal (iv)$\Rightarrow$(v) is false. The viable source (ii)$\Rightarrow$(v) route remains not ready: #6775 tracks the source-context factorization, Proposition C.7 supplies the resulting representative channel pairs, and their outer-sector combination is formalized in #6632. The project-derived direct sector-mixing alternative in #6793 is retired. |
| **Example 4.10** (`ExZCLnoSAL`, l.898) | 898–906 | A mixed state has ZCL but does not saturate the area law | Blueprint `thm:cpsv_examples410_412_status`, `def:cpsv_example410_corrected_tensor`, `thm:cpsv_example410_source_zcl`, `thm:cpsv_example410_four_site_spectrum`, and `thm:cpsv_example410_tensor_entropy_obstruction`; `TNLean/MPS/MPDO/CPSVExample410Operator.lean`; `TNLean/MPS/MPDO/CPSVExample410Spectrum.lean`; `TNLean/MPS/MPDO/CPSVExample410Entropy.lean`; `TNLean/MPS/MPDO/CPSVExamples410411Arithmetic.lean`; `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; issue #6301 | **complete for the corrected fixed-parameter witness** — the printed channel repeats the left-qubit label. At $p=1/4$, the corrected left-right tensor is an MPDO with source ZCL. Its full operator root multisets are $\{0^{[0]},(1/4)^{[4]}\}$ for one site, $\{0^{[8]},(5/32)^{[4]},(3/32)^{[4]}\}$ for two sites, $\{0^{[48]},(7/64)^{[4]},(3/64)^{[12]}\}$ for three sites, and $\{0^{[248]},(41/128)^{[1]},(15/128)^{[4]},(9/128)^{[3]}\}$ for four sites. These spectra are project-derived consequences of the corrected reading, not formulas printed in CPSV16. They yield the exact tensor block entropies and $I_2-I_1=\frac1{16}\log\!\left(\frac{2^{32}7^7}{3^3 5^{20}}\right)>0$, so the corrected tensor satisfies $\mathrm{IsSourceZCL}\land\neg\mathrm{IsSAL}$. The entropy and linking calculations are project-derived. No universal $p\ne0,1/2$ claim is made; the printed exception list also misses $p=1$ |
| **Example 4.11** (`ExSALnoZCL`, l.908) | 908–925 | A mixed state saturates the area law but does not have ZCL | Blueprint `thm:cpsv_examples410_412_status` and `thm:cpsv_example411_not_source_zcl`; `TNLean/MPS/MPDO/CPSVExamples410411Arithmetic.lean`; `TNLean/MPS/MPDO/CPSVExample411SourceZCL.lean`; `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; issue #6414 | **printed SAL clause refuted; independent printed non-ZCL clause verified** — exact finite-ring spectra, entropy, and effective/ambient non-SAL are formalized. Both physical-trace transfers are nonzero, finite-marginal instability refutes the scale-invariant relation, and consequently both displayed tensors fail the literal Definition 4.2 idempotence diagram. No legacy doubled-index ZCL or thermodynamic conclusion is claimed |
| **Example 4.12** (unlabeled, l.932) | 932–939 | The toric-code boundary tensor is claimed to be SAL, ZCL, and RFP, but not of the simple GSNNCH form | `TNLean/MPS/MPDO/CPSVExample412Literal.lean`; `TNLean/MPS/MPDO/CPSVExample412FourCycleEntropy.lean`; `TNLean/MPS/MPDO/CPSVExample412NormalizedRFP.lean`; `TNLean/MPS/MPDO/GSNNCHFourCycleMarkov.lean`; Blueprint `thm:cpsv_example412_literal_formula`, `thm:cpsv_example412_literal_sal`, `thm:cpsv_example412_four_cycle_ssa_defect`, `thm:positive_commuting_overlapping_product_markov`, `thm:mpdo_gsnnch_four_cycle_markov`, `thm:cpsv_example412_not_gsnnch`, `thm:cpsv_example412_literal_zcl_rfp_gap`, and `thm:cpsv_example412_normalized_rfp_maps`; issues #5919, #6044, #6045, #6072, and #6073 | **source claims classified; GSNNCH exclusion complete** — the printed formula, positivity, one-site trace loss, and SAL are complete. Its physical-trace transfer satisfies $\mathcal T_M^2=2\mathcal T_M\ne\mathcal T_M$, so the printed representative fails literal Definition 4.2 ZCL and cannot satisfy the trace-preserving channel equations. For $\widehat M=(1/2)M$, the positive-length periodic family is normalized and explicit parity Kraus maps prove the bare two-channel predicate without added hypotheses. Its horizontal normal-block weights have modulus $1/\sqrt2$, so this result does not supply the line-246 unit-weight convention. Independently, the normalized four-site state has a strict SSA defect. Every four-site Definition 4.8 state has a quantum Markov decomposition for $A=\{0\}$, $B=\{1,3\}$, $C=\{2\}$, derived from positive commuting overlapping factors without ZCL or canonical-form assumptions. The two coordinates agree exactly, so the printed tensor is not GSNNCH. The Markov implication is derived rather than printed as a separate CPSV16 lemma. |
| **Proposition 4.13** (source label `Prop:IV.12`, l.945) | 945–952; proof 1863–1922 | A literal CPSV canonical-form MPDO tensor is vertically in canonical form | `TNLean/MPS/MPDO/CPSVVerticalCanonicalForm.lean` (`MPOTensor.verticalCF_of_cpsvCanonicalForm`) and its prerequisite modules | **complete** — the theorem constructs positive grouped weights and a rectangular coisometry $U$ with $UU^\dagger=I$, $U\widetilde M U^\dagger=\bigoplus_\alpha\mu_\alpha\otimes M_\alpha$, and $\widetilde M=U^\dagger(\bigoplus_\alpha\mu_\alpha\otimes M_\alpha)U$; it does not assert $U^\dagger U=I$ |
| **Theorem 4.14** (source label `thm:IV.13`, l.972) | 972–993; proof 1929–2088 | RFP iff the tensor-attached BNT algebra condition iff the fusion-isometry condition | Blueprint `thm:cpsv_theorem414_printed_status`; `TNLean/MPS/MPDO/BNTAlgebraTensorClauseReflectedTarget.lean`; `CPSVBNTFusionTensorClauseFromRFP.lean`; `CPSVBNTTheoremEquivalence.lean`; `TwoSitePrefixReflectedMarkedChain.lean`; `TNLean/MPS/MPDO/RescalingStableExplicitVerticalBNT.lean` (`MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause`); `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex` | **partial as printed; complete for (i) iff (ii), with the corrected active-support form complete for (i) iff (iii)** — under precisely the standing literal CPSV canonical-form and MPDO hypotheses, the one-site raw corner and two-site gauge corner have the same unblocked reflected tail. Literal Lemma L identifies the raw and Gram-dressed marks, normality makes the gauge Gram matrix scalar, and unitary normalization gives the two trace-preserving completely positive renormalization maps. The remaining qualification concerns only the fusion clause: the formal equivalence uses the documented active-support reading of (iii), including the empty-support and coisometry corrections, rather than the unrestricted printed clause. For the rescaling-stable example, the explicit clause `R_oneLabelBNTAlgebraTensorClause` immediately packages the existential witness. Its tensor-attached component is the rotated vertical contraction, not the original horizontal MPO; its multiplicity matrix $[25/32]$ is distinct from the chi matrix $\operatorname{diag}(1,7/25)$. This example-specific identification does not remove the general blocked-basis or printed fusion-clause restrictions. |
| Open question on length-dependent coefficients | 995–997 | Whether an RFP MPDO can have BNT structure coefficients that genuinely depend on the chain length | `TNLean/MPS/MPDO/LengthDependentRFPExample.lean` (`MPOTensor.BondTwoSingletonBaseModel.exists_isRFPViaTS_not_lengthIndependent_bntCoefficients`); `TNLean/MPS/MPDO/VerticalCoefficientPresentationCounterexample.lean` | **answered affirmatively for an explicit BNT presentation; bare presentation invariance refuted** — the bond-two singleton model is an MPDO in literal CPSV canonical form and is an RFP by Theorem 4.14(ii)$\Rightarrow$(i). Its displayed one-label tensor-attached BNT clause has $c^{(L)}=(\sqrt{1/2})^L$, hence $c^{(1)}\ne c^{(2)}$. The result is existential for this presentation. The separate projection/shear pair proves that horizontal positive-length MPV equality alone does not preserve the vertical coefficients or their length independence: its one-label coefficients are $1$ and $(4/5)^L$. That counterexample does not impose the source's horizontal canonical-form hypothesis on the sheared presentation, so it refutes only the stronger project proposal in issue #6395 and leaves the printed fixed-presentation question unchanged. |
| Theorem (l.1013) | 1013–1016 | Length-independent coefficients imply a topological-projector commuting Gibbs form | `TNLean/MPS/MPDO/CPSVTopologicalPhysicalGibbs.lean` (`MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS_of_cpsvCanonicalForm`) | **complete, with documented local corrections and length boundary** — for a literal CPSV canonical-form MPDO tensor satisfying the RFP condition and clause-relative length independence, the theorem gives the physical-space decomposition for every source-defined chain length $L=N+2$. Active product sectors, empty fixed-pair support, retained-row coisometries, the finite physical complement, and the unspecified length-one two-site convention are recorded in the corresponding paper-gap notes |

### 2.4 Appendix A — Proofs of Section II

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn CFII (l.1058) | 1058–1071 | CFII: canonical form with trace-preserving blocks and diagonal positive fixed points | `TNLean/MPS/CanonicalForm/Definitions.lean` (`CPSVCanonicalFormIIData`) | `leanok` |
| Eq. `II_XAX` | 1072–1077 | Every canonical-form tensor has a nonsingular same-ambient gauge representative in CFII | `TNLean/MPS/CanonicalForm/CPSVCanonicalFormII.lean` (`CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormII`) | **supporting equation; excluded from count** — the Lean result is **complete** |
| **Lemma `equalMPS`** (l.1080) | 1080–1091 | Two normal MPVs have overlap limit zero or one; limit one gives gauge-phase equivalence | `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` (`MPSTensor.IsNormalTensor.overlap_dichotomy`) | **complete** |
| **Corollary `eqV`** (l.1121) | 1121–1128 | Normal MPVs are asymptotically orthogonal or differ by a length-dependent phase | `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` (`MPSTensor.IsNormalTensor.mpv_phase_alternative`) | **complete** |
| **Corollary `Lem1`** (l.1130) | 1130–1133 | Orthogonal normal MPVs are eventually linearly independent | `TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean`; `TNLean/MPS/BNT/Basic.lean` | **complete** |
| Restatement of `prop:char-BNT` | 1137–1142 | BNT characterization | `TNLean/MPS/CanonicalForm/BNTCharacterization.lean` | **complete restatement** — carries the same nonzero-coefficient local correction as Proposition 2.7 |
| **Lemma A.5 `Lem:app_simple`** (l.1155) | 1155–1163 | Equality of finite power sums implies equality of multisets | Blueprint `thm:bounded_power_sum_multiset`; `TNLean/Algebra/ScalarPowerSumIdentity.lean`; `docs/paper-gaps/cpsv16_power_sum_alternative_route.tex` | **complete under the nonzero-coefficient local correction** — the positive-power sums of \([1]\) and \([1,0]\) agree although the multisets differ, so the lemma is applied only to the nonzero canonical-form coefficients, where the multiset conclusion holds |
| Restatement of `thm1` | 1167–1170 | Proportional fundamental theorem | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_proportional_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **complete restatement** — carries the same nonzero-coefficient local correction as Theorem 2.10 |
| Restatement of `II_cor2` | 1172–1179 | Equal-MPV fundamental theorem | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **complete restatement** — carries the same nonzero-coefficient local correction as Corollary 2.11 |
| **Corollary A.6 `thm:Fundamental-CFII`** (l.1197) | 1197–1199 | CFII refinement with unitary global and block gauges | Blueprint `cor:sector_bnt_proportional_unitary_sector_match`; `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm_unitary`) and `SectorBNT/Unitary.lean`; `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`; `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` | **complete under the nonzero-coefficient local correction** — with every CFII weight nonzero, the unitary theorem covers the full BNT surface |

### 2.5 Appendix B — Proofs of Section III

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Renormalization flow convergence | 1209–1244 | Renormalization flow from canonical form converges | `TNLean/MPS/RFP/Convergence.lean` (`rg_flow_converges_of_cf`); `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex` | **not-ready proof segment; refuted as printed and distinct from the completed Theorem 3.1 equivalence** — the current theorem proves convergence for each primitive block. For the literal canonical-form tensor with one physical component \(A^1=\operatorname{diag}(1,\omega)\), where \(\omega\) is a primitive cube root of unity, the dyadic transfer powers alternate on \(e_{21}\). Thus the full weighted repeated-copy assertion is false without an additional relative-phase condition |
| **Lemma `lem:charact-NT-pure-RFP`** | 1274–1301 | Normal-tensor RFP structural theorem | `TNLean/MPS/RFP/NormalIsometryCharacterization.lean` (`MPSTensor.IsNormalTensor.isTransferIdempotent_iff_isIsometryCanonicalForm`); `TNLean/MPS/RFP/StructuralFull.lean`; `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` | **complete, with documented local correction** — under exactly normality, which itself forces positive bond dimension, transfer idempotence is equivalent to the trace-normalized square-root isometry form. The factor $\sqrt{\Lambda}$ is required by the source reference tensor at line 1300 |
| Theorem 3.10 reverse-proof step | 1246–1271 | The printed ZCL-to-RFP argument uses a nonzero subleading eigenvalue | `TNLean/MPS/RFP/ZCLReverse.lean`; `TNLean/MPS/RFP/PhysicalObservableRealization.lean` | **proof segment; counted with Theorem 3.10** — the printed spectral step is invalid because a non-idempotent map may have only a nilpotent Jordan defect at eigenvalue zero. The multiplicity-one unit-weight representative now has an unconditional eigenvalue-free repair using arbitrary sector-supported trace probes; raw weighted copies remain outside this result |
| Theorem 3.10 RFP⇒NNCPH | 1305–1307 | RFP gives a nearest-neighbor commuting parent Hamiltonian | Corrected representative-level theorems in `TNLean/MPS/ParentHamiltonian/Commuting.lean` and the capstone merged by #4860 | **proof segment; counted with Theorem 3.10** — the corrected multiplicity-one, unit-weight representative implication to the all-chain NNCPH ground-space condition is complete. The printed unrestricted theorem remains not-ready because raw repeated-copy weights and the adjacent-gap counterexample already refute Theorem 3.8 |

### 2.6 Appendix C — Proofs of Section IV

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Prop `propsimple` | 1333–1336 | RFP implies literal ZCL and SAL | `TNLean/MPS/MPDO/RFPViaTS.lean` (`MPOTensor.isPhysicalTraceIdempotent_of_isRFPViaTS`, via `MPOTensor.physTraceTransfer_sq_of_isRFPViaTS`); `RFPViaTSSAL.lean` (`MPOTensor.isSAL_of_isRFPViaTS_of_trace_ne_zero` and horizontal specialization); `docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex` | **complete** — the Definition 4.1 equations directly imply the literal Definition 4.2 identity $\mathcal T_M^2=\mathcal T_M$. Positive semidefinite rings with nonzero trace at every positive length also satisfy SAL. This nonvanishing is the normalization boundary implicit in the source's density-operator language; positivity alone admits the zero family. The horizontal form is a stronger specialization that derives nonvanishing. The scale-invariant `IsSourceZCL` conjunction is retained as a broader corollary, not as the paper-facing statement |
| Lemma `Lsigma3` | 1351–1359 | SAL gives the three-site Markov decomposition | `TNLean/Analysis/EntropyMarkovForward.lean` (`Matrix.hayashi_ssa_equality_characterization_forward`); `TNLean/MPS/MPDO/SimpleLocalStructure.lean`; `docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex` | **complete** — the ambient HJPW blocks are normalized with $p_j=\operatorname{Re}\operatorname{tr}\omega_j$, nonnegative weights summing to one, and recovered trace-one right states on every supported sector. At supported zero weight only the left factor may be a normalized filler; on complementary sectors both factors may be fillers. The Hayashi fibre order and unitary orientation are fixed explicitly, and the characterization is axiom-free |
| Lemma `propSN` | 1406–1411 | SAL gives a positive physical-sector factorization with primitive active trace matrix | `TNLean/MPS/MPDO/InverseMapActiveSectorPrimitivity.lean` (`exists_positive_physicalSectorFactorization_activeSectorTraceMatrix_isPrimitive_of_isSAL`) | **complete** |
| Lemma `SALZCL` / Lemma C.5 | 1484–1502 | SAL and ZCL force the trace coefficients to have rank one on every sector label | `TNLean/MPS/MPDO/InverseMapLemmaC5CaseI.lean` (`MPOTensor.exists_neighboringOperator_trace_rank_one_coefficients_of_isSAL_of_literal_ZCL`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **complete** — under the standing normal Case-I hypotheses, injectivity, normality, SAL, and literal physical-trace idempotence give normalized rank-one coefficients for all Hayashi sector labels. The project extends the active coefficients by zero; the zero-weight reparameterized and rephased factorization makes every incident neighboring operator vanish. This realizes the source's all-index coefficient statement, though the source does not distinguish TNLean's active and inactive sectors. This neither replaces literal ZCL by TNLean's scale-invariant source-ZCL condition nor gives a Case-II conclusion. The raw four-sector tensor remains outside the normal Case-I hypotheses, and its normal representative loses literal ZCL |
| Corollary | 1503–1506 | SAL and ZCL imply the displayed structural form | `TNLean/MPS/MPDO/InverseMapLemmaC5CaseI.lean` (`MPOTensor.exists_physicalSectorFactorization_rank_one_coefficients_of_isSAL_of_literal_ZCL`); `PhysicalSectorFactorization.lean`; `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **complete** — on the normal Case-I and literal-ZCL surface, the factorization supplies TNLean's direct-sum physical-slice formula, ambient positive semidefinite neighboring operators, the exact complex identity \(\operatorname{tr}(\eta_{k,h})=a_kb_h\), and \(\sum_k a_kb_k=1\). The inactive-sector zero-weight completion is project-derived; this is neither TNLean's scale-invariant source-ZCL condition nor a Case-II result |
| Prop `3to5` | 1510–1517 | The structural data give trace-preserving coarse-graining and refinement maps | `TNLean/MPS/MPDO/PhysicalSectorCoarseGrainingIdentity.lean`; `PhysicalSectorRefinementIdentity.lean`; `PhysicalSectorBlockedRFP.lean`; `PhysicalSectorPhysicalTransport.lean` (`NeighboringTraceFactorization.blockTwo_isRFPViaTS`); `docs/paper-gaps/cpgsv17_mpdo_blocked_rfp_physical_transport.tex`; `docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`; `docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex`; `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **complete conditional helper for one supplied factorization** — the physical-transport theorem carries one sector-coordinate channel pair back to its original blocked tensor, and zero-weight preparation is completed on the quotient. It assumes a factorization of its full input tensor. Condition (iv) instead supplies separate factorizations for BNT representatives and leaves raw repeated-copy weights unconstrained, so this theorem cannot establish the refuted literal (iv)$\Rightarrow$(v). Its channels remain inputs to the viable (ii)$\Rightarrow$(v) construction after ZCL-derived common-weight absorption; projector-controlled outer-BNT assembly there is formalized in #6632. |
| Prop `3to4` | 1569–1577 | SAL gives the commuting product form | `TNLean/MPS/MPDO/CommutingFormBridge.lean`; `GSNNCHSectorSum.lean`; related physical-sector modules; `docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex` | **complete by a corrected proof; printed proof-path drift** — the Lean proof uses the raw BNT representatives and requires no copy independence. The source proposition is stated from condition-(iv) data alone, but its printed proof invokes `lemmus`, whose hypothesis is ZCL. Thus the formal result verifies the component conclusion while repairing a load-bearing hidden assumption in the source proof |
| Prop `4to2` | 1597–1601 | Commuting form and ZCL imply SAL | `TNLean/MPS/MPDO/CyclicActiveAreaLaw.lean` (`EtaLocalStructureData.isSAL_of_isSourceZCL`); `ZCL.lean` (`MPOTensor.IsSourceZCL.bondDim_ne_zero`); `CyclicActiveMarkovDecomposition.lean`; `FixedBondPositivePhysicalSectorRepresentative.lean`; `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` | **complete** — all-cut Hayashi decompositions for the original injective MPDO tensor in the selected physical coordinates imply SAL there, and the selected one-site isometry preserves SAL for the source tensor. Source ZCL itself forces nonzero bond dimension, so neither normality nor any property of the selected fixed tensor is assumed |
| Lemma `lemmus` | 1647–1650 | ZCL makes repeated-copy weights independent of the copy index | `TNLean/MPS/MPDO/SimpleTensor.lean` (`MPOTensor.weight_copy_independent_of_isPhysicalTraceIdempotent`) | **complete; source specialization linked** — the theorem assumes the literal Definition 4.2 equation and derives copy independence directly from its weighted block restriction. The broader `IsSourceZCL` theorem remains a separate scale-invariant generalization |
| Lemma | 1680–1691 | SAL gives separating orthogonal projectors | `TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`; `BNTSourceSectorProjectors.lean` | **complete** |
| Prop `prop2to3` | 1740–1743 | SAL and ZCL imply the blockwise structural form | `TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`; `BNTSourceSectorProjectors.lean`; `SimpleTensor.lean` (`MPOTensor.weighted_basis_physTraceTransfer_sq_of_literal_ZCL`); `BNTSectorAnalyticProperties.lean` (`MPOTensor.commonWeightAbsorbedBasisMPOTensor_physTraceTransfer_sq_of_literal_ZCL`); `BNTSectorAreaLaw.lean` (`MPOTensor.commonWeightAbsorbedBasisMPOTensor_caseII_properties_of_literal_ZCL`); `NonCartesianActiveSectorCounterexample.lean` (`MPOTensor.NonCartesianActiveSectorCandidate.full_lowLevel_counterexample`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **not ready; low-level implication refuted** — the separating projectors and full sectorwise analytic inheritance are formalized: every absorbed representative is injective, MPDO-positive, SAL, and literally physical-trace idempotent. Coefficient absorption need not preserve normality. The non-Cartesian tensor satisfies these local properties, has a representation $K=\mu A$ with $A$ normal and $0<|\mu|<1$, yet has no required factorization. It does not supply an ambient simple-biCF reconstruction or the global unit-weight witness, so the printed source-context conclusion remains open. |
| Prop `prop3to4` | 1786–1796 | Blockwise structure gives the GSNNCH form | `TNLean/MPS/MPDO/BNTSectorCoefficientPositivity.lean`; `GSNNCHSectorRescaling.lean`; `BNTPhysicalSectorGSNNCH.lean` (`hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization`); `docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex` | **complete by a corrected proof; printed proof-path drift** — global MPDO positivity and orthogonal sitewise compression make each fixed-length BNT power-sum coefficient nonnegative real. Its positive root, divided by the natural copy number, is absorbed into the supported commuting bond. This Lean proof uses raw BNT representatives and requires no copy independence. The printed proof instead invokes `lemmus`, hence silently uses ZCL although the proposition is stated from condition-(iv) data alone |
| **Proposition C.14** (`prop4to2`) | 1801–1808 | GSNNCH gives SAL | Blueprint `thm:mpdo_canonical_bnt_proportional_sectors_zcl_sal` (the printed-status stub `thm:cpsv_prop_c14_printed_status` was removed as redundant once the corrected theorem landed); `TNLean/MPS/MPDO/BNTSectorAnalyticProperties.lean` (`MPOTensor.IsSimpleCanonicalForm.exists_commonWeightAbsorbedBasisMPOTensor_isSourceZCL`); `PhysicalSupportRestriction.lean` (`MPOTensor.commonWeightAbsorbedBasisMPOTensor_isInjective`); `GSNNCHOrthogonalSectors.lean` (`ProportionalOrthogonalCommutingSectorFamily.mpo_posSemidef_of_two_le`, `ProportionalOrthogonalCommutingSectorFamily.isMPDO_of_mpo_one_pos`); `OrthogonalSectorAreaLaw.lean` (`MPOTensor.isSAL_of_proportionalOrthogonalCommutingSectorFamily_of_sectorwise_isSourceZCL`, `MPOTensor.isSAL_of_commonWeightAbsorbedBasisMPOTensor_of_proportionalSectors_of_isSourceZCL`); `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` | **partial as printed; corrected theorem complete** — under ambient source ZCL, the canonical absorbed sectors inherit source ZCL, and the standing Case II biCF one-letter span gives one-site injectivity. Their positive commuting bonds give positivity for every $N\geq2$, so only one-site positivity is separately assumed; this yields full sector MPDO positivity without normality. The corrected canonical-BNT implication is complete at this sharp boundary. The printed GSNNCH-only proposition remains partial because it omits ambient ZCL, and TNLean's unambiguous commuting-bond realization begins at $N=2$ |
| Prop `prop2to5` | 1810–1813 | SAL and ZCL give the two trace-preserving maps | `TNLean/MPS/MPDO/PhysicalSectorCoarseGrainingIdentity.lean`; `PhysicalSectorRefinementIdentity.lean`; `PhysicalSectorBlockedRFP.lean`; `ActiveSectorSpanningRFP.lean`; `BNTSectorAreaLaw.lean` (`MPOTensor.commonWeightAbsorbedBasisMPOTensor_caseII_properties_of_literal_ZCL`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **not ready, but not refuted by the raw-copy example** — this proposition starts from condition (ii). The earlier Case-II derivation uses ZCL to make copy weights independent of the copy label and absorb their common value. The non-Cartesian witness shows that the inherited local analytic properties alone do not yield the printed factorization, but does not refute its ambient source-context form. Issue #6775 tracks that factorization. Proposition C.7 constructs its representative channel pairs, and their projector-controlled outer-sector combination is formalized in #6632. The direct sector-mixing alternative formerly tracked in #6793 is not a separate source assertion. |

### 2.7 Appendix C.3--C.4 — Proofs of Proposition 4.13 and Theorem 4.14

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma `Lemma-L`** | 1835–1846 | Equality of first-site actions on all MPVs implies equality of inserted tensors | `TNLean/MPS/MPDO/CPSVOriginalSpaceLemmaL.lean` (`MPSTensor.IsCPSVCanonicalForm.insertedTensor_eq_of_firstSiteActionAgree`) | **complete** for literal CPSV canonical form |
| Restatement/proof of Proposition 4.13 | 1863–1922 | Vertical canonical form and rectangular coisometry | `TNLean/MPS/MPDO/CPSVVerticalCanonicalForm.lean` (`MPOTensor.verticalCF_of_cpsvCanonicalForm`) | **complete restatement** — $UU^\dagger=I$ and both exact direct-sum identities are proved |
| Restatement/proof of Theorem 4.14 | 1929–2088 | Algebra and fusion characterizations of RFP | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseReflectedTarget.lean`; `CPSVBNTFusionTensorClauseFromRFP.lean`; `CPSVBNTTheoremEquivalence.lean`; `TwoSitePrefixReflectedMarkedChain.lean`; `TNLean/MPS/MPDO/RescalingStableExplicitVerticalBNT.lean` (`MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause`); `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex` | **partial as printed; algebra characterization complete and corrected active-support fusion characterization complete** — the mixed-prefix comparison proves the line-2057 unitary normalization and the physical maps under exactly the source's canonical-form and MPDO assumptions. The equivalence with fusion is stated for the documented active-support correction to printed clause (iii). The rescaling-stable tensor now has the explicit one-label attached algebra clause `R_oneLabelBNTAlgebraTensorClause`, which immediately packages the existential witness. Its tensor-attached component is the rotated vertical contraction $(A\otimes\overline A)$, not the original horizontal MPO, and its multiplicity matrix $[25/32]$ is distinct from the chi matrix $\operatorname{diag}(1,7/25)$. This example-specific closure does not change the printed theorem's partial status. |

### 2.8 Appendix D — Additional results

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Alternative pure RFP up to virtual gauge (`RFP-gauge`) | 2094–2107 | Blocking is allowed to return the tensor up to a virtual gauge; the paper claims equivalence with ordinary pure RFP | Blueprint `thm:cpsv_pure_rfp_gauge_status` (the printed-status stub `thm:cpsv_rfp_gauge_printed_status` was removed; superseded by `thm:cpsv_pure_rfp_gauge_status`, which is `\leanok`); `TNLean/MPS/RFP/PhaseOscillation.lean` supplies the cube-phase obstruction; exact source-shaped gauge identity tracked by issue #5920 | **false as printed; active counterexample target** — the cube-phase tensor blocks to itself up to swap gauge-phase but has non-idempotent transfer, so the printed spectral argument fails |
| Strong unitary-conjugation RFP diagram (`Strong-RFP`) | 2109–2117 | Literal structural relation $M_2=U(M_1\otimes P)U^\dagger$ with $P\geq0$ on the right physical site | `TNLean/MPS/MPDO/StrongRFP.lean` (`MPOTensor.IsStrongRFP`); Blueprint `def:mpdo_strong_rfp`, `thm:mpdo_strong_rfp_phys_close`, `thm:mpdo_strong_rfp_periodic_rank_growth` | **complete** — the unnormalized local tensor relation, physical-closure equivalence, and periodic geometric-rank implication are proved |
| Fibonacci boundary rank formula (`rank-Fibonacci`) | 2118–2125 | $\operatorname{rank}\rho^{(N)}=\tau_+^{2N}+\tau_-^{2N}$, which is not of the form $rs^{N-1}$ | `TNLean/MPS/MPDO/FibonacciPeriodicRank.lean`; Blueprint `thm:cpsv_fibonacci_periodic_rank`, `thm:cpsv_fibonacci_operator_rank_not_geometric`, `thm:cpsv_fibonacci_not_strong_rfp` | **complete** — the periodic rank formula, its non-geometricity, and the resulting $\lnot\,\mathrm{IsStrongRFP}$ theorem hold for every positive choice of fusion weights with the prescribed Fibonacci support |
| Diagonalization identity (`eq:1`) | 2158–2173 | Matrix calculation used to derive the Fibonacci rank formula | Covered by the completed `rank-Fibonacci` formalization | **internal calculation, not an independent theorem** |
| Defn decorrelated | 2187–2192 | Decorrelated regions | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` | `leanok` |
| Defn parent commuting Hamiltonian | 2206–2216 | Parent commuting Hamiltonian subspace | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` | `leanok` |
| Prop | 2221–2223 | Decorrelation iff parent commuting Hamiltonian | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` (`TripartiteDecorrelation.parentHamiltonian_iff_decorrelated`) | **complete** |

---

## 3. Coverage crosswalk: PGVWC07 (quant-ph/0608197)

### 3.1 Section 3 — The canonical form

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem `thm:OBC-Vidal`** (l.431) | 431–443 | Every finite-chain state has a site-dependent OBC canonical MPS representation, with Schmidt-rank bond bound and positive diagonal bond densities | `TNLean/MPS/Chain/Defs.lean` (`MPSChainTensor`, for site-dependent closed chains of one fixed square bond dimension) | **not formalized** — the missing source structure is an open-boundary representation with varying bond dimensions, rectangular local matrices, and endpoint vectors, together with its construction by successive Schmidt decompositions |
| **Theorem `free-OBC`** (l.466) | 466–486 | Every OBC representation factors through the canonical one by local, generally rectangular matrices $Y_j,Z_j$ with $Y_jZ_j=I$ | `TNLean/MPS/Chain/Defs.lean` (`MPSChainTensor.GaugeEquiv`, the cyclic gauge relation for fixed square bond dimension) | **not formalized** — the cyclic relation uses invertible square gauges around a closed chain; it does not express the source's varying bond dimensions, rectangular local maps, or one-sided inverses $Y_jZ_j=I$ for an open chain |
| Theorem "Site-independent matrices" (l.620) | 620–630 | Every finite-ring TI state has a site-independent PBC representation, with bond dimension at most $ND$ when starting from an OBC representation of bond dimension $D$ | `TNLean/MPS/Chain/Defs.lean` (`MPSChainTensor`) | **not formalized** — site-dependent fixed-bond closed chains are represented, but no current declaration constructs the cyclic $ND$-dimensional site-independent tensor from a varying-bond OBC representation |
| **Theorem `Th:TIcanonical`** (l.742) | 742–763 | Arbitrary finite-ring TI representations admit the source block canonical form, with positive weights, unital blocks, positive full-rank dual fixed points, unique identity fixed points, and no increase in bond dimension | `TNLean/MPS/CanonicalForm/NormalReduction/WeightNormalization.lean` (`MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty`) | **complete in the positive-length convention** — after a positive global rescaling, an arbitrary tensor has exactly the same MPV coefficients on every nonempty ring as a possibly empty finite family of positive-weight unital blocks with diagonal positive-definite dual fixed points and scalar fixed-point spaces; the total bond dimension is at most the original bond dimension. The family is empty exactly in the branch where every positive-length MPV coefficient vanishes; otherwise it is nonempty and some normalized weight has norm one. |
| **Theorem `Th:periodic`** (l.849) | 849–858 | For a one-block canonical tensor with $p$ peripheral eigenvalues, if $p\mid N$ the finite-ring state is a superposition of $p$ translated $p$-periodic states, while if $p\nmid N$ the state is zero | `TNLean/MPS/CanonicalForm/SectorComparison/CyclicSectorDecomposition.lean` | **partial**: the peripheral cyclic projections and blocked sector decomposition are formalized, but neither the finite-ring decomposition for $p\mid N$ nor the vanishing theorem for $p\nmid N$ is packaged |
| Proposition `prop-inj` (l.911) | 911–936 | Condition C1 forces a single canonical block and gives reduced-density rank exactly $D^2$ across every cut with both sides of length at least $L_0$ | `TNLean/Wielandt/SpanGrowth/CumulativeSpan.lean` (`isNBlkInjective_of_le`); `TNLean/MPS/ParentHamiltonian/GroundSpaceGram.lean` (`groundSpaceMapES_injective_of_isNBlkInjective_of_le`) | **partial** — exact-length injectivity is propagated to longer boundary maps, but the single-block conclusion and reduced-density-rank statement are not packaged as the source proposition |
| Theorem "Interpretation of $\Lambda$" (l.987) | 987–993 | The half-chain reduced-density spectrum converges to the spectrum of $\Lambda\otimes\Lambda$, namely the products $\lambda_\alpha\lambda_\beta$ | **out of scope** | — |
| **Theorem `thm-uniq`** (l.1002) | 1002–1015 | Fixed-length uniqueness of a TI canonical representation under C1, uniqueness of its OBC canonical form, and $N>2L_0+D^4$, with a unitary conjugacy conclusion | `TNLean/MPS/FundamentalTheorem/Basic.lean`; `TNLean/MPS/FundamentalTheorem/FiniteLength.lean` | **not formalized** — the current single-block theorem assumes equality of the whole MPV family from a threshold onward and concludes general gauge equivalence; it does not derive the source fixed-$N$ unitary conclusion from OBC uniqueness |
| Lemma `lem-same-matr` (l.1022) | 1022–1040 | Same-matrix lemma for $T(Y_k)=S(Y_{k+1})$ | **out of scope** (purely linear-algebraic) | — |
| Lemma `lem-horn` (l.1053) | 1053–1058 | Horn's lemma: solution space of $W(C\otimes I)=(B\otimes I)W$ is $S\otimes M_n$ | **out of scope** | — |
| Theorem "Obtaining TI canonical form" (l.1154) | 1154–1165 | Solving the quadratic equations yields a TI $D$-MPS from a unique OBC canonical form | **out of scope** | — |

### 3.2 Section 4 — Parent Hamiltonians

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem "Uniqueness with OBC" (l.1206) | 1206–1209 | After regrouping so that every site-dependent local matrix family satisfies C1, the canonical OBC MPS is the unique ground state of the associated nearest-neighbor open-chain Hamiltonian | not applicable | **not formalized**: the current parent-Hamiltonian development treats site-independent tensors and periodic-chain translated constraints, not this blockwise-C1 OBC Hamiltonian |
| **Theorem `uniqueGS`** (l.1272) | 1272–1274 | Under C1, the TI parent Hamiltonian has a unique periodic ground state for $N\ge2L_0$ and $L>L_0$ | `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` (`chainGroundSpace_eq_mpvSubmodule_normal`, `parentHamiltonian_unique_gs`, `parentHamiltonian_unique_gs_normal`, `parentHamiltonian_unique_gs_injective`) | **complete with a stronger finite-size range** — `HasUniqueGroundState` is proved for every $L_0<L\le N$ when $N\ge2$ and $L_0+1\le N$, including $L_0=1$, $N=2$; this contains and strengthens the printed range $N\ge2L_0$ |
| Lemma `lem1` (l.1333) | 1333–1344 | For $C\ne0$, the matrices $RCS$ span the full matrix algebra | `TNLean/Algebra/MatrixTracePairing.lean` (`Matrix.span_range_mul_nonzero_mul_eq_top`); `TNLean/Algebra/TracePairing.lean` (`MPSTensor.span_range_evalWord_mul_nonzero_mul_evalWord_eq_top`) | **complete** |
| Lemma `lem:direct-sum` (l.1346) | 1346–1408 | For $L\ge3(b-1)(L_0+1)$, the block spaces $\mathcal G_L^{A^j}$ form a direct sum | `TNLean/MPS/ParentHamiltonian/BNTBlockIntersection.lean` (`MPSTensor.groundSpace_iSupIndep_of_ge_of_bnt_directSum_unital_c1_pgvwc07_of_dualFixedPoint`), using `TNLean/MPS/MPDO/BiCFDerivation/BNTDirectSum.lean` and `Selectors.lean` | **complete under a stronger separation hypothesis**: the exact homogeneous source length is formalized assuming that distinct equal-dimensional blocks are not gauge-phase equivalent. PGVWC07 states only pairwise inequality of the finite-ring component vectors, which does not exclude unequal proportional vectors from gauge-phase-equivalent weighted blocks. Closing the gap requires identifying or proving the projective nonproportionality condition used by the interpolation argument and deriving the formal separation premise from it; if the source is read literally, the extra premise must remain |
| **Theorem `2blocks.1`** (l.1407) | 1407–1415 | If $N\ge3(b-1)(L_0+1)+L$, every component state of a canonical block sum is a ground state of any TI frustration-free $L$-local Hamiltonian that annihilates their sum | not applicable | **not formalized**: current component-annihilation lemmas assume the individual component ground-state conditions rather than deriving them, under the source chain-length bound, from an arbitrary Hamiltonian annihilating the sum |
| **Theorem `2blocks.2`** (l.1424) | 1424–1456 | At the source interaction length, the canonical block-sum parent Hamiltonian has ground space exactly the span of the periodic component vectors | `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean` (`MPSTensor.ker_parentHamiltonian_toTensorFromBlocks_eq_bntMPSVectorSpan_of_global_cut_bnt_c1_pgvwc07_of_dualFixedPoint`) | **complete under a stronger separation hypothesis**: the source unital normalization, arbitrary positive-definite dual fixed points, and source chain-length bounds are formalized, but the theorem assumes gauge-phase inequivalence of distinct equal-dimensional blocks. The printed pairwise inequality of finite-ring component vectors is too weak because unequal vectors may be proportional. The projective condition needed by the interpolation argument must be identified and connected to the formal separation premise, or the extra premise must remain explicit |

### 3.3 Section 5 — Generation of MPS

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem `Thm:seqwith` (l.1569) | 1569–1573 | Sequential generation with ancilla: all OBC MPS with D-dimensional ancilla | **out of scope** | — |
| Theorem "Sequential generation without ancilla" (l.1589) | 1589–1595 | Without ancilla: D ≤ d | **out of scope** | — |

### 3.4 Section 6 — Classical simulation

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem MPS approximation bound (l.1774) | 1774–1781 | ∃ MPS with bond dim D approximating within Σ ε_k(D) | **out of scope** | — |
| Theorem Rényi entropy bound (l.1794) | 1794–1797 | log ε(D) ≤ (1-α)/α (S^α - log D/(1-α)) | **out of scope** | — |
| Theorem D_L polynomial bound (l.1824) | 1824–1828 | D_L ≤ poly(L) for critical systems | **out of scope** | — |
| Theorem `Thm:ClusterComputation` (l.1938) | 1938–1943 | Simulating 1D measurement-based computation | **out of scope** | — |
| Theorem `Thm:CircuitComputation` (l.1952) | 1952–1959 | Simulating quantum circuits with bounded MPS bond dim | **out of scope** | — |

### 3.5 Section 7 — Open problems / Appendix

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Conj `Conj1` (l.2103) | 2103–2107 | f(D) bound for injectivity length | **out of scope** | — |
| Conj `Conj2` (l.2109) | 2109–2111 | f(D) ~ O(D²) | **out of scope** | — |
| Prop `prop:appendix` (l.2116) | 2116–2118 | If A₀ invertible, L₀ ≤ D² | **out of scope** | — |
| Corollary W-state (l.2181) | 2181–2185 | W-state bond dimension lower bound | **out of scope** | — |
| Theorem "Dichotomy for MPS size" (l.2242) | 2242–? | Dichotomy: bond dim either constant or ≥ poly(N) | **out of scope** | — |

---

## 4. Scope-gap crosswalk with tracked issues

There are no current `sorry` or axiom declarations in the MPS files cited by
this audit. The remaining entries under the existing trackers record mismatches
between proved theorem statements and their sources, not unfinished proof
terms.

### 4.1 Periodic overlap and periodic fundamental theorem (issue #82)

`TNLean/MPS/Periodic/FundamentalTheorem.lean` proves conditional block-matching
and scalar multiplicity results. Its declarations still assume a periodic
overlap hypothesis, and the equal-case theorem treats one-dimensional
multiplicity spaces. The source theorem for irreducible forms derives the
matching from equality of the multiplicity-bearing MPV families and permits
general diagonal multiplicity matrices. PGVWC07 Theorem `Th:periodic` also has
unpackaged finite-ring conclusions: the translated periodic decomposition when
$p\mid N$ and vanishing of the state when $p\nmid N$. These are statement-scope
gaps.

### 4.2 Parent Hamiltonians (current trackers #190 and #5455)

The single-block periodic uniqueness and source-normalized block-diagonal
kernel theorems are proved in `ParentHamiltonian/UniqueGroundState.lean` and
`ParentHamiltonian/BNTBlockDiagonalBoundaryClosing.lean`. The `uniqueGS` result
is complete with the stronger finite-size range $N\ge2$ and $N\ge L_0+1$ for
every $L_0<L\le N$. The remaining qualifications in §3.2 are the absence of
the arbitrary-Hamiltonian implication under the stated chain-length bound in
`2blocks.1`, and the stronger block-separation premise in `lem:direct-sum` and
`2blocks.2`. The current Lean theorems assume gauge-phase inequivalence. The
source states only pairwise inequality of the finite-ring component vectors,
which does not exclude unequal proportional vectors. Closing this gap requires
identifying or proving the projective nonproportionality condition used by the
interpolation argument and deriving the formal separation premise from it. If
the source is read literally, the extra premise must remain. These are
statement-scope gaps, not deleted files or proof holes.

CPSV16 Theorem 3.10 is likewise not an axiom-removal problem on the printed
statement. The unrestricted RFP–ZCL equivalence inherits the formal raw-weight
and adjacent-gap counterexamples to Theorem 3.8. The reverse proof at source
line 1250 also fails for a nilpotent Jordan defect at eigenvalue zero. The
corrected multiplicity-one, unit-weight representative equivalence, including
the all-chain NNCPH conclusion, is complete; the unrestricted printed theorem
is therefore retained as not-ready rather than as unfinished formalization
work.

### 4.3 PEPS (out of scope)

PEPS proof status is maintained separately and is not summarized by an MPS
`sorry` count here.

---

## 5. CPSV21 Theorem 4.4 and Corollary 4.5

CPSV21 Definition 4.2 retains the weak BNT clauses of CPSV16: an unrelated
normal representative may be added to the chosen BNT with coefficient zero at
every length. The underlying canonical tensor may nevertheless have only its
original summand, with actual coefficient one. Thus the formal one-versus-two
BNT example literally refutes the equality of chosen-BNT cardinalities in
CPSV21 Theorem 4.4. The sector-BNT proportional theorem is an explicitly
restricted correction of CPSV16 Theorem 2.10 and CPSV21 Theorem 4.4, not
complete coverage of either unrestricted statement.

CPSV21 Corollary 4.5 has a different surface. It concerns the ambient canonical
tensors themselves, and the standing construction at lines 1801--1808 gives
their actual direct-sum summands positive coefficients. The extraneous BNT
representative once used in a withdrawn unequal-cardinality counterexample is
not an ambient canonical summand. Consequently no zero-coefficient correction
applies to Corollary 4.5. The current equal
theorem is only a packaged SectorBNT analogue of Corollary 4.5 until a bridge
from CPSV21 canonical form to the SectorBNT hypotheses is supplied.

| Lean declaration | CPSV21 relation | CPSV16 relation |
|---|---|---|
| `MPSTensor.fundamentalTheorem_proportional_canonicalForm` | Restricted correction of Theorem 4.4 | Restricted correction of Theorem 2.10 (`thm1`) |
| `MPSTensor.fundamentalTheorem_equal_canonicalForm` | Packaged SectorBNT analogue of Corollary 4.5; the canonical-form-to-SectorBNT bridge remains to be supplied | Corollary 2.11 (`II_cor2`) under the nonzero-coefficient local correction |
| `MPSTensor.fundamentalTheorem_equal_canonicalForm_unitary` | No direct CPSV21 identification asserted | Active, nonzero BNT unitary refinement of `thm:Fundamental-CFII` |

---

## 6. File-length note

Two oversized Lean files appear in CI file-length checks but are untouched by this doc-only audit:

| File | Lines |
|---|---|
| `TNLean/MPS/MPDO/BiCFDerivation/PairHomogenization.lean` | ~1460 |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | ~1569 |

These are known oversized (documented in #1512/#1522) and do not block unrelated doc PRs.

---

## 7. Key remaining coverage gaps

The 16 non-complete distinct CPSV16 results comprise 4 partial, 11 not-ready,
and 1 refuted result. They are source-ambiguous, formally refuted, research-level,
owner-held, or scope-restricted by the current formal statement. Lemma
`Lsigma3`, the Hayashi strong-subadditivity equality characterization, and the
Appendix B single-normal-tensor RFP/isometry characterization are complete and
axiom-free.

| Status | Paper | Result | Current certificate | Ownership |
|---|---|---|---|---|
| Complete under local correction | CPSV16 | Prop. 2.7, BNT characterization | Every block is characterized once all coefficients are nonzero by convention | `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` |
| Complete under local correction | CPSV16 | Theorem 2.10 | Every canonical-form coefficient is nonzero by convention (source line 246), so the BNT cardinalities agree | `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` |
| Complete under local correction | CPSV16 | Corollary 2.11 | With nonzero coefficients, equal positive-length MPVs determine the ambient dimension and the global conjugacy | `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` |
| Not-ready | CPSV16 | Appendix A Lemma `Lem:app_simple` | \([1]\) and \([1,0]\) have identical positive-power sums but different multisets; the formal corrections require nonzero entries or filter zeros | `TNLean/Algebra/ScalarPowerSumIdentity.lean`; `docs/paper-gaps/cpsv16_power_sum_alternative_route.tex` |
| Complete under local correction | CPSV16 | Appendix A CFII refinement | With nonzero CFII weights, the Lean unitary theorem covers the full BNT surface | `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`; `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` |
| Not-ready | CPSV16 | Adjacent canonical-form convergence assertion after Theorem 3.1 | `rg_flow_converges_of_cf` proves convergence for each primitive block, but the literal repeated-copy tensor \(A^1=\operatorname{diag}(1,\omega)\) has a phase-oscillating dyadic transfer orbit | `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`; this refuted proof-segment claim is uncounted and is not part of the completed flow-limit equivalence |
| Not-ready | CPSV16 | Theorem 3.8 | Raw weights and the Bell-pair adjacent-gap example refute the two unrestricted directions; the multiplicity-one, unit-weight positive-gap equivalence is complete | `TNLean/MPS/RFP/ZCLReverse.lean`; `TNLean/MPS/RFP/BNTWeightCounterexample.lean`; `TNLean/MPS/RFP/BellPairCIDObstruction.lean` |
| Not-ready | CPSV16 | Theorem 3.10 | Inherits the formal raw-weight and adjacent-gap counterexamples to Theorem 3.8; the corrected multiplicity-one, unit-weight representative equivalence and NNCPH conclusion are complete | `TNLean/MPS/RFP/ZCLReverse.lean`; `TNLean/MPS/RFP/MainMPSConditional.lean`; `TNLean/MPS/RFP/PhysicalObservableRealization.lean` |
| Not-ready | CPSV16 | Theorem 3.11 | The repeated-copy physical isometry lacks a copy index; the literal shared-map reading is false | #2598 closed as source obstruction |
| Complete for phase-class representatives | CPSV16 | Corollary 3.12 | The phase-class statement, including all joint residual-isometry equations, is complete for the canonical-form blocks, all of which carry nonzero coefficients | `TNLean/MPS/RFP/CPSVCanonicalForm.lean` (`CPSVCanonicalFormData.BNTRefinement.exists_residualIsometryFamily_of_isTransferIdempotent`, `IsCPSVCanonicalForm.exists_bntRefinement_residualIsometryFamily_of_isTransferIdempotent`); `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` |
| Not-ready | CPSV16 | Purification RFP equivalence | Nilpotent hidden bond sectors refute the global-to-local implication | #3947 closed as not planned |
| Refuted as printed | CPSV16 | Proposition 4.5 | Monotonicity and the finite-chain bounds are complete as separate results. The source-facing parity theorem proves that an MPDO can have no real mutual-information limit at every fixed nonempty cut, so the unrestricted thermodynamic-limit clause is false. Aperiodicity or convergence is a genuine boundary condition absent from the source statement | `TNLean/MPS/MPDO/MutualInfoMonotone.lean` (`MPOTensor.mutualInfoChain_monotone`); `TNLean/MPS/MPDO/MutualInfoAreaLaw.lean` (`MPOTensor.mutualInfoChain_le_two_log_bondDim`, `MPOTensor.IsMPDO.mutualInfoChain_le_four_log_bondDim`); `TNLean/MPS/MPDO/ThermodynamicLimitCounterexample.lean` (`MPOTensor.ThermodynamicLimitCounterexample.proposition45_limit_counterexample`); `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex` |
| Partial and partly refuted | CPSV16 | Theorem 4.9 | Implication \((i)\Rightarrow(ii)\), HJPW/Hayashi equality, Petz recovery, sectorwise injective+MPDO+SAL+literal-ZCL inheritance, and the complete bond-one neighboring-trace boundary are complete. The non-Cartesian four-letter tensor refutes the implication from those low-level properties to normalized rank-one neighboring traces, but has no ambient simple-biCF witness and does not refute printed (ii)$\Rightarrow$(iv). Separately, the exact scalar repeated-copy theorem satisfies every standing hypothesis and condition (iv), but fails (v), so literal (iv)$\Rightarrow$(v) is false. The source-context factorization remains #6775; Proposition C.7 and the formalized projector-controlled outer assembly supply the subsequent source steps. The project-derived direct sector-mixing route in #6793 is retired. | `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean` (`full_lowLevel_counterexample`); `TNLean/MPS/MPDO/Theorem49RepeatedCopyCounterexample.lean` (`printed_theorem49_iv_to_v_is_false`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex` |
| Partial/corrected | CPSV16 | Theorem 4.14 | The equivalence between the RFP condition and the tensor-attached BNT algebra clause is complete under the printed standing assumptions. The fusion equivalence is complete for the documented active-support correction to clause (iii), but this is not the unrestricted printed clause. The mixed-prefix marked comparison gives the scalar Gram identity, unitary sector gauges, and the full trace-preserving completely positive maps. The rescaling-stable example has the explicit one-label clause `R_oneLabelBNTAlgebraTensorClause`, which immediately packages the existential witness. Its tensor-attached component is the rotated vertical contraction, not the original horizontal MPO, and its multiplicity matrix $[25/32]$ is distinct from the chi matrix $\operatorname{diag}(1,7/25)$. | `TNLean/MPS/MPDO/BNTAlgebraTensorClauseReflectedTarget.lean`; `TNLean/MPS/MPDO/CPSVBNTTheoremEquivalence.lean`; `TNLean/MPS/MPDO/RescalingStableExplicitVerticalBNT.lean` (`MPOTensor.RescalingStableLengthDependentRFP.R_oneLabelBNTAlgebraTensorClause`); `docs/paper-gaps/cpsv16_two_site_sector_unitary_gauge_gap.tex` |
| Complete | CPSV16 | Proposition `4to2`, lines 1597–1601 | The selected physical coordinates give all-cut Markov decompositions for the original tensor, hence SAL, which is transported back through the one-site isometry | `MPOTensor.EtaLocalStructureData.isSAL_of_isSourceZCL` |
| Not ready; low-level implication refuted | CPSV16 | Proposition `prop2to3` | Sectorwise injectivity, MPDO positivity, SAL, and literal physical-trace idempotence are complete for every absorbed BNT representative. At virtual bond dimension one, SAL and literal idempotence also give the full normalized one-sector factorization. The non-Cartesian four-letter tensor satisfies these properties and has a representation $K=\mu A$ with $A$ normal and $0<|\mu|<1$, but no physical-sector factorization has normalized rank-one neighboring traces. It has no ambient simple-biCF reconstruction or global unit-weight witness, so it proves that the local properties are insufficient without refuting the printed source-context assertion. | `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean` (`MPOTensor.NonCartesianActiveSectorCandidate.full_lowLevel_counterexample`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex`; issue #6775 |
| Partial | CPSV16 | Proposition `prop4to2` | The corrected canonical-BNT theorem is complete under ambient source ZCL, the standing biCF one-letter span, and one-site positivity of each absorbed sector. Positive commuting bonds give every $N\geq2$ positivity, so no full sector-MPDO or normality premise remains. The printed GSNNCH-only statement still omits ambient ZCL, and its unambiguous bond realization begins at $N=2$ | `TNLean/MPS/MPDO/OrthogonalSectorAreaLaw.lean` (`MPOTensor.isSAL_of_commonWeightAbsorbedBasisMPOTensor_of_proportionalSectors_of_isSourceZCL`); `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` |
| Not ready | CPSV16 | Proposition `prop2to5` | This is the viable source (ii)$\Rightarrow$(v) route, not the refuted raw (iv)$\Rightarrow$(v) claim. After ZCL-derived common-weight absorption, #6775 tracks the ambient source-context factorization. The non-Cartesian witness shows that the inherited local analytic properties alone do not settle it. Proposition C.7 supplies the representative channels from that factorization, and their projector-controlled outer combination is formalized in #6632. The direct sector-mixing construction formerly tracked in #6793 is project-derived and is retired as a separate source obligation. | `TNLean/MPS/MPDO/PhysicalSectorBlockedRFP.lean`; `TNLean/MPS/MPDO/PhysicalSectorPhysicalTransport.lean`; `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean`; `TNLean/MPS/MPDO/BNTSectorAreaLaw.lean`; `docs/paper-gaps/cpgsv17_pf_rank_one.tex` |
| Complete | PGVWC07 | Theorem `Th:TIcanonical` | The arbitrary-input theorem is formalized in the positive-length convention: after positive global rescaling it gives a possibly empty normalized block family with exact MPV equality on every nonempty ring and total bond dimension at most the original bond dimension; the family is empty exactly when all positive-length MPV coefficients vanish. | `MPSTensor.exists_pgvwc07_normalized_exact_form_after_rescaling_allow_empty` |
| Not formalized | PGVWC07 | Theorem `thm-uniq` | The source fixed-length theorem assumes C1, uniqueness of the OBC canonical form, and $N>2L_0+D^4$, and concludes unitary conjugacy. The current theorem instead assumes equality of the entire MPV family from a threshold onward and concludes general gauge equivalence | #1529 |
| Complete with a stronger finite-size range | PGVWC07 | Theorem `uniqueGS` | `HasUniqueGroundState` is proved for every $L_0<L\le N$ when $N\ge2$ and $L_0+1\le N$, including $L_0=1$, $N=2$; this contains and strengthens the printed range $N\ge2L_0$ | `MPSTensor.parentHamiltonian_unique_gs`; #181/#190 |
| Partial | PGVWC07 | Theorem `Th:periodic` | The finite-ring translated decomposition for $p\mid N$ and the vanishing conclusion for $p\nmid N$ remain unformalized | #82 |
| Out of scope | PGVWC07 | Interpretation of $\Lambda$ | The half-chain reduced-density spectrum converges to the spectrum of $\Lambda\otimes\Lambda$, with eigenvalues $\lambda_\alpha\lambda_\beta$ | — |

---

## 8. Audit methodology

- Source paper lines counted in `Papers/1606.00608/MPDO-22-12-17-2.tex` and `Papers/quant-ph_0608197/MPSarchive.tex`.
- The CPSV16 every-label inventory is validated by `scripts/audit_cpsv16_labels.py` against `docs/audits/data/cpsv16-label-dispositions.tsv`; it counts 187 lexical occurrences and 183 lexical names, derives the 186 active occurrences and 182 active names by stripping unescaped TeX comments, compares source activity with the ledger occurrence by occurrence, checks the four duplicate names listed in §2, and verifies explicit status inheritance for exactly 58 unique theorem/proof-contained equation and figure labels comprising 60 occurrences.
- Lean locations determined by grep for paper citations, theorem names, and type signatures in `TNLean/MPS/`.
- `leanok` status: verified via `rg "\bsorry\b|axiom"` in the referenced Lean files — no sorry/axiom in those specific files means the theorem body compiles. Does **not** guarantee full correctness relative to the paper; formal proof review is separate.
- A source theorem is marked **not formalized** when no Lean theorem has the same hypothesis set and conclusion, even if proved constituent reductions are available.
- `needs verification`: paper label exists but Lean mapping is uncertain, incomplete, or unconfirmed. Items marked `needs verification` should be re-checked by a domain expert before claiming coverage.
- `out of scope`: paper result considered outside the MPS Fundamental Theorem core (e.g., simulation bounds, entropy theorems, sequential generation).

---

*This audit follows the CPSV16 source-faithfulness policy from #1498. All references to CPSV16 theorems use source labels (`thm:main-MPS`, `TheoremZCLPure`, `thm:charact-MPS`, `thm:main-simple`, `thm:IV.13`, `prop:char-BNT`, `thm:Fundamental-CFII`) and line ranges from the source `.tex`.*

---

## 9. Coverage crosswalk: SPGWC09 (arXiv:0909.5347) — Quantum Wielandt's Inequality

**Existing audit**: `docs/audits/issue-1449-wielandt-source-audit.md`
(2026-05-07) covers the Theorem 1 statement faithfulness and the MPS import
inventory. This section provides an expanded source-paper crosswalk.

**Overall status**: **All Wielandt source theorems are `leanok` — zero sorrys, zero axioms** in `TNLean/Wielandt/`. The formalization is fully proved.

### 9.1 Proposition 3 — Equivalence of primitivity notions (l.504–565)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Proposition 3** `prop:equiv` (l.504) | 504–509 | (a) primitive ⇔ (b) eventually full Kraus rank ⇔ (c) strongly irreducible | `TNLean/Wielandt/Primitivity/Equivalence.lean` (full circular equivalence); `Primitivity/EasyDirections.lean` (b→a); `Primitivity/ImpliesStronglyIrreducibleAux.lean` (a→c); `Primitivity/StronglyIrreducibleToFullRank.lean` (c→b) | `leanok` |
| Prop `prop:iq` (l.447) | 447–449 | q(E_A) ≤ i(A) | `TNLean/Wielandt/Inequality/Bounds.lean` (`qIndex_le_iIndex_of_isPrimitivePaper`) | `leanok` |
| Prop (l.478) | 478–482 | For classical stochastic A: p(A)=q(A)=i(A) | **out of scope** (classical specialization) | — |

### 9.2 Lemma 1 — Nonzero-trace word (l.572–590)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma 1** `lemma1` (l.572) | 572–576 | Primitive ⇒ ∃ word of length ≤ D²−d+1 with nonzero trace | `TNLean/Wielandt/Inequality/NonzeroTraceWord.lean` (`exists_nonzero_trace_word_of_isPrimitivePaper_sharp`); internal proof via `SpanGrowth/NonzeroTraceProduct.lean` | `leanok` |
| Cumulative corollary (l.580–584) | 580–584 | dim[T_{D²−d+1}(A)] = D² | `TNLean/Wielandt/Inequality/NonzeroTraceWord.lean` (`cumulativeSpan_eq_top_of_isPrimitivePaper_sharp`) | `leanok` |
| Positive-length variant | — | For D ≥ 2, positive-length word with nonzero trace exists | `TNLean/Wielandt/Inequality/NonzeroTraceWord.lean` (`exists_nonzero_trace_word_of_isPrimitivePaper_sharp_pos`) | `leanok` |

### 9.3 Lemma 2 — Spreading and spanning (l.593–641)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma 2(a)** `lemma2` (l.593) | 593–599 | Primitive + A₁ eigenvector ⇒ H_{D−1}(A,φ) = ℂ^D | `TNLean/Wielandt/Inequality/EigenvectorSpreading.lean` (`vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector`); internal proof via `SpanGrowth/EigenvectorSpreading.lean` | `leanok` |
| **Lemma 2(b)** (l.593) | 593–599 | Primitive + noninvertible A₁ ⇒ |φ⟩⟨ψ| ∈ S_{D²−D+1}(A) | `TNLean/Wielandt/Inequality/MatrixSpanSharpBound.lean` (`vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector`); internal proof via `RectangularSpan/Universality.lean` | `leanok` |
| Coarse existential 2(b) | — | ∃ N : S_N(A) = M_D(ℂ) | `TNLean/Wielandt/Inequality/MatrixSpanExistence.lean` (`exists_wordSpan_eq_top_of_isPrimitivePaper`) | `leanok` |

### 9.4 Theorem 1 — Quantum Wielandt's inequality (l.645–655)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem 1** `thm:mainthm` (l.645) | 645–655 | Main theorem: i(A) bounds in three cases | `TNLean/Wielandt/Inequality/Bounds.lean` | `leanok` |
| Case (1) general bound | l.649 | i(A) ≤ (D² − d + 1) D² | `iIndex_le_general_of_isPrimitivePaper` | `leanok` |
| Case (2) invertible | l.650–651 | i(A) ≤ D² − d + 1 | `iIndex_le_of_mem_wordSpan_one_of_isUnit` (paper-faithful: X ∈ wordSpan A 1) | `leanok` |
| Case (3) noninvertible | l.652–653 | i(A) ≤ D² | `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector` (paper-faithful) | `leanok` |
| q ≤ i bound | l.647 | q(E_A) ≤ i(A) (repeated from Prop. `prop:iq`) | `qIndex_le_iIndex_of_isPrimitivePaper` | `leanok` |

**Deviation note (#1049, resolved)**: The original formalization required the special matrix to be a single Kraus operator `A i₀`. This was resolved via one-step augmentation — the current `_of_mem_wordSpan_one_` variants accept an arbitrary element of `S₁(A)`, matching the paper's hypothesis exactly.

### 9.5 Theorem on zero-error capacity (l.736–771)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem** `thm:zero` (l.736) | 736–741 | Zero-error capacity dichotomy: C₀(E^n) ≥ 1 ∀n or C₀(E^{q(E)}) = 0 | **out of scope** (information theory, not MPS) | — |

### 9.6 Theorems on frustration-free Hamiltonians and MPS (l.828–859)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem** (l.828) | 828–831 | If L > i(A), MPS is unique ground state of parent Hamiltonian with spectral gap | PGVWC07 `uniqueGS`; `ParentHamiltonian/UniqueGroundState.lean`; `ParentHamiltonian/Martingale/Gap.lean` (`parentHamiltonian_gapped_of_anticommutator`); Blueprint Theorem `thm:parent_hamiltonian_gapped` | **partial** — uniqueness is proved for every interaction range $L_0<L\le N$, including the minimal endpoint $L_0=1$, $L=N=2$; see §3.2. The unconditional spectral-gap conclusion remains incomplete: the current source-matching gap theorem assumes the cyclic-window anticommutator estimate, whose MPS-specific proof remains open in #5455 (broader tracker #460). |
| **Theorem** (l.850) | 850–858 | Dichotomy for ground states of frustration-free Hamiltonians: D either O(1) or ≥ Ω(N^{1/5}) | **out of scope** | — |

### 9.7 MPS use of Wielandt infrastructure

The MPS development imports a focused subset of Wielandt declarations (detail
in `docs/audits/issue-1449-wielandt-source-audit.md`, §4):

| MPS file | Wielandt import | Key declaration |
|---|---|---|
| `FundamentalTheorem/FiniteLength.lean` | `SpanGrowth/CumulativeSpan` | local `wordSpan_eq_top_of_isInjective` |
| `CanonicalForm/Existence.lean` | `Primitivity/StronglyIrreducibleToFullRank` | `isNormal_of_isPrimitiveMPS_with_posDef` |
| `CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `SpanGrowth/VectorToMatrixSpan`, `SpanGrowth/CumulativeSpan`, `RectangularSpan/Basic`, `Primitivity/ToNormal`, `Primitivity/StronglyIrreducibleToFullRank` | Multiple span and primitivity lemmas |
| `ParentHamiltonian/UniqueGroundState.lean` | `SpanGrowth/CumulativeToWordSpan` | `cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one` |
| `ParentHamiltonian/IntersectionProperty.lean` | `SpanGrowth/CumulativeToWordSpan` | Same |
| `ParentHamiltonian/WrappingWindow.lean` | `SpanGrowth/VectorToMatrixSpan` | Vector-to-matrix lemmas |

The `Inequality/` files are standalone Wielandt declarations and are not
imported by the MPS development.

### 9.8 Sorry/axiom status for Wielandt

**Zero sorrys, zero axioms** across all 42 Wielandt `.lean` files. The entire quantum Wielandt formalization is fully proved and source-faithful to SPGWC09.
