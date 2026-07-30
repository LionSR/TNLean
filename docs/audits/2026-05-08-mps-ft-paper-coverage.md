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

**Scope**: This audit covers the MPS and MPDO results of CPSV16, the MPS / pure-state sections of PGVWC07, and a full Wielandt source-paper crosswalk (§9). The CPSV16 crosswalk was synchronized with the complete source audit on 2026-07-28.

**Maintainer note** (from #1498, 2026-05-08): "Please please follow CPSV16". For non-periodic FT work, prioritize source-faithful CPSV16 statement/prose and avoid implementation-driven reinterpretations.

---

## 1. May 2026 sorry/axiom snapshot and current periodic-overlap update

Historical snapshot collected 2026-05-08 with
`rg -n "\bsorry\b|axiom" TNLean/MPS/ TNLean/PEPS/`:

| File | Lines | Sorry count | Notes |
|---|---|---|---|
| `TNLean/MPS/Periodic/Overlap/SectorMatch.lean` | 456 | 6 | Periodic overlap Case 3 |
| `TNLean/MPS/Periodic/Overlap/Dichotomy.lean` | 90 | 4 | Overlap dichotomy assembly |
| `TNLean/MPS/Periodic/Overlap/NoSectorMatch.lean` | 394 | 3 | Periodic overlap Case 2 |
| `TNLean/MPS/Periodic/Overlap/SelfOverlap.lean` | 857 | 2 | Self-overlap convergence |
| `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | 937 | 3 | Unique ground state |
| `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | 703 | 1 | Degenerate ground space |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | 1569 | 1 | Martingale proof |
| `TNLean/PEPS/FundamentalTheorem.lean` | 738 | 4 | PEPS FT (out of scope) |
| **Total MPS** | — | **20** | Excluding PEPS |

As of 2026-06-17, the periodic-overlap cluster has been reduced to one live
`sorry`, at `TNLean/MPS/Periodic/Overlap/SectorMatch.lean`, for the
`repeatedBlocks_of_blockedSectorGaugePhase` contraction and phase-assembly
theorem. This is tracked by issue #873 under the proposition-level tracker #81.

---

## 2. Coverage crosswalk: CPSV16 (arXiv:1606.00608)

At this revision, after the normal-tensor RFP characterization, the trace-normalized RFP-to-ZCL-and-SAL result, and the unrestricted Proposition `prop3to4`, the paper has 45 theorem-like occurrences and 40 distinct results. The occurrence-level count is 20 complete, 11 partial, and 14 not-ready; the distinct-result count is 19 complete, 9 partial, and 12 not-ready. Here **not-ready** means that the printed statement is false, ambiguous, or depends essentially on a formally refuted source lemma. It does not mean that every printed result has been formalized.

The distinct count is the 40 source `thm`, `prop`, `cor`, and `lem`
environments. The occurrence count adds five Appendix A/D restatements.
The following ledger makes the count reproducible from source line numbers:

- **Complete (19 distinct):** 249, 253, 398, 606, 945, 1080, 1121, 1130,
  1274, 1333, 1351, 1406, 1510, 1569, 1647, 1680, 1786, 1835, and 2221.
- **Partial (9 distinct):** 278, 342, 583, 801, 851, 972, 1013, 1597,
  and 1801.
- **Not-ready (12 distinct):** 349, 354, 500, 534, 543, 777, 1155, 1197,
  1484, 1503, 1740, and 1810.
- **Additional occurrences:** the Appendix A restatements at 1137, 1167,
  and 1172 inherit partial, not-ready, and not-ready status, respectively; the
  Appendix D restatements at 1863 and 1929 inherit complete and partial status.
  Thus the five restatements add one complete, two partial, and two not-ready
  occurrences, giving the displayed totals 20/11/14.

Definitions, equations, and explanatory proof-segment rows are not counted.
In particular, Eq. `II_XAX` at 1072--1077 is excluded, while the purification
equivalence is counted because it is the `thm` environment beginning at line
777.  The Appendix B rows at 1209--1244, 1246--1271, and 1305--1307 are proof
segments of Theorems 3.1 and 3.10, not additional theorem occurrences.

### 2.1 Section II — Matrix Product Vectors (pure-state canonical form)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| §II Defn (l.132) | 132–139 | MPV definition (`MPV`) | `TNLean/MPS/Defs.lean` | `leanok` |
| Prop (l.249) | 249–251 | After blocking, any tensor has a canonical-form representative with the same positive-length MPVs | `TNLean/MPS/CanonicalForm/CPSVAfterBlocking.lean` (`MPSTensor.exists_cpsvCanonicalForm_representative_after_blocking`) | **complete** |
| Prop (l.253) | 253–255 | Projector criterion for canonical form | `TNLean/MPS/CanonicalForm/ProjectorClosureSpectral.lean` (`MPSTensor.exists_normalTensor_blockDecomp_with_isometry_of_hasInvariantProjectorClosure`) | **complete**; #2634 closed |
| Prop 2.7 (l.278, `prop:char-BNT`) | 278–280 | BNT characterization: every active canonical-form normal tensor is gauge-phase-equivalent to a basis element | `TNLean/MPS/CanonicalForm/BNTCharacterization.lean` (`MPSTensor.isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal`) | **partial** — the active-block characterization is complete, but positive-length MPVs cannot determine listed zero-weight blocks; see `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex` |
| Defn "injective" (l.317, `defnbi`) | 317–322 | A normal tensor is injective when its matrices span the full matrix algebra; biCF is block-injective canonical form | `TNLean/MPS/Defs.lean` (`MPSTensor.IsInjective`) and the biCF development under `TNLean/MPS/MPDO/BiCFDerivation/` | `leanok` |
| Prop (l.342, `propblockinj`) | 342–345 | After blocking at most $3D^5$ spins, any canonical-form tensor becomes biCF | `TNLean/MPS/MPDO/BiCFDerivation/BNTDirectSum.lean` (`IsBNTCanonicalForm.exists_basis_wordTupleSpanTop_le_three_totalDim_pow_five`) with `MPSTensor.hasBiCF_of_wordTupleSpanTop` | **partial** — the bound is proved for the stronger packaged `IsBNTCanonicalForm` surface, but the printed proposition starts from literal canonical form; the zero-weight ambiguity in Proposition 2.7 prevents the missing unconditional conversion |
| **Theorem II.1** (l.349, `thm1`) | 349–352 | Fundamental theorem of MPVs, proportional case | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_proportional_canonicalForm`); `TNLean/MPS/CanonicalForm/BNTUniqueness.lean`; `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **not-ready** — the printed BNT definition permits adjoining an unrelated normal tensor with coefficient zero at every length. The formal one-versus-two-element BNT example for the same tensor refutes the asserted equality of BNT cardinalities. The Lean fundamental theorem proves the corrected active, nonzero, converse-covered BNT statement |
| **Corollary II.2** (l.354, `II_cor2`) | 354–361 | Equal MPVs imply conjugacy by an invertible matrix | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex` | **not-ready** — literal canonical form permits inactive zero-weight blocks, which positive-length MPVs cannot detect; tensors with equal MPVs may therefore have different ambient dimensions, contradicting the printed dimension and global-conjugacy conclusion |

### 2.2 Section III — Pure States: Renormalization of MPS (RFP / ZCL / NNCPH)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem 3.1** (l.398, `thm:renormalization-flow`) | 398–405 | A tensor appears as a renormalization-flow limit iff two blocked physical sites are related to one site by an isometry | `TNLean/MPS/RFP/FlowLimit.lean` (`MPSTensor.AppearsAsRenormalizationFlowLimit`, `MPSTensor.appearsAsRenormalizationFlowLimit_iff_hasPhysicalBlockingIsometry`); `TNLean/MPS/RFP/Defs.lean` (`HasPhysicalBlockingIsometry`); `docs/paper-gaps/cpsv16_renormalization_flow_index_typo.tex` | **complete, with documented local correction** — the flow-limit predicate quantifies the initial physical dimension and tensor, fixes the bond dimension, and uses convergence of the dyadic transfer matrices in their standard finite-dimensional matrix topology. The printed blocking equation has malformed summation and output indices; the preceding renormalization equation, diagrams, and Appendix proof determine the corrected identity without changing the hypotheses or conclusion |
| Defn RFP (l.420, `defRFP`) | 420–424 | Pure-state RFP condition | `TNLean/MPS/RFP/Defs.lean` (`HasPhysicalBlockingIsometry`) | `leanok` |
| Defn CID (l.438) | 438–446 | Correlations independent of distance | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsPhysicalCID`) | `leanok` |
| Defn LO (l.468, `DefLO`) | 468–474 | Local orthogonality | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsBNTLocallyOrthogonal`) | `leanok` |
| Defn ZCL (l.476) | 476–478 | ZCL = LO and CID | `TNLean/MPS/RFP/ZeroCorrelationLength.lean` (`MPSTensor.IsPhysicalBNTZCL`) | `leanok` |
| Defn transfer matrix (l.482) | 482–488 | Transfer map | `TNLean/MPS/Core/Transfer.lean` (`transferMap`) | `leanok` |
| **Theorem 3.8** (l.500, `TheoremZCLPure`) | 500–503 | ZCL iff the transfer map is idempotent | `TNLean/MPS/RFP/BNTWeightCounterexample.lean`; `TNLean/MPS/RFP/BellPairCIDObstruction.lean`; `docs/paper-gaps/cpsv16_pure_zcl_raw_weight_counterexample.tex`; `docs/paper-gaps/cpsv16_pure_zcl_adjacent_gap_cid_scope.tex` | **not-ready** — raw weights refute ZCL⇒idempotence, and the Bell-pair chain at zero complementary gap refutes the unrestricted reverse implication; corrected restricted work is owner-held under #2633 |
| Defn parent Hamiltonian (l.522) | 522–525 | Parent-Hamiltonian BNT ground-space spanning for arbitrary \(L\), with commuting and nearest-neighbor refinements | `TNLean/MPS/ParentHamiltonian/Commuting.lean` (`MPSTensor.HasParentHamiltonianGroundSpaceSpanning`, `MPSTensor.IsCommutingParentHam`, `MPSTensor.IsNNCPH`; `MPSTensor.HasNNCPHGroundSpaces` packages the \(L=2\) all-chain condition) | `leanok` |
| **Theorem 3.10** (l.534, `thm:main-MPS`) | 534–541 | RFP iff ZCL iff NNCPH | `TNLean/MPS/RFP/ZCLReverse.lean`; `TNLean/MPS/RFP/PhysicalObservableRealization.lean`; corrected one-block results including `rfp_iff_zcl` | **not-ready** — the printed equivalence inherits the Theorem 3.8 counterexamples, and the reverse proof at line 1250 fails for nilpotent zero-Jordan defects; #2633 is assigned to `LionSR` |
| **Theorem 3.11** (l.543, `thm:charact-MPS`) | 543–555 | Repeated-copy structural characterization of RFP | `TNLean/MPS/RFP/StructuralFull.lean` (`MPSTensor.rfp_nt_structural_full`); `TNLean/MPS/RFP/PhaseMultiplicityCounterexample.lean`; `TNLean/MPS/RFP/ResidualIsometry.lean` | **not-ready** — the displayed physical isometry has no copy index; the literal shared-map reading is contradicted by the phase-flip repeated-copy tensor; #2598 closed as a source obstruction |
| Corollary 3.12 (l.583, `III_cor3`) | 583–590 | Structural form of the BNT elements of an RFP tensor | `TNLean/MPS/RFP/ResidualIsometry.lean` (`IsBNTCanonicalForm.exists_residualIsometryFamily_of_isTransferIdempotent_basisDirectSum`); `TNLean/MPS/RFP/StructuralFull.lean` | **partial** — the residual-isometry family is constructed for a packaged BNT basis direct sum whose whole transfer is idempotent; the bridge from the literal canonical-form whole-tensor RFP hypothesis to that surface is still missing |
| Prop (l.606) | 606–609 | Pure RFP implies saturation of the area law | `TNLean/MPS/MPDO/PureRFPSAL.lean` (`MPSTensor.isSAL_of_isTransferIdempotent`) | **complete** |

### 2.3 Section IV — Mixed States (MPDO)

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn RFP (mixed) (l.658) | 658–663 | Mixed-state RFP via trace-preserving completely positive maps | `TNLean/MPS/MPDO/RFPViaTS.lean` (`MPOTensor.IsRFPViaTS`) | `leanok` |
| Defn Puri-RFP (l.758) | 758–764 | Purification RFP | `TNLean/MPS/MPDO/PRFP.lean` (`MPOTensor.HasGlobalPurificationEquation`, `MPOTensor.HasPurificationRFPWitness`, `MPOTensor.IsPRFP`) | `leanok` for the definition; the ancillary trace-preserving refinement is recorded separately |
| Unlabeled theorem environment (l.777; counted) | 777–784 | Puri-RFP iff ZCL and the stated purification form | `TNLean/MPS/MPDO/LocalPurificationRFP.lean` (`MPOTensor.exists_isPRFP_isMPDO_physTraceTransfer_ne_zero_not_isSourceZCL` and local corrected equivalences); `docs/paper-gaps/cpsv16_purification_rfp_definition.tex` | **not-ready** — positive-length periodic purification equations do not detect nilpotent hidden bond sectors, even with MPDO positivity and nonzero physical-trace transfer; #3947 closed as not planned |
| Proposition 4.5 (l.801, `PropILILp1`) | 801–807 | Mutual information is monotone, bounded, and has the stated thermodynamic limit | `TNLean/MPS/MPDO/MutualInfoMonotone.lean` (`MPOTensor.mutualInfoChain_monotone`); `TNLean/MPS/MPDO/ThermodynamicLimitCounterexample.lean`; `docs/paper-gaps/cpgsv17_mpdo_mutual_information_bound.tex` | **partial** — monotonicity is complete; a positive parity-sensitive family refutes the unrestricted thermodynamic limit; the finite-chain bound $I_L\le 4\log D$ remains owner-held under #4169/#4242/#4295 |
| Defn SAL (l.811, `def:area-law`) | 811–813 | Saturation of the area law | `TNLean/MPS/MPDO/AreaLaw.lean` (`MPOTensor.IsSAL`) | `leanok` |
| Defn GSNNCH (l.829) | 829–837 | Gibbs state of a nearest-neighbor commuting Hamiltonian | `TNLean/MPS/MPDO/CommutingForm.lean` (`MPOTensor.GSNNCHData`, `MPOTensor.IsGSNNCH`) | `leanok` |
| **Theorem 4.9** (l.851, `thm:main-simple`) | 851–893 | Simple-MPDO implication chain \((i)\Rightarrow(ii)\Leftrightarrow(iii)\Rightarrow(iv)\Rightarrow(v)\) | `TNLean/MPS/MPDO/RFPViaTSSAL.lean`; `TNLean/MPS/MPDO/ActiveSectorSpanningAreaLaw.lean`; `TNLean/MPS/MPDO/PhysicalSectorFactorization.lean`; `TNLean/Channel/PetzProductReference.lean` | **partial** — implication \((i)\Rightarrow(ii)\) is complete at the explicit density-family boundary: positive semidefinite rings, nonzero trace at every positive length, and the Definition 4.1 local RFP equations imply source ZCL and SAL. The horizontal theorem is a stronger specialization deriving nonvanishing. The overall theorem remains partial: \((iv)\Rightarrow(v)\) is proved, but \((ii)\Leftrightarrow(iii)\) is incomplete at commuting-form-to-SAL and the original-to-selected-tensor comparison, and the printed route to \((iv)\) depends on false Lemma C.5. The core lane #4175/#4459 and alternatives #4228/#4405 are owner-held; #4961/#4962 are not independent implementation-ready leaves |
| **Proposition 4.13** (source label `Prop:IV.12`, l.945) | 945–952; proof 1863–1922 | A literal CPSV canonical-form MPDO tensor is vertically in canonical form | `TNLean/MPS/MPDO/CPSVVerticalCanonicalForm.lean` (`MPOTensor.verticalCF_of_cpsvCanonicalForm`) and its prerequisite modules | **complete** — the theorem constructs positive grouped weights and a rectangular coisometry $U$ with $UU^\dagger=I$, $U\widetilde M U^\dagger=\bigoplus_\alpha\mu_\alpha\otimes M_\alpha$, and $\widetilde M=U^\dagger(\bigoplus_\alpha\mu_\alpha\otimes M_\alpha)U$; it does not assert $U^\dagger U=I$ |
| **Theorem 4.14** (source label `thm:IV.13`, l.972) | 972–993; proof 1929–2088 | RFP iff the tensor-attached BNT algebra condition iff the fusion-isometry condition | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean`; `BNTAlgebraTensorClauseSpectrum.lean`; `BNTFusionTensorClauseFromRFP.lean`; `AlgebraFusionCounterexample.lean` | **partial** — several directions and the tensor-attached data are complete; algebra⇒RFP still requires #4648, then #4645, then the CPTP construction and #3949. All three issues are assigned to `LionSR`; Proposition 4.13 does not supply the missing marked/common-target comparison |
| Theorem (l.1013) | 1013–1016 | Length-independent coefficients imply a topological-projector commuting Gibbs form | `TNLean/MPS/MPDO/TopologicalPhysicalGibbs.lean` (`MPOTensor.physicalTopologicalGibbsDecomposition_of_isRFPViaTS`) | **partial** — the physical decomposition is proved for chains of length at least two under the stronger BNT-refined `IsHorizontalCF` hypothesis; the printed theorem assumes only an RFP MPDO and does not state that restriction |

### 2.4 Appendix A — Proofs of Section II

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn CFII (l.1058) | 1058–1071 | CFII: canonical form with trace-preserving blocks and diagonal positive fixed points | `TNLean/MPS/CanonicalForm/Definitions.lean` (`CPSVCanonicalFormIIData`) | `leanok` |
| Eq. `II_XAX` | 1072–1077 | Every canonical-form tensor has a nonsingular same-ambient gauge representative in CFII | `TNLean/MPS/CanonicalForm/CPSVCanonicalFormII.lean` (`CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormII`) | **supporting equation; excluded from count** — the Lean result is **complete** |
| **Lemma `equalMPS`** (l.1080) | 1080–1091 | Two normal MPVs have overlap limit zero or one; limit one gives gauge-phase equivalence | `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` (`MPSTensor.IsNormalTensor.overlap_dichotomy`) | **complete** |
| **Corollary `eqV`** (l.1121) | 1121–1128 | Normal MPVs are asymptotically orthogonal or differ by a length-dependent phase | `TNLean/MPS/Overlap/NormalTensorDichotomy.lean` (`MPSTensor.IsNormalTensor.mpv_phase_alternative`) | **complete** |
| **Corollary `Lem1`** (l.1130) | 1130–1133 | Orthogonal normal MPVs are eventually linearly independent | `TNLean/MPS/CanonicalForm/PhaseClassSectorData.lean`; `TNLean/MPS/BNT/Basic.lean` | **complete** |
| Restatement of `prop:char-BNT` | 1137–1142 | BNT characterization | `TNLean/MPS/CanonicalForm/BNTCharacterization.lean` | **partial restatement** — inherits the zero-weight ambiguity at lines 278–280 |
| **Lemma `Lem:app_simple`** (l.1155) | 1155–1163 | Equality of finite power sums implies equality of multisets | `TNLean/Algebra/ScalarPowerSumIdentity.lean`; `docs/paper-gaps/power_sum_alternative_route.tex` | **not-ready** — the positive-power sums of \([1]\) and \([1,0]\) agree although the multisets differ; the formal alternatives either assume nonzero entries or conclude equality only after filtering out zeros |
| Restatement of `thm1` | 1167–1170 | Proportional fundamental theorem | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_proportional_canonicalForm`); `TNLean/MPS/CanonicalForm/BNTUniqueness.lean`; `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` | **not-ready restatement** — inherits the formal unequal-cardinality counterexample to the unrestricted printed BNT comparison |
| Restatement of `II_cor2` | 1172–1179 | Equal-MPV fundamental theorem | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm`); `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex` | **not-ready restatement** — mirrors the inactive zero-weight block obstruction to Corollary II.2 |
| **Corollary `thm:Fundamental-CFII`** (l.1197) | 1197–1199 | CFII refinement with unitary global and block gauges | `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean` (`MPSTensor.fundamentalTheorem_equal_canonicalForm_unitary`) and `SectorBNT/Unitary.lean`; `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`; `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` | **not-ready** — literal CFII still permits zero weights and therefore inherits Corollary II.2's false dimension and global-unitary conclusion; the Lean unitary theorem covers the active, nonzero BNT surface |

### 2.5 Appendix B — Proofs of Section III

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Renormalization flow convergence | 1209–1244 | Renormalization flow from canonical form converges | `TNLean/MPS/RFP/Convergence.lean` (`rg_flow_converges_of_cf`); `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex` | **not-ready proof segment; refuted as printed and distinct from the completed Theorem 3.1 equivalence** — the current theorem proves convergence for each primitive block. For the literal canonical-form tensor with one physical component \(A^1=\operatorname{diag}(1,\omega)\), where \(\omega\) is a primitive cube root of unity, the dyadic transfer powers alternate on \(e_{21}\). Thus the full weighted repeated-copy assertion is false without an additional relative-phase condition |
| **Lemma `lem:charact-NT-pure-RFP`** | 1274–1301 | Normal-tensor RFP structural theorem | `TNLean/MPS/RFP/NormalIsometryCharacterization.lean` (`MPSTensor.IsNormalTensor.isTransferIdempotent_iff_isIsometryCanonicalForm`); `TNLean/MPS/RFP/StructuralFull.lean`; `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` | **complete, with documented local correction** — under exactly normality, which itself forces positive bond dimension, transfer idempotence is equivalent to the trace-normalized square-root isometry form. The factor $\sqrt{\Lambda}$ is required by the source reference tensor at line 1300 |
| Theorem 3.10 reverse-proof step | 1246–1271 | The printed ZCL-to-RFP argument uses a nonzero subleading eigenvalue | `TNLean/MPS/RFP/ZCLReverse.lean`; `TNLean/MPS/RFP/PhysicalObservableRealization.lean` | **proof segment; counted with Theorem 3.10** — the printed argument is not ready: a non-idempotent map may have only a nilpotent Jordan defect at eigenvalue zero; corrected conditional work is tracked by owner-held #2633 |
| Theorem 3.10 RFP⇒NNCPH | 1305–1307 | RFP gives a nearest-neighbor commuting parent Hamiltonian | Corrected representative-level theorems in `TNLean/MPS/ParentHamiltonian/Commuting.lean` and the conditional capstone merged by #4860 | **proof segment; counted with Theorem 3.10** — the printed unrestricted argument is not ready: raw repeated-copy insertions remain outside the proved representative theorem; #2633 is owner-held |

### 2.6 Appendix C — Proofs of Section IV

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Prop `propsimple` | 1333–1336 | RFP implies source ZCL and SAL | `TNLean/MPS/MPDO/RFPViaTSSAL.lean` (`MPOTensor.isSourceZCL_and_isSAL_of_isRFPViaTS_of_trace_ne_zero`, `MPOTensor.isSAL_of_isRFPViaTS_of_trace_ne_zero`, and horizontal specializations); `docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex` | **complete** — positive semidefinite rings with nonzero trace at every positive length, together with the Definition 4.1 local RFP equations, imply source ZCL and SAL. This nonvanishing is the normalization boundary implicit in the source's density-operator language; positivity alone admits the zero family. The horizontal form is a stronger specialization that derives nonvanishing |
| Lemma `Lsigma3` | 1351–1359 | SAL gives the three-site Markov decomposition | `TNLean/Analysis/EntropyMarkovForward.lean` (`Matrix.hayashi_ssa_equality_characterization_forward`); `TNLean/MPS/MPDO/SimpleLocalStructure.lean`; `docs/paper-gaps/cpsv16_ssa_equality_hayashi_markov.tex` | **complete** — the ambient HJPW blocks are normalized with $p_j=\operatorname{Re}\operatorname{tr}\omega_j$, nonnegative weights summing to one, and recovered trace-one right states on every supported sector. At supported zero weight only the left factor may be a normalized filler; on complementary sectors both factors may be fillers. The Hayashi fibre order and unitary orientation are fixed explicitly, and the characterization is axiom-free |
| Lemma `propSN` | 1406–1411 | SAL gives a positive physical-sector factorization with primitive active trace matrix | `TNLean/MPS/MPDO/InverseMapActiveSectorPrimitivity.lean` (`exists_positive_physicalSectorFactorization_activeSectorTraceMatrix_isPrimitive_of_isSAL`) | **complete** |
| Lemma `SALZCL` / Lemma C.5 | 1484–1502 | SAL and ZCL force the active trace matrix to have rank one | `TNLean/MPS/MPDO/ActiveSectorSpanningAreaLaw.lean` (`ActiveSectorSpanningCounterexample.tensor_refutes_printed_sal_zcl_rank_one_inference`); `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **not-ready** — an injective four-sector counterexample satisfies SAL and source ZCL but has no rank-one active trace factorization; #4270 closed by the formal counterexample |
| Corollary | 1503–1506 | SAL and ZCL imply the displayed structural form | Conditional neighboring-factorization constructions in `TNLean/MPS/MPDO/BlockedRFPConstruction.lean` and related modules | **not-ready** — the only printed derivation uses false Lemma C.5 |
| Prop `3to5` | 1510–1517 | The structural data give trace-preserving coarse-graining and refinement maps | `TNLean/MPS/MPDO/PhysicalSectorCoarseGrainingIdentity.lean`; `PhysicalSectorRefinementIdentity.lean`; `PhysicalSectorBlockedRFP.lean`; `PhysicalSectorPhysicalTransport.lean` (`NeighboringTraceFactorization.blockTwo_isRFPViaTS`); `BlockedRFPConstruction.lean`; `docs/paper-gaps/cpgsv17_mpdo_blocked_rfp_physical_transport.tex`; `docs/paper-gaps/cpgsv17_mpdo_zero_weight_preparation_completion.tex`; `docs/paper-gaps/cpgsv17_mpdo_theorem_4_9_implication_label.tex` | **complete** — the physical-transport theorem carries the sector-coordinate channels back to the original blocked tensor. Two local fixes are disclosed: zero-weight preparation is completed on the quotient, and the source Appendix label \((iii)\Rightarrow(v)\) is corrected to the implication actually proved, \((iv)\Rightarrow(v)\) |
| Prop `3to4` | 1569–1577 | SAL gives the commuting product form | `TNLean/MPS/MPDO/CommutingFormBridge.lean`; `GSNNCHSectorSum.lean`; related physical-sector modules | **complete** |
| Prop `4to2` | 1597–1601 | Commuting form and ZCL imply SAL | `TNLean/MPS/MPDO/PhysicalSectorFactorization.lean` (`PhysicalSectorFactorization.isSAL_of_isSourceZCL`); `CyclicActiveAreaLaw.lean`; `FixedBondPositivePhysicalSectorRepresentative.lean`; `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` | **partial** — the selected fixed tensor has the required factorization and satisfies all-cut SAL, but comparison with the original injective normal tensor remains #4175/#4459, both assigned to `LionSR` |
| Lemma `lemmus` | 1647–1650 | ZCL makes repeated-copy weights independent of the copy index | `TNLean/MPS/MPDO/SimpleTensor.lean` (`MPOTensor.weight_copy_independent_of_isSourceZCL`) | **complete** |
| Lemma | 1680–1691 | SAL gives separating orthogonal projectors | `TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`; `BNTSourceSectorProjectors.lean` | **complete** |
| Prop `prop2to3` | 1740–1743 | SAL and ZCL imply the blockwise structural form | `TNLean/MPS/MPDO/BNTSeparatingProjectors.lean`; `BNTSourceSectorProjectors.lean`; `docs/paper-gaps/cpgsv17_pf_rank_one.tex` | **not-ready** — the printed proof requires the false rank-one conclusion of Lemma C.5 |
| Prop `prop3to4` | 1786–1796 | Blockwise structure gives the GSNNCH form | `TNLean/MPS/MPDO/BNTSectorCoefficientPositivity.lean`; `GSNNCHSectorRescaling.lean`; `BNTPhysicalSectorGSNNCH.lean` (`hasGSNNCHForm_of_bntLayerOrthogonal_of_physicalSectorFactorization`) | **complete** — global MPDO positivity and orthogonal sitewise compression make each fixed-length BNT power-sum coefficient nonnegative real. Its positive root, divided by the natural copy number, is absorbed into the supported commuting bond. The proof uses the raw BNT representatives and requires no copy independence |
| Prop `prop4to2` | 1801–1804 | GSNNCH gives SAL | `TNLean/MPS/MPDO/OrthogonalSectorAreaLaw.lean`; `LocalOrthogonalSumAreaLaw.lean`; `PhysicalSectorFactorization.lean`; `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex` | **partial** — the statement omits the ZCL hypothesis used in its proof; the corrected sectorwise-ZCL result still depends on #4175/#4459 |
| Prop `prop2to5` | 1810–1813 | SAL and ZCL give the two trace-preserving maps | `TNLean/MPS/MPDO/PhysicalSectorCoarseGrainingIdentity.lean`; `PhysicalSectorRefinementIdentity.lean`; `PhysicalSectorBlockedRFP.lean` | **not-ready** — the conditional maps are constructed, but deriving their neighboring trace factorization from the printed hypotheses uses false Lemma C.5 |

### 2.7 Appendix D — Proofs of Proposition 4.13 and Theorem 4.14

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Lemma `Lemma-L`** | 1835–1846 | Equality of first-site actions on all MPVs implies equality of inserted tensors | `TNLean/MPS/MPDO/CPSVOriginalSpaceLemmaL.lean` (`MPSTensor.IsCPSVCanonicalForm.insertedTensor_eq_of_firstSiteActionAgree`) | **complete** for literal CPSV canonical form, including inactive zero-weight coordinates |
| Restatement/proof of Proposition 4.13 | 1863–1922 | Vertical canonical form and rectangular coisometry | `TNLean/MPS/MPDO/CPSVVerticalCanonicalForm.lean` (`MPOTensor.verticalCF_of_cpsvCanonicalForm`) | **complete restatement** — $UU^\dagger=I$ and both exact direct-sum identities are proved |
| Restatement/proof of Theorem 4.14 | 1929–2088 | Algebra and fusion characterizations of RFP | `TNLean/MPS/MPDO/BNTAlgebraTensorClause.lean`; `BNTAlgebraTensorClauseSpectrum.lean`; `BNTFusionTensorClauseFromRFP.lean`; `AlgebraFusionCounterexample.lean` | **partial restatement** — the remaining algebra⇒RFP chain is #4648 → #4645 → #3949, all assigned to `LionSR` |

### 2.8 Appendix E — Additional results

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Defn decorrelated | 2187–2192 | Decorrelated regions | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` | `leanok` |
| Defn parent commuting Hamiltonian | 2206–2216 | Parent commuting Hamiltonian subspace | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` | `leanok` |
| Prop | 2221–2223 | Decorrelation iff parent commuting Hamiltonian | `TNLean/MPS/ParentHamiltonian/TripartiteDecorrelation.lean` (`TripartiteDecorrelation.parentHamiltonian_iff_decorrelated`) | **complete** |

---

## 3. Coverage crosswalk: PGVWC07 (quant-ph/0608197)

### 3.1 Section 3 — The canonical form

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| **Theorem `thm:OBC-Vidal`** (l.431) | 431–443 | Completeness and canonical form for OBC (Vidal form) | `TNLean/MPS/Chain/Defs.lean` (OBC chain definition); left-canonical/right-canonical conditions in `Core/` | `leanok` (definitions); **needs verification** (full completeness theorem) |
| **Theorem `free-OBC`** (l.466) | 466–486 | Freedom in OBC: all representations related by local Y_j, Z_j | `TNLean/MPS/Chain/GaugePhase.lean` (gauge transformations) | `leanok` |
| Theorem "Site-independent matrices" (l.620) | 620–630 | TI state has site-independent MPS representation (bond dim ≤ ND) | `TNLean/MPS/Chain/Defs.lean` (TI chain definitions) | **needs verification** |
| **Theorem `Th:TIcanonical`** (l.742) | 742–763 | TI canonical form: block-diagonal with λ_j > 0, each block satisfies left/right canonical + unique fixed point | Constituent reductions in `TNLean/MPS/CanonicalForm/Reduction.lean` and `CanonicalForm/Existence.lean`; scope boundary recorded in `docs/paper-gaps/pgvwc07_ti_canonical_form_scope.tex` | **not formalized** — the formal declarations prove invariant-subspace splitting, TP gauge, and conditional prepared-block reductions, not the full arbitrary-input source theorem with positive weights, unital blocks, diagonal full-rank dual fixed points, identity fixed-point uniqueness, and the bond-dimension bound; tracked by #1857 |
| **Theorem `Th:periodic`** (l.849) | 849–858 | Periodic decomposition: p eigenvalues of modulus 1 ⇒ superposition of p p-periodic states | `TNLean/MPS/Periodic/Symmetry.lean`, `Periodic/ProjectiveRep.lean` | **partial** — periodic symmetry theory formalized; full theorem statement needs verification |
| Prop `prop-inj` (l.911) | 911–? | C1 condition ⇒ Γ_L injective for L ≥ L₀ | `TNLean/MPS/Core/CPPrimitive.lean` (`IsInjective`), Wielandt span-growth infrastructure | **needs verification** |
| Theorem "Interpretation of Λ" (l.987) | 987–993 | Λ eigenvalues converge to half-chain density matrix eigenvalues | **out of scope** | — |
| **Theorem `thm-uniq`** (l.1002) | 1002–1015 | Uniqueness of TI canonical form (under C1, unique OBC CF, N > 2L₀+D⁴) | `TNLean/MPS/FundamentalTheorem/Basic.lean` (`fundamentalTheorem_singleBlock`, `sameMPV_iff_gaugeEquiv_of_injective` for single-block case); `Chain/FundamentalTheorem.lean` (`fundamentalTheorem_injective_chain`) | **partial** — single-block case fully proved; multi-block TI case with general hypotheses not yet formalized; tracked by #1529 |
| Lemma `lem-same-matr` (l.1022) | 1022–1040 | Same-matrix lemma for T(Y_k)=S(Y_{k+1}) | **out of scope** (purely linear-algebraic) | — |
| Lemma `lem-horn` (l.1053) | 1053–1058 | Horn's lemma: solution space of W(C⊗1)=(B⊗1)W is S⊗M_n | **out of scope** | — |
| Theorem "Obtaining TI canonical form" (l.1154) | 1154–1165 | Solving quadratic equations (S) yields TI D-MPS from unique OBC CF | **out of scope** | — |

### 3.2 Section 4 — Parent Hamiltonians

| Paper label | Lines | Paper description | Lean location | Status |
|---|---|---|---|---|
| Theorem "Uniqueness with OBC" (l.1206) | 1206–1209 | MPS is unique ground state of parent Hamiltonian under C1 (OBC) | `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | **partial** — 3 sorrys remain |
| **Theorem `uniqueGS`** (l.1272) | 1272–1274 | Uniqueness with TI and PBC under C1 | `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean` | **partial** |
| Lemma `lem1` (l.1333) | 1333–? | C1 condition witness lemma | `TNLean/MPS/ParentHamiltonian/` | **needs verification** |
| Lemma `lem:direct-sum` (l.1346) | 1346–? | Direct sum lemma for block decomposition | `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean` (Theorem 3, lines 769–803); `TNLean/MPS/ParentHamiltonian/` | **needs verification** |
| Theorem `2blocks.1` (l.1407) | 1407–1415 | Degeneracy of ground space v1 | `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | **partial** — 1 sorry |
| Theorem `2blocks.2` (l.1424) | 1424–1428 | Degeneracy of ground space v2 (construction) | `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean` | **partial** |

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

## 4. Sorry / gap crosswalk with tracked issues

### 4.1 Periodic overlap dichotomy cluster (issue #81)

| File | Sorrys | Dependency |
|---|---|---|
| `Periodic/Overlap/SectorMatch.lean` | 1 | Full-cycle contraction and phase assembly for repeated blocks (#873) |

This remaining `sorry` cascades into `Periodic/FundamentalTheorem.lean`
(Theorem 3.4 of arXiv:1708.00029), whose conditional proof takes the dichotomy
as a hypothesis.

### 4.2 Parent Hamiltonian cluster (current trackers #190, #2633, #952)

| File | Sorrys | Dependency |
|---|---|---|
| `ParentHamiltonian/UniqueGroundState.lean` | 3 | Uniqueness proof incomplete |
| `ParentHamiltonian/DegenerateGS.lean` | 1 | Degenerate ground space construction |
| `ParentHamiltonian/Martingale.lean` | 1 | Martingale convergence argument |

CPSV16 Theorem 3.10 is not an axiom-removal problem on the printed statement.
The unrestricted RFP–ZCL equivalence inherits the formal counterexamples to
Theorem 3.8, and the reverse proof at source line 1250 also fails for a
nilpotent Jordan defect at eigenvalue zero. Corrected representative-level and
conditional results are proved, but the remaining source-facing work is owned
under #2633.

### 4.3 PEPS (out of scope)

| File | Sorrys |
|---|---|
| `PEPS/FundamentalTheorem.lean` | 4 |

---

## 5. CPSV21 Theorem 4.4 and Corollary 4.5

CPSV21 Definition 4.2 retains the weak BNT clauses of CPSV16: an unrelated
normal representative may be added to the chosen BNT with coefficient zero at
every length. The underlying canonical tensor may nevertheless have only its
original summand, with actual coefficient one. Thus the formal one-versus-two
BNT example literally refutes the equality of chosen-BNT cardinalities in
CPSV21 Theorem 4.4. The sector-BNT proportional theorem is an explicitly
restricted correction of CPSV16 Theorem II.1 and CPSV21 Theorem 4.4, not
complete coverage of either unrestricted statement.

CPSV21 Corollary 4.5 has a different surface. It concerns the ambient canonical
tensors themselves, and the standing construction at lines 1801--1808 gives
their actual direct-sum summands positive coefficients. The extraneous BNT
representative used in the unequal-cardinality counterexample is not an ambient
canonical summand. Consequently that counterexample does not refute Corollary
4.5 and does not impose a zero-weight correction on it. The current equal
theorem is only a packaged SectorBNT analogue of Corollary 4.5 until a bridge
from CPSV21 canonical form to the SectorBNT hypotheses is supplied.

| Lean declaration | CPSV21 relation | CPSV16 relation |
|---|---|---|
| `MPSTensor.fundamentalTheorem_proportional_canonicalForm` | Restricted correction of Theorem 4.4 | Restricted correction of Theorem II.1 (`thm1`) |
| `MPSTensor.fundamentalTheorem_equal_canonicalForm` | Packaged SectorBNT analogue of Corollary 4.5; the unequal-cardinality counterexample does not refute the source corollary, and the canonical-form-to-SectorBNT bridge remains to be supplied | Restricted correction of Corollary II.2 (`II_cor2`) |
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

The 21 non-complete distinct CPSV16 results comprise 9 partial and 12
not-ready results. They are source-ambiguous, formally refuted, research-level,
owner-held, or scope-restricted by the current formal interface. Lemma
`Lsigma3`, the Hayashi strong-subadditivity equality characterization, and the
Appendix B single-normal-tensor RFP/isometry characterization are complete and
axiom-free.

| Status | Paper | Result | Current certificate | Ownership |
|---|---|---|---|---|
| Partial | CPSV16 | Prop. 2.7, BNT characterization | Active blocks are characterized; listed zero-weight blocks are invisible to positive-length MPVs | Source clarification required |
| Partial | CPSV16 | Proposition `propblockinj` | The $3D^5$ bound is proved for packaged BNT data, not for every literal canonical-form tensor | Blocked by the same zero-weight ambiguity as Proposition 2.7 |
| Not-ready | CPSV16 | Theorem II.1 | The printed BNT definition admits an unrelated normal representative with identically zero coefficient; the formal one-versus-two-element example refutes the claimed equality of BNT cardinalities | `TNLean/MPS/CanonicalForm/BNTUniqueness.lean`; `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` |
| Not-ready | CPSV16 | Corollary II.2 | Inactive zero-weight blocks can change the ambient dimension without changing any positive-length MPV | `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex` |
| Not-ready | CPSV16 | Appendix A Lemma `Lem:app_simple` | \([1]\) and \([1,0]\) have identical positive-power sums but different multisets; the formal corrections require nonzero entries or filter zeros | `TNLean/Algebra/ScalarPowerSumIdentity.lean`; `docs/paper-gaps/power_sum_alternative_route.tex` |
| Not-ready | CPSV16 | Appendix A CFII refinement | Literal CFII permits zero weights and inherits the false dimension/global-unitary conclusion; the Lean theorem covers active, nonzero BNT data | `docs/paper-gaps/cpsv16_bnt_characterization_active_blocks.tex`; `docs/paper-gaps/cpsv16_global_vs_persector_unit_witness.tex` |
| Not-ready | CPSV16 | Adjacent canonical-form convergence assertion after Theorem 3.1 | `rg_flow_converges_of_cf` proves convergence for each primitive block, but the literal repeated-copy tensor \(A^1=\operatorname{diag}(1,\omega)\) has a phase-oscillating dyadic transfer orbit | `docs/paper-gaps/cpsv16_canonical_form_renormalization_flow_phase_gap.tex`; this refuted proof-segment claim is uncounted and is not part of the completed flow-limit equivalence |
| Not-ready | CPSV16 | Theorem 3.8 | Raw weights and the Bell-pair adjacent-gap example refute the two unrestricted directions | Corrected branch #2633, assigned to `LionSR` |
| Not-ready | CPSV16 | Theorem 3.10 | Inherits Theorem 3.8 counterexamples; line 1250 also fails for nilpotent zero-Jordan defects | #2633, assigned to `LionSR` |
| Not-ready | CPSV16 | Theorem 3.11 | The repeated-copy physical isometry lacks a copy index; the literal shared-map reading is false | #2598 closed as source obstruction |
| Partial | CPSV16 | Corollary 3.12 | A residual-isometry family is constructed for packaged BNT basis-direct-sum transfer idempotence | The bridge from literal canonical-form whole-tensor RFP to the packaged BNT surface remains open; `docs/paper-gaps/cpsv16_rfp_isometry_scope.tex` |
| Not-ready | CPSV16 | Purification RFP equivalence | Nilpotent hidden bond sectors refute the global-to-local implication | #3947 closed as not planned |
| Partial | CPSV16 | Proposition 4.5 | Monotonicity is proved; the thermodynamic limit is refuted; the finite $4\log D$ bound remains open | #4169/#4242/#4295, assigned to `LionSR` |
| Partial | CPSV16 | Theorem 4.9 | Implication \((i)\Rightarrow(ii)\) is complete for positive semidefinite rings with nonzero trace at every positive length, the normalization boundary implicit in the source density-operator language; Lemma C.5 is false, and commuting-form-to-SAL and the recovery alternative remain incomplete | #4175/#4459 and #4228/#4405, assigned to `LionSR`; #4961/#4962 are dependent research follow-ups |
| Partial | CPSV16 | Theorem 4.14 | Algebra⇒RFP still needs the tensor-attached Gram comparison, unitary normalization, and CPTP maps | #4648 → #4645 → #3949, assigned to `LionSR` |
| Partial | CPSV16 | Topological-projector commuting Gibbs theorem, lines 1013–1016 | The physical decomposition is proved only above one site and under the stronger `IsHorizontalCF` hypothesis | Literal-RFP scope extension remains open |
| Not-ready | CPSV16 | Lemma C.5 (`SALZCL`) | A formal injective four-sector counterexample has SAL and source ZCL but no rank-one active trace factorization | #4270 closed by counterexample |
| Not-ready | CPSV16 | Structural corollary, lines 1503–1506 | Its printed proof depends on false Lemma C.5 | No source-faithful replacement known |
| Partial | CPSV16 | Proposition `4to2`, lines 1597–1601 | The selected tensor satisfies all-cut SAL; comparison with the original tensor is missing | #4175/#4459, assigned to `LionSR` |
| Not-ready | CPSV16 | Proposition `prop2to3` | Its printed SAL+ZCL proof depends on false Lemma C.5 | No source-faithful replacement known |
| Partial | CPSV16 | Proposition `prop4to2` | The statement omits the ZCL hypothesis used in the proof and shares the original-to-selected-tensor gap | #4175/#4459, assigned to `LionSR` |
| Not-ready | CPSV16 | Proposition `prop2to5` | Conditional maps exist, but the printed derivation of their factorization uses false Lemma C.5 | No unconditional source theorem available |
| Partial | PGVWC07 | Theorem `Th:TIcanonical` | Full arbitrary-input canonical-form theorem not yet formalized | #1857 |
| Partial | PGVWC07 | Theorem `thm-uniq` | Multi-block TI case with general hypotheses not formalized | #1529 |
| Partial | PGVWC07 | Theorem `uniqueGS` | Proof incomplete | #1475/#460 |
| Partial | PGVWC07 | Theorem `Th:periodic` | Full periodic decomposition remains incomplete | #81 |
| Out of scope | PGVWC07 | Interpretation of $\Lambda$ | Convergence to half-chain density-matrix eigenvalues | — |

---

## 8. Audit methodology

- Source paper lines counted in `Papers/1606.00608/MPDO-22-12-17-2.tex` and `Papers/quant-ph_0608197/MPSarchive.tex`.
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
| **Theorem** (l.828) | 828–831 | If L > i(A), MPS is unique ground state of parent Hamiltonian with spectral gap | PGVWC07 `uniqueGS` / `ParentHamiltonian/UniqueGroundState.lean` (partial, 3 sorrys) | **partial** — see §4.2 |
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
