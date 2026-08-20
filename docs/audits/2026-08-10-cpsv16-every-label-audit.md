# CPSV16 every-label audit

**Date:** 2026-08-10
**Source:** `Papers/1606.00608/MPDO-22-12-17-2.tex`
**Maintained crosswalk:** `docs/audits/2026-05-08-mps-ft-paper-coverage.md`

## Inventory and reproduction

The source contains **187 lexical `\label{...}` occurrences and 183 lexical
label names**.  Removing the commented-out graphical label `biCF` at source
line 336 leaves **186 active occurrences and 182 active names**.  The canonical
disposition ledger is `docs/audits/data/cpsv16-label-dispositions.tsv`.  It
contains one row for every lexical label, with these fields:

- the label name;
- its number of occurrences and exact source lines;
- whether the label is active or inactive in the source;
- one of the six required classifications: `section`, `definition`,
  `equation`, `figure`, `example`, or `theorem-like`;
- an explicit cross-reference disposition.

Run

```text
python3 scripts/audit_cpsv16_labels.py --list-duplicates
```

from the repository root.  The command parses the source independently,
strips unescaped TeX comments to derive the active occurrence inventory,
checks each occurrence against the ledger activity, verifies the exact duplicate
map, compares every label's classification with the maintained snapshot
`docs/audits/data/cpsv16-label-classifications.tsv`, and checks every
theorem- or proof-contained equation and figure occurrence against
`docs/audits/data/cpsv16-contained-result-anchors.tsv`.  It also requires the
ledger to contain exactly the 183 lexical labels with one activity,
classification, and nonempty disposition each.  The only inactive name is
`biCF`.

The classification totals are:

| Classification | Lexical names | Active names |
|---|---:|---:|
| Section | 10 | 10 |
| Definition | 10 | 10 |
| Equation | 81 | 81 |
| Figure | 45 | 44 |
| Example | 3 | 3 |
| Theorem-like | 34 | 34 |
| **Total** | **183** | **182** |

The source has four repeated names, each occurring twice:

| Label | Source lines | Disposition |
|---|---:|---|
| `thm1` | 350, 1168 | Theorem 2.10 and its Appendix A restatement |
| `II_cor2` | 355, 1173 | Corollary 2.11 and its Appendix A restatement |
| `eq:II_auxcor` | 358, 1176 | The global conjugacy equation and its Appendix A restatement both inherit Corollary 2.11's not-ready inactive-block boundary |
| `eq1:proof.IV.12` | 1838, 1882 | Accidental duplicate: the first occurrence inherits Lemma C.16's complete insertion status, while the second inherits Proposition 4.13's complete rectangular-coisometry status |

Definitions, equations, and figures outside theorem statements and proofs may
be classified as notation or standalone internal material when that is their
actual role.  Every equation or figure label inside a theorem statement or
proof instead explicitly inherits the enclosing result's status and semantic
boundary.  The validator requires exactly 58 unique labels and 60 occurrences
of this kind.  Each occurrence is matched by an explicit regular expression
to its exact enclosing-result anchor, including theorem-number boundaries,
statement-versus-proof distinctions, and separate line-specific anchors for
the two duplicated contained labels.  Thus, for example, the six displayed
clauses of Theorem~4.9 inherit
its partial all-sector Case-II status,
and the algebra and fusion clauses of Theorem~4.14 retain their different
coverage boundaries.  This prevents an internal display from being treated as
independently covered when its enclosing literal source result remains partial,
not-ready, or corrected.

## Numbering and appendix structure

The theorem counter includes definitions and examples.  The proportional and
equal fundamental-theorem statements are therefore **Theorem 2.10** and
**Corollary 2.11**, not Theorem II.1 and Corollary II.2.  The source appendices
are:

- Appendix A: proofs of Section 2;
- Appendix B: proofs of Section 3;
- Appendix C: proofs of Section 4, including Proposition 4.13 and Theorem 4.14;
- Appendix D: additional results.

In particular, the proofs of Proposition 4.13 and Theorem 4.14 are subsections
of Appendix C, and the decorrelation results are in Appendix D.

## Examples

Three examples carry labels and therefore occur in the TSV ledger.  The fourth
is unlabelled and is recorded here and in the maintained coverage crosswalk.

| Source result | Source line | Role | Disposition |
|---|---:|---|---|
| Example 3.4, `Ex:ZCL` | 453 | CID does not imply a renormalization fixed point | **Complete** in Chapter 15: `def:cpsv16_example_34_tensor`, `thm:cpsv16_example_34_mpv`, `thm:cpsv16_example_34_cid`, and `thm:cpsv16_example_34_not_rfp` |
| Example 4.10, `ExZCLnoSAL` | 898 | ZCL does not imply SAL | Source reconciled in `docs/paper-gaps/cpsv16_examples_4_10_4_11_entropy.tex`; the integer comparison and log-ratio positivity are certified in `CPSVExamples410411Arithmetic`, while spectra and tensor links remain under issue #6301 |
| Example 4.11, `ExSALnoZCL` | 908 | SAL does not imply ZCL | Printed SAL claim refuted for the literal finite periodic family; exact spectra, entropy, and effective/ambient non-SAL are formalized, while `CPSVExample411SourceZCL` proves that both physical-trace transfers are nonzero and fail the literal Definition 4.2 idempotence diagram, as well as its scale-invariant repair; no legacy doubled-index ZCL or thermodynamic claim is made |
| Example 4.12, unlabelled | 932 | The toric-code boundary tensor is claimed to be SAL, ZCL, and RFP, but not of the simple GSNNCH form | The formula, positivity, one-site trace loss, and SAL are complete. The printed tensor satisfies $\mathcal T_M^2=2\mathcal T_M\ne\mathcal T_M$, so literal ZCL and RFP are false for that representative. The normalized RFP problem remains in #6044, and the full GSNNCH exclusion remains in #6045 |

## Appendix D omissions and corrections

The every-label pass found four active Appendix D labels that the earlier
theorem-only crosswalk had treated as generic diagrammatic or internal material.
Their dispositions are:

| Source label | Source line | Disposition |
|---|---:|---|
| `RFP-gauge` | 2101 | The printed pure-state equivalence is false.  The cube-phase tensor blocks to itself up to swap gauge-phase but has non-idempotent transfer.  The exact source-shaped counterexample is tracked by issue #5920 and Blueprint node `thm:cpsv_rfp_gauge_printed_status`. |
| `Strong-RFP` | 2110 | The unnormalized structural predicate is `MPOTensor.IsStrongRFP`, with literal relation $M_2=U(M_1\otimes P)U^\dagger$, $P\geq0$, and physical-closure equivalence recorded in Blueprint nodes `def:mpdo_strong_rfp` and `thm:mpdo_strong_rfp_phys_close`. Its general periodic geometric-rank implication and the Fibonacci obstruction are complete. |
| `rank-Fibonacci` | 2122 | The periodic rank formula, its non-geometricity, and the resulting $\lnot\,\mathrm{IsStrongRFP}$ theorem are complete for every positive choice of fusion weights with the prescribed Fibonacci support; see Blueprint nodes `thm:cpsv_fibonacci_periodic_rank`, `thm:cpsv_fibonacci_operator_rank_not_geometric`, and `thm:cpsv_fibonacci_not_strong_rfp`. |
| `eq:1` | 2158 | This is the internal diagonalization calculation supporting `rank-Fibonacci`, not an independent theorem. |

The mixed-state question following `RFP-gauge` cannot be treated as an extension
of a valid pure-state theorem. For `Strong-RFP`, the unnormalized local
structural predicate, physical-closure equivalence, and periodic geometric-rank
implication are complete. The concrete Fibonacci periodic rank formula and its
non-geometric consequence prove that the canonical Fibonacci diagonal MPO
is not `MPOTensor.IsStrongRFP`.

## Source-statement status nodes

The following Blueprint nodes state the literal printed claims separately from
corrected Lean results.  Nodes that already existed were retained; new nodes
were added only where a corrected `\leanok` theorem had obscured the status of
the printed statement.

| Source result | Literal-source Blueprint node | Corrected or partial formal coverage |
|---|---|---|
| Proposition 2.7 | `thm:cpsv_prop27_printed_status` | `thm:cpsv_bnt_characterization` |
| Theorem 2.10 | `thm:cpsv_theorem210_printed_status` | `thm:cpgsv_multiblock_ft_source` |
| Corollary 2.11 | `cor:cpsv_corollary211_printed_status` | `thm:cpgsv_equal_case_source` |
| Theorem 3.8 | `thm:cpsv_theorem_zcl_pure_status` | positive-gap and multiplicity-one results in Chapter 26 |
| Theorem 3.10 | `thm:cpsv_main_mps_status` | corrected representative-level implications in Chapters 26 and 13 |
| Theorem 3.11 | `thm:cpsv_charact_mps_status` | one-copy and direct-sum structural results in Chapter 26 |
| Corollary 3.12 | `cor:cpsv_iii_cor3_status` | active phase-class residual-isometry results in Chapter 26 |
| Theorem 4.4 | `thm:cpsv_theorem44_printed_status` | local purification equivalences and global counterexamples in Chapter 21 |
| Proposition 4.5 | `thm:cpsv_prop45_printed_status` | monotonicity and finite-chain bounds; parity counterexample to the limit |
| Theorem 4.9 | `thm:cpsv_theorem49_printed_status`; `thm:mpdo_theorem49_iv_to_v_counterexample` | completed implications; literal (iv)$\Rightarrow$(v) refuted by the exact repeated-copy capstone; the two preserved not-ready nodes record the viable source (ii)$\Rightarrow$(iv) and (ii)$\Rightarrow$(v) routes |
| Theorem 4.14 | `thm:cpsv_theorem414_printed_status` | algebra equivalence and corrected active-support fusion equivalence |
| Lemma A.5 | `lem:cpsv_power_sum_printed_status` | `thm:bounded_power_sum_multiset` |
| Corollary A.6 | `cor:cpsv_corollary_a6_printed_status` | active nonzero unitary refinements in Chapter 11 |
| Proposition C.14 | `thm:cpsv_prop_c14_printed_status` | `thm:mpdo_canonical_bnt_proportional_sectors_zcl_sal` |
| Examples 4.10--4.12 | `thm:cpsv_examples410_412_status` | Examples 4.10 and 4.11: issues #6301 and #6302; Example 4.12: literal normalization resolved, normalized RFP #6044 and full GSNNCH exclusion #6045 open |
| Appendix D `RFP-gauge` | `thm:cpsv_rfp_gauge_printed_status` | cube-phase obstruction plus active issue #5920 |
| Appendix D Fibonacci periodic rank formula | `thm:cpsv_fibonacci_periodic_rank`; `thm:cpsv_fibonacci_operator_rank_not_geometric`; `thm:cpsv_fibonacci_not_strong_rfp` | complete periodic rank formula, non-geometricity, and $\lnot\,\mathrm{IsStrongRFP}$ conclusion |

Example 3.4 no longer needs a separate source-status node.  Chapter 15 states
and proves the exact printed tensor, its positive-length MPV, physical
correlation independence, and failure of the renormalization fixed-point
equation.  The corresponding declarations are
`MPSTensor.cpsvExample34Tensor`, `MPSTensor.cpsvExample34_mpv`,
`MPSTensor.cpsvExample34_isPhysicalCID`,
`MPSTensor.cpsvExample34_not_isTransferIdempotent`, and
`MPSTensor.cpsvExample34_not_hasPhysicalBlockingIsometry`.

Proposition 4.13 is already represented by a theorem with the literal CPSV
canonical-form hypotheses and the correct rectangular coisometry orientation;
a second source-status node would duplicate it.  The two existing Case-II
nodes `thm:mpdo_sal_zcl_bnt_sector_structure` and
`thm:mpdo_sal_zcl_blocking_channels` remain `\notready`.

## Semantic boundaries retained

- A zero-weight canonical-form block is invisible to all positive-length MPVs.
  It obstructs the literal statements of Proposition 2.7, Theorem 2.10,
  Corollary 2.11, and Corollary A.6.
- Positive power sums do not detect zero entries.  Lemma A.5 requires a
  nonzero-entry hypothesis, exponent-zero data, or a conclusion modulo zeros.
- Theorem 3.8 and Theorem 3.10 retain the raw-weight and adjacent-region
  counterexamples.  Corrected positive-gap results are not classified as
  literal source coverage.
- Theorem 3.11 lacks the repeated-copy physical routing needed to interpret its
  displayed shared isometry.  Corollary 3.12 is false for an arbitrary BNT but
  complete for active phase-class representatives.
- Theorem 4.4 is not recovered by local purification equivalences because
  positive-length global equations do not detect nilpotent hidden sectors.
- Proposition 4.5 is complete for monotonicity and finite-chain bounds, but its
  unrestricted thermodynamic-limit clause is false.
- Theorem 4.9(iv)$\Rightarrow$(v) is refuted by the scalar BNT presentation
  with raw copy weights $1$ and $1/2$: explicit component witnesses establish
  all standing hypotheses, condition (iv), and MPDO positivity of the blocked
  tensor, but Definition 4.1 for that block would force
  $1+2^{-4}=1+2^{-2}$. This is an unfaithful statement, not an unfinished
  outer-sector assembly. The viable route from condition (ii) still has the
  all-sector normality obstruction after coefficient absorption (#5996) and
  the projector-controlled assembly after ZCL-derived common-weight absorption
  (#6632). The two `\notready` nodes record these source (ii)-routes. The
  printed proof of `prop3to4` has separate proof-path drift because it invokes
  the ZCL lemma `lemmus` although its displayed statement assumes only
  condition-(iv) data; the completed Lean proof avoids that hidden hypothesis.
- Theorem 4.14 is complete for the algebra clause and for the corrected
  active-support fusion clause.  This is not the unrestricted printed fusion
  statement.
- Proposition C.14 uses zero correlation length in its proof through
  Proposition C.9 although the printed statement omits it.
