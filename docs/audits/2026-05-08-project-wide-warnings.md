# Project-wide audit warnings (2026-05-08)

**Audit date**: 2026-05-08 (initial scan); doc refreshed on rebase against `origin/main` after a wave of resolution PRs landed.
**Scope**: project-wide, with primary focus on the non-periodic Fundamental Theorem of MPS path (TNLean/MPS/{CanonicalForm, BNT, FundamentalTheorem (single-block), Symmetry, Structure, Irreducible, Overlap, Chain, Wielandt}) and its upstream dependencies.
**Method**: three parallel automated scans (project-wide orphan detection, banned-vocabulary sweep, abandoned-proof / struggle-zone audit), plus targeted import-graph verification.

This file collects warnings surfaced during the audit so they can be triaged in one place. Each warning links to the corresponding GitHub issue where action is tracked. Rows resolved by merged PRs are struck through; the row remains for audit traceability.

---

## 1. Slaughter candidates (orphan exploratory modules)

Five `.lean` files imported only by `TNLean.lean` (root) at audit time, with **no internal consumers** and **no source-paper citation** in their docstrings.

| File | Markers | Tracked in | Resolution |
|---|---|---|---|
| ~~`TNLean/MPS/RFP/Convergence.lean`~~ | original claim "TODO at line 29" was wrong; main's `Convergence.lean` carries an explicit proof outline citing CPGSV21 §2.3 + arXiv:1606.00608 Appendix B, and contains no `TODO` marker | #1511 | **Resolved by PR #1521** (paper citations added; row was inaccurate to begin with — apology to the tracker) |
| `TNLean/PiAlgebra/TIReduction.lean` | exploratory time-invariance reduction | #1511 | partly addressed by PR #1521 (paper-source citations); orphan status unchanged |
| `TNLean/PiAlgebra/GlobalSymmetry.lean` | exploratory global-symmetry variant | #1511 | partly addressed by PR #1521 |
| `TNLean/QPF/Primitive.lean` | orphaned leaf | #1511 | partly addressed by PR #1521 |
| `TNLean/Spectral/CrossCorrelation.lean` | orphaned, no paper citation | #1511 | partly addressed by PR #1521 |

**Action**: NEEDS-USER-DECISION on each remaining file — Archive / delete / cite-and-keep — now that #1521 has supplied the paper-source clarification.

## 2. Large root-only modules with sorrys

Two large modules are imported only by root yet contain unresolved proofs and active churn (8 commits in the last 90 days each). Counts re-verified against post-rebase main.

| File | Lines | Sorrys / Axioms | Tracked in |
|---|---|---|---|
| `TNLean/PEPS/FundamentalTheorem.lean` | 738 | 3 sorrys (lines 553, 602, 735); arXiv:1804.04964 cited; converse branches unproven; marked exploratory in #633 | #1512 |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | 1569 | 1 sorry (line 1526); 0 axioms. The string `axioms or unrelated sorrys` at line 1504 is inside a docstring, not a proof obligation | #1512 |

**Action**: NEEDS-USER-DECISION — demote / archive / wire / keep with `docs/paper-gaps/` entry.

## 3. Paper-cited but unused islands

Modules reachable from root, with paper citations, but no internal consumers outside their own subtree.

| Subsystem | Files | Paper basis | Tracked in | Resolution |
|---|---|---|---|---|
| `TNLean/Wielandt/PaperResults/` | 5 files (~872 lines), renamed via PR #1519 | arXiv:0909.5347 / Wolf §6.9, Theorem 1 — formalized for citation purposes only | #1509 | rename landed; expository-vs-live decision still open |
| `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant{.lean, /ProjectionSpan.lean}` | 915+147 lines | docstring states "not the general CPSV repeated-sector comparison"; only consumer is `MPS/ParentHamiltonian/DegenerateGS.lean` | #1510 | partly addressed by PR #1520 (parent-Hamiltonian role recorded in docstring) |

**Action**: NEEDS-USER-DECISION — keep with annotation, archive, or promote into the FT path.

## 4. CPSV16 sub-discharge hypothesis structures (untracked) — RESOLVED

Three conditional-hypothesis structures on the non-periodic FT path that were not yet covered by tracker #1498's main sub-issues. ~~Each is now annotated with its CPSV16 line range and a back-pointer to #1498.~~

| Structure | File:Line | Source basis |
|---|---|---|
| ~~`CommonPrimitiveSpanHypotheses`~~ | `MPS/CanonicalForm/SectorComparison/CommonPrimitiveProportionalData.lean:36` | CPSV16 §II decomposition (lines 283–302) |
| ~~`CommonPrimitiveProportionalHypotheses`~~ | `MPS/CanonicalForm/SectorComparison/CommonPrimitiveProportionalData.lean:118` | CPSV16 §II proportional FT (Theorem II.1) |
| ~~`SectorBasisOverlapOrthoHypotheses`~~ | `MPS/FundamentalTheorem/SectorDecomposition.lean:428` | CPSV16 §II overlap dichotomy / arXiv:1804.04964 §4 |

**Resolution**: Resolved by PR #1517 — line ranges and #1498 back-references added in docstrings.

## 5. Cross-module duplicates — RETRACTED

The original Section 5 row was based on a misreading. Re-verified after PR #1515 landed:

- `tendsto_norm_selfOverlap_one` is defined exactly once in the project, at `TNLean/MPS/Overlap/SelfOverlapAux.lean:29`.
- `MPS/BNT/PermutationRigidity/Matching.lean:52` is **not** a duplicate of that lemma — it is the end of a different private lemma `tendsto_norm_mpvOverlap_one_of_scaled_self`, which converts a scaled cross-overlap rather than a self-overlap.

Both `Matching.lean` and `Full/DominantWeight.lean` correctly import `MPS.Overlap.SelfOverlapAux` for the public lemma. No deduplication work is needed; **issue #1508 was opened for a phantom duplicate and should be closed as invalid**.

The five additional cross-file private duplicates that the audit flagged in `Channel/` are out of scope per project focus and not separately tracked.

## 6. Banned vocabulary surface — RESOLVED

Per `docs/CONTRIBUTING.md` §6 (mathematical-language renames) and `docs/prose_style.md` §2.

### Section names

| File | Line | Original | Current |
|---|---|---|---|
| ~~`TNLean/Algebra/ProjectionTriangularTrace.lean`~~ | 40 | `section Helpers` | `section Auxiliary` (PR #1516) |

### Docstring / comment prose

| File | Original term | Current |
|---|---|---|
| ~~`TNLean/MPS/CanonicalForm/SectorComparison/CommonBlockedCyclicSectorFamily.lean`~~ | `plumbing` (×2) | removed (PR #1516) |
| ~~`TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean`~~ | `package` (noun, ×2) | removed (PR #1516) |
| ~~`TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorTransport.lean`~~ | `package` (verb) | removed (PR #1516) |
| ~~`TNLean/MPS/Overlap/PeripheralToSpectralGap.lean`~~ | `package` (verb) | removed (PR #1516) |

**Resolution**: All in-scope rows resolved by PR #1516.

Out-of-scope (Channel/, Archive/) banned-vocab matches as of audit time: 3 additional `section Helpers` in `Channel/{Schwarz/MultiplicativeDomain.lean, Schwarz/MultiplicativeDomainFull.lean, FixedPoint/Algebra.lean}`; `pipeline`/`wrapper` in `Archive/PeripheralClosure.lean`, `Archive/BlockingPeriodicity.lean`; `wrapper` in `Entropy/MutualInformation.lean`. These remain pending unless explicitly brought into scope.

## 7. Heartbeat outliers

| File | Line | `maxHeartbeats` | Notes |
|---|---|---|---|
| `Channel/Semigroup/Primitivity/Basic.lean` | 90 | 5,000,000 | Spectral-mapping for `exp` on CLM; legitimate kernel cost |
| `Channel/Semigroup/ReducibleQDS/SubsequenceAnalysis.lean` | 245 | 4,000,000 | Taylor remainder normalization in subsequence limit |
| `Channel/Semigroup/LindbladForm/{TraceBridge.lean, EulerStep.lean}` | various | 2,000,000 | Trace-preserving bridge — standard |
| `Channel/KrausFreedom.lean` | 145 | 1,600,000 | Kraus representation freedom — permutation analysis |

**Action**: all in `Channel/` and currently out of primary FT focus; verdict: monitor, no immediate action.

## 8. Sorry / admit / axiom census (outside FT closure)

Confirmed: **the 74-file non-periodic FT closure carries zero sorrys.** All sorry/admit/axiom occurrences fall into known zones tracked elsewhere.

| File | Sorrys | Notes |
|---|---|---|
| `MPS/Periodic/Overlap/{Dichotomy, Case2, Case3, SelfOverlap}.lean` | 9 | known zone — separate periodic-FT tracker (not this audit) |
| `MPS/ParentHamiltonian/{DegenerateGS, Martingale, UniqueGroundState}.lean` | 6 | covered by PR #1485; Martingale also in #1512 |
| `Channel/Schwarz/POVM*` and `Axioms/OperatorConvexity.lean` | 4 | covered by PR #1484 |
| `Channel/LorentzNormalForm.lean` | 3 | Wolf 6.11 stationary-state route; covered by PR #1471 |
| `Channel/NormalForm.lean` | (out of scope) | — |
| `Channel/Peripheral/ClosureFixedPoint.lean` | (out of scope) | — |
| `PEPS/FundamentalTheorem.lean` | 3 | covered by #1512 |
| `MPS/RFP/Convergence.lean` | 0 | original "TODO" claim was inaccurate; cleared by PR #1521 |
| `MPS/MPDO/AlgebraStructure.lean`, `MPDO/PRFP.lean` | 3 admits total | documented in `docs/paper-gaps/policy.tex` |
| `Axioms/{OperatorConvexity, Entropy, Beigi}.lean` | 8 axioms | documented in `docs/paper-gaps/policy.tex`; deliberate boundaries |

## 9. Re-export shims (acceptable, listed for reference)

Files that contain only imports + namespace, with no original content. These are acceptable organizational shims; flagged here so they are not mistaken for stubs.

- `TNLean/Channel/Semigroup/Primitivity.lean`
- `TNLean/Channel/Semigroup/LindbladForm.lean`
- `TNLean/Channel/Semigroup/ReducibleQDS.lean`
- `TNLean/MPS/CanonicalForm/SectorComparison/StructuralTheorem.lean`
- `TNLean/MPS/Periodic/Overlap.lean`

## 10. Active tracker links

| Issue | Title | Status |
|---|---|---|
| #1498 | Tracking: Non-periodic FT — discharge CPSV16 hypotheses | open |
| #1499 | A. Identity-padded homogeneous pair-span | merged via PR #1505 |
| #1500 | B. Fixed-length trace-dual block-injective span | open |
| #1501 | C. Derive `CommonPrimitiveBNTCoverHypotheses` | open (largest math step) |
| #1502 | D. Global-gauge lift (CPSV16 Cor II.2) | PR #1507 in flight |
| #1503 | E. Wielandt deviation hypothesis audit | merged via PR #1506 |
| #1508 | chore: deduplicate `tendsto_norm_selfOverlap_one` | invalid (no duplicate exists); close |
| #1509 | Audit: Wielandt/PaperResults — paper-cited five-file island | open; rename landed via PR #1519 |
| #1510 | Audit: BlockDiagonalCommutant | open; parent-Hamiltonian role documented via PR #1520 |
| #1511 | Audit: orphan exploratory modules | partly addressed by PR #1521 (paper-source citations); per-file decision pending |
| #1512 | Audit: large root-only modules with sorrys (PEPS.FT, Martingale) | open |
| #1513 | chore: replace banned-vocabulary section names and prose | merged via PR #1516 |
| #1514 | Tracker #1498 follow-up: untracked CPSV16 sub-discharge structures | merged via PR #1517 |

## How to extend this file

When a new audit produces warnings, add rows to the relevant section above. When a warning is resolved (issue closed and the underlying code removed/fixed), strike through the row rather than deleting it, so the audit history remains traceable.
