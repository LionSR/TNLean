# Project-wide audit warnings (2026-05-08)

**Audit date**: 2026-05-08
**Scope**: project-wide, with primary focus on the non-periodic Fundamental Theorem of MPS path (TNLean/MPS/{CanonicalForm, BNT, FundamentalTheorem (single-block), Symmetry, Structure, Irreducible, Overlap, Chain, Wielandt}) and its upstream dependencies.
**Method**: three parallel automated scans (project-wide orphan detection, banned-vocabulary sweep, abandoned-proof / struggle-zone audit), plus targeted import-graph verification.

This file collects warnings surfaced during the audit so they can be triaged in one place. Each warning links to the corresponding GitHub issue where action is tracked. Mark a row "resolved" by striking through it once the linked issue closes.

---

## 1. Slaughter candidates (orphan exploratory modules)

Five `.lean` files imported only by `TNLean.lean` (root) with **no internal consumers** and **no source-paper citation**. Verified via `rg -l "import TNLean.<path>" TNLean/ TNLean.lean`.

| File | Markers | Tracked in |
|---|---|---|
| `TNLean/MPS/RFP/Convergence.lean` | TODO at line 29 ("formalize the convergence in operator norm"), no proof outline | #1511 |
| `TNLean/PiAlgebra/TIReduction.lean` | exploratory time-invariance reduction | #1511 |
| `TNLean/PiAlgebra/GlobalSymmetry.lean` | exploratory global-symmetry variant | #1511 |
| `TNLean/QPF/Primitive.lean` | orphaned leaf | #1511 |
| `TNLean/Spectral/CrossCorrelation.lean` | orphaned, no paper citation | #1511 |

**Action**: NEEDS-USER-DECISION on each — Archive / delete / cite-and-keep.

## 2. Large root-only modules with sorrys

Two large modules are imported only by root yet contain unresolved proofs and active churn (8 commits in the last 90 days each).

| File | Lines | Sorrys / Axioms | Tracked in |
|---|---|---|---|
| `TNLean/PEPS/FundamentalTheorem.lean` | 800 | 3 sorrys (lines 544, 592, 724); arXiv:1804.04964 cited; converse branches unproven; marked exploratory in #633 | #1512 |
| `TNLean/MPS/ParentHamiltonian/Martingale.lean` | 1562 | 2 sorrys (one at 1519), 1 axiom | #1512 |

**Action**: NEEDS-USER-DECISION — demote / archive / wire / keep with `docs/paper-gaps/` entry.

## 3. Paper-cited but unused islands

Modules reachable from root, with paper citations, but no internal consumers outside their own subtree.

| Subsystem | Files | Paper basis | Tracked in |
|---|---|---|---|
| `TNLean/Wielandt/PaperResults/` | 5 files (~872 lines) | arXiv:0909.5347 / Wolf §6.9, Theorem 1 — formalized for citation purposes only | #1509 |
| `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant{.lean, /ProjectionSpan.lean}` | 905+262 lines | docstring states "not the general CPSV repeated-sector comparison"; only consumer is `MPS/ParentHamiltonian/DegenerateGS.lean` | #1510 |

**Action**: NEEDS-USER-DECISION — keep with annotation, archive, or promote into the FT path.

## 4. CPSV16 sub-discharge hypothesis structures (untracked)

Three conditional-hypothesis structures on the non-periodic FT path that are not yet covered by tracker #1498's main sub-issues.

| Structure | File:Line | Source basis |
|---|---|---|
| `CommonPrimitiveSpanHypotheses` | `MPS/CanonicalForm/SectorComparison/CommonPrimitiveProportionalData.lean:36` | CPSV16 §II decomposition (lines 283–302) |
| `CommonPrimitiveProportionalHypotheses` | `MPS/CanonicalForm/SectorComparison/CommonPrimitiveProportionalData.lean:118` | CPSV16 §II proportional FT (Theorem II.1) |
| `SectorBasisOverlapOrthoHypotheses` | `MPS/FundamentalTheorem/SectorDecomposition.lean:428` | CPSV16 §II overlap dichotomy / arXiv:1804.04964 §4 |

**Action**: NEEDS-USER-DECISION — absorb into #1501 / split as own sub-issues / document as deliberate parameterization. Tracked in #1514.

## 5. Cross-module duplicates

| Lemma name | Locations | Layering | Tracked in |
|---|---|---|---|
| `tendsto_norm_selfOverlap_one` | `MPS/FundamentalTheorem/Full/DominantWeight.lean` (public, after PR #1504); `MPS/BNT/PermutationRigidity/Matching.lean:52` (private) | BNT is upstream of FundamentalTheorem.Full → dedup needs an upstream relocation in `MPS/Overlap/` | #1508 |

Five additional cross-file private duplicates surfaced in `Channel/` are out of scope for the current focus and not separately tracked.

## 6. Banned vocabulary surface (non-mathematical noise)

Per `docs/CONTRIBUTING.md` §6 (mathematical-language renames) and `docs/prose_style.md` §2.

### Section names

| File | Line | Current | Suggested |
|---|---|---|---|
| `TNLean/Algebra/ProjectionTriangularTrace.lean` | 40 | `section Helpers` | `section Auxiliary` |

### Docstring / comment prose

| File | Line | Banned term |
|---|---|---|
| `TNLean/MPS/CanonicalForm/SectorComparison/CommonBlockedCyclicSectorFamily.lean` | 18, 408 | `plumbing` (×2) |
| `TNLean/MPS/CanonicalForm/BlockDiagonalCommutant.lean` | 503, 516 | `package` (noun, ×2) |
| `TNLean/MPS/CanonicalForm/SectorComparison/CommonSectorTransport.lean` | 30 | `package` (verb) |
| `TNLean/MPS/Overlap/PeripheralToSpectralGap.lean` | 414 | `package` (verb) |

**Action**: tracked in #1513 (`@claude` mechanical cleanup).

Out-of-scope (Channel/, Archive/) banned-vocab matches: 3 additional `section Helpers` in `Channel/{Schwarz/MultiplicativeDomain.lean, Schwarz/MultiplicativeDomainFull.lean, FixedPoint/Algebra.lean}`; `pipeline`/`wrapper` in `Archive/PeripheralClosure.lean`, `Archive/BlockingPeriodicity.lean`; `wrapper` in `Entropy/MutualInformation.lean`.

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
| `MPS/RFP/Convergence.lean` | 0 (TODO only) | covered by #1511 |
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

| Issue | Title |
|---|---|
| #1498 | Tracking: Non-periodic FT — discharge CPSV16 hypotheses |
| #1499 | A. Identity-padded homogeneous pair-span |
| #1500 | B. Fixed-length trace-dual block-injective span |
| #1501 | C. Derive `CommonPrimitiveBNTCoverHypotheses` |
| #1502 | D. Global-gauge lift (CPSV16 Cor II.2) |
| #1503 | E. Wielandt deviation hypothesis audit |
| #1508 | chore: deduplicate `tendsto_norm_selfOverlap_one` |
| #1509 | Audit: Wielandt/PaperResults — paper-cited five-file island |
| #1510 | Audit: BlockDiagonalCommutant — restricted (non-CPSV) commutant route |
| #1511 | Audit: orphan exploratory modules |
| #1512 | Audit: large root-only modules with sorrys (PEPS.FT, Martingale) |
| #1513 | chore: replace banned-vocabulary section names and prose |
| #1514 | Tracker #1498 follow-up: untracked CPSV16 sub-discharge structures |

## How to extend this file

When a new audit produces warnings, add rows to the relevant section above. When a warning is resolved (issue closed and the underlying code removed/fixed), strike through the row rather than deleting it, so the audit history remains traceable.
