# Physical viable-tree and native-root reconciliation

The source base is TNLean `5fc343a57d70eefd2902780107851ab9b0753a82`,
with its exact QICLean dependency `ba01733099b5a18bed5c9bfb62f95f175b4c9b57`.
The independent physical cutoff contribution is preserved in commit
`3f8f4edf682f85161f02fccc6f9410bef5679aa8`. The new generic word, sampling
and coordinate leaves are the separately checked QICLean contribution
`65f4513e896253dccba07cbb720f9a95122a993b`.

## Mathematical scope

The nearest-neighbour Hamiltonian constructs each improving family before
the child spaces and sampling size. One common physical reference space is
chosen before every interval and candidate space. The interval trim retains
the whole exterior, hence the reference bond enters squared.

The actual recursion merges its two adjacent child spaces, selects an actual
successful Haar unitary, applies all recorded operator words and performs
one collective trim. It retains the same original full ground space at every
interval. The automatic choice uses `m = max(q, 50)` and derives the scalar
tail and filter bounds. The leaves are full block spaces and the quantitative
gap is capped at one. This witness is distinct from an adaptive probability
theorem or the printed interleaved-trim algorithm.

If the recorded generator count is at most M and their ranks are at most
`10^6 Dref² (L+1) M`, the native root span has bond at most
`10^6 Dref² (L+1) M²`. The extra factor M is retained. No independent MPS
approximation is substituted for this root.

The source energy-estimation invariant, final filter-and-trim iteration,
Ritz extraction, adaptive joint success probability and computational cost
remain unproved by this contribution. The low-density extension is separate.

## Source preservation

All twenty-two new module bodies are byte-identical to the preserved
`c2e28b9f85000343593d38a795eb2e02f8f4b584` source. Existing merged physical
viability, entropy, scalar filter and supported polynomial-family sources
are unchanged. The adjacent-interval union proof is moved unchanged from
the Hastings namespace to a small generic leaf. Its former declaration is
removed, with no alias; Hastings now imports that leaf.

## Verification

Every actual module was checked separately against immutable warmed
5fc343a57d/ba017 artifacts, using explicit privately checked new dependencies.
Selected source, object, build-input and prebuilt Mathlib hashes were guarded
before and after each check. The source-only worktree has no Lake directory.
No common provider or cache was modified, and Mathlib was not rebuilt.

| Module | Strict private seconds |
| --- | ---: |
| IntervalUnion | 3.147 |
| AdjacentIntervalMerge | 5.766 |
| IntervalCollectiveTrimming | 6.053 |
| IntervalGenerators | 5.52 |
| IntervalSampledImage | 7.224 |
| IndependentPhysicalDGViability | 22.512 |
| IndependentTruncationParameters | 4.354 |
| SharpApproximationParameters | 4.303 |
| PhysicalDGApproximation | 13.285 |
| SharpRankCount | 7.185 |
| PhysicalDGSharpApproximation | 9.699 |
| PhysicalDGGlobalApproximation | 10.291 |
| MPSReferenceSpace | 5.336 |
| PhysicalDGReferenceSpace | 9.126 |
| PhysicalDGIntervalTrimming | 9.024 |
| PhysicalDGSampledNode | 12.259 |
| BalancedIntervalTree | 4.277 |
| IntervalSamplingTree | 8.484 |
| PhysicalDGIntervalTree | 12.586 |
| PhysicalDGTreeParameters | 11.689 |
| FullIntervalMPS | 5.411 |
| PhysicalDGTreeMPS | 11.799 |
| Current Hastings.Window | 5.28 |

An imported inspection covers all 51 public declarations, including definitions
and inline attributes. Fifty use only `propext`, `Classical.choice` and
`Quot.sound`; the long-interval index definition uses no axioms. The successful
inspection took 8.314 seconds over 738 selected source-object pairs. The first
temporary inspection reported only its own missing module header and prohibited
print-command linter diagnostics; its mathematical output was unchanged. Its
header was corrected and the print-command linter was disabled locally for
that inspection. The temporary source was deleted after the successful audit.

Generated imports and reader-facing prose checks pass. Source blueprint
synchronization passes with read-only QICLean and Mathlib source directories;
the initial source-only attempt lacked those directories and is not counted
as a successful dependency check. A repeated original spectral-coordinate
argument is recorded in the tactic ledger for a separate coupled-theorem
specialization. Ordinary combined dependency, full-library, regression,
compiled blueprint, note rendering and quiet timing gates remain required.
