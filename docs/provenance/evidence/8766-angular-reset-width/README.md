# Local evidence for uniform reset width

This packet records the four scalar reset-width results at author checkpoint
`a2f108f651808dd591361572f4f4cef85cc87871`. It was assembled from existing
local validation runs; no Lean build was run while preparing the packet.

## Successful checks

[verification.json](verification.json) binds the checked source, consumer,
guard and raw-driver bytes to the retained [run record](runs/angular-reset-strict-final.json).
All four recorded processes exited successfully with both implicit-variable
options disabled, Mathlib standard linters enabled and warnings as errors:

- [Production elaboration](source-strict.log): 3.63 seconds
- [Four consumer examples](consumers-strict.log): 3.03 seconds
- [Four guarded axiom reports](guards-strict.log): 2.49 seconds
- [Four raw axiom reports](public-axioms.raw.log): 2.59 seconds

Every public theorem has exactly `[propext, Classical.choice, Quot.sound]`.
The [raw driver](AngularResetWidthAxioms.lean) is retained byte-for-byte with
its recorded SHA256. It differs from the guarded CI file: its four informational
hash-command diagnostics remain in the raw log, whereas the guarded CI file
uses the audit-only linter setting and checks the expected axiom reports.

The [focused native-build log](native-build.log) reports success for 2,047 jobs
and 3.1 seconds for the changed module. Its top-level invocation, process exit
code and source digest were not captured by that log; these are not reconstructed.
This is supporting target-build evidence, not a full-root build.

## Superseded checks

The [history directory](history) retains the first namespace lookup failure,
the same native-build failure, the subsequent native build with unused-ring
warnings, and all outputs referenced by the [superseded strict record](runs/angular-reset-strict-7756.json).
The strict source failure has recorded exit code 1. Historical log-only runs
lack complete command and process metadata; their missing values are explicit.
These failures and pre-rename successes are not presented as final results.

## Rendering and scope

Focused PDF and static HTML rendering pass for the final source leaf. All five
PDF pages were visually inspected; four declaration links, three equation
anchors, seven source labels and 45 internal links were checked. No layout
errors remain. The [render summary](render/render-verification-summary.json)
records exact source hashes and limits: live browser/MathJax execution and
remote documentation deployment were not tested. Full-book CI remains pending.

The source is the scalar argument after `eq:info-reset-scale-cost`, lines
745–778 in the September 24, 2026 paper at pinned `openai/math` revision
`adc7f1241b42e322a6451854ab7e4b4c146bf78a`. All Lean proofs are original;
no upstream OpenAI Lean proof text was reused. The physical reset proposition
and angular information invariant are outside this result.

## Normalization

The verification index records an original-to-normalized SHA256 mapping for
every retained input. Private executor prefixes and the temporary raw-driver
pathname are replaced by role tokens. Log line-end whitespace is trimmed;
no diagnostic lines are removed. Embedded hashes in retained run JSON still
refer to the original bytes. The raw Lean driver receives no normalization.
Token paths describe the original roles and are not runnable paths; the raw
run has a separate replay command using its committed relative pathname.

No full-root or import-aggregator build, complete dependency/cache closure,
remote CI, publication, or issue-completion claim is made by this packet.
