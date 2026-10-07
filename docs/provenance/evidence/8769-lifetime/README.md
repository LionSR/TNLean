# Finite distributed-compression proof evidence

The checked source revision is `d4eb94035d4905c9d243fb1739966a198e266c09` in `LionSR/TNLean`. It contains
47 named public definitions and theorems across `DistributedLifetime`,
`DistributedLinks` and `CorrectedPositionCost`, with unchanged proof bodies from
the original implementation and explicit original-proof provenance notices.
The generated `TNLean.PEPS.Approximation` import exposes these modules.

The build uses the package Lean and Mathlib linter options. All six commands in
[checks.json](checks.json) exited zero and reported no warnings. Every log records
the exact command, committed source revision, UTC start time, elapsed time and
warning count. The complete axiom audit prints all 47 qualified names; its only
axiom dependencies are `propext`, `Classical.choice` and `Quot.sound`.

The source-audit command checks unique blueprint owners, audit/ledger inventory
coverage and immutable paper labels, and archives the actual manuscript excerpts.
It does not mechanically establish semantic source faithfulness. An independent
OpenAI Codex assistant reviewed the finite mathematical statements and blueprint
hypotheses; human maintainer review remains pending.

| Check | SHA-256 | Log |
| --- | --- | --- |
| `build` | `aa1e5c394d5cf8519a93149c06354a6c3a387eefcedd0ff96d86339768a918c5` | `build.log` |
| `axioms` | `8f295ba386ce50f93d0d73ee532cca46a1f60279093ffb882c5fc4607c924180` | `axioms.log` |
| `layout-regression` | `758564e866fb4509ffa9166ec8eb171b942de34319668c81bafb6f52641614c5` | `layout-regression.log` |
| `choice-cost-regression` | `f3c3e8095fd2af35e278bc937a8e87ff9256a4f7d2f3ac9254b7878d67099109` | `choice-cost-regression.log` |
| `source-audit` | `5e1e1fa382e41fedb5c498bb0f81e5763f1b10939bbfda6511e4b29d3a0e0892` | `source-audit.log` |
| `imports` | `5db399745c73a2ae713aa8f8728240c9be15b4ac5582df11f5c54350bfa07a67` | `imports.log` |

The issue-owned ledger is [8769-lifetime.json](../../openai-math.d/8769-lifetime.json).
It records all 47 declarations as original implementations, with no upstream Lean
proof text reused, citing the September 24, 2026 manuscript at
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

[Original check archives](original/archive.json) preserve the earlier raw logs and
19-declaration selected audit with hashes. Their incomplete metadata is explicitly
recorded, so they are not used as completion evidence. The public equivalent
source revision preserves the original source tree while using the account's
public noreply email. Only the current logs above promote ledger rows.

These finite counting, locality and choice-cost results do not complete Theorem
5.2. Actual circuit expansion and coefficient identification, local tensor
evaluation, virtual dimension bounds, approximate expansions, and composition
with the quantum and sampling results remain open in issue #8769.

Assisted-by: OpenAI Codex (GPT-6). Human contributor accountability remains with
the submitting `LionSR` account; no human mathematical review is claimed.

The completed ledger was validated through the unchanged `validate` API from
LionSR/TNLean PR #8789 at `4e9d9c898a4401d51cf1eeeabcea8572242387fe`.
Policy/schema ownership remains with that PR; this branch adds only the issue-owned shard.
The archived validator output is [provenance-validation.log](provenance-validation.log),
SHA-256 `585a15f797f76099e48779cf02fedc77a6d2556be2cd5d332568dc7cd8fb46ed`.
