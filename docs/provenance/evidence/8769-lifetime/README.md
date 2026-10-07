# Finite distributed-compression proof evidence

The checked source revision is `2a5a7a5b17fb0cd71d9555a88b7249e04f550b87` in `LionSR/TNLean`. It contains
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
| `build` | `d66c5310fbec371f6a04914d4978948a6fa43213133cc5022e22c60da8fb0d4a` | `build.log` |
| `axioms` | `5246fbad97b23232f80641298c4002d63ddb37ead369e4e7533e68d82cea17fa` | `axioms.log` |
| `layout-regression` | `9880a6c7fc16a8d70de0be447241a171fb0abbed294bc611eed43f4ef7db3d39` | `layout-regression.log` |
| `choice-cost-regression` | `abac68e941a96a8f107ddfe8f1135562c9325cddd27a7e6cacfe123e5e01c064` | `choice-cost-regression.log` |
| `source-audit` | `c20f809dd3e85a0155e1b1a6bd8440a733f16eda3a99def62e40c046913d418f` | `source-audit.log` |
| `imports` | `70bed3720ad928ddb561be99104396f3c131c9b6c8c8de6902fdbae0192aec9f` | `imports.log` |

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
SHA-256 `16e07db55f52a4c71a96fc5afd59ad779a150782c23c5262c744b974bfe32cdc`.
