# Contribution Policy

TNLean is a Lean 4 formalization of quantum information theory, quantum channel
theory, and tensor network theory. It is public so that the formalization and
its blueprint can be read, checked, and cited.

Issues are the front door. Bug reports, mathematical corrections, and questions
about a statement or its source are welcome from anyone.

## What a contributor needs to know

Contributing code here requires working knowledge of quantum mechanics and
tensor networks — density matrices, completely positive maps and their Kraus
and Choi representations, matrix product states, injectivity and normality,
transfer matrices and their spectra — together with enough Lean 4 and Mathlib
to write a proof that a reviewer can follow.

This is not gatekeeping for its own sake. The results here are formalizations
of specific published theorems, and the review question is never "does it
compile" but "is this the theorem the paper states." Answering that requires
reading the source, which requires the physics.

If you do not have this background, issues and corrections are still welcome.
Code contributions are not.

## Pull requests are by assignment

**Unsolicited pull requests are closed without review**, whether written by a
person, by an agent, or by both, and regardless of the quality of the patch.

To contribute code:

1. Open an issue describing what you propose to change, or comment on the
   existing issue you want to take.
2. Wait for a maintainer to assign it to you. An open issue is not an
   invitation; only an assignment is.
3. Open a pull request that references the assigned issue.

A pull request that arrives without a prior assignment is closed, and the
account may be blocked from the repository.

## Automated and agent-generated contributions

TNLean is developed with coding agents, so this is not an objection to the
tools. It is an objection to arriving unannounced. An agent pointed at a public
issue tracker can open a patch in minutes; checking that patch against a source
paper takes far longer, and the imbalance is the whole problem.

Agent-assisted contributions are accepted under an assigned issue, subject to:

- **Disclose.** Name the tool and model, and say which parts of the change they
  produced.
- **A human is accountable.** An agent may be credited with `Assisted-by:`; it
  may not be the author of record. The person opening the pull request answers
  for the change.
- **Understand what you submit.** You must be able to explain every line, and
  to justify the mathematics, without consulting the agent.

Unsolicited agent-generated pull requests are closed on sight and the account
blocked. Maintainers are exempt from the assignment requirement; the disclosure
and accountability requirements bind everyone.

## Why assignment, and not open season

This is a formalization, not an application. A patch that compiles can still be
mathematically wrong: it can prove a theorem the cited paper does not state, add
a hypothesis the source does not have, or restate a result more weakly than the
source proves it. `docs/CONTRIBUTING.md` and the faithfulness rule in
`CLAUDE.md` describe what a reviewer has to check against the source. Verifying
a plausible-looking proof costs more than producing one, which is why the work
is scoped in an issue before it is written rather than after.

A correction that identifies a wrong statement is more useful than a patch, and
carries none of that cost.

## tenkz is closed

The `tenkz` sources — `tex/tenkz/`, `tests/tenkz/`, `docs/tenkz/`, and the
`tenkz` entries under `scripts/` — are an internal project under active
redesign. They accept no outside contributions under any circumstance, assigned
or not.
