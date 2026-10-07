# Continuing goal for the area-law and PEPS formalization

Establish source-faithful Lean proofs of the two-dimensional area law and
polynomial PEPS approximation tracked in
[TNLean #8733](https://github.com/LionSR/TNLean/issues/8733), including their
necessary geometric and analytic arguments. This is a sustained objective
across successive working periods and continuations, rather than a task ending
with one auxiliary theorem or pull request.

Work in the TNLean repository and follow `AGENTS.md`, its mathematical and
contribution conventions, and the relevant Lean skills. Write mathematical
explanations for readers who have not seen the working conversations.

## Method of continuation

1. Read the [continuation record](area-law-peps-continuation.md), then inspect
   current issue claims, main, pull requests, CI, active worktrees and builds.
   Reuse completed proofs and their exact evidence.
2. Select the next necessary unclaimed obligation and publicly claim its
   mathematical scope, branch and files before implementation. Respect the
   existing assignments and coordinate before changing a shared interface.
   Check other agents' progress approximately every thirty minutes and before
   each new claim.
3. Use a small team with distinct responsibilities and file ownership. Delegate
   useful proof work, independent source review, and documentation or provenance
   preparation. Avoid duplicating another agent's work.
4. Scout TNLean, QICLean and Mathlib first. Preserve the source hypotheses and
   prove the missing argument. Do not substitute an assumed conclusion,
   additional hypothesis, or misleading definition. Apply the repository's
   explicit paper-realignment rules where necessary.
5. Follow the canonical hot-main and prebuilt-cache protocols. Never rebuild
   Mathlib from source or modify an active peer worktree. Serialize local
   builds and cache mutations through the repository wrapper; prefer targeted
   checks, reuse warmed artifacts, and wait without consuming CPU.
6. Complete each contribution with its proof, appropriate verification,
   compiled-declaration and standard-axiom audits, mathematical blueprint, and
   exact source, license and provenance records. Preserve existing evidence
   for unchanged proof sources. Publish focused pull requests and precise
   issue handoffs, following the repository's merge protocol.
7. After a completed contribution, proceed to the next necessary obligation.
   While CI or another agent's result is pending, work on an independent
   prerequisite. Update the continuation record with exact revisions, ownership,
   completed mathematics, outstanding obligations and the next concrete action.

Continue autonomously for many hours or days across successive continuations.
Routine reversible implementation choices do not require another confirmation.
The objective remains unfinished until the faithful main theorems are proved.
An explicit request to stop, an execution limit, or exhaustion of every useful
independent next step may interrupt work; report the remaining mathematics
accurately in that case.
