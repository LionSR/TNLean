# MPO cochain consumers: first migration for #8321

This candidate is an incomplete first part of
[#8321](https://github.com/LionSR/TNLean/issues/8321). It must stay draft and
must not be merged into main while its prerequisites remain unmerged.

## Exact prerequisite sources

The isolated integration branch combines these two unmerged draft heads:

- [#10616](https://github.com/LionSR/TNLean/pull/10616),
  `7c911dcb2911762ea83e5e16dac743af26bf3eab`;
- [#10615](https://github.com/LionSR/TNLean/pull/10615),
  `d6b3712c10cd005a44ed37f3c5de2118a73abcc6`.

Their shared base is `eb588dc15332a3798431015e6c27ecbaf329b2d1`.
The original environment checkout was 257 commits older. The GitHub source API
was used to restore the exact shared base, checking every imported Git object
against its SHA. Applying the prerequisite patches reproduced their published
tree hashes `3710b3e1076f93f0819d65273b78742e523ccef2` and
`c4877329323a0179325133aac7ee3f7990dd3dc2`. Their changes merge without conflict.
The integration commit has both prerequisite heads as parents. No main branch
or prerequisite branch was modified.

After integration, #10616 advanced to
`3ba155b6ea409bfde12e4ee915c0ab702642b455`. Its only change is LaTeX
formatting in the fusion-gauge chapter; its Lean source is identical to the
pinned head. This candidate carries that formatting correction while retaining
the immutable integration base. #10615 remains at the selected head above.

At inspection, both exact heads passed their hosted Lean build jobs, including
the full library build, strict checks, compilation-time checks, style lint, and
compiled blueprint declaration checks. Their web/PDF checks were not all
finished. Those separate builds do not validate this combined consumer candidate.

## Retyped consumers

- `FusionData.omega` now returns
  `groupCohomology.cocycles (Rep.ofMulDistribMulAction G ℂˣ) 3`.
  Normality supplies the proved cocycle equation. Its scalar extraction is
  named `FusionData.associatorScalar`, and all existing scalar computations
  were updated to that name. No deprecated scalar-valued `omega` alias remains.
- `FusionData.relativeScalar` now returns a two-cochain with values in the
  additive coefficient representation. Its differential is the ratio of the
  associators, proved by `d₂₃_relativeScalar`.
- `ActionData.lSymbol` now returns a two-cochain with permutation coefficients
  on the single block. The tensor-derived values use the coordinate change
  supplied by #10615. Its differential is the constant-function image of the
  associator, proved by `d₂₃_lSymbol`.
- The normal-representation anomaly class and its choice-independence
  statements project the certified Mathlib cocycle directly.

Fusion and action tensors retain their existing mathematical definitions.
No theorem loses a conclusion or gains a hypothesis, and no proof hole or
additional axiom is introduced.

The scalar extractor is required independently of normality: the explicit
group-cocycle MPO construction has non-normal tensors, as proved by its
`not_isNormalRepresentation` theorem. Requiring normality of all fusion tensors
would discard that existing construction. The certified cocycle is constructed
after the pentagon proof, without strengthening `FusionData`.

## Remaining work

This does not close #8321. The group-cocycle MPO gate inputs and the cyclic
example constructors still use the scalar cochain functions. The common scalar
cohomology predicates have not been deleted; their retirement belongs to the
remaining work in #8319 and #8320.

There is also a universe mismatch for the generic permuted-block consumer.
`BlockActionData.lSymbol` currently allows `X : Type v`, whereas #10615 fixes
`G X M : Type` and its coefficient representation in the lowest universe.
Replacing the generic consumer by that representation would narrow its
statement. This candidate leaves that API unchanged. A universe-compatible
cochain interface is needed before migrating it without loss of generality.

## Verification

Local Lean execution cannot start: `lake` and `lean` are absent, there is no
`.lake` dependency cache, and the environment reports an enforced disabled
network policy. A direct GitHub fetch returns proxy HTTP 403. No Mathlib source
build was attempted. Source restoration used the authorized connected GitHub
tools; it did not change the environment's network policy.

Generated-import completeness, reader-facing prose, blueprint mathematical
roles, module-policy checks, whitespace checks, and proof-integrity scans are
run on the combined source tree. Source-level blueprint checks find the new
declarations. Their full-tree report also contains references into unavailable
Mathlib/QICLean dependency checkouts, so it is not a substitute for compiled
declaration checking.

Hosted consumer compilation and downstream checking remain required. The
candidate must not be described as validated until those checks pass on its
actual combined source tree.

The [hosted build at `5197337`](https://github.com/LionSR/TNLean/actions/runs/43745039062/job/132907421071)
compiled both foundations together, `Associator`, `AssociatorCohomology`, the
dagger-fusion modules, and several Klein and cyclic anomaly examples. It found
an inference error in the single-block L-symbol evaluation: the coefficient
group was inferred as complex numbers instead of complex units. The explicit
complex-unit parameter was pushed in `0e4f591`; its rerun was queued at the last
inspection. This is partial compilation evidence, not a successful complete
consumer check. The subsequent prerequisite-formatting correction changes no
Lean source.

Prepared with OpenAI Codex (GPT-6); maintainer review is required.
