# Capped dyadic partition verification

Scope: the finite maximal-contained dyadic-square partition step in
`scanner:templates`, source lines 641–649 of `08-scanner.tex`, pinned to
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

These are original proofs from the manuscript. The existing TNLean dyadic
grid, parent, ancestry and refinement APIs from #8837 are reused unchanged.
The branch is stacked on #8837 at `4e12e35eb90436f776d998345950e70bfdce68b2`.
Claims on #8754, #8758 and #8837 were inspected; scope was announced in
#8754 comment 6044978027 and #8837 comment 6044979072. The separately owned
#8798/#8826/#8832/#8840 proofs are unchanged.

## Current evidence

The production module compiled successfully at
`b6f1f462625c3d83074b1c3c1299d6cc30c3b4b2` in both normal CI and the reviewer's
compatible warmed worktree. CI run
[37682366487, job 113017568227](https://github.com/LionSR/TNLean/actions/runs/37682366487/job/113017568227)
completed the 1,150-job production target and the 12,511-job full library build.
The subsequent strict regression step failed; the strict imported dependency
command did not run in that job. Therefore overall verification remains
pending, as do the new provenance records. The separate blueprint entries
have no `leanok`.

The canonical reviewer check and its actual command, revision, timing and
exit-code logs are in
[#8863 comment 6046537485](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6046537485).
Its successful production log is preserved verbatim in
`8754-capped-dyadic-build-b6f1f462.log`. The reviewer separately ran the strict
regression and dependency commands: both exited 1. The twenty-three actual
dependency reports contained only the three standard logical dependencies,
and passed the unchanged exact-name policy, but the audit command's lint
errors prevent treating it as a successful strict audit.

The selected Linux workspace began without Lean or `.lake`. The pinned Lean
4.35.0-rc3 release was installed from GitHub; all dependency source checkouts
match `lake-manifest.json`. `lake exe cache get` built only the cache client,
then the default `cache.mathlib.org` server returned HTTP 403 for the prebuilt
artifacts. A read of the supported Azure cache endpoint also returned HTTP
403, including with sandbox escalation. No Mathlib proof source build was
started. No local Lean proof success is claimed.

Source-only checks passed: complete pinned-source provenance validation
(205 entries), blueprint/source synchronization and reverse coverage for all
23 public declarations, generated-import completeness, numbered-module and
file-length policies, new-prose checks, pinned LaTeX formatting, and
`git diff --check`. The provenance-checker suite passed 52 tests; the
compatible-cache policy suite passed 51 tests. The tactic-pattern scan found
no new repeated block in this module among its reported candidates. These
checks do not replace Lean compilation or the imported dependency audit.

The CI workflow first builds the new production module with package options,
then retains the full library build and runs strict regressions and all 23
exported declaration dependency prints. Regressions cover empty sets, zero cap,
negative coordinates, mixed scales, disconnected sets, holes, and containment
of parents above the cap. Exact guarded dependency output will be added only after
observing a successful audit.

The mixed-square count for actual templates, safe-square clearance, entropy
subadditivity and dyadic entropy summation remain separate. This contribution
does not complete Lemma 9.4, #8754 or either headline manuscript theorem.

## Reviewed source corrections

The reviewer in #8863 comment 6045767900 checked two corrections in a temporary
copy of source `2b639859360e28322f83702d82a33b1b064a2ab9`, after comparing the
toolchain, dependency pins and recursive import sources. The reported check
used TNLean's package options and produced no warnings. The reviewer did not
modify the production branch or its provenance.

The owner reviewed and applied the explicit search bound `(n := K)` and
`Nat.lt_succ_self k` in the maximal-scale argument, and removed `not_imp` from
the mixedness simplification. These preserve the statements and mathematical
proofs. The later canonical build evidence above supersedes the temporary-copy
check; regression and strict audit verification remain pending.

The imported dependency script prints all 23 exact export names. CI now saves
the actual output and applies the existing `check_axiom_output` validator to
every name in this contribution's ledger. The validator rejects missing or
malformed records, inconsistent repeated output, and any dependency beyond
`propext`, `Classical.choice` and `Quot.sound`. This makes successful execution
alone insufficient for an audit pass. Verification statuses remain pending
until a successful strict audit and repaired regression run are observed.

## Regression and audit repairs

The failed CI log identifies a missing module docstring, expensive implicit
index inference in the mixed-scale disjointness example, and elaborator
recursion depth in the disconnected cap-three computation. The repair adds
the docstring, supplies the two selected indices explicitly, reuses the
already checked finite partition equality, and evaluates the unchanged
cap-three fixture with `decide +kernel`. This uses trusted kernel reduction
without increasing resource limits. The production theorem file is unchanged.

The diagnostic dependency module now has its required module docstring and
locally disables `linter.hashCommand`, because its purpose is to print those
reports. All twenty-three exact declaration names and the dependency policy
validator are unchanged. Successful compilation of these repaired diagnostic
files is still pending at publication of this repair.

The previous blueprint job was still installing system dependencies when the
regression failure was inspected; it had produced no blueprint source
diagnostic. That infrastructure state is separate from the concrete Lean
regression failure.
