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

## Successful Lean evidence

[CI run 37712363292, build job 113102108581](https://github.com/LionSR/TNLean/actions/runs/37712363292/job/113102108581)
passed at head `f4593c1e97adacc224a3407c745fb7582d0e6be0`:

- The production target compiled in 1.9 seconds, completing 1,150 jobs.
- The full library build completed 12,511 jobs.
- Strict partition regressions and the imported dependency audit both passed
  with the package options, Mathlib standard linters and warnings as errors.
- All twenty-three actual exported dependency reports passed the unchanged
  exact-name policy. Each contained only `propext`, `Classical.choice` and
  `Quot.sound`.
- Changed-module timing, the text style linter, compiled blueprint declaration
  checks and paper-gap declaration checks passed. The separate
  [timing job 113107041605](https://github.com/LionSR/TNLean/actions/runs/37712363292/job/113107041605)
  also passed.

CI checked out merge `d180dfbe10e08812adfc10562ca00ef192a517e4`. Its complete
Git tree and the head's tree are both
`4047845de5568fc90803c272ae0c9032932b54a2`, verified locally after fetching
that immutable merge. The production theorem file, regressions and audit
script have not changed since this successful run.

The two ledger evidence files preserve complete relevant CI step excerpts:
`8754-capped-dyadic-build-f4593c1e.log` and
`8754-capped-dyadic-strict-f4593c1e.log`. Only GitHub's timestamp prefixes and
ANSI color escapes were removed; command text, output order, multiline
dependency reports and the policy's success message were retained. Exit
codes are established by the successful step conclusions and the step's
`set -eo pipefail`. SHA-256 digests bind the recorded excerpts to all
twenty-three original-proof records. The existing dependency validator was
also rerun locally on the preserved audit excerpt.

These records now have `ported` status, declared names and passed verification
at the immutable head above. Completion tags cover only the separate finite
geometry blueprint entries. They do not mark the manuscript's full entropy
lemma complete.

## Blueprint correction and rendering

[Blueprint job 113102108505](https://github.com/LionSR/TNLean/actions/runs/37712363292/job/113102108505)
installed its dependencies successfully, then failed at ChkTeX warning 44
on the two literal opening brackets of the half-open rectangle. Web rendering
and subsequent checks were skipped. The correction uses the existing
`\lbrack` interval notation found elsewhere in the blueprint. It preserves
both half-open intervals and changes no mathematical or Lean statement.
No check or warning is suppressed. Local ChkTeX 1.7.9 with the global defaults
and repository configuration reproduces warning 44 on the original file and
passes the corrected file. The corrected file also passes pinned latexindent
3.24.7 and blueprint/source synchronization, including reverse declaration
coverage. Complete rendering at the corrected head remains pending until its
new CI run finishes.

## Earlier checks and local limitations

Production compilation already passed at
`b6f1f462625c3d83074b1c3c1299d6cc30c3b4b2` in both normal CI and a compatible
warmed review. The latter's actual successful log is preserved verbatim in
`8754-capped-dyadic-build-b6f1f462.log`, from
[#8863 comment 6046537485](https://github.com/LionSR/TNLean/pull/8863#issuecomment-6046537485).
That revision's strict regressions and audit had concrete diagnostic errors;
they are superseded by the successful run above, not counted as passing runs.
The diagnostic repair added module docstrings, explicitly supplied the two
mixed-scale indices, reused the finite partition equality, used trusted
`decide +kernel` reduction for the unchanged disconnected cap-three fixture,
and locally permitted intentional `#print` commands in the audit.

The selected Linux workspace began without Lean or `.lake`. The pinned Lean
4.35.0-rc3 release was installed from GitHub; all dependency source checkouts
match `lake-manifest.json`. Both supported prebuilt Mathlib endpoints returned
HTTP 403, including an escalated read attempt. No Mathlib proof source build
was started. The successful Lean evidence above comes from CI and the
attributed warmed review, not a local proof build.

Source-only checks separately passed: complete pinned-source provenance
validation, blueprint/source synchronization and reverse coverage for all
23 public declarations, generated-import completeness, numbered-module and
file-length policies, new-prose checks, pinned LaTeX formatting, and
`git diff --check`. The provenance-checker suite passed 52 tests; the
compatible-cache policy suite passed 51 tests. These checks do not replace
Lean compilation or imported dependency verification.

The mixed-square count for actual templates, safe-square clearance, entropy
subadditivity and dyadic entropy summation remain separate. This contribution
does not complete Lemma 9.4, #8754 or either headline manuscript theorem.
