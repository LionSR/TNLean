# Exact small-size approximation: checked local downstream integration

## Scope

The authored module `TNLean/PEPS/Approximation/ExactSmallSizeApproximation.lean`
proves the pointwise and uniform finite-size approximation corollaries against
the native model interface owned by TNLean #8788. It does not restate, replace,
or edit that interface and does not prove `PolynomialPEPSApproximation`.

For `q > 0`, `0 < L ≤ L₀`, a real exponent `c ≥ 0`, any previous prefactor `C`,
and a unit vector `Ω`, the conclusion is
`HasPEPSApproximation (max C (q ^ (L₀ * L₀))) c L q Ω`.
The witness has the exact coefficients of `Ω`, unit norm, nonzero contraction,
and normalized error zero at phase zero. No Hamiltonian or gap assumptions
are needed for this finite-size result.

## Source and dependency provenance

- Mathematical source: `openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`,
  `preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/07-assembly.tex`,
  lines 203–214; approximation convention in `00-introduction.tex`, Theorem 1.1.
- Exact-tree base: `ec0672f82f4bc499c1aea862a53319aeb0770fb7`.
- Public model dependency: TNLean #8788 head
  `158bc6bb178ee53a2c981ba751fadf6e7a3ff0a2`, open and draft on 2026-10-07.
- The unchanged `TNLean/PEPS/Approximation/Basic.lean` dependency is materialized
  in local-only commit `797aa3681`, on `local/peps-8788-basic-158bc6bb`.
  Its Git blob was checked as `df2002c0ec0defb72188220cc03c4fa3ad1a7797`, exactly
  matching the verified public file. It is reused TNLean source, not newly
  authored content. See `docs/provenance/evidence/8773-8788-local-dependency.md`.
- The authored integration commits are separate from the dependency commit:
  `52c6a074d` adds the corollary and consumers, `b42a7c725` simplifies the
  normalization proof, and `07d36596d` guards the axiom closure.
  Integrate only the authored commits after the owned model interface lands;
  do not publish or cherry-pick the local dependency commit.

No original OpenAI Lean proof was copied or adapted. Only the mathematical
manuscript was consulted for the new proof.

## Files and validation boundary

New production source:

- `TNLean/PEPS/Approximation/ExactSmallSizeApproximation.lean`

New regression source:

- `TNLeanTest/PEPS/Approximation/ExactSmallSizeApproximation.lean`: Euclidean
  coefficient identification, complex normalization scalar, unit norm and zero
  error; a consumer of `IsGappedGroundState`; and the `q = L = 1`, `c = 0` endpoint.
- `docs/provenance/evidence/8773/ExactSmallSizeApproximationAxioms.lean`: raw
  axiom query. Its output and the regression's permanent `#guard_msgs` check
  both confirm exactly `propext`, `Classical.choice`, and `Quot.sound`.

The matching mathematical entry is prepared in
`blueprint/src/chapter/ch34_peps_exact_small_size_approximation.tex`.
Its theorem and proof carry `leanok` after the local native checks below.
It is not registered in `content.tex`. No aggregate imports are changed while
the owned dependency remains unmerged. These marks certify the local checked
proof against the pinned interface, not availability on main.

## Checked revision and retained evidence

The parent compiler checked revision
`07d36596d2195ebbfb2e8558e1f6e2ee6726b893` in the existing compiler worktree.
The review worktree fast-forwarded to that revision and independently matched
all three authored source hashes against the recorded strict results. It also
rechecked the unchanged Basic dependency hash.

| Source | SHA-256 |
| --- | --- |
| `TNLean/PEPS/Approximation/Basic.lean` (reused dependency) | `16c669175f00af22a6e8e274d8210423356ed6b0e88e99f1b1b38d6775a8854c` |
| `TNLean/PEPS/Approximation/ExactSmallSizeApproximation.lean` | `1bee42ba2d3a98e58cadf1028d362984a1c7195eb163848d900fd721b61329a2` |
| `TNLeanTest/PEPS/Approximation/ExactSmallSizeApproximation.lean` | `d06618821ef1ffc13f2fd9be65d46d111083f7219a6260ae41b1ceb070dedd8a` |
| `docs/provenance/evidence/8773/ExactSmallSizeApproximationAxioms.lean` | `ad045c04a9c1b693131a884cc3fad0fc72eaa0f1acb5fe84950f478ff9e2b8b7` |

The first native package build completed 2819 jobs, including Basic and the
wrapper. It reported an unnecessary `simpa` in the wrapper, repaired in
`b42a7c725`; the subsequent 2818-job package build succeeded without that warning.
The original first-build log also retains a QICLean release-fetch/source-fallback
warning; this audit does not claim the entire first build was warning-free.

After the permanent axiom guard was added in `07d36596d`, all three files passed
strict Lean checks with both implicit-variable options disabled, the standard
Mathlib linters enabled, and `warningAsError=true`. The production file took
3.086 seconds, the three-consumer regression plus guarded axiom check 2.873
seconds, and the raw axiom query 3.364 seconds. Every exit code is zero.

The original validation artifacts are preserved privately. The bounded evidence
packet is retained under `docs/provenance/evidence/8773/small-size/`, with
executor-local log paths normalized as described below:

| Evidence file | SHA-256 |
| --- | --- |
| `small-size-strict.json` | `06811d25ac8ffdb732692f0377cc7c6ec1fd3c7e992789f67d6985e027cd7a0d` |
| `TNLean_PEPS_Approximation_ExactSmallSizeApproximation.lean-small-size-strict.log` | `c8d5238eb7bc25a88ef9b7233b4e1c379ede42ab3669d576f129cd679631c269` |
| `TNLeanTest_PEPS_Approximation_ExactSmallSizeApproximation.lean-small-size-strict.log` | `85ac04e3eec56ac3c884045d43d49a5e5b5e93c6d00faa38a840556948b14c22` |
| `docs_provenance_evidence_8773_ExactSmallSizeApproximationAxioms.lean-small-size-strict.log` | `e9b09ff8cb21fbe3167f926cd6ee1e91423ef195bc793fb01b5b291fd0d378b8` |
| `small-size-integration-first.log` | `c57a87f38097abff8fdb72876024bb1e91a7d0651f96add4a01a6837f6cfb8c2` |
| `small-size-integration-repair.log` | `a042409ef1f23399fe574674b7199ae74cd2005b427a4894e0f0f7e2d900c98d` |

The source/provenance worker performed no builds or cache mutations. These
results are local checks against the unmerged owned interface, not full CI,
merge readiness, publication, or main-branch availability. Aggregate and chapter
registration, declaration checks, and rendered inspection of this new blueprint
entry remain pending dependency integration. Publication was not attempted by
this worker.

## Final checked uniform-quantifier corollary

After the checked revision above, the source adds
`TNLean.PEPS.Approximation.exists_uniform_small_size_approximation`.
For fixed positive `q`, threshold `L₀`, nonnegative real exponent `c`, and
previous prefactor `C`, it chooses one positive `C' ≥ C` before all sizes
`2 ≤ L < L₀` and all unit vectors, then proves the native approximation
predicate throughout that range. The witness is `max C (q ^ (L₀ * L₀))`.
An additional consumer makes explicit that the same constant can be chosen
before each Hamiltonian and ground vector.

Revision `6b194ffc9ce8d8ab5b39b9be31cc0c489d01e41d` passed the parent's native
2818-job package build without an elaboration repair. The production module,
regression file containing four consumers and two guarded axiom queries, and
raw file containing both axiom queries then passed the same strict options as
above, with exit zero and times 2.819, 2.894, and 2.584 seconds respectively.
Both declarations have exactly `propext`, `Classical.choice`, and `Quot.sound`
as axiom dependencies. Both blueprint theorem/proof pairs now carry `leanok`.

| Final source | SHA-256 |
| --- | --- |
| `TNLean/PEPS/Approximation/ExactSmallSizeApproximation.lean` | `1cdb20f6b529272fe47b24558f43eb9b371c5f1be3db92da3b516b0e87fbfd35` |
| `TNLeanTest/PEPS/Approximation/ExactSmallSizeApproximation.lean` | `1efec20337e5cfb97c6442f8cb384b41508245689ca3f1141b9433c92ebc3645` |
| `docs/provenance/evidence/8773/ExactSmallSizeApproximationAxioms.lean` | `6509f62caae253a4fc41d4eddf569f3cbc7de84a4aeff7a3204fc33157afebd5` |

All three final hashes were matched directly against the current source and
the original final strict-check manifest. The final bounded evidence packet
is retained under `docs/provenance/evidence/8773/small-size-uniform/`, with
executor-local log paths normalized as described below:

| Final evidence file | SHA-256 |
| --- | --- |
| `small-size-strict.json` | `cc51266a907eaf448eb7f3587a44a18390a1c73b1d48f6c6a98aa3aeb288ccd4` |
| `TNLean_PEPS_Approximation_ExactSmallSizeApproximation.lean-small-size-strict.log` | `4aff4eca38407ecaccb00c60db5a95df094a836d1bb83678b55e2e00dabc3e15` |
| `TNLeanTest_PEPS_Approximation_ExactSmallSizeApproximation.lean-small-size-strict.log` | `4ceba010d26cd417bc4185cbb52aba75ec765c612bd4f089bc4cc4c795e1410f` |
| `docs_provenance_evidence_8773_ExactSmallSizeApproximationAxioms.lean-small-size-strict.log` | `08f1d47ff1aa51880e1e9c04612f5e1374aa4fd0bdf301606bbc380ed3e57e1d` |
| `small-size-uniform-native.log` | `79bf974dd9ba208b82e974a33aa005db683b20066ba05cda0374417406a678a7` |

The earlier `small-size/` evidence still certifies `07d36596d` and remains
separate from the final uniform evidence. The new proof closes the finite-range quantifiers locally against
the same pinned, unmerged Basic interface. It does not establish the large-size
theorem, full CI, publication, or availability on main. The blueprint remains
unregistered pending dependency integration. The source/provenance worker did
not run a build, change a Lean cache, or attempt publication.

Final source prechecks passed: the reader-facing prose gate against the local
dependency commit `797aa3681`, `git diff --check`, and a check of the three Lean
files for forbidden proof constructs outside comments. The repository's broad
diff-token utility also scans documentation and therefore reports the ordinary
word `axiom` in the audit and raw-query comments; this is not a new declaration.
The new blueprint chapter was formatted with the already cached, checksum-pinned
latexindent 3.24.7 and checked for idempotence. Only whitespace changed, with
mathematical content compared before and after. Rendering and chapter registration
remain deferred as stated above.

## Evidence path normalization

The two strict-check manifests replace only each `log` field's executor-local
absolute path with the sibling log filename. Commands, source hashes, exit
codes, timings, and recorded output are unchanged. The text logs contain no
executor-private paths and retain their original bytes. The evidence tables
above give the current, normalized-file hashes; they do not claim that the
normalized JSON files are byte-identical to the original manifests.

`docs/provenance/evidence/8773/small-size-normalization.json` records the original
and normalized SHA-256 values for every retained evidence file and this audit,
together with the transformation applied. Exact originals and any historical
compilation failures remain preserved locally outside this publication packet.
The retained packet contains only these bounded build, strict-check, and
axiom-report results. No source or proof result was changed by normalization.

Earlier local commits retain the original metadata in their history. Any
future publication must use a sanitized snapshot or squashed authored diff,
not publish that local branch history. This preparation does not authorize or
attempt publication, and the owned model dependency remains separate.
