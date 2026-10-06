# Fibonacci symmetric families: unrestricted multiplicities and remaining associators

Baseline: `227c905a7456efc4c0cf151bb178081d3a7a272d` of `LionSR/TNLean`,
refreshed 2026-10-06 UTC after the initial audit at `79655a18c`.
Source: `Papers/2203.12563/REsubmission.tex`, GLM23 v3, lines 458–460,
564–605 and 1991–1993.

## Existing classification

The baseline already contains the unrestricted natural-matrix theorem in
`TNLean/MPS/Examples/Fibonacci/FibonacciNIMRepDecomposition.lean`:

- `exists_fibNim_pair` constructs isolated reciprocal partners.
- `fibNimPartner_involutive` and `fibNim_symmetric_of_sq` derive involutivity
  and symmetry from the equation, without assuming them.
- `exists_equiv_prod_of_fibNim_sq` indexes regular summands by the
  zero-diagonal labels, with no rank or nonemptiness assumption.
- `exists_equiv_prod_of_isNIMRep_fibNim` explicitly supplies the unit condition.
- `exists_equiv_of_isIndecomposable_fibNim` proves the corrected nonempty
  indecomposable two-label conclusion.

The associated regression already checks an empty index set and the direct
sum of two regular representations. The 2026-10-05 inventory describes its
older audit baseline; its EX5/FIB wording about a missing arbitrary-rank
matrix classification does not describe this inspected baseline. The
historical inventory and its generated companions are not rewritten here.

## New physical consumer

`FibonacciSymmetricFamilyDecomposition.lean` adds
`FibonacciCompression.exists_equiv_prod_of_isMPOSymmetricFamily_fibNim`.
For any Fibonacci MPO fusion algebra and finite family of normal tensors,
it derives an even number of blocks and the full direct-sum coefficient
formula. The summands are indexed by the zero diagonal entries of the
original complex-valued tau coefficients.

Its physical inputs are invariance with length-independent coefficients,
positive bond dimensions, independence of periodic vectors at one positive
length, and the unit operator fixing those vectors at that length.
The proof first derives natural multiplicities from the existing symmetry
theorem. Independence then derives the identity unit matrix. Only after
this step does the proof invoke the existing unital Fibonacci NIM theorem.
There is no bound of two on the state labels, assumed coefficient symmetry,
indecomposability, or assumed matrix classification.

The one-length unit premise is necessary: `IsNIMRep` expresses only the
fusion multiplication law. The all-zero matrices satisfy it even on one
label. Moreover, the concrete Fibonacci unit is an admissibility projector,
not the identity on the full physical space (`mpo_fibOne_ne_one`); mere
invariance cannot replace the stated fixed-vector condition.

This consumer retains the periodic-boundary scope of its input theorem.
It does not establish a new arbitrary-boundary action reconstruction.

## Associator classification remains open

[Issue #8053](https://github.com/LionSR/TNLean/issues/8053) still separates
the multiplicity classification from the statement that L is gauge
equivalent to F. The source's regular solution at lines 603–605 proves the
existence of a regular-module solution; the claim at line 1993 additionally
requires classification of all admissible Fibonacci module associators.

The baseline's `FibonacciFSymbol.lean` defines the golden F/G coefficients,
checks the nontrivial two-by-two F block is involutive, and identifies
physical MPO tensor entries with those numbers. `FibonacciAction.lean` and
`FibonacciAnomaly.lean` construct a periodic regular action on two normal
states. Neither result computes that action's extracted L matrices or
classifies arbitrary action associators up to gauge. Equality of an MPO
tensor entry with a named F coefficient does not identify its extracted
fusion comparison with that coefficient.

[Issue #8348](https://github.com/LionSR/TNLean/issues/8348) and
`docs/paper-gaps/glm23_reps3_su24_module_list.tex` illustrate the distinction
for the other examples: the bare NIM equations even allow an unwanted
nonsymmetric Rep(S3) action. Fibonacci itself needs no added symmetry
premise, because its matrix equation already forces symmetry. That fact
still supplies no associator data.

A concrete next theorem is regular-module associator gauge uniqueness.
After identifying each indecomposable Fibonacci summand with its two
labels, let x0 be the zero-diagonal label and extract the one-dimensional
comparisons g(a,b;c) = L(a,b,x0;c). Their nonvanishing follows from
invertibility of these one-dimensional L matrices, not from entrywise
nonvanishing of general F or L matrices. Specializing the coupled pentagon
to x0 gives, in multiplicity-free coordinates,

    sum_v L(a,b,c;e)[f,v] g(v,c;e) F(a,b,c;e)[v,h]
      = delta(f,h) g(b,c;f) g(a,f;e).

Thus rescaling action channels by g(a,b;c)^(-1) makes the transformed L
matrix the inverse of the source-oriented F matrix. The source-oriented
F in the pending exact-boundary work is left analysis followed by right
synthesis, whereas L is sequential analysis followed by fusion synthesis;
this inverse is an orientation requirement. For the printed Fibonacci
coefficients all admissible blocks are involutions, yielding L = F after
matching the channel order and identifying the extracted fusion data.

Reuse candidates, inspected in the existing source branches but not
claimed as merged baseline coverage, are `BoundaryActionLMatrix.lean`
(`actionLMatrix_inverse`), `BoundaryFusionFMatrix.lean`, and
`BoundarySourceMixedPentagon.lean` (`actionLMatrix_mixed_pentagon`). A full
source-level result must use actual derived action comparisons and the
action-channel gauge law, not define L to be F or accept gauge equivalence
as an assumption.

## Validation

No actual-import Lean check or Lake command was run by this worker; the
coordinated builder owns compilation and cache writes. One authorized
read-only Mathlib-only probe of the coefficient casts, subtype equivalence
and cardinality calculation timed out after 30.22 seconds, exit 124, with
no diagnostic output. It is inconclusive, not a passed or failed source
check. It used the pinned Lean v4.35.0-rc3 toolchain, one worker thread,
the repository's strict Lean flags, and no output artifact or cache write.
The exact probe, log and exit record are respectively
`/workspace/shared/glm23-fibonacci-glue-probe.lean`, `.log` and `.exit` in
the task workspace; these transient files are not repository dependencies.

The new regression file checks the actual
Fibonacci MPO consumer at arbitrary rank, parity exclusion at rank three,
the empty family, the nonunital one-label counterexample, and a guarded
standard logical-dependency report. These checks are prepared, not asserted to have
passed. No tensor diagram was introduced or changed.

### Integrated draft checkpoint

The generated `TNLean/MPS/Examples/Fibonacci.lean` aggregator now imports
the physical consumer. Its regression runs in the existing strict
`Test boundary transport and fusion actions` loop in `pr-ci.yml`; the
Fibonacci change adds no job, dependency pin, or timeout. The packet contains one new public
theorem in 86 production lines and five examples plus a guarded
logical-dependency report in 88 regression lines.

The new theorem and proof deliberately have no `\leanok` markers pending
native validation. Previously checked decomposition entries are unchanged.
No Lean or Lake command was run during the original integration. The
subsequent CI results below distinguish production elaboration from the
still-pending complete regression pass.

The first published checkpoint `ead8307519e4f5f59dca88978d9a3c8fb43c0db3`
was checked by GitHub CI run `37438244286`, build job `112185315154`.
The production module reached its final coefficient transport but failed
because rewriting the equality of subtype representatives produced an
ill-typed dependent decidability motive. The repair casts the already
proved natural coefficient equality and uses the simplifier's congruence
rule for the conditional. It changes no hypothesis or conclusion. Both
module-documentation headings were normalized in the same repair batch.
At that checkpoint the repaired production proof and strict regression
were unvalidated.

The next published head `02ae27198f3bc4152e7bfc670e3af9d76413ad60`
passes the complete 12,444-target Lean build in run `37439623349`, job
`112190222498`; the new production module takes 2.6 seconds. Its strict
regression then reports two errors: the rank-three contradiction needs
the witness in the definition of evenness exposed to integer arithmetic,
and the empty subtype has an unused named binder. The current test-only
repair handles those two diagnostics. The production proof is unchanged;
the complete repaired regression and all final-head checks remain pending.

Run `37441641307`, job `112197081418`, subsequently exposed a parser error
in the anonymous empty-subtype binder. Naming it `_x` preserves the exact
predicate and suppresses the intended unused-binder warning. The pinned
Lean parser accepts this binder form; the full regression still awaits CI.

Source checks passed: generated-import coverage (71 aggregators, 2765
production modules), the existing strict-loop YAML and regression entry,
unique ownership of the new theorem, all seven distinct references in the
owned fragment, reverse declaration coverage, paper-gap declaration
extraction, numbered-file and size policies, forbidden-token and changed-prose
guards, and whitespace checks.
The global source scan resolved 19760 blueprint references against 39434
declaration names, with no missing references or duplicate ownership tags.
This is source inspection, not elaboration.

The dependency scan used an isolated source export of the exact QICLean
revision accepted by the refreshed baseline,
`8d5389d23c8e675a0117442e1a0d2c683a4bad41`.
The separate warmed validator uses `2ba242ee081d7dcc1274c7a5b23bffb368a9fa6f`;
its build artifacts do not validate this branch. Both pin Mathlib
`c55e6e786f49471c72fbddbec5415808896aec1e`. Dependency files exactly match
the refreshed baseline; no dependency pin was manually changed and no Lean
build cache was written.

The unpublished branch merged the refreshed baseline without conflicts.
Both of main's rectangular-window build and strict regression steps remain
intact, alongside the separate Fibonacci entry. All source checks above
were repeated after the merge using the accepted QICLean revision.

Both changed TeX files pass the pinned latexindent 3.24.7 byte comparison.
A focused fixture containing the complete owned fragment and its referenced
statements renders to a nine-page XeLaTeX PDF and six plasTeX HTML pages.
The two physical PDF pages containing the new theorem and proof were
visually inspected; the new entry has no checked badge. All five fragment
labels appear in the HTML, with no broken local anchors, duplicate IDs,
unresolved-reference sentinels, or renderer errors. Two overfull boxes of
0.23 and 1.48 points occur only in copied prerequisite context. Inherited
diagrams use the supported XeLaTeX/PDF conversion fallback because dvisvgm
is absent. No new tensor diagram was needed. No browser inspection was run.

The render is reused after the baseline merge: the owned fragment is
byte-identical, with SHA-256
`e694bdc8c7a84e9a252b55ee6b3777ff1feaa060ff7f86a88792cc453a06299a`,
and none of the six source files supplying the copied prerequisite context
changed in the merge. The fixture's context SHA-256 is
`60fc7f763a84b9d6475deb793f8c750fd1e235a87000547e42f2c6ca8381ac9a`.

The separate paper-gap PDF attempt stopped because `dsfont.sty` is absent
from the documentation environment; it is not counted as a passed render.
The isolated source exports, render fixture, logs, and JSON review reports
are under `/workspace/shared/glm23-blueprint-validation/fibonacci-family/`
in the task workspace and are not repository dependencies.
