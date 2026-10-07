# Selective source preparation: verification evidence

The 37 public declarations in `declarations.json` were verified at source
revision `8689eafdd341540d4dd7e6848707646d6e3a0970`. They establish fixed source positions, selective
preparation, and the resulting local contractions in Theorem 5.2 of the pinned
polynomial-PEPS manuscript, `04-compression.tex`, lines 233–299 and 342–434.

On a prescribed finite set of participating parties, every finite sum of actual
allowed monomials whose aggregate operator is a contraction has common finite
source positions, normalized source vectors, and source-free remaining
compositions. The original scalar coefficients and the
aggregate operator are preserved. The source positions are chosen on each
gate's prescribed finite set of participating parties and do not depend on its
monomial label. Owner relabelling retains the aggregate contraction without an
assumption on the sum of absolute coefficients. An untouched exterior gate can
therefore remain one local aggregate operation.

Selective preparation fixes some normalized source vectors and leaves all other
source registers as input. Its actual composition is independent of the vectors
later supplied to those free registers. If every fixed source is internal to a
chosen side, two allowed source-free contractions recover the whole operator.
These two contractions are chosen before every family of free vectors, and their
norm bounds hold on the entire free input memory. No normalization condition is
imposed on the free vectors. A separate construction places any actual word
beside spectator registers, preserving its source inventory and tensoring its
operator with the spectator identity.

The results supply the operations needed for the separation argument. They do
not yet construct the chronological partially expanded circuit. The full
compression theorem and its trace-norm estimate remain separate obligations.

All six exact-source modules compiled with the package options and warnings
treated as errors, without diagnostics. `direct-build.log` records commands,
source hashes, artifact hashes and durations. The compiled source snapshots and
new Lean artifacts were written only in temporary directories; predecessor
artifacts were read without modification. No Lake command was used. A full
package build is a separate CI check.

The imported audit covers all 37 explicit public declarations. Every axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The
compressed manifests identify all 4,354 imported
artifacts. Final verification compared committed sources to the compiled
snapshots and rechecked every imported artifact hash.

The `blueprint` and `regression` directories contain their commands, results and
source hashes. The blueprint report distinguishes focused rendering and source
synchronization from a full-root compiled declaration check. The regressions
check mixed fixed and free source positions, both constant masks, and the
existence of local contraction witnesses before all free-vector assignments.

Run this command in a checkout containing the proof revisions to validate all
eight contributions, comprising 268 declarations, with the packaged canonical
checker and schema:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-selective-source-preparation/replay.py \
  --root . --upstream-root /path/to/openai-math
```

This replay validates recorded evidence, source notices, manuscript labels and
identifier collisions. It does not recompile Lean or repeat the unrelated
historical provenance and license audit. Without `--upstream-root`, the checker
explicitly reports that manuscript labels were not rechecked. All 37 declarations
are independent formalizations; no upstream Lean proof text was reused.
