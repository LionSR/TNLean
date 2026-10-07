# Grouping parties and internal preparations: verification evidence

The 28 public declarations in `declarations.json` were verified at source
revision `2609edd456a91c7d5b34e23b0b8a7e3d8626f54f`. They establish the owner
identifications and local preparations used in Theorem 5.2 of the pinned polynomial-PEPS manuscript,
`04-compression.tex`, lines 383–448.

A map on party labels induces a canonical isometry of memories. Applying it to
an actual composition preserves its operator under these isometries. Pair
sources whose endpoints acquire the same owner become local preparations of
their original vectors; they are removed only from the pair-source inventory.
Every surviving source is retained in its original order, including distinct
occurrences that now have the same pair of owners. The operator identity holds
for arbitrary source vectors. Normalization is used only for allowedness.

For a partition into two sides, the explicit condition that every original
source has both endpoints on one side implies that the grouped composition has
no pair sources. Its two actual restrictions then give source-free contractions
whose tensor product recovers the original operator in canonical coordinates.
There is no assumed factorization and no injectivity condition on the owner map.

The results supply the internal-source part of the separation argument. They do
not yet construct the chronological partially expanded circuit or its selective
source preparation. The full compression theorem and its trace-norm estimate
remain separate obligations.

All five exact-source modules compiled with the package options and warnings
treated as errors, without diagnostics. `direct-build.log` records commands,
source hashes, artifact hashes and durations. The compiled source snapshots and
new Lean artifacts were written only in temporary directories; predecessor
artifacts were read without modification. No Lake command was used. A full
package build is a separate CI check.

The imported audit covers all 28 explicit public declarations. Every axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The
compressed manifests identify all 4,331 imported artifacts. Final verification compared committed sources to the compiled
snapshots and rechecked every imported artifact hash.

The `blueprint` and `regression` directories contain their commands, results and
source hashes. The blueprint report distinguishes focused rendering and source
synchronization from a full-root compiled declaration check. The regressions
check that two surviving occurrences remain separate and that a collapsed
source retains its nonreal phase in the actual memory operator.

Run this command in a checkout containing the proof revisions to validate all
seven contributions with the packaged canonical checker and schema:

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-party-coarsening/replay.py \
  --root . --upstream-root /path/to/openai-math
```

This replay validates recorded evidence, source notices, manuscript labels and
identifier collisions. It does not recompile Lean or repeat the unrelated
historical provenance and license audit. Without `--upstream-root`, the checker
explicitly reports that manuscript labels were not rechecked. All 28 proofs
are independent formalizations; no upstream Lean proof text was reused.
