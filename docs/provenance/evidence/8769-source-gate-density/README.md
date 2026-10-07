# Source-gate density expansions: verification evidence

The 16 public declarations in `declarations.json` were verified at source
revision `86ed134591132d21ab3046d504e84196e2ee5ec6`. They prove exact preparation, matrix, and density
identities used in the proof of Theorem 5.2 of the pinned polynomial-PEPS
manuscript, `04-compression.tex`, lines 233–355, and the elementary preparation
contraction bounds used at lines 409–427.

The actual-gate theorem starts from the original finite family of allowed
compositions. It constructs common finite pair spaces, normalized sources,
source-free remaining operations, and coefficient matrices. Their finite sum
gives the density of the original weighted matrix, with the exact factors
`c ξ * conj (c ζ)`, for every complex input matrix. All witnesses precede the
quantification over the input matrix. Finite orthonormal bases are prescribed
only on the external input and output memories.

The coordinate-basis statements use full orthonormal bases. The more general
finite-component identities accept arbitrary endpoint vector families,
including families spanning proper subspaces. They do not themselves supply
the actual Schmidt frames. Individual elementary prepared matrices are proved
contractive. The separated affected-side and exterior maps needed for the joint
contraction argument, the Gaussian source replacement, and the circuit
trace-norm error estimates remain to be derived. This contribution does not
establish the full compression theorem.

All four exact-source modules compiled with the package options and warnings
treated as errors, without diagnostics. `direct-build.log` records the exact
commands, source hashes, artifact hashes, and durations. Sources and new Lean
artifacts were written only in temporary directories; predecessor artifacts
were read without modification. No Lake command was used. A full package build
is a separate CI check.

The imported audit covers all 16 explicit public declarations. Every axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The
compressed manifests identify all 4,346 imported artifacts.
Final verification compared committed sources to the compiled snapshots and
rechecked every imported artifact hash.

The `blueprint` and `regression` directories contain their separate commands,
results, and source hashes. The blueprint report distinguishes focused
rendering and source synchronization from a full-root compiled declaration
check. The regressions use actual preparations and matrices, including empty
slots, unequal ket and bra index families, proper source subspaces, a nonreal
bra coefficient, and a non-Hermitian input matrix.

Run the following command in a checkout containing the proof revisions to
validate all five contributions with the packaged, unmodified canonical
checker and schema. The canonical policy commit itself need not exist in the
local Git object database.

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-source-gate-density/replay.py \
  --root . --upstream-root /path/to/openai-math
```

This replay validates recorded evidence, source notices, manuscript labels,
and identifier collisions. It does not recompile Lean or repeat the unrelated
historical provenance and license audit. Without `--upstream-root`, the checker
explicitly reports that manuscript labels were not rechecked. All 16 proofs
are independent formalizations; no upstream Lean proof text was reused.
