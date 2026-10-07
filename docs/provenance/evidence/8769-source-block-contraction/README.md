# Joint source-coordinate contractions: verification evidence

The 21 public declarations in `declarations.json` were verified at source
revision `c80913b10d9926f31004705c78f136ade6b8b466`. They prove the finite-coordinate operator identities
and contraction bounds used in Theorem 5.2 of the pinned polynomial-PEPS
manuscript, `04-compression.tex`, lines 279–355 and 383–427.

Tensoring the endpoint bases and the physical input basis gives an actual
orthonormal basis of every free input register. The matrix of the remaining
allowed word in these coordinates is a contraction jointly in all source and
physical coordinates. Its column blocks are the matrices of elementary source preparations followed
by that word. The bra-adjoint–ket product allows distinct coordinate spaces and
is again a contraction. Exact rectangular trace identities apply to arbitrary
complex input matrices without positivity or Hermiticity assumptions.

A single word applies the prescribed endpoint maps independently of all source
vectors. Its exact preparation identity holds for arbitrary endpoint linear
maps, and endpoint contractions make it an allowed word containing no sources.
This construction derives the complete matrix bound for proper source frames:
their images need not span the ambient private halfspaces. The inventory count
identifies a completed source list with all unordered distinct party pairs.

The results do not yet construct the chronological affected/exterior separation
of the partially expanded circuit, nor substitute its actual Schmidt frames.
That construction must retain untouched aggregate operators and absorb internal
preparations into their own side. Gaussian source replacement and the final
circuit trace-norm error estimates also remain open. This contribution does not
establish the full compression theorem.

All five exact-source modules compiled with the package options and warnings
treated as errors, without diagnostics. `direct-build.log` records commands,
source hashes, artifact hashes and durations. The compiled source snapshots and
new Lean artifacts were written only in temporary directories; predecessor
artifacts were read without modification. No Lake command was used. A full
package build is a separate CI check.

The imported audit covers all 21 explicit public declarations. Every axiom
report contains only `propext`, `Classical.choice`, and `Quot.sound`. The
compressed manifests identify all 4,351 imported
artifacts. Final verification compared committed sources to the compiled
snapshots and rechecked every imported artifact hash.

The `blueprint` and `regression` directories contain their separate commands,
results and source hashes. The blueprint report distinguishes focused rendering
and source synchronization from a full-root compiled declaration check. The
regression report states exactly which rectangular, phase, zero-slot and
coordinate identities were checked.

Run this command in a checkout containing the proof revisions to validate all
six contributions with the packaged, unmodified canonical checker and schema.
The canonical policy commit need not exist in the local Git object database.

```sh
uv run --no-project --with jsonschema==4.26.0 python \
  docs/provenance/evidence/8769-source-block-contraction/replay.py \
  --root . --upstream-root /path/to/openai-math
```

This replay validates recorded evidence, source notices, manuscript labels and
identifier collisions. It does not recompile Lean or repeat the unrelated
historical provenance and license audit. Without `--upstream-root`, the checker
explicitly reports that manuscript labels were not rechecked. All 21 proofs
are independent formalizations; no upstream Lean proof text was reused.

A later comment-only correction is verified in [style-recheck](style-recheck/README.md).
Its seven source-block declarations now use that exact revision in the provenance ledger.
The original records above remain unchanged historical evidence.
