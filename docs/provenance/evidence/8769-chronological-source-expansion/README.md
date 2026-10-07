# Chronological partial source expansion: verification evidence

The 55 public declarations in `declarations.json` were verified at source
revision `02ff0a871f6e1847f847f00609ba89c3942ab5c4`. They formalize the chronological partial expansion in
the proof of Theorem 5.2 of the pinned polynomial-PEPS manuscript,
`04-compression.tex`, lines 342–417.

Each nonprivate gate has its own finite participant set and common source
positions. The chronological composition records actual private maps, placed
gates, register exchanges and spectator identities. Partial branches choose
labels only at gates touching the affected parties. Untouched exterior gates
retain their aggregate contractions. The weighted sum is exactly the original
operator under canonical owner identifications. In orthonormal coordinates its
density has independent ket and bra choices with coefficients c times conjugate c.

Original gate occurrences remain distinct when the same gate is used repeatedly.
A source position is an occurrence and a slot number, independent of labels.
Both endpoints are proved to participate in the owning gate. The actual ordered
source inventory is obtained by filtering the original positions by affected
endpoints; its endpoint spaces and register layout are independent of labels.
The sum of absolute partial coefficients is the product of the original
coefficient sums at touched occurrences. The ket–bra cost is its square.

These results do not assert the corrected-position trace-norm bound or the full
compression theorem. The physical protocol construction, source-operator
corrections, separated contractions and their trace-norm estimate remain
separate obligations.

All eight exact-source modules compiled with package options and warnings
treated as errors, without diagnostics. `direct-build.log` records commands,
source hashes, artifact hashes and durations. These are direct Lean checks;
no Lake command or cache mutation was used. New snapshots and artifacts were
written only in temporary directories. A full package build and CI compilation
time check are separate. Local elapsed times reflect concurrent verification
work and are not comparable to CI timings.

The importing audit covers all 55 explicit public declarations. Its reports
contain only `propext`, `Classical.choice`, and `Quot.sound`. Compressed manifests
identify all 4,358 imported artifacts. Final
verification byte-compared committed sources and rechecked every artifact hash.

The blueprint directory records exact declaration coverage, source
synchronization, dependency-graph inspection, formatting, focused PDF and web
rendering, and browser checks. It distinguishes these from a compiled full-root
declaration check. The three regressions construct actual prepared gates from
words: an untouched empty branch family has one choice and zero aggregate;
repeated touched gates have independent choices; a phase gate and its double
composition retain phases i and minus one under the weighted operator identity.

Run the packaged canonical provenance check for the nine source-gate
contributions, comprising 323 declarations:

```sh
uv run --no-project --with jsonschema==4.26.0 python   docs/provenance/evidence/8769-chronological-source-expansion/replay.py   --root . --upstream-root /path/to/openai-math
```

This checks recorded evidence, source notices, manuscript labels and identifier
collisions. It does not recompile Lean or repeat the unrelated historical license
audit. Without `--upstream-root`, manuscript labels are explicitly not rechecked.
All 55 declarations are independent formalizations; no upstream Lean proof text
was reused.
