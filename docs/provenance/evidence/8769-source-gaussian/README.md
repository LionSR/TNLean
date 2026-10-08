# Gaussian operators at original source positions

Source revision: `258925377085dec88db0d45131c6c1d569303ae0`.
Parent TNLean revision: `329d192af8c46f7ff540610de918d5179d13d46e`.
QICLean dependency: `b2521d2a2843d824ce85a4d94bf4b60d322d6c6f`.

The contribution chooses Schmidt probabilities and proper endpoint frames for
each original source occurrence and each local gate label. These choices precede
all affected sets and partial branches. A single probability space assigns
Gaussian coordinates to each original occurrence and ordered pair of local
labels. Its sampled operators are averages of product operators; they need not
have rank one. The mean is the exact mixed source matrix.

The covariance of the actual centered entry products follows from the existing
QICLean Gaussian theory. An exact operator identity then expresses each globally
defined corrected term as a sum of these coefficients times the actual prepared
ket and bra words. Taking the actual final partial trace gives the pointwise
physical error expansion and its triangle bound. The further identification of
original registers with the affected and exterior contractions, and the resulting
expected physical error estimate, are separate obligations.

Eight new modules contain 29 public declarations. The generic selected-argument
multilinear identity is shared by the transported-source proof and the existing
matrix-unit expansion in `SelectedSourceContraction`. The latter public statement
is unchanged. The general rank-one transport identity belongs to QICLean and is
provided by the separately checked dependency update, QICLean PR #646.

## Source preservation

The six unchanged mathematical modules preserve every noncomment token from
their checked drafts. The actual theorem in `PreparedSourceTransport` preserves
its proof after renaming the use of the extracted multilinear lemma. The moved
lemma preserves its proof body, with a public name in the multilinear-map
namespace. `source-preservation-final.json` records these comparisons and hashes.
Canonical provenance notices were added to all new declarations.

The inherited matrix-unit helper now applies the shared expansion after proving
the matrix-unit reconstruction formula. Its public theorem and hypotheses are
unchanged. The exact inherited diff is retained as a compressed patch. The old
provenance shard is preserved in `historical-shards/`; only the verification field
of its one affected entry is refreshed. No historical evidence is removed.

## Verification

All 17 modules in the affected TNLean import closure were checked directly with
the package options and warnings as errors. All final checks succeeded without
diagnostics; their recorded elapsed times total 276.450 seconds. Exact unchanged
checks were reused, and the affected root imports were refreshed after the
isolated QIC artifact links were completed. The records identify every command,
source hash and output hash. This is direct Lean verification, not a local Lake
build or a CI measurement.

The importing audit checks all 29 new declarations and the one refactored public
declaration. All use only `propext`, `Classical.choice` and `Quot.sound`.
The 14,643 actually imported artifact hashes were rechecked at the source pin.
The worktree has no `.lake` directory. Existing dependencies were read through
file links; all new compiler outputs were written under `/tmp`. Mathlib was not
rebuilt and no peer cache was changed.

Initial checks are retained. The first generic-helper check reported a deprecated
import; the canonical import was substituted. An initial dependent lambda in
the matrix-unit refactor needed explicit index types. The first root importing
audit found an incomplete temporary QIC artifact tree; adding read-only links
for the remaining dependency roots and root companion artifacts resolved it.
The two affected root modules and the complete importing audit were then checked
again. These setup failures are not counted as successful final checks.

The canonical provenance checker validates all 614 TNLean entries, including
29 new entries and the one refreshed verification. The unchanged checker and
schema are also retained under `canonical/` for inspection. From the repository
root, the recorded evidence may be validated without compiling Lean:

```bash
python3 docs/provenance/evidence/8769-source-gaussian/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python scripts/check_openai_provenance.py --root . --upstream-root /path/to/openai-math
```

The second command requires the pinned manuscript revision in the supplied
checkout. Exact successful arguments and logs are
recorded in this directory. Recompilation requires the recorded toolchain and
matching dependency artifacts.

## Mathematical documentation

The new chapter has exactly one tag for each of its 29 declarations. Full source
synchronization passes for 20,899 blueprint reference entries. A direct check in
the compiled TNLean root finds all 20,906 names in the synchronized declaration
list. This is a compiled declaration-presence check, not Lake's `checkdecls`.
The complete source dependency graph has 7,692 nodes and 18,895 edges, without
cycles or duplicate labels.

The focused PDF includes the preceding source chapters and the new Gaussian
section. Every page containing the new section was inspected visually. The final
section has no overflowing text or undefined references. An inherited 0.991-point
overfull heading remains in the common-source chapter. The focused web check
passes on seven pages with 3,248 typeset elements. These are focused renders,
not a full-book build. The first render's two small overfull paragraphs were
shortened without changing their mathematics; its logs are retained.

The canonical formatter is idempotent. The scoped tactic-pattern scan found no
repetition at its configured thresholds. The shared multilinear expansion and
its two consumers are recorded in the project's proof-pattern ledger.
