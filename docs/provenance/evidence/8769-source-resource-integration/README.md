# Source-only reduction, original resources, and actual local coordinates

This record accompanies the source-only reduction of an original distributed
circuit and the identification of its actual corrected inputs and local outputs.
The source revision is recorded in `source-revision.json`. The base is
`456204230ab8548568dbbccdac39b894d1539ff5`; the QICLean dependency remains
`caac4b549c1b5c14fcedbee647567f51e27b296d` in all three dependency files.

## Mathematical scope

The reduction constructs one auxiliary vector shared by the ideal and
approximating circuits, proves the operator error and the physical density error,
bounds the replacement coefficient sums by the original sums, and preserves
participating parties and lifetime counts. Physical dimensions may depend on the party; the regional dimension is
the product of the original local dimensions.

For the corrected source expansion, the construction retains original source
occurrences and register order. It provides one source permutation before the
branch and source-vector choices, derives normalized crossing vectors and their
Schmidt isometries, and constructs the two actual local contractions. The output
identities use the original physical and discarded registers, with the exact
four-coordinate permutation between physical/discard and affected/exterior order.
These results do not assert the final Gaussian corrected-term estimate or the
existence of an approximating sample. Those conclusions are separate subsequent
results.

The contribution contains 300 new public declarations. The earlier relay audits
selected 80 declarations; its complete public inventory contains 206 declarations,
all included here. Original relay sources and historical evidence are retained.
The long replacement module is split at its preparation/auxiliary-register
boundary, with all public names preserved. Two extra end-of-file blank lines
were removed. Headers, imports and provenance notices were adapted to this
repository. The source-preservation and promotion records distinguish these
changes from complete token preservation.

Two repeated proofs are shared without changing public mathematical statements.
The existing evaluation lemma for equal register lists is moved to
`WordEvaluationTransport`, and four copies use it. The existing coordinate
formula for the physical partial inner product is made public, and the duplicate
in the new output module is removed. Verification is refreshed for 28 inherited
provenance entries; the prior entries and their records remain archived.

## Verification performed

* 48 direct Lean module compilations, including the complete affected import
  closure and the library root, use the package options and warnings as errors.
  All finish without diagnostics; their recorded times sum to 380.241 seconds.
  Three modules exceed the local 25-second warning threshold (28.668, 27.307 and
  37.574 seconds); none reaches the 50-second failure threshold.
* An imported audit of 328 declarations (300 new and 28 inherited) reports only
  `propext`, `Classical.choice` and `Quot.sound`. All 14,697 imported artifact
  hashes are recorded and rechecked at the source pin.
* A direct Lean check importing the full library finds all 21,283 names in the
  synchronized declaration list. This is an imported-environment check, not a
  `leanblueprint checkdecls` or local Lake invocation.
* Full source synchronization passes with 21,176 blueprint references and
  44,172 source declarations. The three new chapters contain each of the 300
  new names exactly once. The complete source dependency graph has no cycle
  or duplicate label.
* The focused PDF has 55 pages. Every page containing the new chapters (PDF
  pages 44–54) was inspected visually. The seven-page web build passes the
  browser check, including 4,406 mathematical expressions. No overflow remains
  in the new chapters; one inherited 0.99057-point heading overflow remains
  in the common-source chapter.

No Mathlib compilation, cache mutation, or Lake build was performed. Previously
checked artifacts are read through immutable copies and links; changed modules
are compiled only into the temporary contribution directory. Commands, options,
source bytes, elapsed times and imported hashes are recorded explicitly.

## Earlier checks and reproducibility

The successful 41-module / 314-declaration checkpoint before the shared transport
lemma is preserved. An intermediate removal accidentally omitted a neighboring
lemma and namespace. Source synchronization and strict compilation detected it;
the exact checkpoint source was restored and only the intended private helper was
removed. The failed source, diagnostics and command are retained under
`initial-checks`, followed by the complete successful 48-module / 328-declaration
verification. No published source or evidence was changed by that intermediate
failure. Earlier render passes and the final render logs are also retained.

`record-evidence.py` packages completed checks without compiling Lean.
`validate-evidence.py --root <repository>` checks the recorded hashes, exact source
revision, archived streams, public inventories and inherited provenance changes.
The canonical provenance checker and schema are included verbatim. Its full run
is recorded separately in `full-provenance-command.json` and `full-provenance.log`.

Large source fixtures, logs, historical evidence and patch files are stored using
deterministic gzip. `compression.json` records hashes of the uncompressed bytes;
`manifest.json` records the packaged bytes. The evidence is local direct-Lean and
focused blueprint verification; no unperformed CI or full-book build is claimed.
