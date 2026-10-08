# Sampling an actual source-only circuit

This record verifies the Gaussian sampling approximation for an actual allowed
source-only circuit. The exact source revision is in `source-revision.json`.
The parent is `2f5a2d3f4163dd25caf8c0845bc81b6c5826493f` (TNLean #8912).
QICLean remains pinned to `caac4b549c1b5c14fcedbee647567f51e27b296d` in all
three dependency files.

## Mathematical statements

The argument first constructs the actual local contractions and input isometries
for each pair of partial branches. It proves their expected physical trace-norm
bound, retains the original branch coefficients, and sums over the actual gate
choices. The original lifetime participation and local physical-dimension bounds
then yield

\[
  \mathbb E\|F_S\|_1
  \le (B^{4b}D^4)^{|S|} k^{-|S|/2}.
\]

Every discarded register is finite dimensional, as in the manuscript; these
private dimensions are otherwise arbitrary and do not enter the estimate.
Their finiteness supplies the actual regional orthonormal bases. No estimate
for a source coefficient, supplied factorization, or desired corrected-term
bound is assumed in the final sampling theorem.

The final theorem chooses Schmidt data indexed by each original source occurrence
and its local branch label, then chooses one actual global Gaussian sample. For
an allowed scalar-input preparation containing no sources, that sample gives
physical operator error at most one quarter of the prescribed accuracy. The
sampled quantity is an operator; positivity is not asserted. The intermediate
sample-choice theorem explicitly assumes a corrected-term integral bound, and
the final theorem discharges that assumption using the circuit resources.

For arbitrary real accuracy exponent p and scale L at least one, the same
sample and the same positive integer sample count give error at most L^(-p)/4,
with the displayed polynomial count obtained by rounding p upward only in the
chosen accuracy. Four further statements identify the effect-elimination stack
count with the scalar sample-count expression and bound the actual replacement
branch count by the original monomial and coefficient bounds.

This contribution proves sampling approximation for source-only circuits and
its numerical resource estimates. The tensor-network representation and the
assembly of all reductions into the full paper theorem remain separate.

## Exact-source verification

The ten modules contain 18 public declarations. All mathematical tokens from
the frozen checked sources are preserved. Only provenance notices are inserted;
canonical imports were already present. The original sources and hashes are
retained. There are no inherited proof edits or provenance refreshes.

* Thirteen strict direct Lean checks cover the ten modules and all three
  affected import aggregators, including the library root. Package options and
  warnings as errors are explicit. Every check has zero diagnostics; the total
  recorded compilation time is 70.951 seconds, with no module above 25 seconds.
* The imported 18-declaration audit reports only `propext`, `Classical.choice`
  and `Quot.sound`. All 14,707 imported artifact hashes are recorded and checked
  again at the source pin.
* A direct Lean check importing the full library finds all 21,301 synchronized
  blueprint declaration names. This is not a local Lake build or an invocation
  of `leanblueprint checkdecls`.
* Full source synchronization passes with 21,194 blueprint references and
  44,190 source declarations. All 18 new declarations occur exactly once in the
  new chapter, and the full source dependency graph has no cycle or duplicate
  label. The principal completed arguments appear as explicit dependency edges.
* The focused PDF has 59 pages. Every page containing the new chapter (PDF
  pages 54–58) was inspected visually. The seven-page web build passes the
  browser check with 4,790 mathematical expressions. There is no new overflow;
  one inherited 0.99057-point heading overflow remains in an earlier chapter.

No Lake build, Mathlib build, or cache mutation was performed. The exact checked
parent artifacts are read through immutable copies and links; new artifacts are
written only to the temporary contribution directory. The package pins and
all historical evidence remain unchanged.

## Recorded checks

`record-evidence.py` packages completed checks without compiling Lean.
`validate-evidence.py --root <repository>` verifies the source revision, archived
streams, hashes, imported audit, complete public inventory and provenance scope.
The canonical provenance checker and schema are copied verbatim; its full run
is recorded in `full-provenance-command.json` and `full-provenance.log`.

The exact commands and environment are retained. Large fixtures and logs use
deterministic gzip, with uncompressed hashes in `compression.json` and packaged
hashes in `manifest.json`. These are local direct-Lean and focused blueprint
checks; no unperformed CI or full-book build is claimed.
