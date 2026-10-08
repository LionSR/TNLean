# Sampling the original distributed construction

This contribution proves 15 public declarations in six modules. The original
construction records its finite party memories, normalized product input,
physical dimensions and order, retained private registers, and actual original
circuit. Its physical density is defined by tracing the actual output vector.
It is positive semidefinite and has trace at most one; no division by the output
norm is made. Resource estimates and approximation conclusions are not fields
of the construction.

A single nonempty-party convention is part of this definition. The accompanying
clarification note explains the scalar boundary case and the proof's absorption
of scalars at an existing party. General circuits and gates with no participating
parties retain their previous definitions. The note does not claim that the
printed source explicitly contained the nonempty qualifier.

The approximation results retain the original gate operators. A fixed
inverse-power local accuracy meets the actual gate-count budget, and the original
polynomial term-count and individual-coefficient bounds yield a coefficient-sum
majorant at least one. For an original contraction circuit, the constructed
pair-effect replacement and actual Gaussian source sample give physical error
at most `3 ε / 4`. For locally approximated original gates, rescaling and the
proved local-error estimate add at most `ε / 4`, giving total error at most `ε`
against the original gate-map density. The necessary input coordinates, original
source Schmidt data and sample are constructed in the relevant theorems.
The original-circuit theorem accepts finite input coordinates explicitly; the
approximate-gate theorem obtains them from the original finite party memories.

The link theorem combines the actual sample and branch counts into one explicit
polynomial alphabet bound. Its scalar lifetime and dimension parameters acquire
their physical interpretation only when the corresponding resource hypotheses
are supplied. The sampled physical operator need not be positive. An identity
expressing it as a contraction of local tensors remains a separate assertion.

## Sources and preservation

- Source revision: `3a0472ab259c7aec88fb5699f776eaf6f02c9160`.
- Parent: `a2cb859ca1ce60c154d58e9fdce20c2fec278fb8`.
- Unchanged QICLean dependency: `caac4b549c1b5c14fcedbee647567f51e27b296d`.
- Manuscript: September 24, 2026, Theorem 5.2 and its proof; individual source
  anchors are recorded in the provenance shard.

All six incoming mathematical token streams are preserved exactly. Only
canonical provenance notices were added. The original sources and five
historical verification directories are preserved under deterministic gzip.
The relay's original-circuit sampling source also matches its committed source
at `dae297bb54a3c08e41afe7e65d6d8754f1e4e06c` byte for byte. No inherited theorem
or dependency pin was changed. The tactic ledger records the two trace-norm
triangle calculations as a candidate for shared reuse before a third occurrence.

## Verification

All nine modules in the affected import closure, including the three enclosing
aggregators through `TNLean`, passed direct Lean compilation with the package
options and warnings as errors. The checks took 147.135 seconds in total and
produced no diagnostics. They used a private output directory and read-only
compiled dependencies. No Lake build, dependency cache mutation, or Mathlib
compilation was performed.

The imported audit reports all 15 new declarations with only `propext`,
`Classical.choice`, and `Quot.sound` among their axioms. All 14,736 imported
artifact hashes were recorded and rechecked at the source revision. The full
compiled-root declaration check found all 21,456 synchronized blueprint names.
This is a direct Lean environment check, not a `leanblueprint checkdecls`
invocation through Lake. Exact commands, options, sources and logs accompany
these records.

The new chapter attaches all 15 declarations exactly once. Full source
synchronization passes with 21,323 blueprint reference entries and 44,361 parsed
Lean declarations. The dependency graph has 7,834 nodes and 19,074 edges, with
no cycles or duplicate labels. The disposable focused PDF and web builds include
the preceding compression chapters. The browser check passes for seven pages and
5,865 mathematical expressions. PDF pages 67–70 were visually inspected; no new
overflow remains. The sole 0.99057pt warning belongs to an unchanged inherited
common-source heading. The exact one-page clarification note was also visually
inspected, and its original rendered evidence is preserved.

The full canonical provenance check passes for 1,164 entries. The final
`manifest.json` and `compression.json` record evidence bytes and uncompressed
stream hashes. The supplied validator checks these records and the source Git
objects without compiling Lean. Historical audits may include prerequisites;
they are preserved as historical records and do not enlarge the current 15-name
scope.
