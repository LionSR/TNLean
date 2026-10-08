# Finite message expansions and physical-output resource bounds

The eleven modules in this contribution prove 65 public declarations. A message
on a finite-dimensional space is expanded in an orthonormal basis as a sum of
sender bras followed by receiver kets. These are actual allowed local words with
no pair source. Their sum is the original transmitted identity, tensored with the
identity on every spectator register. Composing the literal finite expansions
preserves the evaluated operator and the pair-effect count; both the term count
and the absolute coefficient sum are the product of the message dimensions.
The weighted-gate construction then supplies an actual original-circuit gate
and its expansion bounds.

The remaining results concern the original input memory and the source circuit
after the physical output exchange. They prove finite-dimensionality of the
actual input memory, the source-count bound from original gate count and arity,
and explicit polynomial sample and branch counts. They also derive the actual
star/sample alphabet bounds, identify each link's endpoints in a common original
gate, and bound the incident-link count by `2 b (b - 1)` from original arity and
whole-lifetime participation bounds. Occurrences and parallel links are counted
separately. A root is chosen on all replacement gate occurrences and is required
to participate only at the retained gates.

These results do not identify the sampled physical operator with a contraction
of local tensors. The virtual-alphabet and locality conclusions concern the
already defined links. Private input spaces are finite dimensional, as assumed
in the manuscript, but their dimensions have no numerical bound in these results.
The physical-dimension and lifetime parameters of the scalar sample estimate
are distinguished from their intended application.

## Sources

- Source revision: `b661d5aae743568fede6a5b087c9d6d03f4a8f20`.
- Parent: `a1be4cc9ba5a7e8f20bd24267b5c4cff77563a45`.
- Unchanged QICLean dependency: `caac4b549c1b5c14fcedbee647567f51e27b296d`.
- Manuscript: September 24, 2026, Section 5 and the proof of Theorem 5.2.
  The source anchors for individual declarations appear in the provenance shard.

`source-preservation.json` compares every incoming frozen proof with its
canonical source. All eleven noncomment token streams are unchanged. Only the
provenance notices were added. The original sources and eight independent
historical verification directories are preserved under deterministic gzip.
No inherited theorem or dependency pin was changed. The tactic ledger records
the shared membership lemma for composed gate expansions and its consumers.

## Verification

All 14 modules in the affected import closure, including the three enclosing
aggregators through `TNLean`, passed direct Lean compilation with the package
options and warnings as errors. The checks took 114.147 seconds in total and
produced no diagnostics. They used a private output directory and read-only
compiled dependencies; no Lake build, dependency cache mutation, or Mathlib
compilation was performed.

The imported audit reports all 65 public declarations with only `propext`,
`Classical.choice`, and `Quot.sound` among their axioms. All 14,730 imported
artifact hashes were recorded and rechecked at the source revision.
The full compiled-root declaration check found all 21,441 synchronized blueprint
names. This is a direct Lean environment check, not a `leanblueprint checkdecls`
invocation through Lake. Exact commands, options, source hashes, logs and
artifact hashes are recorded beside this document.

The two new chapters attach all 65 declarations exactly once. Full source
synchronization passes with 21,308 blueprint reference entries and 44,332 parsed
Lean declarations. The full dependency graph has 7,824 nodes and 19,059 edges,
with no cycles or duplicate labels. A disposable focused PDF and web build
includes the preceding source-compression chapters; the browser check passes
for seven pages and 5,554 mathematical expressions. PDF pages 62–67 were
rendered and visually inspected. No new overflow remains; the 0.99057pt warning
belongs to an unchanged inherited common-source heading.

The notice check uses the pinned `jsonschema==4.26.0` environment, since the
system Python does not provide that dependency. The full canonical provenance
check passes for 1,149 entries. The final `manifest.json` and `compression.json`
record the preserved evidence bytes and uncompressed stream hashes. The supplied
validator checks these records and the source Git objects without compiling Lean.
