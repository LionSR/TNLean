# Exact same-root Ritz extraction in the flat branch

The new auxiliary assumes the existing spectral gap implication and the
absence of an actual excited spectral value. It derives that the original
full ground space is top. Closeness with any error below one forces the
specified native root, and therefore the same full-interval root, to be top.
No independent approximation space is selected.

The actual zero-th filter-and-trim iterate is the initial root itself. The
actual Ritz space is contained in its candidate and has the same full
dimension, hence equals it. Both projection errors vanish. The raw filter
is never applied; it can be zero for a positive scalar Hamiltonian. Every
output vector has exact MPS bond at most the full ground multiplicity and
therefore at most the supplied initial dimension bound.

No new positive-local-dimension hypothesis is imposed. Ground spectral
membership supplies a configuration. If an internal cut exists, that
configuration gives a value in the local alphabet, establishing its
positivity exactly where the elementary power bound needs it. Empty chains
have no internal cuts. No interaction, normalization or MPS hypothesis on
the initial root is assumed.

The public result is a flat-branch auxiliary, not a final theorem carrying
an extra excitation premise. A gap-implication-only final wrapper must split
internally between this exact branch and the existing nonflat automatic
refinement. The initial and final trimming radii need not coincide.

The production source passed a serialized strict private check in 6.296
seconds against fully verified TN
`107e2726f679d75b51c621694d2216fb1cd0771a` and its own QIC
`68481832e01180e472712ab6dc916199c7b3dd67`, with 271 selected source/object
pairs, root inputs and the prebuilt Mathlib object guarded. The final proof
uses the direct Ritz inclusion and dimension theorems rather than an
analytic error-zero specialization. Imported foundation inspection passed
in 4.828 seconds and reported only `propext`, `Classical.choice` and
`Quot.sound`; temporary inspection commands were removed. Earlier partial
proof diagnostics and the superseded analytic specialization are preserved.

Full source blueprint synchronization passed with the exact verified QIC
and Mathlib sources resolved read-only. Generated imports, reader-facing
prose, tactic scanning and whitespace checks passed. The repeated flat
spectral and full-dimension MPS arguments are recorded as a two-occurrence
candidate in the tactic ledger. Combined ordinary gates remain required.
No provider, dependency pin, cache or Mathlib source was modified.
