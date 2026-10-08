# Physical contractions and actual Gaussian source operators

Source revision: `5547d32efa79b3b18150eb07be2bfcda4a68f79a`.
Parent TNLean revision: `ba98122703560ffc2ee68779bc175319ad226400`.
QICLean dependency: `caac4b549c1b5c14fcedbee647567f51e27b296d`.

This contribution proves physical component, mixed Gram, and exterior partial-
trace contraction estimates for actual allowed words. Their input frames are
proper isometries and need not span the ambient memories. The bra indices are
rows of the mixed Gram matrix; its ket indices are columns. The resulting
weighted source matrix uses an ordinary transpose and does not conjugate the
Gaussian coefficient.

For specified separated words and normalized crossing Schmidt weights, the
actual original-position Gaussian law gives the expected physical block bound
`k^(-|S|/2)`, and the full physical trace-norm bound includes the square of the
affected physical dimension. The contribution separately derives vector and
branch identities, square integrability, and physical trace-norm integrability
for the actual globally defined corrected circuit terms. It obtains an actual
sample bounded by the sum of their expectations. The actual selective two-side
factorization and lifetime bounds preserve original occurrences, including
repeated gates. The final sample-count statements are numerical finite-subset
estimates. The identification of the original free-source and physical/discard
registers with the specified separated frames is a further obligation; this
contribution does not claim the full compression theorem.

Nineteen new TNLean modules contain 77 public declarations. The generic
physical basis-invariance, physical-block norm, and finite matrix integrability
results are imported from the separately checked QICLean contribution #650.
They are not duplicated in TNLean. The dependency pin is synchronized in both
root files and the docbuild manifest.

## Exact sources and proof reuse

The frozen draft snapshots and their hashes are preserved. Except for the two
private concatenation-partition coherence proofs, all new mathematical tokens
are preserved after removing the generic theorem blocks moved to QICLean and
canonicalizing imports. Copyright and provenance comments were added without
changing the mathematics. One terminal empty line in PhysicalOutputContraction
was removed. `source-preservation.json` records each comparison explicitly.

The two private PartyPartitionAppend proofs now use the existing Mathlib
`TensorProduct.ext_fourfold'` in place of repeated double tensor inductions.
Their public statements and all other proofs are unchanged. The exact diff is
retained in `party-partition-extensionality.patch.gz`.

The existing PreparedMatrixNorm and SourceBlockMatrix now use QICLean's
orthonormal-coordinate norm identity. Their nine public statements are
unchanged. The approved diff is retained in `norm-refactor.patch.gz`, and the
old provenance shards are preserved in `historical-shards/`. Only the verification
fields of these nine inherited entries are refreshed. No historical evidence
is removed or silently rewritten.

## Verification

All 27 changed modules and their TNLean import dependents, including the root
import, passed direct Lean compilation with the package options and warnings
as errors. The worktree has no `.lake` directory. The compiler read individually
preserved, immutable dependency artifacts; all new outputs were written under
`/tmp`. Mathlib was not rebuilt and no peer cache was modified. These are direct
Lean checks, not a local Lake build or a CI measurement.

The final imported audit checks all 77 new and nine refactored declarations.
Only `propext`, `Classical.choice`, and `Quot.sound` occur. The hashes of all
14,665 actually imported artifacts were rechecked at the source commit. A
separate direct Lean check in the complete root environment found all 20,983
synchronized blueprint declaration names. This is not an invocation of
`leanblueprint checkdecls` through Lake.

The original warmed-parent artifacts had previously been transiently removed
by another cache-seeding process. The verification baseline was preserved by
individual APFS file clones, with every public artifact matching its prior
recorded hash. Its interpreter companions were also preserved. Six checked QIC
helper and aggregator artifacts were added; all overlapping unchanged QIC
artifact hashes matched. `environment-preparation.json` records the exact
artifact selection. The initial verification base was `f96e06dc01118fd3778b58f197ac3dcb14c37e48`;
the subsequent parent update changed only archival evidence packaging.

Initial failed checks and superseded successful records are retained. Two long
fully qualified names in provenance notices exceeded the standard line limit;
the notices now use their API-documentation URLs. No linter was disabled. The
strict module and root checks and imported audit were refreshed after the
private extensionality refactor and again after the final empty-line correction.
The final records are identified separately from these initial checks.

The canonical provenance checker validates all 691 TNLean entries, including
77 new entries and the nine refreshed verifications. Its unchanged source and
schema are preserved under `canonical/`. From the repository root:

```bash
python3 docs/provenance/evidence/8769-source-physical/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python scripts/check_openai_provenance.py --root . --upstream-root /path/to/openai-math
```

The first command validates the recorded checks without compiling Lean. The
second requires the pinned manuscript in the supplied checkout. Recompilation
requires the recorded toolchain and exact dependency artifacts, or a fresh
canonical build with the published pins.

## Mathematical blueprint

The new chapter has all 77 declaration tags exactly once, with explicit
hypotheses and proof sketches. Full-source synchronization and the complete
blueprint dependency graph pass. The disposable source snapshot was compared
with the committed TNLean tree and the exact published QICLean tree.

The focused PDF contains 45 pages, including the preceding source-preparation
chapters. Every page containing the new chapter was visually inspected. Its
formulas, quantifiers, and tags are legible and have no overfull boxes. One
inherited 0.99057-point heading overfull box remains in the common-source
chapter. The focused web build and browser checks pass on seven pages and
3,719 typeset nodes. Exact render inputs, commands, source hashes, and logs are
retained. Only source files were copied into the disposable render directory;
no live build cache was modified.
