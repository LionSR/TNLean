# Deterministic source corrections

The 67 declarations in `declarations.json` are verified at source revision
`f932b80f1b67668584120403b983be0633f62602`, with QICLean pinned to
`4be0ef429c5048cf1bf4f5b7afd5b9f7b9361ca0`. They formalize the deterministic
corrected-subset expansion in the proof of Theorem 5.2 of the September 24, 2026
polynomial-PEPS manuscript, `04-compression.tex`, label
`eq:compression-subset-expansion`.

The corrected term is defined on original source occurrences before any set of
affected parties is chosen. Substitution depends only on an occurrence and its
own gate's branch label. When several selected sources belong to one gate,
compatibility of their labels is enforced without repeating the gate coefficient.
The partial expansion retains exterior aggregate gates. Its canonical remaining
operation is independent of substitutions whenever both-exterior source vectors
are unchanged. Exact ordered inventory identities identify its source coordinates.

Finite coordinate expansion then identifies the corrected term with the existing
multilinear source contraction. The density obtained by local source-operator
replacement is defined independently of the corrected-subset sum. Its difference
from the exact density is proved to equal the sum over nonempty sets of original
source occurrences. The same identity holds after tracing the retained discarded
registers, and the trace-norm triangle inequality gives the corresponding sum of
norms. Finite input and output orthonormal bases are explicit; the manuscript's
finite-dimensional convention is cited, and no bound on private dimensions is
introduced. Gaussian sampling and quantitative bounds for individual corrected
terms are separate contributions.

## Lean verification

The complete affected import closure consists of 35 modules, including the 16 new
modules, four inherited proof refactors and the root aggregators. All 35 were
compiled directly with the package options and `warningAsError=true`; every check
succeeded without diagnostics. Their total recorded time is 241.528 seconds.
`strict-checks/build-commands.json` and `direct-build.log` record the actual commands,
source hashes, output hashes and durations. These are direct Lean checks against
existing pinned artifacts, not a Lake build or a CI measurement. No package cache
or dependency pin was changed.

The importing audit covers all 67 new declarations and all 24 public declarations
in the four refactored files. Their only axiom dependencies are `propext`,
`Classical.choice` and `Quot.sound`. The 14,632 imported artifact hashes were
rechecked unchanged when the source commit was pinned. A separate direct Lean
check of the complete root environment found all 20,877 names in the synchronized
blueprint declaration list. This is a compiled declaration-presence check, not an
invocation of `leanblueprint checkdecls` through Lake.

The new files preserve the noncomment tokens of the previously checked proofs.
The source-preservation records and compressed original sources document this
comparison. The four inherited refactors replace repeated owner-support and
rectangular matrix-sum proofs by the two shared lemmas. Their statements and
hypotheses are unchanged. Independent source review is recorded separately.

## Provenance preservation

The new shard contains 67 original formalizations. In the inherited shards, only
the verification records of the 24 declarations in the four changed source files
are updated to the new exact bytes. All previous evidence remains unchanged.
The preceding shard contents and their verification records are retained here in
`historical-shards/` and `inherited-verification-history.json`.

The full canonical provenance check is recorded in `full-provenance-command.json`
and `full-provenance.log`. It scans the entire current declaration-notice collection,
including all 585 entries in the new and inherited shards, against the pinned manuscript.
The checker and schema used for it are also retained in `canonical/`.

To validate the packaged evidence without compiling Lean, run from the repository:

```bash
python3 docs/provenance/evidence/8769-source-corrections/validate-evidence.py --root .
uv run --no-project --with jsonschema==4.26.0 python scripts/check_openai_provenance.py --root .
```

Supplying `--upstream-root` to the second command also rechecks the pinned
manuscript objects. This was done in the recorded full check. The scripts in
`verification-scripts/` retain the actual isolated compiler commands and source
checks; their absolute paths describe the verification environment at execution.
Recompilation requires the pinned Lean toolchain and corresponding dependency
artifacts. The evidence validator does not fetch or rebuild them.

## Blueprint verification

All 67 new declaration tags occur exactly once. Full-source synchronization
passed against the exact TNLean commit and the exact pinned QICLean sources.
The report contains 20,870 blueprint reference entries; the generated declaration
list checked in Lean contains 20,877 names. The complete dependency graph has
7,679 nodes and 18,882 edges, with no cycles or duplicate labels.

The focused PDF includes the preceding eleven source chapters and the new chapter,
for 34 pages in total. Every page of the new chapter, PDF pages 29–33, was visually
inspected. The focused web build has no warnings, and the browser check passed
on seven pages with 2,972 typeset elements. Its focused configuration is retained
alongside the original full configuration. The canonical formatter was applied
and checked for idempotence.

The initial PDF had a 10.95 pt overfull line in the new introduction; the prose was
shortened and the PDF, web and browser checks were repeated. Both sets of records
are retained. The final PDF has one inherited 0.99057 pt overfull heading in the
common-source chapter; the new chapter has none. This verification does not claim
a full-book render. Source hashes, exact commands, the final PDF and page images
are recorded under `blueprint/`.
