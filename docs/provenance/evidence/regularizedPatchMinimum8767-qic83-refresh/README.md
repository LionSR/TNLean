# QIC83 minimum prose refresh

These records bind the 24 regularized-minimum declarations to immutable source
`bb3043de9849792685781949ddc2aca8e711fda5`, with accepted QICLean
`83fdc804bb0ce258a41d32ecb1063e0c7fa8b84c`.

The change removes six words from docstrings, three blueprint comment lines
and a duplicate canonical conjugator import. Declaration/proof tokens and
the import set are unchanged. The source hashes are new; the byte-level
provenance guard correctly required fresh checks. The initial guard refusal
is retained in `initial-prose-checks-and-byte-gate.json`.

`checks.json` records four actual serial Lean invocations: the revised core,
both regression modules and the 24-name axiom audit. Each invocation has a
90-second limit, package options, standard linters and warnings as errors.
All four pass, and their pre/post source closures are unchanged. Successful
silent compiler logs are empty. `public-axioms.raw.txt` is copied unchanged
from the new compiler output; all 24 reports contain only the standard
`propext`, `Classical.choice` and `Quot.sound` axioms.

`source-artifact-audit.json` binds 71 source/artifact pairs. The 69 seeded
artifacts were admitted only after matching the exact QIC83/TN source bytes
and the original successful command/artifact records. Their original records
are retained in `seed-origin-records.json`. No Lake traces were fabricated,
and no Mathlib cold build or full Lake build was run.

The original QIC378 evidence remains unchanged in
`../regularizedPatchMinimum8767/`. Its original immutable source, dependency
pin and hashes remain historical. Only the 24 active minimum rows are rebound
to this new source. The other provenance shards and all old raw evidence are
unchanged. The earlier a5 integration build is not relabelled as a build of
this refreshed head; fresh integration CI is still required.
