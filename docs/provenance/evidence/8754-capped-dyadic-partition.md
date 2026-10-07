# Capped dyadic partition verification

Scope: the finite maximal-contained dyadic-square partition step in
`scanner:templates`, source lines 639–649 of `08-scanner.tex`, pinned to
`openai/math@adc7f1241b42e322a6451854ab7e4b4c146bf78a`.

These are original proofs from the manuscript. The existing TNLean dyadic
grid, parent, ancestry and refinement APIs from #8837 are reused unchanged.
The branch is stacked on #8837 at `4e12e35eb90436f776d998345950e70bfdce68b2`.
Claims on #8754, #8758 and #8837 were inspected; scope was announced in
#8754 comment 6044978027 and #8837 comment 6044979072. The separately owned
#8798/#8826/#8832/#8840 proofs are unchanged.

## Current evidence

Kernel verification, regression elaboration and exported axiom results are
pending normal draft-PR CI. The new provenance records are `planned` with
pending verification, and the separate blueprint entries have no `leanok`.

The selected Linux workspace began without Lean or `.lake`. The pinned Lean
4.35.0-rc3 release was installed from GitHub; all dependency source checkouts
match `lake-manifest.json`. `lake exe cache get` built only the cache client,
then the default `cache.mathlib.org` server returned HTTP 403 for the prebuilt
artifacts. A read of the supported Azure cache endpoint also returned HTTP
403, including with sandbox escalation. No Mathlib proof source build was
started. No local Lean proof success is claimed.

The CI workflow first builds the new production module with package options,
then retains the full library build and runs strict regressions and all 23
exported declaration axiom prints. Regressions cover empty sets, zero cap,
negative coordinates, mixed scales, disconnected sets, holes, and containment
of parents above the cap. Exact guarded axiom output will be added only after
observing a successful audit.

The mixed-square count for actual templates, safe-square clearance, entropy
subadditivity and dyadic entropy summation remain separate. This contribution
does not complete Lemma 9.4, #8754 or either headline manuscript theorem.
