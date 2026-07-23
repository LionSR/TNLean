# tenkz catalogue-demolition record

The blueprint now uses native tenkz bodies. The former central catalogue,
its TeX support tree, and its per-command web registry have been retired.
This file records the completed transition and the checks that keep it
complete.

## Final pre-removal census

The exact post-migration base contained seven tracked files and 2,353 lines in
the retired TeX tree. The four registry-pipeline files contained 2,831 lines:
2,191 in the web registry, 3 in its style stub, 252 in its reference checker,
and 385 in its static-page builder. The two-line web template owned by that
pipeline was a separate orphan and is not included in the four-file total.

Earlier planning documents quoted larger snapshots from before the non-PEPS
and PEPS migrations. Those numbers were not the demolition baseline.

## Completed removals

- [x] The seven-file TeX tree and its loader were removed.
- [x] The four registry-pipeline files and orphan web template were removed.
- [x] Print and web entry points load tenkz directly.
- [x] Build paths and workflow filters point at the native package.
- [x] Chapter figures are inline native bodies or exact mathematical formulas.
- [x] The catalogue-era diagram-grammar policy was retired.
- [x] The manual, examples, adopted corpus, linter, event audit, and generic web
      renderer are the maintained validation surfaces.

## Persistent exit gates

The completed state is guarded by repository-wide literal scans: chapter
sources contain no catalogue-era calls, and build configuration contains no
retired package path or registry entry point. Changes to the package or its
clients also run the native source lint, targeted regressions, the adopted
compile-and-audit corpus, manual compilation, and print/web smoke tests.

The migration changed ownership, not the mathematical standard. Each diagram
still carries an adjacent source/formula comment, ink-to-index explanation,
contraction account, and boundary signature. Print and web output must be
inspected whenever the visible figure changes.
