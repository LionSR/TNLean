# Verification of the finite exponent improvement

The ten declarations in `8756-bootstrap.json` were verified at source revision
`c8dda1255e76316961e66d98b795a078ab9468b1`. They give the fixed scalar exponent
inequalities and the finite iteration used in the safe-box estimate. The analytic
improvement is a hypothesis of the iteration theorem; its proof remains separate.

The full library build passed in [GitHub Actions job 112855574904](https://github.com/LionSR/TNLean/actions/runs/37639834213/job/112855574904).
The job records head revision `c8dda1255e76316961e66d98b795a078ab9468b1` and checked
out merge revision `71c40dacdf706b87df3c8b5cca405ea99e3aa251`. Fetching that merge
commit and comparing both trees with `git rev-parse <revision>^{tree}` gave the
same tree, `59f8297d04461fcda2f0aa8c38a0ba7b6021d1aa`. Thus the CI build used exactly
the recorded source tree. Its full build step is retained in
`8756-bootstrap-ci-build.log`, including the actual `lake build` command and
successful completion. Existing dependency warnings remain in the log.

The same job successfully ran the following commands. Their complete step output
is retained in `8756-bootstrap-ci-declarations.log`.

```bash
lake exe lint_style --github
python3 scripts/blueprint_lean_sync.py --root . --update-lean-decls
lake exe checkdecls blueprint/lean_decls
```

The imported-declaration axiom audit was performed separately by compiling the
exact committed bytes of `Geometry/Exponents.lean`, `Scan/BootstrapParameters.lean`,
and `Scan/ExponentBootstrap.lean` into a temporary directory. The primary worktree's
Lean toolchain and Mathlib manifest pins were checked against the committed source;
Mathlib was clean at `c55e6e786f49471c72fbddbec5415808896aec1e`. All Mathlib dependency
pins also matched. The import path contained the temporary compiled modules,
Mathlib and its dependencies, and Lean itself. It excluded other TNLean and QICLean
compiled modules. All generated artifacts stayed outside the repository.

`8756-bootstrap-axioms.log` preserves the actual executable, commands, import path,
source SHA-256 values, elapsed times, and exit statuses. Each Lean invocation used
`-Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dlinter.mathlibStandardSet=true
-DmaxSynthPendingDepth=3`; the package's weak linter default was supplied explicitly.
All three source compilations and the unchanged committed audit script returned
zero, taking 86.444 seconds in total. This was direct Lean compilation; the full
Lake build evidence is supplied by CI.

All ten declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`.
The audit script emitted a header-style warning because it has no module docstring;
that warning is retained in the log. The three mathematical modules emitted no
diagnostics. The source modules and audit script were kept unchanged. Each of the
ten provenance entries records the actual build and axiom commands and the SHA-256
hashes of their evidence logs.
