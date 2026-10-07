# Verification of the finite exponent improvement

The ten declarations in `8756-bootstrap.json` were verified at source revision
`d62f169decd531ac3c8b770d847431c6a9099fa5`. They give the fixed scalar exponent
inequalities and the finite iteration used in the safe-box estimate. The analytic
improvement is a hypothesis of the iteration theorem; its proof remains separate.

This revision corrects the inline mathematical notation in the docstrings and
adds a module header to the axiom-audit script. Every theorem statement and proof
body is unchanged. The exact committed bytes of `Geometry/Exponents.lean`,
`Scan/BootstrapParameters.lean`, and `Scan/ExponentBootstrap.lean` were compiled
into a temporary directory, followed by the imported-declaration axiom audit.
`8756-bootstrap-direct-build.log` records all three successful compilations;
`8756-bootstrap-axioms.log` records those compilations and the successful audit.
The provenance build command denotes direct Lean module compilation. No local
Lake build or CI build of this corrected source revision is claimed.

The Lean toolchain and Mathlib manifest pins were checked against the committed
source. Mathlib was clean at `c55e6e786f49471c72fbddbec5415808896aec1e`, and all
Mathlib dependency pins matched. The import path contained only the temporary
compiled modules, Mathlib and its dependencies, and Lean itself. All generated
artifacts stayed outside the repository. The logs preserve the actual executable,
commands, import path, source SHA-256 values, elapsed times, and exit statuses.

All invocations used the package options explicitly and enabled
`-DwarningAsError=true`. The audit alone also used `-Dlinter.hashCommand=false`,
because its purpose is to execute `#print axioms`. The three source compilations
and the audit returned zero without diagnostics. All ten declarations depend only
on `propext`, `Classical.choice`, and `Quot.sound`. The provenance entries record
the exact revision, actual commands, and SHA-256 hashes of the current logs.

The retained CI evidence concerns the earlier source revision
`c8dda1255e76316961e66d98b795a078ab9468b1`, before the docstring correction.
[GitHub Actions job 112855574904](https://github.com/LionSR/TNLean/actions/runs/37639834213/job/112855574904)
passed the full `lake build`, text style check, blueprint declaration generation,
and compiled blueprint declaration check. Its checked-out merge revision
`71c40dacdf706b87df3c8b5cca405ea99e3aa251` has the same Git tree as that earlier
source revision: `59f8297d04461fcda2f0aa8c38a0ba7b6021d1aa`.
`8756-bootstrap-ci-build.log` and `8756-bootstrap-ci-declarations.log` preserve
the complete relevant steps as historical evidence. The current verification
records use the new direct compilation and imported audit above.
