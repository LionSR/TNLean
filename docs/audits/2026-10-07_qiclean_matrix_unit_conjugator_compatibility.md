# QICLean matrix-unit conjugator compatibility

The QICLean upgrades used by the PEPS conditional-information and regularized
patch-minimum work expose a duplicate declaration when the full TNLean import
closure is loaded. `TNLean.MPS.Symmetry.LocalVirtualGauge` and
`QICLean.Algebra.MatrixUnitConjugator` both declared these three names:

- `Matrix.matrixUnitConjugator`
- `Matrix.matrixUnitConjugator_eq_smul`
- `Matrix.matrixUnitConjugator_intertwines`

## Ownership and preserved mathematics

The generic construction belongs to QICLean. TNLean now imports that module and
removes only its duplicate declaration block. Each removed definition, theorem
statement, proof, and docstring is byte-identical to the canonical block at both
QICLean revisions:

- `826a56f5d2a3d0c5b5027c4ab536d24feadbdbb6`
- `378bef486fc0241dee8ad875ccaf659d51d33ac9`

The canonical module SHA-256 is
`1521a4d6320e0df379c2ff6580e6dd835cf3667f068e7db12ab7387b06820493`.
All three public names remain available through the existing TNLean import.
No compatibility alias, hypothesis, proof, or tensor-specific declaration is
added or changed. Existing blueprint declaration references retain their names.

The direct TNLean importers are `TNLean.MPS.Symmetry.GlobalVirtualGauge` and the
`TNLean.MPS.Symmetry` aggregator. The generic differentiable-action consumer in
QICLean and the continuous local/global gauge consumers in TNLean are checked
together by `TNLeanTest/QICConjugatorCompatibility.lean`.

## Validation

Fresh, serialized Lean elaboration passed with package-equivalent strict options,
Mathlib standard linters, warnings as errors, one thread, and a 90-second limit
per module for the canonical conjugator, its differentiable-action consumer,
TNLean's local and global gauge modules, and the mixed-import regression. The
regression also passed against the newer QICLean pin. All 41 production sources
in its import closure match the regularized-patch worktree after applying this
same one-file compatibility change.

As a negative control, the original local module was freshly compiled in an
isolated overlay. The same regression then failed with the original duplicate
`Matrix.matrixUnitConjugator` error. This demonstrates that separately compiling
the original modules would have missed the regression.

An axiom audit of the three canonical declarations and all 16 public local/global
gauge declarations found only `propext`, `Classical.choice`, and `Quot.sound`.
A comment-stripped, non-Archive source scan found no further cross-library public
declaration collisions at either pin. This textual scan includes explicit
declarations and structure projections; it is not a kernel inventory of all
generated names.

Import-generator tests (9), Lean file-policy tests (16), import completeness, and
workflow ordering/strict-option checks passed. The CI regression runs after the
ordinary full build, with the same strict options and 90-second limit. The local
checks reused source-and-artifact-audited dependency outputs and prebuilt Mathlib;
they did not run a full `lake build`. Full aggregate verification remains the
ordinary CI build gate. No unrelated String Order or converse work is included.
