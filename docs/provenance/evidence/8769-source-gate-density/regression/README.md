# Density expansion regressions

The four statements in `SourceGateDensityRegression.lean` were compiled against
exact source revision `86ed134591132d21ab3046d504e84196e2ee5ec6`, with the package
options and warnings treated as errors. The imported axiom audit contains only
`propext`, `Classical.choice`, and `Quot.sound`.

The one-slot calculation uses actual identity operations and prescribed
orthonormal memory bases. Its ket index is `Unit × Unit`, while its bra index is
`Bool × Unit`. All supplied endpoint vectors lie in a proper coordinate
hyperplane of the three-dimensional halfspace. The bra coefficient `I` becomes
`−I` after taking the adjoint. The statement holds for every input matrix; a
separate matrix-unit example verifies that the chosen test input is not
Hermitian.

The empty-slot calculation applies the weighted gate density theorem to two
identity branches with coefficients `1` and `I`. It proves that their output is
`2 • ρ` for every complex matrix `ρ`, including the empty product and the unique
empty coordinate assignment. It imposes no positivity or normalization premise
on `ρ`.

The commands and source/artifact hashes are recorded separately. Compilation
and its outputs used only temporary paths. No Lake command or cache mutation
was performed. These are focused regressions, not a full package build.
