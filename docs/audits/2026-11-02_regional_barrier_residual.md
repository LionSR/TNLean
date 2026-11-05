# Regional residuals with an arbitrary commuting interior

The contribution exposes the existing weighted hard-tail argument with separate projection
threshold and projection floor. A second result composes it with the existing positive-matrix
soft–hard restricted-norm comparison. The local conjugation estimate still uses the original
nearest-neighbour terms. The interior may contain functions of other regional Hamiltonians.

The former private hard-tail proof in `SoftTruncationReverseResidual` is removed and its
existing exact-center physical theorem uses the shared declaration. Its public statement,
physical construction and residual constants are unchanged. No alternative compatibility
wrapper or additional hypothesis is introduced in that theorem.

These are auxiliary estimates supporting ALVV, arXiv:1602.08828v2,
`lem:exp-approx`, lines 1195–1255, and `t:aisefficient`, lines 1373–1392.
The generic theorem explicitly requires commutation and a projection floor. The physical
application is responsible for deriving them. This contribution does not complete the
simultaneous estimated-center construction, the efficient-filter theorem, or the printed
uniform energy estimate. The false cluster estimate and its counterexamples are unchanged.

## Verification

Strict private actual-module checks used the fully warmed immutable TNLean provider
`d316e8cbe52bd5f12bcfbeec687d1dbef7633586` and its own QICLean package
`d1317fdb229a1048cc65ec5ab1912403ab6bcbc0`. Selected source and object hashes,
both package configurations, warmed Mathlib and changed-importer closure were guarded.
Outputs were written only under `/tmp`; no dependency or production cache was modified.
The shared module passed in 4.855 seconds and its existing consumer in 6.660 seconds.

An imported foundation audit checked both new public declarations and
`exists_single_region_soft_truncation_residuals`; it passed in 4.354 seconds.
All three depend only on `propext`, `Classical.choice` and `Quot.sound`.
The audit commands remain temporary and are not part of the repository.
Whitespace, generated imports and added-prose checks pass. The full source-to-blueprint
scan in the source-only worktree cannot discover the absent dependency checkouts; its
564 unresolved references are not a compiled declaration check. Ordinary combined builds,
the dependency-aware source scan and compiled blueprint checks are required after adoption.
