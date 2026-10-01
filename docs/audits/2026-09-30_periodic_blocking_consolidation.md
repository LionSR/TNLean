# Prescribed periodic blocking: one implementation

The new `BlockingDecomposition.lean` duplicated existing results in
`StateVectorDecomposition.lean` and `PrescribedBlocking.lean`.
The latter already constructs the same cyclic projections, compressed blocks,
nonzero dimensions, supporting isometries, and all-length MPV equality, and
proves the quotient period whenever the blocking length is positive.

The duplicate declarations `MPSTensor.IsPeriodic.exists_paper_cyclic_projections`
and `MPSTensor.IsPeriodic.exists_periodic_stepOrbit_decomposition` are removed.
Their replacements are `MPSTensor.exists_paper_cyclic_projectors_of_isPeriodic`
and `MPSTensor.IsPeriodic.exists_stepOrbit_blockDecomposition`, respectively.
The existing positive-length implication in the latter is specialized at the
consumer's `hp`; no mathematical premise is added.

`IrreducibleFormBlocking`, `OrbitUnitary`, and `RefinementNormalization` use this
single implementation. The duplicate blueprint theorem is removed and its
references use the existing prescribed-blocking entry. Paper-gap references
point to the surviving declarations. No compatibility aliases are retained: TNLean has no
stable public API, and every local consumer is migrated in the same change.
