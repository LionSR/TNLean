# Physical string order: projective convention and import owners

## Physical and virtual predicates

`MPSTensor.HasPhysicalStringOrder` now requires its unitary physical twist to
be nonscalar: `∀ c : ℂ, u ≠ c • 1`. This is an explicit correction to the
literal `u ≠ 1` printed in arXiv:0802.0447, lines 114–121. The definition's
own documentation states the correction. There is one global physical
predicate; standalone existential propositions express the literal source
condition when testing scalar phases.

The fixed-endpoint predicate `HasPhysicalStringOrderWith` is unchanged.
The fixed-twist virtual-boundary predicate `HasStringOrder` is also unchanged;
its symmetry examples legitimately include the identity group element. Their
prose now identifies virtual-boundary nondecay explicitly rather than calling
it the physical endpoint assertion of the source's Theorem 1.

The two existing global physical consumers are
`akltPGWSVC08_hasPhysicalStringOrder` and
`clusterBlockedRMP_hasPhysicalStringOrder`. The AKLT twist has distinct
`0,0` and `1,1` entries, and the cluster twist has a nonzero `0,3` entry.
Their original physical correlators are retained.

## Direct import owners

`StringOrderDefs` used none of the seven declarations in
`TNLean.Spectral.TransferOperatorGapInjective`. Its actual requirements from
that import were:

- `Kraus.mixedMapLM` and `Kraus.mixedMapLM_apply`, owned by
  `QICLean.Kraus.MixedMap`
- `pow_tendsto_zero_of_spectralRadius_lt_one`, owned by
  `QICLean.Analysis.SpectralRadiusPowerDecay`
- The matrix operator-norm structures, owned by
  `QICLean.Algebra.MatrixOperatorSpace` and selected with `TNOperatorSpace`,
  replacing their incidental availability through the spectral `Kraus` scope

The same file used no declaration from `TNLean.MPS.Symmetry.Defs`; its tensor
vocabulary is supplied by `TNLean.MPS.Defs`. The direct importers outside the
generated aggregator are `StringOrder`, `StringOrderAux`,
`PhysicalStringEndpoints`, and `AKLTPhysicalStringOrder`. None uses an export
of the removed injective spectral leaf. `StringOrder` does use
`modulus_one_eigenvalue_implies_gauge_of_irreducible_TP`, so it imports its
actual owner `TNLean.Spectral.TransferOperatorGapNT` directly. Its
`twistedTensor` and `IsOnSiteSymmetric` uses remain supplied by the existing
`VirtualRepresentation` import.

At base commit `046cf8e2eadf06d8dc2d194f701baa65047cfe2e`, recursively following
real TNLean/QICLean imports with comments removed gives:

- `StringOrderDefs`: 106 reachable TNLean/QICLean modules before, 21 after
- `StringOrderScalarPhase`: 211 before, 210 after, because the full proof
  independently needs the irreducible spectral theory

These are structural module counts, including each target and excluding
Mathlib and toolchain modules. No timing comparison was made. No declaration
or theorem signature was changed by this import correction, and no library
fact was copied into a tensor-network module.

## Irreducible rigidity without the legacy symmetry layer

The source-canonical selection and endpoint modules need only two declarations
from `StringOrder`: `twistedTransfer_eigenvalue_norm_le_one_of_irreducible` and
`twistedTransfer_modulus_one_implies_gaugePhase_of_irreducible`. Their complete
declarations, including signatures and proof bodies, move byte-for-byte into
the existing `StringOrderAux` owner. No new declaration family or aliases are
introduced. `StringOrder` still reexports them through its existing import.

The auxiliary owner directly imports `Core.TPGauge` and
`Spectral.TransferOperatorGapNT`; the second moved proof retains its original
`Kraus` norm scope locally. `PureTwistedSpectrum` now imports `StringOrderAux`
instead of the legacy on-site symmetry/SPT owner. The independent virtual
symmetry and SPT APIs are unchanged.

On the integrated endpoint/phase source graph, recursively counted TNLean and
QICLean modules change as follows, with Mathlib/toolchain modules excluded:

- `PureTwistedSpectrum`: 181 to 172
- `PhysicalStringPhase`: 200 to 191
- `StringOrderScalarPhase`: 210 to 201
- `PhysicalStringBlockOrder`: 211 to 202

The nine removed modules comprise the legacy `StringOrder`,
`VirtualRepresentation`, `GaugeUniqueness`, symmetry definitions, the
projective/cocycle/list/cyclic-trace owners, and QICLean's `ScalarCommutant`.
These are source-closure measurements, not timing estimates. The declaration
hashes and unique destination sites are recorded in the adjacent extraction
JSON. Actual-import validation of the moved declarations and reverse
consumers remains required.
