# Constructed ground-space bases under polynomial sphere growth

This contribution reuses the full-Hamiltonian basis construction preserved at
TNLean `1659116509dc8cec5d4a2aec8ddd131cc88da31d`. Its generic proofs now belong
to QICLean mathematical commit `1690919b` and documentation successor
`4a838eec6ab738edaa50190f34c5dc6d5eb78345`. The common providers remained
read-only at TNLean `7f87bdc8f1b2354be4950ad515dedda7ee9bec96` and QICLean
`ec3434f7d6fbdfc5318dc55934feb9532e239b81`. Dependency pins were not changed in
this source-only checkpoint; integration must use the companion contribution.

## Mathematical statement and scope

The theorem restricts actual local observables to the actual ground eigenspace,
uses the proved physical commutator estimate, and invokes the constructed
finite-dimensional basis. It assumes no basis, separated eigenvalue labels,
inverse-spacing lower bound or uniform condition number. Zero local terms are
allowed. Scalar terminal subspaces of any dimension are handled by the shared
recursion. Disconnected graph components have zero mutual decay kernel.

For fixed ground-space dimension n and fixed displayed local, gap and polynomial
sphere-growth parameters, the final sum is independent of the number of sites
and local terms. Its explicit coefficient contains
sqrt(n^3 C (1+2n^3)^n) and shell decay rate gamma/2^n. Neither uniformity in n nor
the printed sharper quantitative expression is asserted. The sphere-growth
hypothesis is additional to the unrestricted metric source statement, and is
explicit in the theorem, its separate blueprint entry, and the physical note.

The operators in this checkpoint are original terms filtered under the full
Hamiltonian. Their ground-space compressions equal the original compressions.
Hastings's actual terms filtered under locally truncated generators require a
subsequent bounded physical step. The older conditional labelled-basis
estimates are retained as distinct auxiliary statements, not used to assume
the conclusion of the new construction.

The two old generic definition-bearing TNLean modules LowEnergyBasis and
LowEnergyBasisSimpleSpectrum are deleted. Their consumers, imports and blueprint
tags now use the single companion definitions in ApproximateDiagonalization.
There are no compatibility aliases. The conditioned quotient-map construction
is not imported or added. The other existing physical statements are unchanged;
LowEnergyCommutatorSum only reuses the preserved weight-budget refactor.

The complete tree-counterexample note is preserved verbatim from 1659116509dc.
It gives a mathematical argument and explicitly says that the full family,
its gap and the divergent every-basis sum are not formalized in Lean. Its partial
Lean certificates were not adopted and are not cited as proving the complete
counterexample. The generic cross-term/rate correction has its own QIC-owned
note; the TNLean basis note concerns the physical growth restriction and cites
the companion note by its published URL.

## Verification

All eight actual named TNLean modules passed private strict checks, with implicit
variables disabled, Mathlib standard linters and warnings as errors. All 80
public declarations in these modules were imported and inspected; only
propext, Classical.choice and Quot.sound occur. The companion's nine modules
and all 85 public declarations passed their separate strict/foundation checks.
The 94 selected provider source/object pairs and own imported sources/objects
were guarded before and after checks. No shared source, cache or build object
was changed. No Lake environment was initialized, no artifact was copied, and
no Mathlib source was built. Temporary output objects and manual inspection
commands live outside the repositories.

The first final-module attempt overlapped removal of a duplicated import and
therefore does not certify the final source hash. It was followed by a successful
unchanged-source check of the exact final module (hash below). Earlier extraction
errors were fixed before these final checks; no proof holes remain.

Source blueprint synchronization and the added-prose check passed. The source
checker resolved the companion to its isolated source tree and Mathlib to the
existing provider source, without creating package checkouts. The imported
foundation inspection checks every new declaration name against actual compiled
modules. Compiled blueprint and ordinary/full-library gates remain pending
integration. The new chapter follows ch35_hastings_local_projective_form.

Private physical wall times were 19.79 / 20.36 / 15.37 / 86.72 / 31.45 / 15.72 /
20.29 / 64.60 seconds in dependency order. The long checks coincided with about
39 host Lean processes and heavy CPU contention, independently observed by root.
These are retained as evidence, not quiet compilation measurements. The mandatory
changed-module timing gates remain to be run under sufficiently quiet conditions;
no threshold was raised and no timing-only repeat was performed.

Evidence: /tmp/tnlean-hastings-basis-physical-checks.log,
/tmp/tnlean-hastings-basis-final-physical-check.log,
/tmp/tnlean-hastings-basis-physical-foundation-audit.log,
/tmp/tnlean-hastings-basis-private-provider-guard-v2.json,
and /tmp/tnlean-hastings-basis-blueprint-sync.json.

## Exact checked mathematical sources

- `TNLean/Lattice/GraphDegreeGrowth.lean`: `a51d6b90613667f6d3fe2853ee8492e3eba66272d6236d1d8ec0ab198b022f33`
- `TNLean/Lattice/GroundSpaceCompression.lean`: `1d8a777485bac97fdb6da98bffc9c8b41ee5f6bb0e87b6e80e7c8862f8e3a0f1`
- `TNLean/Lattice/LowEnergyBasisIteration.lean`: `4404f8741195a7dd61029f9e7d3acf30d68db09c026f3710e265874819578ace`
- `TNLean/Lattice/LowEnergyBasisUniformGeneral.lean`: `9825c00dbfd3083263e9b27f104452630a1c0ac115f73ea9f2d6363cbed710f1`
- `TNLean/Lattice/LowEnergyCommutator.lean`: `c4fc717c94b62a7c2b8e82b8c063c7e1b5db857727efb35cf22fa7ab68f2fc0b`
- `TNLean/Lattice/LowEnergyCommutatorSum.lean`: `26b5cab34e69f7f7f4c55ca73c67716f48297da1a6ae241af93e095eab3bb163`
- `TNLean/Lattice/LowEnergyDecayKernel.lean`: `b3f4d089daadae0bb22038bf73331eb93e9020c49192126ddefcfdbe535e7210`
- `TNLean/Lattice/LowEnergyWeightedRowSum.lean`: `ef45f8eb6017e1dd87eea31e583868b22f98a347f5112de9a1196a10158b0fd9`
