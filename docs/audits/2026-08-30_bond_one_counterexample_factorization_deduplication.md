# Bond-one counterexample factorization deduplication

## Scope

This audit concerns the one-sector physical factorizations used by two MPDO
counterexamples associated with CPSV16 Appendix C.2. It changes no mathematical
statement, neighboring operator, trace calculation, or public capstone.

## Removed declarations and replacements

Five declarations had no repository consumer beyond the displayed local
constructions and are removed:

- `MPOTensor.CaseIIAbsorptionCounterexample.scalarSectorEquiv` is the
  one-dimensional instance of
  `MPOTensor.BondOnePhysicalSectorFactorization.sectorEquiv`.
- `MPOTensor.CommutingBondTraceMatrixObstruction.oneSectorEquiv` is the
  two-dimensional instance of the same generic sector equivalence.
- `MPOTensor.NeighboringTraceObstructionAmbientBlocks.obstructionTerminalDecomposition_basisCount`,
  `..._copies`, and `..._weight` merely exposed fields of the reducible
  decomposition by reflexivity. Their sole consumer now supplies those
  definitional witnesses directly. The substantive `_basisDim` and `_basis`
  lemmas remain.

The public names `scalarFactorization` and `oneSectorFactorization` remain as
thin specializations of
`MPOTensor.BondOnePhysicalSectorFactorization.factorization`. Thus downstream
statements retain their exact types while using the common bond-one
construction.

A repository-wide search over Lean, Blueprint, documentation, scripts, papers,
and notes found no other consumer or Blueprint citation of the removed names.

## Import cleanup

`CaseIIAbsorptionCounterexample.lean` no longer imports the six modules named in
issue #7412. Its remaining three direct imports supply the declarations used by
the file. No generated import aggregator changes.

## Source and validation

The one-sector terminology and notation follow
`Papers/1606.00608/MPDO-22-12-17-2.tex:1381--1403,1441--1450`, in particular
the physical direct-sum factorization and the neighboring operators
$\eta_{k,h}$. Targeted linter-bearing builds cover all four changed Lean
modules; the root build, generated-import check, Blueprint synchronization and
declaration checks, forbidden-token check, and `git diff --check` form the
final validation set.
