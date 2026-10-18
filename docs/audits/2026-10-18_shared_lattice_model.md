# Shared finite-lattice model for the area laws

## Scope

The finite-domain model of the area law is stated for an arbitrary finite
domain `Λ : Finset (ℤ × ℤ)` and uses no rectangle, template or dyadic
construction. The one-dimensional area law (`TNLean/MPS/AreaLaw/`) and the
two-dimensional one (`TNLean/PEPS/AreaLaw/`) both use it, so it moves to a
neutral layer, `TNLean/Lattice/`, with namespace `TNLean.Lattice`. This is the
first phase of issue [#9534](https://github.com/LionSR/TNLean/issues/9534).

No statement or proof changes. Every consumer imports the new modules and
opens `TNLean.Lattice`, or names the declarations with the new qualifier.
No deprecated alias, compatibility module or `export` is kept.

The two-dimensional target `UniformAreaLaw` stays in
`TNLean/PEPS/AreaLaw/TheoremStatements.lean`. The graph counting modules
(`GraphExtendedMetric`, `GraphLatticeDistance`, `GraphInteractionBudget`,
`GraphLatticeDiamond`, `GraphInteractionDiamondCounting`) and the
one-dimensional chain model `ChainHamiltonian` are not part of this phase.

## Module paths

| Old module | New module |
| --- | --- |
| `TNLean.PEPS.AreaLaw.FiniteDomain` | `TNLean.Lattice.FiniteDomain` |
| `TNLean.PEPS.AreaLaw.LocalHamiltonian` | `TNLean.Lattice.LocalHamiltonian` |
| `TNLean.PEPS.AreaLaw.TheoremStatements` (regional states and entropy) | `TNLean.Lattice.RegionalEntropy` (new) |
| `TNLean.PEPS.AreaLaw.MarginalTails` | `TNLean.Lattice.MarginalTails` |
| `TNLean.PEPS.AreaLaw.RegionalEntropyBridge` | `TNLean.Lattice.RegionalEntropyBridge` |
| `TNLean.PEPS.AreaLaw.TwoFamilies` (the two finite-product identifications) | `TNLean.Lattice.RegionalEntropyBridge` |
| `TNLean.PEPS.AreaLaw.EntropyDimension` | `TNLean.Lattice.EntropyDimension` |
| `TNLean.PEPS.AreaLaw.ProductGroundState` | `TNLean.Lattice.ProductGroundState` |

`TNLean.PEPS.AreaLaw.TheoremStatements` keeps only `UniformAreaLaw`, and
`TNLean.PEPS.AreaLaw.TwoFamilies` keeps its seven declarations on ordered
two-family partitions. `TNLean.Lattice.EntropyDimension` no longer imports the
template geometry; the modules that used that geometry through it now import
`TNLean.PEPS.AreaLaw.TwoFamilies` directly. `TNLean/MPS/AreaLaw/` imports
nothing from `TNLean/PEPS/`.

## Moved declarations

Each name `TNLean.PEPS.AreaLaw.X` below becomes `TNLean.Lattice.X`.

| Module | Declarations |
| --- | --- |
| `FiniteDomain` | `Site`, `Configuration`, `domainGraph`, `IsAdmissibleSupport`, `AdmissibleSupport`, `graphNeighborhood`, `edgeBoundary`, `ambientDilation`, `mem_ambientDilation_iff`, `configurationSplit`, `card_configuration`, `edgeBoundary_empty`, `edgeBoundary_univ`, `isAdmissibleSupport_singleton`, `exists_walk_length_le_iff_edist_le`, `isAdmissibleSupport_zero_iff`, `isAdmissibleSupport_pair_of_adj`, `exists_edgeBoundary_of_walk`, `ambientDilation_zero`, and the two anonymous instances (decidable adjacency of `domainGraph`, finiteness of `AdmissibleSupport`) |
| `LocalHamiltonian` | `StateSpace`, `LocalHamiltonian` with its fields `term`, `supported`, `hermitian`, `norm_le`, `LocalHamiltonian.operator`, `LocalHamiltonian.operator_isHermitian`, `LocalHamiltonian.zero`, `localLift`, `localLift_mem_supportedOperators`, `IsGappedGroundState` |
| `RegionalEntropy` | `reducedState`, `reducedState_posSemidef`, `reducedState_isHermitian`, `regionalEntropy` |
| `MarginalTails` | `partialTraceRight_cutVector`, `cutLogBudget`, `concentrationWidth`, `LocalHamiltonian.log_surprisalMoment_reducedState_le`, `LocalHamiltonian.surprisalTail_reducedState_le`, `LocalHamiltonian.one_sub_rpow_le_typicalMass_reducedState` |
| `RegionalEntropyBridge` | `reducedState_eq_regionState`, `regionalEntropy_eq_regionEntropy`, `localLift_eq_entropyLocalLift`, `card_regionConfig`, `reducedState_eq_finiteProduct`, `regionalEntropy_eq_finiteProduct` |
| `EntropyDimension` | `regionalEntropy_le_card_mul_log` |
| `ProductGroundState` | `exists_eq_mul_of_gap`, `vonNeumannEntropy_partialTraceRight_eq_zero_of_gap` |

`QuantumCircuit.isSupportedOn_of_mem_supportedOperators` moves with
`MarginalTails` and keeps its name.

## Renamed declarations that stay in place

These declarations extend the namespaces of moved types, so that dot notation
such as `hX.card_le` and `h.positiveTerm` keeps resolving. Each
`TNLean.PEPS.AreaLaw.T.x` becomes `TNLean.Lattice.T.x` in its current file.

| File | Declarations |
| --- | --- |
| `TNLean/PEPS/AreaLaw/GraphPropagation.lean` | `IsAdmissibleSupport.edist_le`, `IsAdmissibleSupport.card_le`, `LocalHamiltonian.normBound_nonneg`, `LocalHamiltonian.sum_norm_term_containing_le`, `LocalHamiltonian.anchors`, `LocalHamiltonian.anchors_mem`, `LocalHamiltonian.anchors_self` (the last three private), `LocalHamiltonian.norm_commutator_le_graphDistance`, `LocalHamiltonian.commutator_eq_zero_of_edist_eq_top`, `LocalHamiltonian.norm_sub_siteExpectation_graphBall_le` |
| `TNLean/PEPS/AreaLaw/TailParameter.lean` | `LocalHamiltonian.one_sub_rpow_le_typicalMass_edgeBoundary` |
| `TNLean/PEPS/AreaLaw/ZeroBoundary.lean` | `IsAdmissibleSupport.reachable` |
| `TNLean/PEPS/AreaLaw/Scan/ActualEnergyTerms.lean` | `LocalHamiltonian.positiveTerm` |

## Counts

- 46 named declarations change namespace (the list above, without the
  structure fields and the two anonymous instances), and one keeps its name.
- 13 declarations are renamed in place.
- The blueprint `\lean{...}` tags, `docs/glossary.md`, `docs/formalization/`,
  `docs/tactic_patterns.md`, `docs/import_structure.md` and the `CLAUDE.md`
  tables carry the new names.
