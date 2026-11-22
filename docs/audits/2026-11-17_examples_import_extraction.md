# Theory and worked-example import extraction

Issue: #10721. Original combined-tree build baseline: TNLean `612f8998752998486c6e080a427c65dc6a6847e7`, with QICLean `e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`.

## Review units

The six directory-scoped units are MPU, MPDO, Preparation, FundamentalTheorem, Symmetry, and PEPS. They are stacked in that order. MPU supplies the identity prerequisite for MPDO; MPDO supplies Core/GHZ for Preparation and Symmetry. The other ordering is for review and ratchet integration. No enforcement logic is added: merged #10740 already supplies all three ratchets.

### mpu

Extract binary configuration operations into `MPS/Tensor/Chain/BinaryPhase` and the identity MPU and source ranks into `MPS/Operator/Unitary/Identity` and `IdentitySourceRanks`. Retain the new QICLean ComplexSqrt import in ShiftSourceFactors. ClusterIsingSymmetry imports CZXUnitary explicitly.

### mpdo

Extract GHZ tensor/sectors into `MPS/Tensor/GHZ` and binary-group algebra into `Algebra/ZMod2Representation`. The three CZX consumers import those shared interfaces and the identity MPU introduced by the preceding partition.

### preparation

GHZSectorParent imports the shared GHZ tensor/sectors from the preceding partition.

### fundamental-theorem

Move arbitrary-tensor counterexamples, embedding sharpness, and the weighted counterexample consumer into Examples/MultiBlock. Keep the three old module paths as import-only compatibility modules.

### symmetry

Move the concrete CZX permuted-block, Z3 fusion, Ising fusion, and Kramers-Wannier demonstrations into their Examples directories. Keep the four old module paths as import-only compatibility modules and update direct example consumers.

### peps

Extract general-group dual quantum-double coordinates into PEPS/QuantumDoubleTensor. Keep the explicit TorusLatticeGraph and TorusOperatorString imports in the three downstream consumers.

At this point in the series, the checker records 0 example-import edges and 54 mutual-directory pairs. Each unit removes only entries that its source changes resolve.

## Compatibility semantics

Names and mathematical statements are preserved. The complete series keeps seven old module paths outside Examples as import-only wrappers: three under FundamentalTheorem/Arbitrary and four under Symmetry/MPOSymmetry. Thus seven literal outside-to-Examples imports remain in the final source. The upstream checker deliberately excludes import-only modules as importers and expands them when checking a declaration-bearing caller. Zero checker debt is not a claim of zero literal import statements. The seven paths under `TNLean/MPS/` are `FundamentalTheorem/Arbitrary/Examples.lean`, `FundamentalTheorem/Arbitrary/OneBlockSharpness.lean`, `FundamentalTheorem/Arbitrary/WeightedExamples.lean`, `Symmetry/MPOSymmetry/CZXPermutedBlocks.lean`, `Symmetry/MPOSymmetry/Examples.lean`, `Symmetry/MPOSymmetry/IsingFusion.lean`, and `Symmetry/MPOSymmetry/KramersWannierBimodule.lean`. Keeping historical module imports is an explicit design choice for compatibility, not a new exemption in the checker. The old Examples/ZMod2 path also remains as a wrapper importing library algebra.

## Historical combined validation

The combined extraction was tested before partitioning at staged tree `93c21ae17c50adeb6b31f509b3a640978cb2c231`: one Lake build of 92 targets covering 171 affected non-aggregator modules through 59 leaves, including changed compatibility paths, passed (21,219 jobs). All 40 changed handwritten/compatibility modules passed strict elaboration with automatic implicits disabled, synthesis depth three, Mathlib standard linters, and warnings as errors. The API audit retained all 453 public declarations and their headers, with 115 relocated.

These are combined-tree results, not independent builds of each intermediate branch. Each partition additionally checks its import layers, pass-through ratchet, generated aggregators, and whitespace. The full-root build, generated-aggregator elaboration, and standalone regressions remain for CI.

The tested base includes #10761 and #10748. Main later advanced to `55cab8718` with #10697; #10813 subsequently repaired its reported ShiftTildeSymmetricPhases build break. This series does not duplicate that fix. Active #10626 overlaps GroupCocycleMPO/Instances and the old CZXPermutedBlocks owner: retain its cohomology migration in the new owner when integrating. Other active code overlaps are generated aggregators; regenerate them rather than restoring stale imports.

## Latest-main reconciliation

The stack was rebuilt on `95f5970db777f4c2fd1e16d1ac36281b84f46aff`, including
merged #10813 and QICLean `e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`.
The former ShiftTildeSymmetricPhases failure is resolved by upstream; no repair
is duplicated in this campaign. External bot fixes on #10821 (`6d6d0dc0`) and
#10822 (`5c528061`) repeated that repair with local proof differences; both were
inspected and preserved in backup refs before using the canonical upstream file.

Each intermediate head independently passed a Lake build of its changed
handwritten/compatibility modules, strict elaboration (9, 7, 1, 6, 11, and 6
files respectively), import-layer and pass-through checks against its parent,
generated-aggregator content checks, and whitespace checks. The first head also
built ShiftTildeSymmetricPhases explicitly. The combined head passed all 92
selected build targets covering 171 affected non-aggregator modules through 59
leaves (21,221 jobs), followed by strict elaboration of all 40 changed files.
Strict checks disable automatic implicits, use synthesis depth three, enable
Mathlib standard linters, and treat warnings as errors. The API audit retains all
453 public declaration headers, with 115 relocated. All 116 module-policy,
aggregator-generator, and CI-selection tests passed.

Main then advanced to `868d2c957aebacdf8807b2fbe78abdc01edb0a85` through the
single documentation-only #10808 commit. The stack was rebased onto it;
every intermediate head's Lean sources, scripts, and build configuration were
compared with its tested counterpart and remained identical. The final audit
update is documentation-only. The original campaign branch and staged
integration tree `93c21ae17c50adeb6b31f509b3a640978cb2c231` remain preserved.

These checks do not establish a full-root/generated-aggregator Lean build or
complete the standalone regression suite; those remain for CI. All six PRs stay
drafts pending current-head CI and substantive scope/mathematical review.
No approval or merge readiness is inferred from local checks, and no PR was
merged in this pass. The seven literal compatibility imports remain intentional
and are distinguished from zero checker-defined example-import debt above.
