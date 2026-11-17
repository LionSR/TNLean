# Theory and worked-example import extraction

Issue: #10721. Original combined-tree build baseline: TNLean `612f8998752998486c6e080a427c65dc6a6847e7`, with QICLean `e9cc1cc6cd52c6dfc27d7b3aab4b1ba39ea7ed19`.

## Review units

The six directory-scoped units are MPU, MPDO, Preparation, FundamentalTheorem, Symmetry, and PEPS. They are stacked in that order. MPU supplies the identity prerequisite for MPDO; MPDO supplies Core/GHZ for Preparation and Symmetry. The other ordering is for review and ratchet integration. No enforcement logic is added: merged #10740 already supplies all three ratchets.

### mpu

Extract binary configuration operations into `MPS/Chain/BinaryPhase` and the identity MPU and source ranks into `MPS/MPU/Identity` and `IdentitySourceRanks`. Retain the new QICLean ComplexSqrt import in ShiftSourceFactors. ClusterIsingSymmetry imports CZXUnitary explicitly.

### mpdo

Extract GHZ tensor/sectors into `MPS/Core/GHZ` and binary-group algebra into `Algebra/ZMod2Representation`. The three CZX consumers import those shared interfaces and the identity MPU introduced by the preceding partition.

### preparation

GHZSectorParent imports the shared GHZ tensor/sectors from the preceding partition.

### fundamental-theorem

Move arbitrary-tensor counterexamples, embedding sharpness, and the weighted counterexample consumer into Examples/MultiBlock. Keep the three old module paths as import-only compatibility modules.

### symmetry

Move the concrete CZX permuted-block, Z3 fusion, Ising fusion, and Kramers-Wannier demonstrations into their Examples directories. Keep the four old module paths as import-only compatibility modules and update direct example consumers.

At this point in the series, the checker records 1 example-import edges and 55 mutual-directory pairs. Each unit removes only entries that its source changes resolve.

## Compatibility semantics

Names and mathematical statements are preserved. The complete series keeps seven old module paths outside Examples as import-only wrappers: three under FundamentalTheorem/Arbitrary and four under Symmetry/MPOSymmetry. Thus seven literal outside-to-Examples imports remain in the final source. The upstream checker deliberately excludes import-only modules as importers and expands them when checking a declaration-bearing caller. Zero checker debt is not a claim of zero literal import statements. The seven paths under `TNLean/MPS/` are `FundamentalTheorem/Arbitrary/Examples.lean`, `FundamentalTheorem/Arbitrary/OneBlockSharpness.lean`, `FundamentalTheorem/Arbitrary/WeightedExamples.lean`, `Symmetry/MPOSymmetry/CZXPermutedBlocks.lean`, `Symmetry/MPOSymmetry/Examples.lean`, `Symmetry/MPOSymmetry/IsingFusion.lean`, and `Symmetry/MPOSymmetry/KramersWannierBimodule.lean`. Keeping historical module imports is an explicit design choice for compatibility, not a new exemption in the checker. The old Examples/ZMod2 path also remains as a wrapper importing library algebra.

## Validation and integration

The combined extraction was tested before partitioning at staged tree `93c21ae17c50adeb6b31f509b3a640978cb2c231`: one Lake build of 92 targets covering 171 affected non-aggregator modules through 59 leaves, including changed compatibility paths, passed (21,219 jobs). All 40 changed handwritten/compatibility modules passed strict elaboration with automatic implicits disabled, synthesis depth three, Mathlib standard linters, and warnings as errors. The API audit retained all 453 public declarations and their headers, with 115 relocated.

These are combined-tree results, not independent builds of each intermediate branch. Each partition additionally checks its import layers, pass-through ratchet, generated aggregators, and whitespace. The full-root build, generated-aggregator elaboration, and standalone regressions remain for CI.

The tested base includes #10761 and #10748. Main later advanced to `55cab8718` with #10697; open #10813 addresses its reported ShiftTildeSymmetricPhases build break. This series does not duplicate that fix. Active #10626 overlaps GroupCocycleMPO/Instances and the old CZXPermutedBlocks owner: retain its cohomology migration in the new owner when integrating. Other active code overlaps are generated aggregators; regenerate them rather than restoring stale imports.
