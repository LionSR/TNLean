# Simplification of MPS examples and preparation proofs

Date: 2026-10-22; reviewed 2026-10-23. PR: #9963. Addresses #9881.

The PR removes 20 public theorems and one private theorem, and shares repeated
proofs. The signatures of retained public declarations are unchanged. It is a
partial contribution to #9881, not completion of that issue.

The comparison is against the merge base of `main` and reviewed commit
`669142203515d3f23eaedcea474ba6b18397ab89`, covering all 20 changed Lean files.
The following table accounts for every deleted declaration. Each replacement is
an existing general theorem or an explicit derivation from retained definitions;
it does not assert that a new theorem with the old signature was added. There
were no callers to migrate. No compatibility aliases are retained, in accordance
with `docs/project_conventions.md`.

## Removed declarations and retained derivations

Names in the first column are relative to the namespace of the listed file.
The three Fibonacci off-diagonal lemmas are private: their applications below
are derivations inside `FibonacciAction.lean`, not exported substitute names.

| Removed | File | Retained derivation |
|---|---|---|
| `fibUnitAllTau_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | Unfold `FibonacciCompression.fibUnitAllTau_compression` and apply `MPSTensor.MultiBlockCompression.remainder_ofRing fibUnitAllTau_offDiagonal i` in its defining module. |
| `fibActAllTau_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | Unfold `FibonacciCompression.fibActAllTau_compression` and apply `MPSTensor.MultiBlockCompression.remainder_ofRing fibActAllTau_offDiagonal i` in its defining module. |
| `fibActChain_remainder_eq_zero` | `TNLean/MPS/Examples/Fibonacci/FibonacciAction.lean` | Unfold `FibonacciCompression.fibActChain_compression` and apply `MPSTensor.MultiBlockCompression.remainder_ofRing fibActChain_offDiagonal i` in its defining module. |
| `thetaTwo_eq_fromBlocks` | `TNLean/MPS/Examples/Ising/IsingGauge.lean` | `IsingTwist.thetaTwo`, `IsingTwist.thetaTwoZ`, `IsingTwist.isingOne`, `IsingTwist.isingPsi`, and `MPSTensor.complexOfZsqrt2_apply`: expand entries of the two blocks and use preservation of numerals by the ring homomorphism. |
| `isingSigma_apply_zero_six` | `TNLean/MPS/Examples/Ising/IsingTensors.lean` | `IsingTwist.isingSigmaZ 0 6 = Matrix.single 2 2 sqrtd` by definition; `IsingTwist.isingSigma` and `MPSTensor.complexOfZsqrt2_apply` send this to the complex matrix unit scaled by `√2`. |
| `siteX_mul_self` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | `KWExample.siteX_mul_apply`, followed by `KWExample.siteX` and `Matrix.one_apply`; flipping the same bit twice is the identity. |
| `siteZ_mul_self` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | `KWExample.siteZ`, `Matrix.diagonal_mul_diagonal`, `neg_one_pow_mul_neg_one_pow_self`, and `Matrix.diagonal_one`. |
| `siteX_mul_siteX_comm` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | Apply `KWExample.siteX_mul_apply` twice and expand `KWExample.siteX`; the two additions of single-site configurations commute (including when the sites coincide). |
| `siteZ_mul_siteZ_comm` | `TNLean/MPS/Examples/KramersWannier/KramersWannierSource.lean` | `KWExample.siteZ`, `Matrix.diagonal_mul_diagonal`, and commutativity of scalar multiplication. |
| `complexOfGolden_sum` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | `MPSTensor.complexOfRing_sum goldenToComplex t f`. |
| `complexOfGolden_single` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | `MPSTensor.complexOfRing_single goldenToComplex i j`. |
| `complexOfGolden_smul` | `TNLean/MPS/Examples/Rings/GoldenRing.lean` | `MPSTensor.complexOfRing_smul goldenToComplex c X`. |
| `complexOfZsqrt2_single` | `TNLean/MPS/Examples/Rings/Zsqrt2Ring.lean` | `MPSTensor.complexOfRing_single zsqrt2ToComplex i j`. |
| `defectEis_apply_one_zero` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousDefect.lean` | Evaluate `Z3Anomalous.defectEis 1 0` using `summandEis`, `defectBond`, `identityEis`, `uEis`, and `uDagEis`; the only nonzero block is `uEis 1 0` on coordinates 1 and 2. |
| `pairTarget_eq` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousDefectCompression.lean` | `Z3Anomalous.summandMPS_eq (ab.1 + ab.2) i`, after unfolding `pairTarget` and `pairTargetEis`. |
| `uMPS_apply_three` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | `Z3Anomalous.uMPS_eq 3`, `uEisMPS`, and the `(1, 0)` clause of `uEis`, followed by entrywise evaluation of `complexOfEisenstein`. |
| `uMPS_apply_seven` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | `Z3Anomalous.uMPS_eq 7`, `uEisMPS`, and the `(2, 1)` clause of `uEis`, followed by entrywise evaluation of `complexOfEisenstein`. |
| `uMPS_apply_two` | `TNLean/MPS/Examples/Z3Anomalous/Z3AnomalousTensor.lean` | `Z3Anomalous.uMPS_eq 2`, `uEisMPS`, and the `(0, 2)` clause of `uEis`, followed by entrywise evaluation of `complexOfEisenstein`. |
| `mpvExpectation_add` | `TNLean/MPS/Preparation/DepthLowerBoundCore.lean` | Expand `MPSTensor.mpvExpectation` and use `map_add`, `LinearMap.add_apply`, and `inner_add_right`. |
| `conjTranspose_physicalMatrix_approximatingTensor_mul_blocked` | `TNLean/MPS/Preparation/OrthogonalBlockSum.lean` | `Matrix.conjTranspose_polarIso_mul_eq_zero h` in `Preparation/PolarUniqueness.lean`, after expanding `approximatingTensor`, `physicalMatrix_rotatePhysical`, and `polarIsoMatrix`; conjugate transpose reverses the product, and `Matrix.submatrix_mul` transports the bond coordinates. |
| `posSemidef_embeddedBlockState` (private) | `TNLean/MPS/Preparation/OverlappingBlockOverlap.lean` | `Matrix.PosSemidef.mul_mul_conjTranspose_same`: apply `hσ.mul_mul_conjTranspose_same _` to the definition of `MPSTensor.embeddedBlockState`. |

## Worked examples and source citations

Absence of callers alone is not the reason for removing an example conclusion.
The deleted Fibonacci lemmas assert that three particular remainders vanish.
Their docstrings cite the local verification record, §§4.2–4.4, and their proofs
are direct applications of `MultiBlockCompression.remainder_ofRing`. The retained
compression definitions and off-diagonal proofs still establish this vanishing.
The source's periodic-state action remains explicitly stated and proved by
`FibonacciCompression.mpo_fibOne_mulVec_allTau`,
`FibonacciCompression.mpo_fibTau_mulVec_allTau`, and
`FibonacciCompression.mpo_fibTau_mulVec_chain`. These are still cited by blueprint
label `thm:asymex_fib_state_action`. The Fibonacci passage in
`Papers/2203.12563/REsubmission.tex`, lines 1991–1993, states the two-block action;
it does not specify these three compression constructions.

The Ising deletions are the expansion of a weighted direct sum and one matrix
entry evaluation. The weighted direct sum remains the definition of `thetaTwoZ`;
the `(0, 6)` matrix unit remains an explicit clause of `isingSigmaZ`.
`IsingTwist.isingBondObject_remainder`,
`IsingTwist.isingBondObject_trace_evalWord`, and `IsingTwist.isingTwist_mpo`
remain in `IsingWeightedTwist.lean`, with the latter two linked from
`blueprint/src/chapter/ch25_asymmetric_examples_ising.tex`.

The four Kramers–Wannier deletions are elementary identities for the individual
Pauli operators, recovered as in the table. The duality relations
`KWExample.kwTensor_mpo_mul_siteX` and `KWExample.kwTensor_mpo_mul_siteZZ`, the
square relation `KWExample.kwTensor_mpo_mul_self`, and the state actions
`KWExample.kwTensor_mpo_mulVec_plus` and `KWExample.kwTensor_mpo_mulVec_ghz`
remain. In particular, the duality relations retain their blueprint references.

The four deleted ℤ₃ matrix evaluations cite the local verification record,
§§2.0 and 2.5. They evaluate entries already specified by `uEis` and `defectEis`;
they are not separate assertions printed in the cited paper. The cited passage
`Papers/2405.00439/MPU-DW.tex`, lines 2038–2068, gives cocycles and domain-wall
statistics, not these tensors. The normality results `Z3Anomalous.uMPS_isNormal`
and `Z3Anomalous.uDagMPS_isNormal`, and the defect conclusions
`Z3Anomalous.mpo_defect_mul_defect`,
`Z3Anomalous.defectSquare_evalWord_remainder_eq_zero`, and
`Z3Anomalous.defectSquare_remainder_mul_ne_zero` remain. The defect square identity
is still linked from `blueprint/src/chapter/ch25_asymmetric_examples_z3.tex`.
The deletion of `pairTarget_eq` removes only a specialization of `summandMPS_eq`;
`pairTargetEis` itself is unchanged.

The deleted mixed orthogonality theorem in `OrthogonalBlockSum.lean` follows from
the retained general polar-isometry orthogonality theorem, with the same hypothesis
`B₁ᴴ B₂ = 0` and arbitrary `σ₁`. The retained theorem
`MPSTensor.conjTranspose_physicalMatrix_approximatingTensor_mul` concerns two
approximating tensors and is not by itself a replacement for this mixed statement.
No change is made to the module's documented restrictions on multiplicities and
orthogonality. The other preparation deletions are linearity of expectation and
positivity of `E σ Eᴴ`, as specified in the table.

The local verification records under `Notes/OpenProblemsTN/checks/` cited by the
old docstrings are absent from this checkout. Their numerical contents were not
independently rechecked. The deletion decisions above use the old proof bodies,
retained definitions and the available paper and blueprint sources; they do not
claim a fresh audit of those absent records.

## Other changes

Repeated arguments are shared by the private lemmas `groundSpaceES_map_withLp`
in `AKLTSpinSectors.lean`, `neg_one_pow_rev_add_rev` in
`CZX/ClusterIsingSymmetry.lean`, and `snoc_enc_injective` in `Staircase.lean`.
The CZX proofs also use `neg_one_pow_mul_neg_one_pow_self` in place of local
proofs of the same identity. Other changes remove repeated alternatives in
`ZMod2.lean`, a repeated simplification rule in `UnequalMERA.lean`, and redundant
`by exact` syntax in `AKLT.lean`, `Cluster.lean`, and `PVBSLocalInteraction.lean`.

## Verification

- `python3 scripts/zero_reference_scan.py --json` at the reviewed commit reported
  83 candidates, including 12 in `MPS/Examples` and none in `MPS/Preparation`.
  The 12 are the three `AnomalousCondensationZ2Z2NonSplit` conclusions, four
  Kramers–Wannier `plusLeft`/`plusRight` definitions and their four intertwiner
  theorems, and `Z3Anomalous.pairTargetEis`. They remain outside this deletion
  list; the scan is not a reason to delete them automatically.
- `python3 scripts/generate_import_aggregators.py --check` passed: 83 generated
  files cover 4352 production modules. `git diff --check` passed.
- All 21 deleted names were extracted from the full Lean diff and compared with
  the 21 table entries. Searching all tracked files for each final name component
  found no occurrences outside this audit, including no blueprint tags. This is
  a reference check, not a claim that an unused theorem lacks mathematical value.
- The full diff adds no `sorry`, `admit`, `axiom`, `native_decide`, or `unsafeCast`.
- The three REST comment/review endpoints and GraphQL review threads were inspected:
  one conversation comment about a transient blueprint installation timeout,
  no inline comments, no reviews, and no threads. The blueprint rerun succeeded.
- At `669142203515d3f23eaedcea474ba6b18397ab89`,
  [PR CI run 39831211656](https://github.com/LionSR/TNLean/actions/runs/39831211656)
  passed the build, strict changed-file checks, compilation-time checks, module
  policies, and blueprint web checks. The build job's successful steps include
  `lake build`, the style linter, blueprint declaration checking and paper-gap
  declaration checking. The PDF and inline-diagram jobs were skipped.
- The review correction changes only this Markdown audit. No local Lean build or
  local `leanblueprint checkdecls` is claimed; compilation evidence is the CI run
  above, whose Lean sources are unchanged by this correction.
