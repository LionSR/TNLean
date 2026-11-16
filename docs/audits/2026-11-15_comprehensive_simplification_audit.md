# Comprehensive simplification audit

Date: 2026-11-15. Scope: all principal TNLean module families, including work
outside area law. This is a source audit and a small draft implementation;
compiler acceptance remains pending.

## Evidence and limits

- Local inventory/scans: `cbf482955f46f36c71c95ab1547b3cc86b6d58c2`.
- Current source revision checked through the GitHub connector:
  `eb588dc15332a3798431015e6c27ecbaf329b2d1`. It is 257 commits ahead of
  the local checkout. The comparison response contains 300 paths and is
  incomplete; absence from that response never establishes an unchanged file.
- Candidate and replacement files were individually read at that exact
  current revision. Representative files whose scope is broader than the
  verified set are identified below. Line references describe the original
  current-main source unless expressly marked as local-scan evidence.
- Current dependencies: Mathlib `625d8914199bc567cca9b91f90e8e5afafa5ae51`
  (`v4.36.0-rc1`), QICLean `603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac`.
- Read `AGENTS.md` (the `CLAUDE.md` symlink), project conventions, the proof
  debt and tactic ledgers, the October directory audits, and the shared
  find-simplification and Lean-conventions instructions. Archive declarations,
  generated aggregators, mathematical witnesses, and documented source
  restrictions retain their established policies.
- No Lean/Lake executable or dependency cache is installed. Enforced network
  mode is disabled; `git ls-remote` fails with HTTP 403. Connected GitHub reads
  work. No compilation, timing improvement, root build, or checkdecls success
  is claimed. Source-level arguments below still require elaboration.

The broad survey covered Algebra; Circuit; Lattice; QCA; Spectral; Wielandt;
PiAlgebra; PEPS and its approximation, area-law, examples and parent-Hamiltonian
layers; and MPS Core/Chain/Overlap, canonical forms, BNT, fundamental theorems,
periodic tensors, MPDO/RFP, MPU, symmetry, examples, preparation,
parent Hamiltonians and area law. It combined inventory/scanner coverage with
targeted mathematical inspection; it is not an assertion that every possible
simplification in every current-main file has been proved or enumerated.

## Ranked work

Values are mathematical/API value and maintenance value, each out of ten.
Risk is implementation risk out of ten. Owners are proposed responsibility
areas or existing issue/PR owners, not new contributor assignments.
Line savings are estimates unless explicitly measured.

| Rank | Concrete simplification | Value | Risk | Proposed owner and overlap |
|---|---|---|---|---|
| 1 | Specialize constant physical-product range proofs from the existing dependent theorem; preserve the three public statements, remove about 140–150 private proof lines. | 7 / 8 | 4 | PEPS product-support and Lattice compression owners; updates the deferred 2026-10-05 audit, outside active flux files. |
| 2 | Remove the phantom tensor argument of the geometric crossing predicate; migrate graph-only uses without changing either boundary condition. | 7 / 8 | 5 | PEPS geometry/RegionBlock owner; broad migration needs a fresh PR-file overlap check. |
| 3 | Derive `d ≤ D` from finite word-compression data inside the theorem family instead of requesting it from every caller. | 8 / 7 | 5 | Fundamental-theorem reduction owner; no supplied active PR edits this module. |
| 4 | Reuse QICLean's Hermitian kernel-gap theorem in the existing TNLean statement. | 7 / 8 | 3 | Existing #10599 / draft #10613 owner; do not duplicate that patch. |
| 5 | Finish native cochain consumer migration and remove the old parallel scalar theories when their users move. | 8 / 9 | 6 | Existing #8315, #8319–#8321 owners and #10615/#10616/#10626; high active overlap. |
| 6 | Replace finite-subcover/minimum/maximum bookkeeping by Mathlib's directed-cover theorem. | 6 / 7 | 3 | Existing #10598 owner; retain that issue instead of opening duplicate debt. |
| 7 | Share the dependent physical product-map expansion used by four inverse/cut identities. | 6 / 7 | 3 | Lattice compression and PEPS product-map owners; coordinate with rank 1. |
| 8 | Reuse the already-proved product-gauge intertwining identity across MPS and PiAlgebra symmetry. | 6 / 7 | 4 | Low-level symmetry owner, coordinated with the cochain migration. |
| 9 | Share the three exponential approximation preludes at the existing preparation-bound owner. | 5 / 7 | 3 | #8620 preparation owner; separate files from active #10617/#10622. |
| 10 | Reuse core scalar-invariance theorems in periodic sector matching. **Implemented: net −40 Lean lines.** | 5 / 7 | 2 | Independent slice under #4529; no Lean-file overlap in 23 open PRs. A disjoint ledger entry shares a file with #10629. |
| 11 | Derive sitewise matrix isometry identities by the module's multiplication, adjoint and identity laws. | 5 / 6 | 2 | MPDO physical-map owner; no new theorem or abstraction required. |
| 12 | Specialize the shared normalized variable-rank truncation theorem in AKLV and remove its incidental dependency on the independent approximation route. | 6 / 7 | 4 | AKLV/shared truncation owner; preserve actual truncation and ranks. |
| 13 | Reuse `IsOpenMPS.mono` at four bond-enlargement sites instead of reconstructing through cut ranks. | 4 / 6 | 2 | LVV approximation owner; no supplied active PR edits these sites. |
| 14 | Use QICLean blocking definitions directly in foundational QCA blocking. | 3 / 7 | 3 | QCA blocking/MPU-correspondence owner; preserve genuine downstream MPS dependencies. |

### Exact trails and mathematical arguments

1. `PEPS/PhysicalProductRangeSupport.lean:29–188` contains the constant-alphabet
   private matrix, composition, coordinate and retraction machinery.
   `Lattice/Compression/DependentPhysicalProductRangeSupport.lean:137,174,210`
   proves the dependent-alphabet versions. Instantiate the alphabet constantly.
   Import that Lattice owner directly: `PhysicalProductFamilyRangeSupport`
   already imports the constant module and would create a cycle in reverse.
   This is the consolidation deliberately deferred by
   `2026-10-05_dependent_physical_product_ranges.md`.

2. `TNLean.PEPS.IsCrossingEdge` in
   `PEPS/RegionBlock/CoarseThreeSiteCoherentFrame.lean:91` takes `_A : Tensor G d`
   but defines only `IsRegionBoundaryEdge R g ∧ IsRegionBoundaryEdge R' g`.
   The defining current-main file is verified. The local migration census is
   202 matching lines across 27 production files, not 202 distinct consumers.
   Remove the unused argument, then remove physical-dimension/tensor binders
   only where the resulting theorem actually becomes graph-only.

3. `Kraus.FiniteWordCompression` contains `W * V = 1`. Therefore `V` is
   injective and finite-dimensional linear algebra gives `d ≤ D`.
   `MPS/FundamentalTheorem/Reduction/FiniteWordCompression.lean:112,285,315,367,446`
   threads `hD` through five forward results. The first proof already establishes
   injectivity at line 122 and the dimension comparison at line 133.
   Derive the inequality internally; preserve the threshold `D - d + 1` and
   every conclusion. This premise is mathematically redundant even though
   `omega` currently consumes it. Public callers require migration and builds.

4. `Algebra/CommonKernelSpectralGap.lean` repeats the eigenbasis expansion
   exported by QICLean as
   `Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap`.
   Draft #10613 already removes 49 net lines, with unchanged public statements.
   Its compiled acceptance is explicitly pending. Retain arbitrary real gap
   and orthogonality to the entire kernel.

5. #10615 supplies permutation-coefficient cochains; #10616 supplies degree
   three; #10626 begins consumer migration. Their purpose is to delete
   parallel definitions once native consumers replace them, following the
   project's Mathlib-structure policy. Foundational availability alone does
   not complete #8321 or justify deleting live anomaly/L-symbol consumers.

6. `Algebra/CompactGapBounds.lean:30` can use
   `IsCompact.elim_directed_cover`, verified in pinned Mathlib
   `Topology/Compactness/Compact.lean`. Index the interiors of
   `{x | P δ N x}` by positive real `δ` and natural `N`; `min δ δ'` and
   `max N N'` supply directed upper sets by the existing monotonicity premises.
   The index is nonempty even for an empty compact set, avoiding a separate
   empty finite-subcover branch. Preserve both existing public statements.
   #10598 already owns this exact change.

7. The same six-line distributivity expansion occurs at
   `PEPS/DependentBondLocalInverse.lean:67,84` and
   `PEPS/TorusCutPhysicalMap.lean:44,64`. A dependent-alphabet product map
   applied to a coherent sum gives one common identity. Four sites across
   two files meet the ledger threshold. The existing mixed-boundary lemma
   `sum_prod_sum_mul_eq_sum_prod_smul` has a different statement and is not a
   demonstrated direct replacement. Prefer the general product-map owner.

8. `PiAlgebra/GlobalSymmetry.lean:127–166` reconstructs the private
   `gauge_product_intertwines` argument of
   `MPS/Symmetry/VirtualRepresentation.lean:79–97`, including its twist
   compatibility at lines 64–77. Expose the existing elementary identity at
   the low symmetry owner. Preserve the order `X(h) * X(g)` and chosen gauges;
   importing a heavy downstream theorem backwards would worsen dependencies.

9. `Preparation/LogDepthPreparation.lean:98–111`,
   `LogLogDepthEveryLength.lean:109–122`, and `UnequalTreeMERA.lean:123–136`
   specialize `exists_blockApproximationError_le_mul` at `γ = 1/2`, set
   `r = -log t > 0`, and rewrite the same exponential rate. One specialization
   at the current block-approximation owner removes about 15–20 net lines.
   Keep all nonzero-state hypotheses and the distinct circuit constructions.

10. `Periodic/Overlap/SectorMatch/Basic.lean:59–94` privately reproves
    fixed-length injectivity and normality under nonzero scalar multiplication.
    `Core/ScaledNormality.lean` already exports
    `MPSTensor.isNBlkInjective_smul_iff` and `MPSTensor.isNormal_smul_iff`.
    The sole retained normality consumer now calls the latter directly.
    No replacement API is introduced. See implementation evidence below.

11. `MPDO/SitewisePhysicalMatrix.lean:119–154` expands the isometry and adjoint
    identities entrywise despite its existing multiplication law at line 97,
    adjoint law at 111, and identity law at 169. Move the identity law before
    the isometry theorem, rewrite with these laws, and apply the input Gram
    identity. About 26 net proof lines can leave; public statements stay.

12. Current `AreaLaw/AKLV/SequentialApproximation.lean:44–85` reconstructs
    normalized truncation guarantees available in
    `AreaLaw/NormalizedVariableTruncation.lean:36`,
    `normalized_sequentialTruncation_of_prefix_mass`. Use constant rank `D`
    and `δ = ε²/2`; the required tail budget is `δ/8 = ε²/16`.
    The same actual truncated and normalized vectors are used, so positive
    norm, unit norm and cut ranks survive. The squared error bound `ε²/4`
    implies the existing error bound. Keep the scalar tail-budget argument.
    QICLean already owns `norm_inv_norm_smul_sub_le_two_mul` in
    `Analysis/UnitNormalizationDistance`; do not propose extracting it again.
    Direct imports of these owners can replace `MPSApproximation` here.

13. Existing `IsOpenMPS.mono` in `AreaLaw/OpenMPSCutRank.lean:201` applies at
    `ViableSet/FinalMPS.lean:83`, `SuccessiveApproximation.lean:78,98`, and
    current `SampledSuccessiveConstruction.lean:152`. These four arguments
    only enlarge a bond bound. Keep each arithmetic inequality and replace
    the cut-rank reconstruction by `hMPS.mono` (about 15–25 lines).

14. `QCA/Blocking.lean:7,115–169` imports MPS blocking for `blockPhysDim` and
    `decodeBlockEquiv`. `MPS/Core/Blocking.lean:36–61` makes them abbreviations
    of QICLean's `Kraus` definitions. Use `QICLean.Kraus.Blocking` directly.
    `BlockingIntervalCoordinates` genuinely uses `blockedConfigEquiv`; retain
    an explicit MPS import there unless that coordinate theorem is separately
    generalized. `MargolusTensorLocalRule` genuinely depends on MPU. The
    proposed change isolates a foundational cone; it does not remove all
    QCA-to-MPS dependencies or promise a measured build-time reduction.

## Further candidates requiring design or additional formal work

- **Shared Hamiltonian extension:** six image/default-zero case splits occur
  in `PEPS/Approximation/SquareAreaLawHamiltonian.lean:169,179,186` and
  `SwappedSquareHamiltonianInteraction.lean:119,129,136`, with duplicate sum
  transport at 206–216 and 143–153. Coordinate a property-preserving
  `Function.extend` lemma or a support-indexed constructor with #10609.
  Do not add `0 ≤ J` to the first constructor: it currently derives this
  only where needed from an actual site bound. Medium risk.
- **Gaussian integral splitting:** `Lattice/GaussianFilteredLocality:64–93`,
  `GaussianFilteredTruncation:133–162`, and `GaussianFilteredIncrement:100–125`
  repeat indicator/integrability/norm-integral estimates. A probability-measure
  lemma with an integrable outside envelope could cover constant and weighted
  tails. Scout QICLean/Mathlib before adding it; upstream analysis owner,
  medium risk. A matching upstream theorem has not been established.
- **Positive local states:** `QCA/CompatibleLocalState.lean:51` stores
  contractivity alongside normalization and positivity on adjoint squares.
  Contractivity should be derived mathematically; the sole constructor proves
  a separate bound in `ParentHamiltonian/LocalObservableQuasiLocalState:30–55,83`.
  A complete Lean proof for arbitrary inputs has not been supplied. A theorem
  controlling only positive inputs is insufficient. QCA state-extension and
  QICLean analysis owners; medium-high risk, not implementation-ready.
- **Dependent metric packages:** `MPU/MinimalCutEndpointMetrics.lean:333`
  and `MinimalLeafCircuits.lean:87` repeat a long simultaneous existential.
  Six local modules use the shape; only representative current files were
  verified. Bundle exact coherent bases, metrics, isometries, endpoint and
  full-unitary identities at their owner before further duplication. Preserve
  complex phase and simultaneous choices; medium risk.
- **Cyclic-decomposition packages:** `Periodic/Overlap/SelfOverlapSetup:86–115`
  already defines `IsCyclicSectorDecompWith`; the construction in
  `CanonicalForm/SectorComparison/CyclicSectorDecomposition:248–266,312–330`
  spells its eight conditions out again. This updates existing D1 debt.
  Move the predicate to a dependency-neutral owner before reuse; the current
  import direction prevents simply importing it backwards. Preserve every
  condition and all trace-preservation and nondegeneracy data; medium risk.
- **Infinite-volume gap property:** `ParentHamiltonian/FaithfulQuasiLocalGap:44`
  and `PeriodicQuasiLocalGroundStateGap:52` repeat a 23-line quantified
  conclusion. Sixteen local modules contain this shape; only representative
  current files were verified. A precise property at `QuasiLocalEventualKernelGap`
  could unify it, retaining arbitrary filters and independently diverging
  margins. This is an API-design proposal, not a proved replacement.
- **Example/geometry residue:** move `MultiBlock/RunningFactorization:62`
  `redUpper_spec` next to `Running.redUpper` and use its components at
  `Running:245,261,486`; similarly, three PEPS example copy-constraint sums
  and three torus-edge coordinate equalities may use small owner lemmas.
  These are low-risk follow-ups, below the principal structural priorities.

## Active ownership and rejected findings

All 23 open PR file lists (#10613–#10635) were read. This verifies published
PR overlap, not the absence of unpublished remote sessions or branches.
No remote-session listing tool is available here. Recheck ownership before a
large migration; leave active source files with their current owners.

The final overlap check found that #10629 also edits `docs/tactic_patterns.md`.
Its exact patch adds an AKLV threshold entry at line 82; this audit changes
only the pre-existing scalar-injectivity entry, over 7,000 lines away.
The ledger edits are disjoint and the Lean implementation has no shared file.

- #10621/#10631 own interaction-budget and lattice hard truncation.
  #10631 already replaces about 500 chain-specific lines with the general
  lattice statement; this is a top-value owner continuation, not a new patch.
- #10628–#10635 own AKLV/ALVV robustness, resampling trees, spectral projection,
  gap comparisons and soft truncation. #10619/#10623/#10624/#10627 own PEPS flux
  deformation/density/walks. #10617/#10618/#10622 own preparation continuation.
- The unital transfer contraction is already consolidated at
  `UncleTrialTransferNorm.norm_mapLM_pow_apply_le_of_mapLM_one` and used by
  factorization, pinned norms and overlaps (#10487). Current tactic ledger
  line 11126 records completion while line 11670 still requests extraction.
  The stale duplicate should be removed by the ledger owner.
- The trace-one dimension helper is deliberately parked in
  `Preparation/SecondOrderOverlap.lean:64` because of compile-time constraints.
  Its parent-Hamiltonian dependency cost is real but already recorded;
  propose an upstream move only after current-API scouting and measurements.
- The four zero-reference Kramers–Wannier intertwiners are advertised concrete
  example conclusions. Lack of named consumers is not grounds for deletion.
- Affected-owner fibre blocks already use the promoted `affectedOwner_eq_iff`.
  Generic `ext`/case-split scanner matches do not establish duplicated facts.
- Spectral injective results already derive from irreducible theory;
  Wielandt's tensor-facing conclusions retain genuine domain content.
- Keep PiAlgebra's distinction between primitivity and irreducibility, the
  documented small-torus restrictions, nondegenerate counterexamples and
  the empty-register reflection's exact phase. No source statement is weakened.

## Implemented independent subset and validation

Only the periodic sector-scaling subset is implemented in Lean. Original
current-main blobs were checked against the local pre-edit files:

- `SectorMatch/Basic.lean`: `6fbbd2b8bc5b9126808aa2cbbf12e2ba781494e8`.
- `Core/ScaledNormality.lean`: `35f99a3ce381bc570cdcf9ebc75c8a212375708b`.

Removed private declarations and replacements:

- `MPSTensor.isNBlkInjective_smul_of_ne`: existing
  `MPSTensor.isNBlkInjective_smul_iff`; its sole consumer was the removed
  private normality wrapper.
- `MPSTensor.isNormal_smul_of_ne`: existing
  `MPSTensor.isNormal_smul_iff`, applied at the retained normality consumer.

The explicit core import plus direct application gives **2 added, 42 removed
Lean lines: net −40**. All six public declaration headers are byte-for-byte
unchanged. No blueprint anchor refers to either private name. No new generic
lemma, tactic, hypothesis, compatibility alias, test fixture or integrity
exception is introduced. The existing tactic-ledger entry records reuse.

Passed: `git diff --check`, forbidden-token diff check, public-header equality
check, added-Lean-line length check, and current-source/active-PR path checks.
The local zero-reference scan returned only the four retained example claims;
the tactic scan's top 25 patterns were triaged against the ledger and actual
goal shapes. The local size report is 1,094,829 lines and 3,585 duplicated
ten-line windows, including Archive and textual matches. Those are historical
baseline metrics, not current-main totals or independent deletable proofs.

Before integration, fetch and verify the pinned prebuilt Mathlib cache under
the repository's platform-specific cache policy, then run:

```sh
lake build TNLean.MPS.Periodic.Overlap.SectorMatch.Basic
lake build TNLean.MPS.Periodic.Overlap.SectorMatch
lake build
python3 scripts/ci_lean_checks.py strict --base origin/main
```

The focused target checks the refactor; the root build checks downstream
consumers of the deleted private machinery. Compilation and hosted acceptance
remain pending. No pull request is merged by this audit.
