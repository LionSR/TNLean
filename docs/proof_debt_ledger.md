# Proof-Debt Ledger

Living ranked registry of structural proof debt. Process rules:
[`docs/proof_debt.md`](proof_debt.md). Seeded from the 2026-07-20 tournament
(51 raw findings from 10 lenses, merged to 18 debts, 16 survived adversarial
verification; ranked by a three-judge Borda panel). Entry ids are stable;
weekly audits update evidence and status rather than renumbering.

Tracking issue: [#4529](https://github.com/LionSR/TNLean/issues/4529), with
each open debt attached as a native sub-issue.

## Demolition candidates (2026-07-20 shrink tournament)

From the `proof-shrink-tournament` workflow: 34 raw candidates from 9 lenses,
merged to 16 distinct demolitions, each checked by a safety refuter (nothing
blueprint-cited or paper-load-bearing lost) and a net-LoC skeptic (recounts
gross lines and migration cost). **6 survived with a verified 10,200 net
deletable lines** — every survivor had its claimed size cut down by
verification (23-58%), and two required real re-scoping to avoid deleting
live mathematics. Tracked under [#4529](https://github.com/LionSR/TNLean/issues/4529).

### S3. Delete the superseded edge-centred three-block union-injectivity route — net 3,180 lines, risk 3/10
- **Status**: in-progress ([#4581](https://github.com/LionSR/TNLean/pull/4581), net -200 lines; sub-issue #4563)
- **What**: `PEPS/RegionBlock/{ThreeBlockResonate,ThreeBlockResonate2,ThreeBlockReconcile,UnionInjectivity,ThreeBlockTransfer,BondLocalFromReconcile}.lean`
  (3,438 gross lines). `BondLocalFromReconcile.lean` (176 ln) has zero
  importers anywhere and is pure dead weight.
- **Why it's excess**: proves the paper's `injective_union` lemma
  (arXiv:1804.04964) only for an edge-centred red/blue/complement triple
  with a distinguished-edge restriction the source does not have — a
  specialization, not the theorem. The general `ThreeBlockGeometry` route
  (`UnionInjectivityGeneral*`) already proves the source statement over an
  arbitrary partition and recovers this route as the special case
  blue := S, complement := T, red := univ \ (S ∪ T).
- **First PR**: delete `BondLocalFromReconcile.lean` outright (176 ln,
  confirmed zero importers, zero migration cost).

### S2. Delete ~185 zero-reference declarations across ~103 files — net 2,950 lines, risk 3/10
- **Status**: open (#4564)
- **What**: top-level declarations whose name appears exactly once
  repo-wide (their own definition), including attribute-carrying
  declarations and instances cleared by a root build. Largest
  concentrations:
  `Wielandt/RectangularSpan/Universality.lean` (144 ln),
  `Wielandt/RankOne/ExtractionFull.lean` (123 ln),
  `MPS/ParentHamiltonian/BNTBlockIntersection.lean` (117 ln).
- **Why it's excess**: no proof, no blueprint `\lean{}` tag, no doc
  reference — staged helpers for abandoned proof attempts.
- **First PR**: the Wielandt-module wave (~30 declarations, ~300+ lines) —
  the most isolated directory, zero blueprint exposure.
- **Evidence update (2026-08-26)**: the
  `MPS/ParentHamiltonian/BNTBlockIntersection.lean` concentration was the
  pre-Condition-C1 branch of the BNT block-diagonal route. Thirteen
  declarations across `BNTBlockIntersection.lean`,
  `BNTBlockDiagonalChain.lean`, and `BNTBlockDiagonalBoundaryClosing.lean`
  formed a closed subgraph referenced only by one another and were removed
  (−507 Lean lines); see
  `docs/audits/2026-08-26_pre_condition_c1_bnt_route_retirement.md`.
- **Evidence update (2026-08-26)**: the `MPS/MPU` slice contributed a
  further three zero-reference declarations — the canonical-form bridge
  from the stronger normal-block data to the weaker MPU predicate, and one
  orphan physical-slice identity for identity-ancilla attachment. The
  bridge's target predicate is already used directly downstream, so it has
  no replacement; see
  `docs/audits/2026-08-26_mpu_duplicate_and_dead_surface.md`.
- **Evidence update (2026-08-26)**: the PEPS subdirectories contributed two
  more zero-reference declarations — the complement-vertex distinctness
  restatement of an existing `@[simp]` iff, and the local tensor evaluation
  whose only occurrence was its own definition. The latter also owned a
  blueprint definition node that nothing cited, so the node was deleted
  rather than redirected; see
  `docs/audits/2026-08-26_peps_forwarders_and_mirrors.md`.
- **Evidence update (2026-08-27)**: the PEPS subdirectories contributed a
  further three zero-reference declarations that fall outside this entry's
  original scope, which excluded instances and `@[simp]`-tagged lemmas
  because a name search cannot clear them. Two `@[simp]` lemmas and one
  `Fintype` instance whose body was `inferInstance` were retired with a
  root `lake build` as the oracle, and the **What** bullet above is widened
  accordingly; see
  `docs/audits/2026-08-27_peps_attribute_carrying_dead_weight.md`.
- **Evidence update (2026-08-27)**: the `MPS/MPU` transport module contributed
  one further declaration of a kind this entry's original scope missed — a
  forwarder whose body is a bare `exact` of an identically stated QICLean
  theorem. A name search does clear it, but only once the search is run against
  the companion library as well as this repository; see
  `docs/audits/2026-08-27_mpu_reduced_to_hat_qiclean_forwarder.md`.
- **Evidence update (2026-08-27)**: the BNT refinement record in
  `MPS/CanonicalForm/BNTRefinement.lean` contributed three structure fields that
  a name search cannot clear at all, because a field's spelling is shared with
  the local name that populates it. Two restated the copy-gauge relation that
  the regrouped carrier already states, and the third pinned a field to the
  parent record by `rfl` with nothing reading the pin; see
  `docs/audits/2026-08-26_canonical_form_retirements.md`.
- **Evidence update (2026-08-30)**: three successive thirty-area surveys found
  eight unused declarations with no production Lean consumer or Blueprint tag.
  Five canonical-form forwarding theorems and the constructor orphaned by
  their removal in `PiAlgebra/CanonicalFormSepAux.lean` were deleted, with
  their glossary listings migrated (−37 Lean lines). The second pass also
  discharged the deferred
  `PEPS.edgeGaugeOfCycleGauge` construction from
  `PEPS/CycleMPSFundamentalTheorem.lean`; its round-trip theorem had already
  been removed, and the inverse construction had no remaining consumer
  (−12 net Lean lines including the shorter module description). The two
  batches remove 49 net Lean lines. The third pass removed the
  attribute-carrying projection wrapper
  `MPOTensor.BNTFusionTensorClause.retainedMultiplicityWeightEntry_verticalCopyCoordinateEquiv_symm`
  from `MPS/MPDO/TopologicalMultiplicityEnergy.lean` (−14 Lean lines). Its
  linter-bearing target build passed, confirming that its `@[simp]` attribute
  was not used implicitly within the module. The three batches therefore
  remove 63 net Lean lines. See
  `docs/audits/2026-08-30_thirty_area_simplification_survey.md`.

### S5. Preserve the ch23 algebraic-FT chapter — retirement cancelled
- **Status**: cancelled (#4565; owner decision on #7220)
- **Decision**: the Chapter 23 algebraic Fundamental Theorem material is a
  useful account of András's paper and remains part of the Blueprint. Its
  chapter router and three section files are restored to the full build; they
  are not deletion candidates.
- **History**: earlier Lean-side deduplication and the relocation of
  `fundamentalTheorem_normalMPS_translationInvariant_gauge_unique` remain in
  place. Those implementation cleanups do not justify deleting the mathematical
  chapter. Any future citation migration caused by Lean refactoring must update
  the retained chapter in place.
- **Scope**: no further chapter or Lean deletion is authorized by S5. Any
  future CycleMPS simplification requires a separate, freshly verified issue.

### S12. Collapse duplicated spectral-split proofs onto `ProjectionSpectralSplit`/corner-compression API — net 520 lines, risk 5/10
- **Status**: burned down (#7218, follow-ups #7224 and #7237)
- **What**: `MPS/Structure/InvariantSubspaceDecomp.lean`'s strict-case
  theorem re-proves its base theorem's 129-line body near-verbatim
  (728 → ~380 ln after fix); `MPS/CanonicalForm/CyclicSectors/Compression.lean`
  hand-derives its 7 conclusions entrywise despite already constructing
  the isometry the existing `cornerCompression*` API needs (433 → ~140 ln).
- **Why it's excess**: both are one construction (diagonalize via
  `ProjectionSpectralSplit`, split by eigenspace, conjugate to block form)
  proved twice; strictness is a two-line cardinality bound the paper
  treats as one step. Pure proof-internals rewrite — zero signature or
  blueprint changes, every consumer destructures via opaque existentials.
- **First PR**: `InvariantSubspaceDecomp.lean` alone — extract the shared
  spectral-split body, derive both public theorems as corollaries. Net
  ~-300 to -350 lines, proof-only.
- **Outcome (2026-08-27)**: commit `f3ae05159` factors the two-block
  decomposition through the shared private theorem
  `exists_twoBlock_decomp_of_lowerZero_aux` and reduces
  `MPS/CanonicalForm/CyclicSectors/Compression.lean` to the support-isometry
  route. Follow-ups #7224 and #7237 close the remaining review items. The
  present files are approximately 399 and 160 lines, respectively, rather
  than the 728- and 433-line versions measured by the original audit.

### S7. Delete the confirmed-dead half of the UnionInjectivityOverlap chain — completed
- **Status**: burned down (#4567, #4625, follow-up #7232)
- **What**: all scattered dead spans in files 1/2/3/6 are gone. PR #4625
  removed seven zero-reference wrappers (78 lines); follow-up #7232 removes
  the final three zero-call-site declarations (37 lines).
  `PEPS/RegionBlock/UnionInjectivityOverlap4.lean` (238 ln, formerly 100%
  dead) had already been removed before this audit.
  **Correction**: the original candidate
  wrongly proposed also collapsing files 1-2 (`overlapLeftGeometry`/
  `overlapRightGeometry`) — those are live, called directly by the
  chain's capstone proof, and must be kept. **Update 2026-08-27**: the
  `overlapHostGeometry` sub-chain in file 5 (211 ln) is already gone, and
  file 5 itself was dissolved into `RegionBlock/Basic.lean` and
  `RegionBlock/UnionInjectivityGeneral.lean`
  (`docs/audits/2026-08-27_peps_regionblock_overlap_chain_retirement.md`).
  File 4 was already absent before this PR, and the scattered spans in files
  1, 2, 3, and 6 are now deleted as well.
- **Why it's excess**: the project's own paper-gap note
  (`docs/paper-gaps/peps_normal_ft_section3_route.tex`) documents this
  exact sub-route as an abandoned dead end that forced a switch to the
  surviving P0-outer parametrization.
- **Resolution**: the dead spans were deleted without changing the live
  `overlapLeftGeometry`/`overlapRightGeometry` machinery or the capstone.

### S8. Derive injective-tensor Perron-Frobenius as a corollary of the irreducible-CP-map theory — completed
- **Status**: closed 2026-07-23 (#4568; #4594 and #4628)
- **What**: the injective-only QPF theorem bodies are direct corollaries in
  `QPF/{PosDef,Uniqueness,Assembly}.lean`; all seven injective-named spectral
  corollaries now live in `Spectral/TransferOperatorGapInjective.lean`.
- **Why it's excess**: `IsInjective` strictly implies irreducibility via
  an existing one-composition bridge
  (`injective_implies_irreducibleCP` + `isIrreducibleTensor_of_isIrreducibleMap`),
  and both Wolf Thm 6.3 and the Wolf 6.6 rigidity argument need only
  irreducibility — every injective-hypothesis theorem is a direct
  instance of the already-proven irreducible one.
- **Outcome**: #4594 removed 61 net lines from the QPF proofs. #4628 completed
  the spectral relocation within a broader 483-net-line dependency reorganization,
  preserving all public theorem signatures.

### Degenerate-case hypothesis: tested and refuted (do not re-propose without new evidence)

Two candidates directly tested whether admitting `D = 0` / `N = 0` in core
definitions is excess baggage that should be eliminated (structure fields,
`[NeZero]` discipline). Both were refuted by the safety refuter with
concrete blueprint evidence — this is worth recording precisely because it
contradicts the natural intuition that degenerate cases are dead weight:

- **PEPS bond-dimension positivity as a structure field**: the blueprint's
  `def:peps_tensor` deliberately states the tensor concept with **no**
  positivity clause; positivity is introduced only as an explicit
  theorem-level hypothesis, matching the Lean code exactly. The two
  "zero-bond counterexample" files are not dead scaffolding — one of them
  proves the headline theorem is **false without** the positivity
  hypothesis (a documented adversarial scope-check that caught the
  hypothesis being silently dropped). Baking positivity into the
  definition would smuggle a stricter hypothesis into an already-`\leanok`
  general definition — exactly what the faithfulness rule forbids.
- **Repo-wide `[NeZero D]`/`[NeZero d]` discipline**: sampled instances
  were `\leanok`, blueprint-cited theorems proved for *all* `D : ℕ`
  including 0 (`posSemidef_fixedPoint_unique`, Wolf Thm 6.3(2)), with a
  dedicated corollary (`injective_transfer_unique_fixed_point'`) whose
  entire docstring purpose is "lift the `0 < D` restriction to the vacuous
  `D = 0` case," consumed by 7 live call sites. The blueprint statements
  themselves carry no dimension restriction; narrowing them would need a
  blueprint restatement the sources don't support.

Verdict: in this codebase the degenerate cases are, in the sampled
instances, doing real work — either witnessing a hypothesis is necessary
(counterexamples) or matching an unrestricted source statement. A narrower
audit (single-branch `(hD : 0 < D)` arguments with **no** companion
vacuous-case corollary anywhere) might still find a real subset, but
neither broad-brush attempt survived verification, and both defaulted to
`corrected_net_deletable = 0`.

### Other rejected candidates (net-deletable claim did not survive)

- **S1** — an apparently-orphaned 26-file, 8,103-line PEPS "TorusWindow"
  subsystem: REFUTED. `docs/paper-gaps/peps_normal_ft_2d_overlap.tex`
  (edited 10 days before the audit) documents it as an *active* staged
  campaign toward an open theorem from the cited paper, with one file
  (`TorusWindowSingleCrossingObstruction.lean`) a machine-checked
  impossibility proof that redirected (not ended) the campaign. Action
  item, not a deletion: register that file in `docs/counterexamples.md`.
- **S4** — Wolf chapter index files: REFUTED for 4 of 16 targeted files —
  they are the *sole* import path from the root manifest into 3,856 lines
  of live, blueprint-cited content (`lake build` would stay green while
  `leanblueprint checkdecls` silently broke). A corrected ~2,282-line safe
  subset exists among the rest.
- **S6** — PEPS vertical/rotated mirror collapse via torus rotation
  transport: REFUTED as incomplete — 70% of the target mass is on the
  open square lattice, not the torus, and needs its own untbudgeted
  isomorphism; corrected estimate ~1,000-1,200 net, not the claimed 1,800.
- **S9, S15** — see degenerate-case section above.
- **S10** — CoarseThreeSite chain pruning: REFUTED — the chain is
  declaration-by-declaration documented in an issue-tracked paper-gap note
  as live formalization of an open theorem; only ~150 of a claimed ~800
  lines are genuinely uncited dead code.
- **S11** — mirror-lemma transport (blue/complement, left/right): mixed —
  ~365 of a claimed 750 lines survive; the largest named target
  (`CompleteZipperFusionSupport.lean`) is blueprint-cited, load-bearing,
  and mathematically distinct content, not a mirror.
- **S13** — unitary-conjugation calc consolidation: REFUTED — 3 of 7 named
  files contain zero unitary-conjugation instances (they're
  invertible-gauge algebra, a different theorem); forcing a unitary-only
  simp set onto them would smuggle unitarity into a general-invertible,
  blueprint-cited theorem.
- **S14** — Mathlib-shadow consolidation: only the `supportProj` piece
  survives (~300 lines); `IsOrthogonalProjection` retirement, the CFC
  shim files, and the `SameIsotype` redefinition are all blueprint-cited
  or load-bearing and were rejected outright.
- **S16** — KernelDescent-via-general-theorem: mathematically sound but
  REFUTED for wrong blast-radius accounting — the theorem is called
  directly inside the PEPS Fundamental Theorem capstone proof, not the
  single peripheral caller claimed; needs re-scoping as capstone-adjacent
  surgery.

## Metrics

Weekly snapshot from `python3 scripts/loc_report.py` (see the shrink rhythm
in [`docs/proof_debt.md`](proof_debt.md)); every quantity should trend down.

| Date | Total lines | Dup 10-line windows | Sequel files (lines) | Cap-riding | Degenerate sites | Sorries |
|------|-------------|---------------------|----------------------|------------|------------------|---------|
| 2026-07-20 | 319,850 | 1,260 | 48 (20,500) | 29 | 1,934 | 4 |

## Ranked debts (tournament order)

For closed entries, the **Evidence**, **Remediation**, and **First PR** fields
are an archival record of the 2026-07-20 tournament baseline, not a
description of current `main`.

## D1. Unbundled hypothesis telescopes and giant anonymous existentials at the MPDO/ParentHamiltonian frontier — abstraction-gap, impact 6/10, effort 6/10
- **Status**: closed 2026-07-22
  ([#4517](https://github.com/LionSR/TNLean/issues/4517),
  [PR #4618](https://github.com/LionSR/TNLean/pull/4618))
- **Evidence**: a 40-line byte-identical hypothesis telescope heads three
  theorems (`MPS/MPDO/VerticalSectorCompletePositivity.lean:257`,
  `VerticalSectorIdentity.lean:44`, `VerticalSectorTracePreservation.lean:49`)
  plus a 33-line pair inside `VerticalSectorFixedGenerators.lean`; a 20-line
  telescope repeats 7x across `MPS/Periodic/Case2.lean`/`Case3.lean`; the
  `hIrr`/`hLeft`/`hOverlap`/`hBlocks` block appears verbatim 69x across 9
  files. 103 `obtain`-destructurings with >= 8 components across 57 files;
  `VerticalCanonicalForm.lean:49` positionally destructures 34 components
  (discarding 13) of the 107-line existential
  `exists_verticalBNTGrouping_with_isometry` (`VerticalBNT.lean:155`).
  634 theorem names exceed 60 chars, concentrated in MPS/MPDO (183) and
  MPS/ParentHamiltonian (146).
- **Remediation**: bundle each chapter's telescope into a hypothesis
  structure (the idiom already used by the PEPS `*Hypotheses` structures,
  e.g. `PEPS/TorusRectangleRegion.lean:120`); replace >= 10-conjunct
  existentials with named witness structures (model:
  `ProjectionSpectralSplit`, `Channel/Peripheral/CyclicDecomposition/Basic.lean:626`);
  migrate consumers from positional `obtain` to field access.
- **First PR**: a `VerticalSectorHypotheses` structure bundling the shared
  40-line telescope; restate the 5 byte-identical-signature theorems over
  it (~180 duplicated signature lines removed, proofs unchanged modulo
  projections).

## D2. Fundamental-Theorem gauge-extraction spine re-instantiated per setting; capstone conditional on an unconstructed bridge — abstraction-gap, impact 7/10, effort 7/10
- **Status**: closed 2026-07-25
  ([#4518](https://github.com/LionSR/TNLean/issues/4518),
  [PR #4818](https://github.com/LionSR/TNLean/pull/4818))
- **Evidence**: the intertwining-hom -> AlgEquiv -> Skolem-Noether ->
  gauge-read-off ladder is re-derived in 8 files
  (`MPS/FundamentalTheorem/Basic.lean:59`, `MPS/Chain/AlgebraIsomorphism.lean:109`,
  both CycleMPS overlap-insertion files, MPDO `PairHomogenization/Algebra.lean`,
  `Channel/Determinant/UnitaryCharacterization.lean:196`, + 2 partials);
  `PEPS/CycleMPSChainOverlapInsertion.lean:33` states it "mirrors the
  site-independent file" — 2,916 lines across 6 `*Overlap*` files. `hbond`
  is derived internally at `NormalGeneralFundamentalTheorem.lean:163` yet
  assumed at `NormalSquareFundamentalTheorem2.lean:111` and
  `TorusFundamentalTheorem2.lean:180`. `SameStateBridgeHyp`
  (`MPS/Chain/SameStateBridge.lean:30`) has hypothesis uses but zero
  constructions repo-wide, leaving the PiAlgebra capstone conditional on an
  unproven structure (verified 2026-07-20).
- **Remediation**: extract one packaged gauge-extraction lemma parametric
  over the index data (words, arcs, graph configurations); unify the 6
  `*InjectivityHypotheses` structures behind one interface that derives
  `hbond` internally; collapse to one canonical closed-chain statement.
- **First PR**: discharge or delete `SameStateBridgeHyp` — prove it from
  the overlap route, or restate `PiAlgebra/TIReduction.lean:58` against the
  bridge-free capstone (`PEPS/CycleMPSChainOverlapCapstone.lean:692`).

## D3. No module hierarchy: flat 121/187-file directories, a hand-listed 821-import root manifest at the CI cap, orphan files CI never builds — architecture, impact 5/10, effort 4/10
- **Status**: closed 2026-07-22
  ([#4519](https://github.com/LionSR/TNLean/issues/4519),
  [PR #4619](https://github.com/LionSR/TNLean/pull/4619))
- **Evidence**: `TNLean.lean` is exactly 1000 lines (the CI hard cap) with
  821 hand-listed imports, 84% transitively redundant; `lakefile.toml` has
  no globs, so files omitted from the manifest are silently never
  typechecked — 6 files are imported by nothing, and
  `Channel/Semigroup/Resolvent.lean` and `PEPS/PositivityCounterexamples.lean`
  are outside the build entirely (verified 2026-07-20). PEPS/ has 121 flat
  files (Torus* 49, Normal* 23, Cycle* 16); MPS/MPDO 187 (PhysicalSector*
  36); all 8 directories with > 30 files lack an aggregator;
  `PEPS/FundamentalTheorem.lean` (981 lines) shadows the directory of the
  same name.
- **Remediation**: script-generate one pure-import aggregator per directory
  with a CI completeness check (Mathlib's `mk_all` pattern; the executable
  already ships in `.lake/packages/mathlib`); shrink `TNLean.lean` to the
  top-level aggregators; promote prefix families to subdirectories one
  family per PR.
- **First PR**: generated, completeness-checked root manifest + CI check +
  cap exemption for pure-import files — closes the build-integrity hole in
  one PR and pulls the orphans back under CI.

## D4. BNT/canonical-form carriers in three generations with no carrier-level bridge; live bifurcation in MPDO — duplication, impact 5/10, effort 5/10
- **Status**: tracker closed 2026-07-22
  ([#4520](https://github.com/LionSR/TNLean/issues/4520),
  [PR #4622](https://github.com/LionSR/TNLean/pull/4622)); follow-up
  [PR #4678](https://github.com/LionSR/TNLean/pull/4678) merged 2026-07-23
- **Evidence**: `IsCPSVBasisOfNormalTensors` (`MPS/CanonicalForm/Definitions.lean:180`,
  18 files), `IsBNT` (`MPS/BNT/Basic.lean:80`, 10 files),
  `IsBNTCanonicalForm` (`MPS/FundamentalTheorem/SectorBNT/Basic.lean:106`,
  33 files) coexist with no general bridge — one file converts inline for
  one special case (`MPDO/VerticalBNTConstruction.lean:111-145`). MPDO's
  vertical route builds on `IsBNT` (`VerticalCF.lean:623`) while the
  horizontal rides `IsBNTCanonicalForm` (`HorizontalBNT.lean:135`), joined
  by `HasFiniteWordTraceSeparation` across the missing bridge; `Axioms/Beigi.lean:104` binds the
  axiom-discharge path to one side.
- **Remediation**: pick one core predicate; define others as abbreviations
  or explicit iff-bridges (the `IsNormal` vs `IsNormalTensor` gap needs a
  real theorem); migrate the smaller stacks; deprecate superseded carriers.
- **First PR**: the bridge file — publish the private `basis_isNormal`
  projection (`MPS/RFP/ResidualIsometry.lean:401`) as a public lemma and
  generalize the inline conversion at `MPDO/VerticalBNTConstruction.lean:111`
  into standalone lemmas.

## D5. General/special variant pairs maintained as forked full proofs while proven bridge lemmas sit unused — duplication, impact 6/10, effort 6/10
- **Status**: closed 2026-07-25
  ([#4521](https://github.com/LionSR/TNLean/issues/4521)); final follow-up
  [PR #4806](https://github.com/LionSR/TNLean/pull/4806)
- **Evidence**: `SectorBNT/ExactMatch.lean` (381 lines) vs
  `ProportionalMatch/Core.lean` (285 lines) share 69 ten-line duplicated
  windows including a 51-line verbatim run, while the bridge
  `SameMPV₂Pos.toNonzeroProportionalMPV₂` (`MPS/Defs.lean:294`) has zero
  call sites. `InvariantSubspaceDecomp.lean:484` comments "same as
  exists_twoBlock_decomp_of_lowerZero" above a 129-line identical fork;
  `TransferOperatorGap.lean` rebuilds the square case despite
  `mixedMapLM_self` having 3 consumers. Repo-wide: 1,575 distinct
  cross-file duplicated 10-line windows.
- **Remediation**: derive each special case as a corollary of its general
  version through the existing bridges; extract shared setup runs into
  standalone lemmas; delete superseded copies.
- **First PR**: rewire `ExactMatch` as the c = 1 corollary of the
  proportional theorem via the unused bridges at `MPS/Defs.lean:244,294`.

## D6. PEPS insertion/transfer machinery rebuilt at edge, region, and coarse granularities — abstraction-gap, impact 6/10, effort 8/10
- **Status**: open ([#4522](https://github.com/LionSR/TNLean/issues/4522))
- **Evidence**: the shared configuration calculus has landed
  ([PR #4623](https://github.com/LionSR/TNLean/pull/4623),
  [PR #5188](https://github.com/LionSR/TNLean/pull/5188)); `hostMerge` is
  now a thin `regionMerge` specialization, and the duplicate
  vertex-complement kernel descent was removed by
  [PR #4757](https://github.com/LionSR/TNLean/pull/4757). The edge
  `edgeTransferMatrix` and region `regionTransferMatrix` developments
  remain parallel, while the coarse three-site machinery still lacks a
  blocked-tensor interface to `RegionInsertionTransfer`.
- **Remediation**: recover the edge transfer as the singleton-region case
  of `RegionInsertionTransfer`, including the boundary-data equivalences
  and physical-configuration reindexing. Then connect the coarse case
  through the blocked-tensor dictionary and retire the parallel stacks.
- **First PR**: construct the singleton-region boundary and physical
  configuration equivalences, then package the existing edge transfer as
  a `RegionInsertionTransfer`; leave the coarse blocked-tensor dictionary
  to a separate follow-up.

## D7. Layer leakage: the support projection built three times, the designated Algebra home holding the weakest version — architecture, impact 5/10, effort 3/10
- **Status**: closed 2026-07-22
  ([#4523](https://github.com/LionSR/TNLean/issues/4523),
  [PR #4606](https://github.com/LionSR/TNLean/pull/4606))
- **Evidence**: `Algebra/PosSemidefSupport.lean:33` defines `supportProj`
  for `Fin D` only; `Channel/MaximalOverlap.lean:136-208` rebuilds it
  generically over any Fintype without importing the Algebra file;
  `MPS/Irreducible/FixedPointProjection.lean:85-122` imports the Algebra
  file yet re-proves hermiticity/idempotence via ~70 lines of private
  spectral machinery. Four Channel/FixedPoint files (layer 2b) import
  `MPS/Irreducible/FixedPointProjection` (layer 5) for this generic fact —
  a layering inversion. 7 generic `supportInvSqrt` lemmas sit in
  `Channel/.../PetzRecovery.lean:79-220` away from `Analysis/MatrixSqrt.lean`.
- **Remediation**: hoist the general-Fintype family into
  `Algebra/PosSemidefSupport.lean`, derive the `Fin D` version, delete both
  rebuilds, repoint importers; reunite `supportInvSqrt` with
  `Analysis/MatrixSqrt.lean`.
- **First PR**: the consolidation itself (~1,500 lines across 3 files plus
  mechanical import fixes) — best impact/effort ratio in the field.

## D8. Fragmented concept vocabulary with no glossary — naming-docs, impact 4/10, effort 3/10
- **Status**: closed 2026-07-20
  ([#4524](https://github.com/LionSR/TNLean/issues/4524),
  [PR #4538](https://github.com/LionSR/TNLean/pull/4538))
- **Evidence**: `IsNormal` (`MPS/Defs.lean:372`, 248 uses / 54 files) vs
  `IsNormalTensor` (`MPS/CanonicalForm/Definitions.lean:101`, 64 / 17) name
  different notions with no bridge lemma; 5-6 primitivity predicates
  bridged by a 285-line pairwise-equivalence file; 28 distinct `*Injectiv*`
  definition names reaching 272 files; 38 `CF`-abbreviated declarations vs
  99 files spelling out `CanonicalForm`; ~71 MPS-namespace declarations
  live inside 8 PEPS files where directory-scoped search misses them; no
  glossary exists anywhere.
- **Remediation**: a concept glossary mapping each notion to its canonical
  predicate, paper source, and sanctioned equivalence lemmas (leave
  paper-faithful names alone); standardize on namespace overloading for new
  definitions; relocate the stranded MPS-namespace declarations.
- **First PR**: `docs/glossary.md` for the normal/primitivity/injectivity/
  canonical-form clusters + a review-checklist line requiring a glossary
  entry for any new predicate.

## D9. 1000-line CI hard cap + stage-per-session habit produce numbered-sequel chains with duplicated context and dead stages — hygiene, impact 5/10, effort 4/10
- **Status**: closed 2026-07-22
  ([#4525](https://github.com/LionSR/TNLean/issues/4525),
  [PR #4633](https://github.com/LionSR/TNLean/pull/4633))
- **Evidence**: hard gate at `scripts/check_oversized_lean_files.py:21`
  with no splitting guidance; ~50 numbered-sequel files / ~22.9k lines, 39
  in PEPS (CoarseThreeSite x11, Recovery x11, UnionInjectivityOverlap x7,
  TorusWindowChain x6, TorusWindowPeel x4);
  `UnionInjectivityOverlap3b.lean:12` says "split for the file-length
  convention"; `TorusWindowPeel3.lean` is dead (Peel4 imports Peel2
  directly); `UnionInjectivity.lean` vs `UnionInjectivityGeneral2.lean`
  share 485 identical nonblank lines; 28 files parked at 900-999 lines.
- **Remediation**: pair the size gate with a split policy — concept-named
  modules plus an aggregator, a lint on numbered-sequel filenames, cap
  exemption for pure-import files; per chain, extract re-pasted setup into
  a `Basic` file, rename stages by content, delete dead stages.
- **First PR**: the CI-policy PR (lint + exemption + guidance in the
  failure message) + delete the dead `TorusWindowPeel3.lean`.

## D10. PEPS mirror-direction duplication: horizontal/vertical and blue/complement re-proved by hand while generic transport sits unused — duplication, impact 5/10, effort 6/10
- **Status**: closed 2026-07-23
  ([#4526](https://github.com/LionSR/TNLean/issues/4526),
  [PR #4634](https://github.com/LionSR/TNLean/pull/4634))
- **Evidence**: 84 exact vertical<->horizontal rename pairs among PEPS
  top-level declarations; `TorusWindowFamilyVertical.lean` (412 lines,
  created after `IsoTransport.lean` landed) says it is the transpose of
  `TorusWindowFamily.lean` "with the roles of the two coordinate axes
  interchanged throughout"; `UnionInjectivityGeneralBlue.lean` (415 lines)
  carries 6 per-lemma "blue mirror of" docstrings; only 3 files import
  `IsoTransport.lean`; the vertical gauge capstone at
  `NormalEdgeGaugeFamily.lean:287` independently re-derives its horizontal
  twin at line 212.
- **Remediation**: define the coordinate-swap lattice isomorphism next to
  `PEPS/IsoTransport.lean`, prove a transport lemma pack, derive vertical
  statements as horizontal + transport, retire the mirror files
  (~1,200 lines).
- **First PR**: the swap isomorphism `torusGraph w h ≃g torusGraph h w` +
  window/blocked-weight covariance + re-derive
  `TorusWindowFamilyVertical.lean`'s 17 declarations via transport.

## Hand-added debts (2026-09-03 MPU source-chain audit)

Evidence and remediation in
[`docs/audits/2026-09-03_mpu_source_chain_faithfulness.md`](audits/2026-09-03_mpu_source_chain_faithfulness.md);
counts checked on `origin/main` at `fb847cd35`. Ranked among themselves by
compounding cost; D13 precedes D14 because every new MPU statement pays it.

## D13. The MPU canonical-form-II convention is threaded pointwise, while admissible path nodes carry an additional continuous-source-data gap  —  api-design, impact 7/10, effort 5/10
- **Status**: open. The convention predicate exists, the reduced
  representative is constructed in the ambient diagonal gauge, and the
  MPU-level theorem migration has landed: the stabilized pair is now a
  consequence of the predicate at the single positive exponent
  $\max(D^2-1,1)$, and the forced-block contractions, the source-$u$
  isometry with its rank bound, the source-$v$ isometry with its rank bound,
  and the simple-tensor equivalence take the predicate in place of the
  `(cfii, hfull)`, `(ρ, hρ, hρdiag)` and `(J, hJ, hpower)` groups. The
  source-labelled nodes `lemuisometry` and `ThmFund1` are therefore checked
  against those statements. What remains is the blueprint-side merge of the
  surviving pointwise `mpu_admissible` twins, the `HasFullSupport` deletion
  (still consumed by the physical-adjoint, identity-ancilla, and
  tensor-product transports and by the reduced-representative construction),
  and the `fin_one` stabilization branch (still consumed on route by
  `cor:simple1` and `blockingsimple`(ii) in `SimpleBlocking.lean`). The
  blueprint-side merge is now blocked on preservation rather than on the
  predicate. Of the 16 pointwise nodes,
  `lem:mpu_admissible_source_u_isometry` is the generic supplied-fixed-pair
  step whose Lean statements still carry `(ρ, hρ, K, hpower)` and which the
  `lemuisometry` proof consumes; 3
  (`thm:mpu_admissible_simple_tensor_equivalence`,
  `def:mpu_admissible_standard_form`, `thm:mpu_admissible_fundamental`)
  restrict only the tensor their source-labelled counterpart already places
  under the convention and have no Lean restriction left; the other 12
  restrict a physical block, a physical-adjoint, transposed, or conjugate
  comparison tensor, a tensor product, or a composition, for which no
  preservation statement of the predicate exists. The 3 are cited by 11
  retained nodes (7 pointwise plus the path nodes
  `prop:mpu_admissible_continuity_index`, `thm:mpu_admissible_index`,
  `cor:mpu_admissible_continuous_standard_form`, and
  `lem:mpu_admissible_symmetry_path_criterion`) whose tensors carry only a
  supplied fixed pair, so deleting them singly would strengthen those 11
  statements silently. Two independent unblockers are needed, and neither
  substitutes for the other. The converse
  `E ^ J = vecMulVec ρ.vec 1.vec → IsMPUCanonicalFormII`, by the spectral step
  of `Papers/1703.09188/paper_v2.tex` lines 344--355, turns a supplied pair
  into a presentation of the same tensor; it therefore reaches only the 4
  nodes whose restricted tensor is the one the convention already governs
  (`lem:mpu_admissible_source_u_isometry` and the 3 candidates), and it
  dissolves the citation obstruction, but it constructs no datum for a
  derived tensor and so leaves all 12 restricted. Preservation of
  `IsMPUCanonicalFormII` under positive physical blocking (asserted at source
  line 356), physical adjunction, transposition, conjugation, tensor
  products, and composition is what reaches the 12; each such statement must
  produce all four clauses (`isMPU`, `cfii`, `fullSupport_eq`, and the
  positive diagonal trace-one `ρ` with `ρ_fixed`) for the derived tensor. For
  blocking, physical adjunction, and tensor products every clause is
  separately available (`IsMPU.blockTensor`, `blockTensorCFIIData`,
  `hasFullSupport_blockTensor`, `transferMap_blockTensor`;
  `IsMPU.physicalAdjointTensor`, `physicalAdjointNormalizedFlattening`,
  `hasFullSupport_physicalAdjointNormalizedFlattening`,
  `transferMap_mapStar`; `IsMPU.tensorProduct`, `tensorProductCFIIData`,
  `hasFullSupport_tensorProductCFIIData`,
  `transferMap_tensorProduct_kronecker`) and only the assembled statement is
  missing; transposition and conjugation exist only as the composite. For
  composition only `IsMPU.mulTensor` is available: `TNLean/MPS/MPU/` has no
  canonical-form-II construction for `mulTensor` and no transfer-map identity
  for it, only the entrywise `normalizedFlattening_mulTensor_apply`, so that
  case needs two new results and
  `lem:mpu_admissible_index_composition` stays restricted until it has them.
  The
  nonsymmetric same-fixed-point problem in #7653 remains an optional
  out-of-source question; the transpose-reparameterized construction rejected
  in #7705 is not part of this plan.
- **Evidence**: `TNLean/MPS/MPU/` carries the paper's standing convention
  (`Papers/1703.09188/paper_v2.tex` lines 271--281 and 356--361) as explicit
  hypotheses in three shapes: `hρ : ρ.PosDef` at 65 sites in 11 files,
  `hpower : E ^ J = vecMulVec ρ.vec 1.vec` at 12 theorem-parameter binders in
  4 files, and `hfull : … .HasFullSupport` at 28 sites in 6 files; an exact
  `hpower` token search gives 34 lines in 6 files, including uses, derived
  locals, and an unrelated 3-line helper in `SimpleBlocking.lean`; 8
  `hasFullSupport_*`
  transport theorems and 3 canonical-form-II constructions
  (`PhysicalAncilla.lean`, `TensorProductCanonicalForm.lean`) exist only to
  carry the pair between statements; a separate `D = 1` branch
  (`normalizedTransferStabilization_fin_one`,
  `normalized_transfer_matrix_eq_one_fin_one`, consumed on route by
  `cor:simple1` and `blockingsimple`(ii) in `SimpleBlocking.lean`) exists
  because `Matrix.StabilizedRankOneData` needs a positive exponent at most
  `D * D - 1`, which is empty at `D = 1`. Chapter 28 has 82 `\notready`
  nodes among 508, of which 39 carry an `mpu_admissible` label: 16 are
  pointwise, while 23 define or use the pathwise equivalence datum. The
  fixed-tensor nodes replace the standing convention by a supplied fixed
  pair. The family also contains
  `def:mpu_admissible_equivalence_datum`, which has no source-labelled twin
  and requires continuously varying reduced source data for the actual
  blocked path and its conjugate, adjoint, transpose, and symmetry comparison
  paths. The continuity, index, equivalence, symmetry, and example nodes that
  depend on it record a separate continuous-selection gap. Four
  `**Scope restriction (full support)**` markers repeat the pointwise
  restriction.
- **Remediation**: one predicate on `MPOTensor d D` stating canonical form
  II for an MPU tensor by bundling `IsMPU`,
  `CPSVCanonicalFormIIData U.normalizedFlattening`, the equality
  $\sum_k D_k=D$ rather than the old `HasFullSupport` predicate, and an
  ambient positive definite diagonal trace-one fixed matrix $\rho$. The
  left-canonical equation is inherited from the CFII witness, but ambient
  diagonality is an additional field: blockwise diagonal fixed points may be
  scrambled by the ambient coisometry. The existing stabilization and
  normality theorems apply to the CFII and full-support fields, with
  $E^{\max(D^2-1,1)}=|\rho)(\Phi|$ stated as one power
  identity (no `D = 1` branch), normality, the forced-block simple
  contractions, and the five preservation lemmas proved once (the
  identity-ancilla and tensor-product lemmas build the `cfii` field with the
  retained witness constructors `normalizedDiagonalLiftCFIIData`,
  `tensorPhysicalIdCFIIData`, and `tensorProductCFIIData`, so only the
  `hasFullSupport_*` wrappers are deleted);
  their stabilized fixed matrix proved equal to the recorded $\rho$.
  `exists_reduced_cfii_representative` is strengthened to choose the ambient
  diagonal gauge and restated as the without-loss-of-generality theorem. This
  supplies the explicit $\rho^{\mathsf T}=\rho$ boundary now required by #7633
  under #5982, without an arbitrary nonsymmetric strengthening. While
  `HasFullSupport` still exists, current consumers derive it by unfolding the
  definition from the equality field. Every MPU-level step-7-to-13 statement
  (one that also assumes `IsMPU`, CFII data, full support, or the stabilized
  pair) is then migrated to the predicate or the equality directly, while the
  generic positive-metric constructions of `SourceFactors.lean` (lines
  82--476) and the gate constructors of `SourceUV.lean` (lines 141--202) keep
  their `(ρ) (hρ : ρ.PosDef)` parameters, since they assume nothing about
  $U$ and migrating them would shrink the API; only afterward delete
  `HasFullSupport`,
  the transports, the `fin_one` branch,
  `def:mpu_reduced_full_support_source_datum`, and only the
  admissible twins whose extra content is pointwise. In the same migration,
  delete or retarget the Chapter 28 tags on `def:mpu_full_support`,
  `thm:mpu_full_support_blocking`, `thm:mpu_full_support_reindexing`,
  `thm:mpu_physical_adjoint_full_support`, `thm:mpu_tensor_product_cfii_data`,
  `thm:mpu_identity_ancilla_reduced_cfii`, and
  `thm:mpu_normalized_transfer_fin_one`, and retarget the 17 surviving
  `\uses` references to `def:mpu_full_support` in 14 nodes (the
  reduced-representative, stabilization, forced-contraction, and normality
  nodes among them) to the convention predicate's node before that label is
  removed. Retain
  `def:mpu_admissible_equivalence_datum` and every node requiring its
  continuously varying path data until a continuous-selection theorem is
  proved. Keep the positive-power API in `TransferStabilization.lean` and the
  forced-block contractions in downstream `MatchingContractions.lean`; moving
  the latter into `CanonicalForm.lean` would create an import cycle through
  `SimpleBlocking.lean`. Rewrite
  `docs/paper-gaps/mpu_canonical_form_full_support.tex` as the pointwise
  convention record while keeping the pathwise supplier gap explicit.
- **First PR**: define the predicate in `CanonicalForm.lean` with the CFII,
  full-support-equality, and ambient-diagonal-$\rho$ fields. Use the existing
  theorems for normality and stabilization, prove that the stabilized matrix is
  this recorded $\rho$, and strengthen `exists_reduced_cfii_representative` to
  choose the ambient diagonal gauge; no consumer changes yet.

## D14. Residue of the pre-#7424 mixed-kernel route: five `MixedKernel*` modules, the reflected kernel, and their example twins  —  dead-weight, impact 5/10, effort 3/10
- **Status**: closed 2026-09-04 (#7658)
- **Evidence**: `MixedKernelOpenTail.lean` (246, of which five paper-gate
  $v$ identities and the weighted $X_1$ entry formula survive),
  `MixedKernelBoundary.lean` (105),
  `MixedKernelClosedNetwork.lean` (166), `MixedKernelRangeTransport.lean`
  (232), `MixedKernelSecondCutMetric.lean` (109),
  `ReflectedTransferKernel.lean` (396), `SuppliedWitnessReblocking.lean`
  (66), the `sourceY₁X₂`/`sourceX₁Y₂` half of `SourceUV.lean`, two mixed
  product formulas in `SourceFactorsTensorProduct.lean`,
  `normalized_mpo_tail_coisometry` in `MatchingContractions.lean`, and the
  mixed formulas of `Examples/ShiftSourceMixedKernels.lean` (908; 34
  zero-reference declarations): about 2,300 lines built to prove
  $u^\dagger u=1$ for the pre-#7424 gate $Y_1$--$X_2$ in the output-first
  orientation. Every consumer is another module of the set or an example
  file; the on-route proof in `SourceUCompleteNetwork.lean` uses none of it;
  21 Chapter 28 nodes tag these declarations;
  The retired range-restriction note stated that this route is no longer a
  route to `lemuisometry`.
- **Remediation**: delete the set (plan step 1 of the audit) after moving
  all five surviving $v$ identities to `StandardForm.lean`, moving
  `sourceX₁_weighted_isometry_apply` to `SourceFactors.lean`, and moving the
  shift examples' supplied factors and rank equivalences to
  `Examples/ShiftSourceFactors.lean`. Before deleting `sourceY₁X₂` and
  `sourceX₁Y₂`, delete or migrate all six remaining consumers in that
  destination file: the identity, right-shift, and left-shift entry formulas
  for each kernel. The surviving blueprint node
  `def:threeMPU_supplied_source_factors` lists eight declarations deleted by
  this step in its `\lean{}` tag: those six entries and the two mixed
  independent-tensor-product formulas. Remove all eight names or repoint them
  if replacements are introduced. Before deleting
  `ShiftSourceMixedKernels.lean`, also move
  `shiftTwoSitePhysicalEquiv`, the three shared four-spin matrices, and their
  five entry and product formulas to `ShiftSourceFactors.lean`; the surviving
  gate, blocked-formula, and swap-matrix modules use them. In the same step
  retire the `docs/tactic_patterns.md` candidate "supplied mixed-kernel
  indicator entries" (lines 1609--1627, all sixteen occurrences in the deleted
  formulas) and reword or drop its promoted-entry note at lines 899--900 that
  names the auxiliary $Y_1$--$X_2$ mixed-kernel consumer. Reword the
  surviving prose that treats the kernels as present (`StandardForm.lean`
  lines 14--15, `Examples/ShiftPaperSourceFactors.lean` lines 22--24,
  `ch28_mpu.tex` lines 5081--5082 and 8421--8426), and after every module
  deletion, the first PR's four included, regenerate the aggregators
  (`python3 scripts/generate_import_aggregators.py`, then `--check`), since
  `TNLean/MPS/MPU.lean` and `TNLean/MPS/MPU/Examples.lean` import the deleted
  modules and are never edited by hand. Correct the
  `MatchingContractions.lean` docstring, which disclaims the on-route
  input-first identity as auxiliary; delete the 21 nodes, explicitly including
  `thm:mpu_output_layer_tail_entry`, `thm:mpu_source_x1_range_projection`, and
  `thm:mpu_source_x2_range_projection`. Before deleting the supplied-witness
  and reflected-coordinate nodes, retarget
  `blockTensor_succ_simple2_of_supplied` and
  `IsMPU.simple1_of_simple2_supplied` to
  `thm:mpu_all_later_simple_blockings`, and retarget `bondPairSwapEquiv` with
  its apply and inverse formulas to a surviving physical-adjoint coordinate
  node. Repoint the admissible `ThmFund1` proof's dependency and prose reference
  to `thm:mpu_all_later_simple_blockings`, whose linked same-witness lemma is
  `MPOTensor.IsMPU.isMPUSimple_of_simple2`; retire the range-restriction note.
- **Resolution**: #7658 carried out the whole step in one pull request. The
  seven modules and `Examples/ShiftSourceMixedKernels.lean` are gone, the
  surviving $v$ identities and the weighted $X_1$ entry formula moved to
  `StandardForm.lean` and `SourceFactors.lean`, and the shift examples' shared
  witnesses moved to `Examples/ShiftSourceFactors.lean`. One theorem of
  `ReflectedTransferKernel.lean` that is not reflected at all,
  `normalizedDiagonal_blockTensor_mul_sq_eq_vecMulVec_of_transfer_power`,
  had gained an on-route consumer in `SourceURetainedInterior.lean` after the
  audit was written; it moved to `DoubleLayerContraction.lean` and keeps a
  blueprint node under the new label
  `thm:mpu_blocked_transfer_power_rank_one`. Twenty of the twenty-one nodes
  were deleted and that one was replaced. The range-restriction note is
  retired.

## D15. The MPU canonical-form endpoint predicate omits nonzero weights and full support  —  api-design, impact 2/10, effort 2/10
- **Status**: open
- **Evidence**: `MPUCanonicalForm.lean` (78 lines) defines
  `IsMPUCanonicalBlock`, `MPUCanonicalFormData`, and `IsMPUCanonicalForm`,
  the paper's canonical form CF (`Papers/1703.09188/paper_v2.tex` lines
  259--262: irreducible blocks with transfer spectral radius one, periodic
  blocks allowed, gauge free). Its sole consumer is the "in CF" endpoint
  clause of `StrictlyEquivalent` in `Equivalence.lean`, which transcribes
  `def:strictly-equivalent-tensors` (lines 708--714: endpoints "in CF", the
  path "not necessarily in CF"). `MPUCanonicalFormData` repeats every field
  of `CPSVCanonicalFormData` (`TNLean/MPS/CanonicalForm/Definitions.lean`)
  except the block predicate (irreducible with spectral radius one, against
  normal) and the `weights_ne_zero` local fix, and no lemma relates the two;
  `prop:normal-tensor` (lines 344--355), which says that an MPU tensor in CF
  has one block and that block is normal, is not stated for this predicate.
  The missing nonzero-weight field is logically prior: for $d=1$ and $D=2$,
  the tensor with sole matrix $\operatorname{diag}(1,0)$ is an MPU and has a
  current-form witness with two one-dimensional canonical blocks weighted by
  $1$ and $0$. Nonzero weights alone do not exclude the same tensor: it also
  has a one-block, weight-one witness embedded in the first coordinate, with a
  nontrivial ambient zero complement.
- **Remediation**: keep the clause. CF is gauge free while canonical form II
  (lines 271--281) fixes the gauge, so two MPU tensors in CF outside that
  gauge are strictly equivalent under the paper's definition; replacing the
  clause by the D13 convention predicate would add a hypothesis the source
  does not carry (the first limit of the `CLAUDE.md` convention rule: the
  paper writes "in CF" here and distinguishes CF, CFII, and SF throughout).
  First add `weights_ne_zero` and require $\sum_k D_k=D$ (equivalently, full
  support) in `MPUCanonicalFormData`, and update the source-labelled
  `def:mpu_canonical_form` blueprint statement before retaining its `\leanok`.
  Then prove `prop:normal-tensor` for `IsMPUCanonicalForm` on MPU tensors (one normal block), using transfer
  multiplicity only after the zero-weight witness is excluded. Finally extract
  a common retained-block reconstruction base with separate support-policy
  wrappers. Literal `CPSVCanonicalFormData` keeps $\sum_k D_k\leq D$ and its
  optional ambient complement; the MPU endpoint wrapper requires nonzero
  weights and $\sum_k D_k=D$. Parametrizing only the block predicate would
  conflate these two source policies.
- **First PR**: add `weights_ne_zero` and full support to
  `MPUCanonicalFormData`, update any direct witnesses, and add an inline
  `**Local fix (nonzero canonical weights and full support):**` marker in
  `MPUCanonicalForm.lean`. The marker must cite both
  `mpu_canonical_form_full_support.tex` for the ambient zero complement and the
  dedicated one-page paper-gap note titled "Nonzero weights in MPU canonical
  form" created in the same PR for the zero-coefficient convention. Update the
  `def:mpu_canonical_form` blueprint statement in the same PR. No one-block
  theorem or consumer changes yet.

## Honorable mentions (ranks 11-12)

- **D11 (plumbing tax)** — 486 `finCongr`/`Fin.cast` sites in 91 files;
  a 434-line proof repeating one insert-and-cancel calc four times
  (`MPS/CanonicalForm/CyclicSectors/Compression.lean:72`); 435
  inference-redundant `(d := d) (D := D)` annotations;
  `matrix_entry_cases` unpromoted at 10 occurrences. Fix as transport
  lemma packs, simp sets, and tactic promotion — not a Fin-generalization
  rewrite.
- **D12 (scope-restriction accumulation)** — 251 `**Scope restriction**`
  markers across 107 files (MPDO 82, ParentHamiltonian 46, RFP 38);
  headline results including
  `fundamentalTheorem_normalSquarePEPS_unconditional` are narrower than
  their cited sources. Mostly missing mathematics, not refactoring: track
  marker density, eliminate per-cluster definitional restrictions
  (closing-matrices and periodic-boundary families first).

## Quick wins flagged by the judges (below top-12 but near-free)

- **CLAUDE.md documentation rot** (#4527): PEPS/ (187 files, 73k lines) is still
  labelled "exploratory"; the nonexistent `Scratch/` is still referenced.
  One small PR; every agent session starts with a wrong map until then.
- **Tactic-ledger integrity** (#4528): `docs/tactic_patterns.md` claims
  `block_words` is "used across" three files, but it has zero invocations;
  `peps_prod_entry_congr` (x12) and `matrix_entry_cases` (x10) are past
  the promotion threshold. Fix the ledger and promote per
  `docs/tactic_development.md`.

## Rejected by adversarial verification (do not re-propose without new evidence)

- **MPV-predicate fragmentation** (8 comparison predicates): counts real,
  impact refuted — `SameMPV`/`SameMPV₂` are definitionally equal with zero
  conversion friction in 94 files; the variant predicates encode distinct
  paper hypotheses and merging them would conflict with the faithfulness
  rule. Surviving kernel: a small abbrev-unification cleanup, not a
  ranked debt.
- **Bare `simp` without lemma lists** (2,051 sites): impact refuted by
  bump history — the worst Mathlib adaptation cost 402 simp-related lines
  in one day, and broken sites were disproportionately calls *with*
  explicit lists; ~524 bare simps are terminal, which is idiomatic.
  Residual: a hygiene ratchet on the few hundred non-terminal sites only.

## Burned down / retired

(none yet)
