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
  repo-wide (their own definition), excluding instances and
  `@[simp]`/`@[grind]`-tagged lemmas. Largest concentrations:
  `Wielandt/RectangularSpan/Universality.lean` (144 ln),
  `Wielandt/RankOne/ExtractionFull.lean` (123 ln),
  `MPS/ParentHamiltonian/BNTBlockIntersection.lean` (117 ln).
- **Why it's excess**: no proof, no blueprint `\lean{}` tag, no doc
  reference — staged helpers for abandoned proof attempts.
- **First PR**: the Wielandt-module wave (~30 declarations, ~300+ lines) —
  the most isolated directory, zero blueprint exposure.

### S5. Retire the ch23 algebraic-FT route and the redundant TI CycleMPS mirror — net 2,400 lines, risk 6/10
- **Status**: open (#4565)
- **What**: `MPS/Chain/{GaugePhase,SameStateBridge}.lean`;
  `PiAlgebra/{Construction,FundamentalTheoremComplete,TIReduction}.lean`;
  `PEPS/{CycleMPSOverlapWindow,CycleMPSOverlapInsertion}.lean`; only the
  ~30-line redundant wrapper in `CycleMPSTranslationInvariant.lean` (NOT
  its ~150-line gauge-uniqueness theorem — see caution below);
  `blueprint/src/chapter/ch23_algebraic_ft.tex` (1,776 ln, already dormant).
- **Why it's excess**: the ch23 route proves a stronger-hypothesis variant
  gated on the never-instantiated `SameStateBridgeHyp`
  ([D2](#d2-fundamental-theorem-gauge-extraction-spine-re-instantiated-per-setting-capstone-conditional-on-an-unconstructed-bridge--abstraction-gap-impact-710-effort-710));
  a translation-invariant closed chain is the constant instance of the
  site-dependent one, so the TI window/insertion lemmas are second proofs
  of already-proved content.
- **Caution (verified)**: `CycleMPSTranslationInvariant.lean`'s
  `fundamentalTheorem_normalMPS_translationInvariant_gauge_unique` (~150-160
  ln) is the sole, currently-irreplaceable formalization of the source's
  uniqueness clause, `\leanok`-cited 3x from `ch24_peps_ft_normal_capstone.tex`
  — it only looks deletable because its chapter is dormant. It must be
  **relocated** into `CycleMPSOverlapCapstone.lean`, not deleted.
- **First PR**: rehome `piTrace_mul_right_eq_zero` into
  `BiCFDerivation/Core.lean`, then delete the four zero-consumer PiAlgebra
  files plus `GaugePhase.lean`/`SameStateBridge.lean` (~940 lines, zero
  blueprint exposure). The CycleMPS collapse and gauge-uniqueness
  relocation are separate follow-on PRs given the content-loss risk above.

### S12. Collapse duplicated spectral-split proofs onto `ProjectionSpectralSplit`/corner-compression API — net 520 lines, risk 5/10
- **Status**: open (#4566)
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

### S7. Delete the confirmed-dead half of the UnionInjectivityOverlap chain — net 750 lines, risk 4/10
- **Status**: open (#4567)
- **What**: `PEPS/RegionBlock/UnionInjectivityOverlap4.lean` (238 ln, 100%
  dead) plus the `overlapHostGeometry` sub-chain in
  `UnionInjectivityOverlap5.lean:139-349` (211 ln) plus scattered dead
  spans in files 1/2/3/6 (~123 ln). **Correction**: the original candidate
  wrongly proposed also collapsing files 1-2 (`overlapLeftGeometry`/
  `overlapRightGeometry`) — those are live, called directly by the
  chain's capstone proof, and must be kept.
- **Why it's excess**: the project's own paper-gap note
  (`docs/paper-gaps/peps_normal_ft_section3_route.tex`) documents this
  exact sub-route as an abandoned dead end that forced a switch to the
  surviving P0-outer parametrization.
- **First PR**: delete `UnionInjectivityOverlap4.lean` in full plus the
  211-line dead block in file 5. Net -449 lines, zero consumers, zero
  proof changes to the live capstone.

### S8. Derive injective-tensor Perron-Frobenius as a corollary of the irreducible-CP-map theory — net 400 lines, risk 6/10
- **Status**: open (#4568)
- **What**: the injective-only theorem bodies in
  `QPF/{PosDef,Uniqueness,Assembly}.lean` (~70 ln); the injective-named
  corollaries in `Spectral/{TransferOperatorGap,TransferOperatorGapRect,MPVOverlapDecay}.lean`
  (~330 ln, relocated to a new leaf file to dodge an import cycle through
  `TransferOperatorGapNT.lean`).
- **Why it's excess**: `IsInjective` strictly implies irreducibility via
  an existing one-composition bridge
  (`injective_implies_irreducibleCP` + `isIrreducibleTensor_of_isIrreducibleMap`),
  and both Wolf Thm 6.3 and the Wolf 6.6 rigidity argument need only
  irreducibility — every injective-hypothesis theorem is a direct
  instance of the already-proven irreducible one.
- **First PR**: the QPF half only — rewrite the three injective-only
  bodies as 2-3 line corollaries via the existing bridge. Net -70 lines,
  zero signature/consumer/blueprint changes.

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
  by `HasBiCF` across the missing bridge; `Axioms/Beigi.lean:104` binds the
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
  `mixedTransferMap₂_self` having 3 consumers. Repo-wide: 1,575 distinct
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
