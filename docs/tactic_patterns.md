# Tactic Pattern Ledger

Living registry of repeated proof patterns, maintained under the process in
[`docs/tactic_development.md`](tactic_development.md). Agents and contributors:
**consult the promoted section before writing proofs; append candidates when
you meet repetition; promote when the criteria are met.**

Entry format:

```markdown
### <short-name> — <status>
- **Pattern:** the repeated tactic block (fenced code)
- **Seen:** N occurrences (representative `file:line` list, or scanner output date)
- **Abstraction:** the promoted declaration, or the proposed one for candidates
- **Notes:** goal shape, caveats, line delta after refactor
```

Statuses: `candidate` (recorded, below promotion threshold or not yet
implemented), `promoted` (abstraction exists; call sites refactored),
`retired` (abstraction removed), `rejected` (examined and deliberately not
abstracted — record why, so it is not re-proposed).

---

## Promoted

### contiguous restriction of open-boundary MPS vectors — promoted
- **Pattern:** split a full-chain configuration into the words left of, inside,
  and right of a nonwrapping window; absorb both outside words into the boundary
  matrix; then use trace cyclicity to identify the restricted vector.
- **Seen:** duplicate private proofs in
  `TNLean/MPS/ParentHamiltonian/Martingale/OpenHamiltonian.lean` and
  `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalChain.lean` before promotion
  (2026-08-14).
- **Abstraction:** `MPSTensor.contiguousRestrictₗ_groundSpaceMap_mem_groundSpace`
  in `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean`.
- **Notes:** the candidate met the ledger's long-pattern two-file promotion
  criterion: both copies exceeded 70 lines and the nonwrapping restriction is
  shared ParentHamiltonian infrastructure. Both callers now use the public
  theorem, removing 70 Lean source lines net without changing their statements.

### ambient compression eigenbasis equations — promoted
- **Pattern:** derive that a compression eigenbasis vector is fixed by the first
  projection from subtype range membership, and recover its ambient compression
  eigenvalue equation by applying `Subtype.val` to the compressed equation.
- **Seen:** six paired occurrences across
  `TNLean/Analysis/TwoProjectionCompressionSpectrum.lean` and
  `TNLean/Analysis/TwoProjectionAngleOrthogonality.lean` before promotion
  (2026-08-13).
- **Abstraction:** `LinearMap.IsSymmetricProjection.rangeCompressionEigenbasis_apply_self`
  and `LinearMap.IsSymmetricProjection.rangeCompressionEigenbasis_apply_compression`
  in `TNLean/Analysis/TwoProjectionCompressionSpectrum.lean`.
- **Notes:** all six motivating call sites now use the public ambient equations;
  later two-projection block assembly can use the same facts without repeating
  subtype coercion arguments.

### fixed point from idempotent range membership — promoted
- **Pattern:** derive `P x = x` from `x ∈ LinearMap.range P` when `P` is
  idempotent.
- **Seen:** the two range-subtype arguments in
  `TNLean/Analysis/TwoProjectionAngleBlock.lean` and the compression-eigenbasis
  argument in `TNLean/Analysis/TwoProjectionCompressionSpectrum.lean` before
  cleanup (2026-08-14).
- **Abstraction:** `LinearMap.IsIdempotentElem.mem_range_iff` in Mathlib.
- **Notes:** use the forward implication directly rather than unpacking a range
  witness and applying idempotency by hand.

### pointwise idempotent endomorphism application — promoted
- **Pattern:** apply an equality `P * P = P` to a vector with `congrArg`, then
  simplify `Module.End.mul_apply` to obtain `P (P x) = P x`.
- **Seen:** nine occurrences across
  `TNLean/Analysis/ProjectionGeometry.lean` and
  `TNLean/Analysis/TwoProjectionAngleBlock.lean` before promotion (2026-08-12).
- **Abstraction:** `LinearMap.IsIdempotentElem.apply_apply` in
  `TNLean/Analysis/IdempotentEndomorphism.lean`.
- **Notes:** all motivating call sites now use the generic pointwise lemma. The
  abstraction assumes only a semiring, an additive commutative monoid, and a
  module; it does not depend on inner-product or projection symmetry.

### two-site cyclic local-embedding reindexing — promoted
- **Pattern:** reindex a cyclic two-site embedding by the equivalence between
  two-site configurations and ordered pairs, prove agreement outside the full
  window by finite index cases, and identify the extracted coordinates.
- **Seen:** the sector-specific public proof in
  `TNLean/MPS/MPDO/PhysicalSectorBondTwoSite.lean` and the private generic proof
  in `TNLean/MPS/MPDO/IsometricAdjacentBondTransport.lean` before promotion
  (2026-08-12).
- **Abstraction:** `MPOTensor.reindex_embedLocalOperator_two_zero` and
  `MPOTensor.reindex_embedLocalOperator_two_one` in
  `TNLean/MPS/MPDO/EmbedLocalOperatorTwoSite.lean`.
- **Notes:** the promoted theorems apply to arbitrary two-site matrices. The
  site-one conclusion states the factor exchange directly with
  `Matrix.reindex (Equiv.prodComm ...)`. The two
  `PhysicalSectorFactorization.reindex_embedLocalOperator_two_*` declarations
  remain public sector-specific specializations, while the isometric
  calculation uses the generic identities directly.

### Hayashi state evaluation in middle-sector coordinates — promoted
- **Pattern:** evaluate `EtaStructure.h_state` at decomposed middle-site coordinates,
  identify both inverse reindexings, apply the lifted-conjugation entry formula, and
  simplify the dependent block-state conditional.
- **Seen:** five occurrences in `HayashiSectorComparison.lean`,
  `BNTMarkovKeyFormula.lean`, `SectorFactorization.lean`,
  `BNTMarkovSectorProjectors.lean`, and `InverseMapActiveSectorRecurrence.lean`
  before promotion (2026-08-11).
- **Abstraction:** `HayashiMarkovDecomposition.h_state_apply_middle_sector` in
  `TNLean/Analysis/EntropyMarkovReverse.lean`.
- **Notes:** the theorem routes the coordinate evaluation through
  `HayashiMarkov.liftB_conj_apply` and `HayashiMarkov.blockState_apply` while retaining
  the dependent conditional for equal versus unequal sectors. Diagonal and off-diagonal
  consumers perform their respective specializations locally, while the mixed-sector
  consumer uses the full formula.

### retained vertical-copy dependent-cast evaluation — promoted
- **Pattern:** unfold the multiplicity-expanded assembled tensor at two coordinates
  in the same retained copy, identify the round-tripped dependent copy index, and
  transport both matrix coordinates across the resulting bond-dimension equality.
- **Seen:** three 30-line occurrences in
  `TNLean/MPS/MPDO/VerticalCopyBlocks.lean`,
  `TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean`, and
  `TNLean/MPS/MPDO/BNTAlgebraTensorClausePositivity.lean` before promotion
  (2026-08-11).
- **Abstraction:** `MPOTensor.verticalAssembledTensor_apply_copy_same` in
  `TNLean/MPS/MPDO/VerticalSectorCoordinates.lean`.
- **Notes:** the shared theorem is generic only in the existing dimension,
  multiplicity, weight, and tensor families. The structure-specialized caller
  supplies its fields directly, and all existing public declarations retain
  their statements. The refactor removes 98 lines and adds 38 Lean source lines.

### left finite-Gram cancellation in spectator coordinates — promoted
- **Pattern:** cancel the fiberwise finite Gram against its inverse Gram, then use
  the left-boundary common-map identity to recover the adjoint of the full
  ground-space map.
- **Seen:** duplicate 28-line arguments in the tail and full inverse-Gram C3
  correction factorizations before promotion (2026-08-10).
- **Abstraction:** `MPSTensor.leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
  in `TNLean/MPS/ParentHamiltonian/C3CorrectionBounds.lean`.
- **Notes:** both factorizations retain their statements and tail-after-left
  orientation; the shared theorem records only the exact finite-dimensional
  cancellation and makes no FNW or Nachtergaele numerical claim.

### single-Kraus Kronecker and isometric multiplication identities — promoted
- **Pattern:** unfold `singleKrausMap`, reassociate matrix products, and use
  Kronecker multiplication or the identity `Vᴴ * V = 1`.
- **Seen:** duplicate 7-line and 8-line helpers in
  `TNLean/MPS/MPDO/IsometricAdjacentBondTransport.lean` and
  `TNLean/MPS/MPDO/PhysicalSupportProductTransport.lean` before promotion
  (2026-08-10).
- **Abstraction:** `Matrix.singleKrausMap_kronecker` and
  `Matrix.singleKrausMap_mul_of_isometry` in
  `TNLean/Channel/SingleKrausPositivity.lean`.
- **Notes:** both consumer modules now invoke the two matrix identities directly;
  the private helper copies were removed.

### finite-sum submatrix distribution — promoted
- **Pattern:** prove that taking a submatrix commutes with a finite sum by
  extensionality and entrywise simplification.
- **Seen:** duplicate 6-line helpers in `TNLean/MPS/RFP/BNTOrthogonality.lean`
  and `TNLean/MPS/RFP/PhysicalObservableRealization.lean` before promotion
  (2026-08-10).
- **Abstraction:** `Matrix.submatrix_sum` in `TNLean/Algebra/FinSum.lean`.
- **Notes:** the theorem is polymorphic over the entry additive commutative
  monoid. Its four motivating calls now share the neutral matrix identity.

### transfer-map irreducibility in Kraus-map notation — promoted
- **Pattern:** use `Kraus.mapLM_eq_transferMap` to restate
  `IsIrreducibleMap (MPSTensor.transferMap F)` as
  `IsIrreducibleMap (Kraus.mapLM F)` before applying generic peripheral
  theorems.
- **Seen:** the five transfer-map compatibility declarations in
  `TNLean/Channel/Peripheral/{ClosureFixedPoint,CyclicGroup}.lean` (2026-08-09).
- **Abstraction:** `Kraus.isIrreducibleMap_mapLM_of_transferMap` in
  `TNLean/MPS/Core/TransferChannel.lean`.
- **Notes:** the generic theorems use `Kraus.mapLM`; each transfer-map statement
  applies this conversion once before invoking its generic counterpart.

### CFC square-root Hermiticity — promoted
- **Pattern:** derive `(CFC.sqrt ρ)ᴴ = CFC.sqrt ρ` from `CFC.sqrt_nonneg`,
  `Matrix.nonneg_iff_posSemidef`, and positive-semidefinite Hermiticity.
- **Seen:** six occurrences across `Channel/FixedPoint/Corollaries.lean`,
  `MaximalRank.lean`, and `WeightedCornerFixedPoints.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Matrix.conjTranspose_cfc_sqrt` in
  `TNLean/Analysis/MatrixSqrt.lean`.
- **Notes:** the helper needs no positivity hypothesis because `CFC.sqrt_nonneg`
  is unconditional. All six motivating proofs are now one-line applications;
  the caller files lose fifteen lines.

### positive-definite CFC square-root determinant unit — promoted
- **Pattern:** combine `CFC.isUnit_sqrt_iff`, `Matrix.PosDef.isUnit`, and
  `Matrix.isUnit_iff_isUnit_det` to prove `IsUnit (CFC.sqrt ρ).det`.
- **Seen:** four occurrences across `Channel/FixedPoint/Corollaries.lean` and
  `WeightedCornerFixedPoints.lean` before promotion (2026-08-09).
- **Abstraction:** `Matrix.PosDef.isUnit_det_cfc_sqrt` in
  `TNLean/Analysis/MatrixSqrt.lean`.
- **Notes:** the theorem retains the caller's `DecidableEq` instance so the
  determinant does not require proof-irrelevance transport. The four proof
  blocks become one-line applications.

### transfer-map trace-adjoint pairing — promoted
- **Pattern:** rewrite a linear map equality `E = transferMap K`, apply the
  finite-Kraus trace-adjoint identity, and unfold the adjoint transfer family.
- **Seen:** three occurrences across `Channel/Irreducible/FromSpectral.lean`,
  `PerronFrobenius.lean`, and `SpectralRadius.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Kraus.trace_mul_transferMap_adjoint` in
  `TNLean/Channel/Irreducible/KrausSetup.lean`.
- **Notes:** Channel callers use the theorem on the existing Kraus-setup import
  boundary, while `MPS.Core.TransferChannel` provides the root-level transfer-map
  compatibility statement without importing irreducibility theory. The declaration
  `Kraus.isChannel_transferMap` retains its name and statement but now requires the
  MPS compatibility import instead of `Channel.FixedPoint.MaximalSupport`; this
  intentional import-level change removes the former Channel-to-MPS dependency.

### pure gauge to heterogeneous repeated blocks — promoted
- **Pattern:** convert `GaugeEquiv A B` to `HetRepeatedBlocks A B` by passing
  through `EquivalentBlocks`, choosing unit phase, and embedding the
  equal-dimension repeated-block relation.
- **Seen:** four occurrences across
  `TNLean/MPS/Periodic/FundamentalTheorem.lean` and
  `TNLean/MPS/Periodic/ProportionalOverlap.lean` in the sectorwise-normalization
  draft (2026-08-02).
- **Abstraction:** `MPSTensor.GaugeEquiv.toHetRepeatedBlocks` in
  `TNLean/MPS/Periodic/FundamentalTheorem.lean`.
- **Notes:** the lemma fixes the otherwise easy-to-reverse orientation between
  pure gauges and `RepeatedBlocks`, while `HetRepeatedBlocks.trans` absorbs all
  bond-dimension casts. It replaces four explicit conversion chains with
  one-line calls; the source delta is four added lines after documentation.

### spectral-radius-one matrix dimension — promoted
- **Pattern:** exclude zero matrix dimension by observing that every
  endomorphism of the zero-dimensional square-matrix space has spectral radius
  zero.
- **Seen:** three occurrences across `CanonicalForm/Definitions.lean`,
  `CanonicalForm/NormalTensorGauge.lean`, and `Periodic/Defs.lean` before
  promotion.
- **Abstraction:** `matrix_dim_ne_zero_of_spectralRadius_eq_one` in
  `TNLean/Channel/Peripheral/Spectrum.lean`.
- **Notes:** the shared lemma is independent of positivity and transfer-map
  structure; callers supply only the spectral-radius-one identity. Net source
  delta: 0 lines relative to the unabstracted draft (14 removed, 14 added).

### positive-semidefinite support congruence — promoted
- **Pattern:** transport the support projection across an equality of positive
  semidefinite matrices while identifying the two positivity proofs by proof
  irrelevance.
- **Seen:** three occurrences across `MatrixFamilySupport.lean` and
  `WeightedHilbertSchmidt.lean` before promotion.
- **Abstraction:** `Matrix.PosSemidef.supportProj_congr` in
  `TNLean/Algebra/PosSemidefSupport.lean`.
- **Notes:** the lemma isolates the dependent proof transport that ordinary
  rewriting does not resolve directly.

### mpv_ext — promoted
- **Pattern:** `intro N σ` / `intro N hN σ` prelude for `SameMPV₂` /
  `SameMPV₂Pos` goals.
- **Abstraction:** `mpv_ext` (elab tactic, `TNLean/MPS/Tactic/Basic.lean`).
- **Notes:** elab rather than macro because it inspects the goal to
  distinguish the two predicate forms.

### transfer_simp — promoted
- **Pattern:** unfolding `transferMap A X` to `∑ i, A i * X * (A i)ᴴ`.
- **Abstraction:** `@[mps_transfer]` simp set + `transfer_simp` macro
  (`TNLean/MPS/Tactic/Basic.lean`).

### finite-sum common-left-factor normalization — promoted
- **Pattern:** a finite sum differs from a factored form only by pulling one
  index-independent left factor through summands of the form `a * f i * g i`.
  The original proofs used `rw`, `simp_rw`, or `simp only` with
  `Finset.mul_sum`, a `Finset.sum_congr` binder (tactic, functional, or
  semicolon form), and `ring`.
- **Seen:** 37 directly equivalent occurrences across 27 files:
  `TNLean/Algebra/PerronFrobenius/PerronVector.lean`,
  `TNLean/Analysis/MarginalSupport.lean`,
  `TNLean/Channel/BreuerHallIndecomposable.lean`,
  `TNLean/Channel/KoashiImoto/MarkovBipartiteBlockForm.lean`,
  `TNLean/Channel/WolfProps.lean`,
  `TNLean/Channel/Wigner/ProjectivePureState.lean`,
  `TNLean/Channel/Wigner/TwoPureStateCharpoly.lean`,
  `TNLean/Entropy/ClassicalMutualInformation.lean`,
  `TNLean/MPS/MPDO/BNTFusionTensorClauseFromRFP.lean`,
  `TNLean/MPS/MPDO/BNTLeftTripleFusion.lean`,
  `TNLean/MPS/MPDO/BNTProjectorSelection.lean`,
  `TNLean/MPS/MPDO/BNTRightTripleFusion.lean`,
  `TNLean/MPS/MPDO/BNTSectorAreaLaw.lean`,
  `TNLean/MPS/MPDO/BNTThreeSiteReducedClosure.lean`,
  `TNLean/MPS/MPDO/CompleteZipperFusionPentagon.lean`,
  `TNLean/MPS/MPDO/CyclicActiveFourthRegionFormula.lean`,
  `TNLean/MPS/MPDO/KatoDeformedRFPObstruction.lean`,
  `TNLean/MPS/MPDO/PerCopyHorizontalCF.lean`,
  `TNLean/MPS/MPDO/PhysicalSectorCoordinateTransport.lean`,
  `TNLean/MPS/MPDO/RepresentativeGroupedLemmaL.lean`,
  `TNLean/MPS/MPDO/TopologicalProjectorRecursion.lean`,
  `TNLean/MPS/MPDO/TopologicalTerminalSpectral.lean`,
  `TNLean/MPS/MPDO/VerticalProductPairBlocks.lean`,
  `TNLean/MPS/RFP/AppendixBSupport.lean`,
  `TNLean/MPS/RFP/BellPairCIDObstruction.lean`,
  `TNLean/MPS/RFP/StructuralFull.lean`, and
  `TNLean/PEPS/TorusWindowChain4.lean`.
- **Abstraction:** `Fintype.sum_mul_mul_eq_mul_sum_mul` in
  `TNLean/Algebra/FinSum.lean`.
- **Result:** all 37 sites call the shared lemma, and all 27 consumer files
  import `TNLean.Algebra.FinSum` directly. The broad final passes found 18 sites
  in 13 new files, including functional binders, one-line semicolon proofs,
  both levels of the nested `distribute` identity in
  `CyclicActiveFourthRegionFormula.lean`, and the two commutative-factor forms
  in `WolfProps.lean`. They replaced 47 old tactic source lines; together with
  the earlier 76, the promotion removes 123 repeated tactic lines. The broad
  final passes have 85 additions and 50 deletions in Lean source.
  Cumulatively, the promotion has 164 additions and 128 deletions, for a net
  36 Lean-source lines added; the increase comes from explicit factors in
  theorem applications rather than repeated per-summand proofs.
- **Audit scope:** at reviewed head `2231755c7`, the final audit examined all
  453 textual occurrences of `Finset.mul_sum` across 445 Lean source lines,
  without assuming a tactic head, rewrite direction, binder spelling, line
  breaks, or semicolon layout. Eight lines contain the token twice. The audit
  therefore used token occurrences for the broad population, but source-line
  windows and enclosing proof blocks for classification; duplicated tokens on
  one line were not counted as separate proofs. The forward-window triage
  retained 109 source-line windows across 55 files having `sum_congr` and
  `ring` within the next 16 lines. Two windows were the directly equivalent
  commutative-factor forms in `WolfProps.lean` and are now migrated. Among the
  remaining audited windows, 21 are token/nearby-step false positives, 60
  perform nested, two-sided, or reordered sums, and 26 use additional
  per-summand mathematics. These residual windows are category (B), not further
  instances identified as the promoted identity. Representative proofs
  simultaneously distribute both left and right factors or reorder nested sums
  (`EntropyMarkovReverse.lean`,
  `ProjectionGeometry.lean`, `BNTMarkovKeyFormula.lean`,
  `HayashiSectorComparison.lean`); rewrite each summand using mathematical
  hypotheses, field identities, indicators, or case splits
  (`Proportional.lean`, `CyclicActiveThreeBoundaryTrace.lean`, and the PEPS
  kernel-descent files); or combine subtraction, division, real-part, and
  two-sided sum transformations (the relative-entropy files). Some windows
  are deliberate false positives where the `ring` belongs to a later proof
  step, such as `TorusWindowChain3.lean`. The indicator expansion in
  `UnionInjectivityOverlap3.lean` remains in this class: it is part of a sum
  expansion and permutation, and replacing its inner reassociation by the
  shared lemma increases AC-normalization cost without removing that
  transformation. A stricter command-only screen leaves nine syntactic
  occurrences, forming six nested or indicator proof blocks, all among these
  category-(B) cases. Accordingly, this entry reports the 37 sites actually
  migrated and the residual candidate classification at the audited head; it
  does not claim repository-wide completeness or the absence of further
  `Finset.mul_sum`/`sum_congr`/`ring` combinations.

### dependent finite-sum flattening — promoted
- **Pattern:** pass between the double sum over `j` and `q : Fin (mult j)` and the
  single sum over `Fin (∑ j, mult j)` reindexed by `finSigmaFinEquiv.symm`.
- **Seen:** five proofs across `VerticalCanonicalForm.lean`,
  `CPSVVerticalCanonicalForm.lean`, `RFPPositiveFusionDecomposition.lean`,
  `CPSVVerticalDecomposition.lean`, and `PooledKrausFamily.lean` before promotion.
- **Abstraction:** `Fintype.sum_finSigmaFinEquiv` in
  `TNLean/Algebra/FinSum.lean`.
- **Notes:** the shared lemma is polymorphic over the additive commutative monoid,
  so callers retain only their application-specific summand.

### finite-sum coefficient isolation after complement substitution — promoted
- **Pattern:** split a finite sum into a chosen subfamily and its complement,
  replace each complementary vector by a scalar multiple of a vector in a
  second family, collect coefficients along the resulting finite map, and use
  linear independence of the combined family to isolate a chosen coefficient.
- **Seen:** three proof sites across
  `TNLean/MPS/CanonicalForm/BNTCharacterization.lean`,
  `TNLean/MPS/FundamentalTheorem/SectorBNT/ProportionalMatch/Core.lean`, and
  `TNLean/MPS/Periodic/ProportionalOverlap.lean` (2026-08-02).
- **Abstraction:** `LinearIndependent.coefficient_eq_zero_of_sum_eq_of_complement_smul`
  in `TNLean/Algebra/FinSum.lean`.
- **Notes:** the lemma is polymorphic over the scalar ring and module. The first
  two callers now retain only their decomposition-specific total-sum and
  complementary-state identities; the periodic overlap bridge is the third
  consumer that triggered promotion. The two existing caller files lose 145
  lines net.

### suffix marginal sector-block expansion — promoted
- **Pattern:** reindex a normalized reduced state into physical-sector
  coordinates, change the discarded-site sum to dependent sector fibers, and
  identify equal retained-sector words with a dependent block-diagonal entry.
- **Seen:** three suffix lengths in
  `CyclicActiveFourthRegionContraction.lean` and
  `CyclicActiveSuffixMarginal.lean` before promotion.
- **Abstraction:**
  `PhysicalSectorFactorization.reindex_reducedBlockState_add_eq_suffixSectorContraction`
  in `TNLean/MPS/MPDO/CyclicActiveFourthRegionContraction.lean`.
- **Notes:** the arbitrary suffix length is the mathematical parameter; the
  source-facing one-, two-, and three-suffix theorems are specializations.

### partial trace under product reindexing — promoted
- **Pattern:** split a simultaneous relabelling of both tensor factors into
  left- and right-factor submatrices, change the summation index in the traced
  factor, and compose the resulting submatrices.
- **Seen:** three occurrences across `PartialTrace.lean`,
  `RelativeEntropyDataProcessing.lean`, and `StrongSubadditivityPosDef.lean`
  before promotion.
- **Abstraction:** `Matrix.partialTraceRight_submatrix_prod_equiv` in
  `TNLean/Channel/PartialTrace.lean`.
- **Notes:** the two data-processing proofs now call the shared covariance
  theorem; the same theorem is also used to transport partial-trace Petz
  recovery from finite cyclic coordinates to arbitrary finite products.

### tripartite right partial trace after reassociation — promoted
- **Pattern:** reassociate a matrix indexed by
  \(A\times(B\times C)\) to \((A\times B)\times C\), expand the right
  partial trace, and identify the result with the direct tripartite trace over
  \(C\).
- **Seen:** three occurrences across `StrongSubadditivityPosDef.lean` and
  `SSAEqualityPetzRecovery.lean` before promotion.
- **Abstraction:** `Matrix.partialTraceRight_submatrix_prodAssoc` in
  `TNLean/Analysis/Entropy.lean`.
- **Notes:** the two strong-subadditivity data-processing proofs and the HJPW
  product-reference recovery proof now use the shared reassociation identity.

### eventual word-tuple span from selectors — promoted
- **Pattern:** propagate block injectivity from a positive length to the prefix remaining after
  a fixed selector suffix, concatenate the prefix and suffix, and simplify their total length.
- **Seen:** four occurrences across `PostBlockedRepresentativeSpan.lean` and
  `SourceBNTBlocking.lean` before promotion.
- **Abstraction:**
  `eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective` in
  `TNLean/MPS/MPDO/PostBlockedRepresentativeSpan.lean`.
- **Notes:** the shared theorem gives the explicit eventual threshold `s + p`; all four
  source-facing theorem statements and their selector-plus-injective-prefix proof route remain
  unchanged.

### invariant MPDO first-site action — promoted
- **Pattern:** extract the two doubled-index matrix entries from
  `P₁ H = P₁ H P₁` and `P₁ H = H P₁`, rewrite them as first-site action identities,
  and compose through the common left action.
- **Seen:** formerly handwritten in the BNT-basis and per-block proofs in
  `InvariantProjection.lean` and the representative proof in `HorizontalBNT.lean`; the
  literal CPSV original-space invariant proof uses the same identity.
- **Abstraction:**
  `MPOTensor.firstSiteActionAgree_braRight_ketLeftBraRight_of_invariant` in
  `TNLean/MPS/MPDO/InvariantProjection.lean`.
- **Notes:** the abstraction concludes the physical positive-length identity before any
  canonical-form separation. The BNT-basis, representative, per-block, and literal CPSV
  original-space callers now supply it to their respective forms of Lemma L.

### peps_prod_entry_congr — promoted
- **Pattern:** product congruence followed by component-function extensionality:
  `refine Finset.prod_congr rfl (fun w _ => ?_); congr 1; funext ie`.
- **Seen:** 12 expanded occurrences across 10 PEPS files before promotion. Nine call sites
  now use the shared lemma; one expanded occurrence is its proof, while the two occurrences
  in `RegionBlock/Recovery.lean` remain for the #4522 owner (2026-07-22).
- **Abstraction:** `regionProd_subtype_congr` in
  `TNLean/PEPS/RegionBlock/Basic.lean`, supported by
  `isRegionBoundaryEdge_of_disjoint_incident` for the repeated disjoint-region side goal.
- **Notes:** the abstraction is a lemma rather than a tactic and quantifies over arbitrary
  region physical configurations. The existing `regionProd_congr` statement is preserved
  as a wrapper. The migrated PEPS slice loses 60 source lines (92 additions,
  152 deletions); all existing theorem statements are unchanged.

### eta_cyclic_local_operator_transport — promoted
- **Pattern:** reindexing a translated two-site bond into cyclic edge coordinates, then
  proving it is block diagonal with a single active edge factor.
- **Seen:** two implementations: 269 declaration/proof lines in
  `PhysicalSectorProductRealization.lean` and 250 in
  `CommutingBondEtaCyclicTransport.lean` before the refactor.
- **Abstraction:** `MPOTensor.reindex_embedLocalOperator_etaPairBond` in
  `TNLean/MPS/MPDO/CommutingBondEtaCyclicCore.lean`; the physical-sector route supplies
  only its coordinate equivalence and local block-decomposition law.
- **Notes:** the physical specialization is 10 proof lines. Its two coordinate bridges
  are 30 and 44 declaration/proof lines. Including the dependency-neutral module split,
  the refactor removes 364 source lines overall (865 additions, 1229 deletions).

### physical-sector virtual-matrix transport — promoted
- **Pattern:** absorb two virtual matrices into the left and right tensor
  families of a physical-sector factorization, expand the transported physical
  slice, and discharge the equal- and unequal-sector blocks separately.
- **Seen:** two implementations exceeding 70 proof lines each in
  `PhysicalSectorGaugeTransport.lean` and
  `PhysicalSectorVirtualCompression.lean`; both also expanded the same
  neighboring contraction.
- **Abstraction:** `MPOTensor.PhysicalSectorFactorization.ofVirtualMatrices`
  and `ofVirtualMatrices_neighboringOperator` in
  `TNLean/MPS/MPDO/PhysicalSectorVirtualTransport.lean`.
- **Notes:** gauge transport specializes the two matrices to an invertible
  gauge and its inverse; virtual compression specializes them to an adjoint
  and its coordinate map.  The source-facing definitions and theorem
  statements remain unchanged.

### list_ofFn_products — promoted
- **Pattern:** induction on the length to distribute an ordered `List.ofFn` product over
  finite sums, or to extract scalar coefficients from such a product.
- **Seen:** the sum identity occurred in `SitewisePhysicalMatrix.lean`,
  `PhysicalSectorProductTransport.lean`, `CornerContraction.lean`,
  `MPS/Symmetry/Defs.lean`, and `MPS/Periodic/Symmetry/Theorem41Forward.lean`;
  the scalar identity also occurred in `TopologicalDensityDecomposition.lean`.
- **Abstraction:** `List.prod_ofFn_sum` and `List.prod_ofFn_smul` in
  `TNLean/Algebra/ListProduct.lean`.
- **Notes:** the common statements hold over arbitrary semirings, and each application
  imports the algebra module directly.  The two older symmetry proofs now pass through
  `evalWord_ofFn_eq_prod` and these shared identities.

### ofCommutingInvolutions_mul_conjTranspose — promoted
- **Pattern:** split a `Z₂ × Z₂` element into four cases, expand the representation,
  and prove unitarity from two unitary commuting involutions.
- **Seen:** the cluster-state and AKLT examples each used a four-case finite-matrix
  proof for their physical action.
- **Abstraction:** `ofCommutingInvolutions_mul_conjTranspose` in
  `TNLean/MPS/Examples/ZMod2.lean`.
- **Notes:** each example now supplies only the involution, commutation, and generator
  unitarity facts. The public action and unitarity theorem statements are unchanged.

---

## Completed refactors

### Finite Kraus setup for channels
- **Seen:** 2 occurrences in `Channel/Peripheral/IrreducibleChannel.lean` and
  `Channel/Semigroup/Primitivity/Helpers.lean` before promotion (issue #6576).
- **Abstraction:** `IsChannel.exists_kraus_map_eq_and_normalized` in
  `TNLean/Channel/KrausMap.lean` packages a finite Kraus family, the equality with
  its Kraus linear map, and the trace-preserving normalization.
- **Notes:** issue #6576 deliberately promoted this two-copy pattern before a third
  occurrence because both peripheral arguments require the complete setup. Each
  caller now uses one `obtain`; the refactor has a net Lean-source delta of
  6 lines (22 added, 16 removed).

### Literal-span form of block injectivity
- **Pattern:** recover the span of fixed-length word generators as `⊤` from an
  `IsNBlkInjective` hypothesis after the predicate was single-sourced through
  `Kraus.wordSpan`.
- **Reuse:** `MPSTensor.IsNBlkInjective.span_eq_top` in
  `TNLean/Kraus/Injectivity.lean` supplies the literal span equality.
- **Call sites:** the odd- and even-length Majumdar-Ghosh obstructions and the
  diagonal-restriction non-normality counterexample.

### Euclidean linear-map multiplicativity
- **Pattern:** prove that `Matrix.toEuclideanLin (A * B)` is the composition of the
  Euclidean linear maps represented by `A` and `B` by expanding both sides through
  `Matrix.toLin_mul` in the standard orthonormal basis.
- **Reuse:** `Matrix.toEuclideanLin_mul` in `TNLean/Analysis/TraceNormAbs.lean` is the shared
  layer-0 statement.
- **Result:** `TNLean/Analysis/MatrixReducedProjection.lean` uses the shared theorem directly,
  and `PositiveOnAbelian.Internal.toEuclideanLin_mul` remains as a compatibility wrapper for
  its three existing Channel call sites. The two-copy candidate was promoted early as required
  by issue #6525, preventing a third layer-crossing copy.

### One-step cyclic-forward offset
- **Identity:** `MPSTensor.cyclicForwardSite_one_offset` states that the old starting site has
  offset `N - 1` from its one-step cyclic successor.
- **Call sites:** `MPSTensor.cyclicRestrictₗ_restrictFirst` in `ParentHamiltonian/CyclicWindow.lean`,
  `MPSTensor.replaceWindow_three_replaceWindow_two_right` in
  `ParentHamiltonian/LocalSupportTransport.lean`, and
  `offset_from_finRotate` in `MPDO/PhysicalSectorBondTransport.lean` after identifying
  `finRotate N i` with `MPSTensor.cyclicForwardSite i 1`.

### Unequal retained vertical-copy evaluation
- **Pattern:** unfold an assembled vertical tensor at two retained coordinates whose copy
  indices differ, then reduce the cross-copy matrix entry to zero through the block-diagonal
  assembly.
- **Reuse:** `MPOTensor.verticalAssembledTensor_apply_copy_ne` in
  `TNLean/MPS/MPDO/VerticalSectorCoordinates.lean` owns the shared unequal-copy argument.
- **Result:** the former private implementations
  `VerticalCopyBlocks.verticalAssembledTensor_apply_copy_ne` in
  `TNLean/MPS/MPDO/VerticalCopyBlocks.lean` and
  `VerticalProductRetainedBlocks.verticalAssembledTensor_apply_copy_ne` in
  `TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean` now delegate to the shared owner.
  Unlike `MPOTensor.verticalAssembledTensor_apply_copy_same`, this theorem handles distinct
  retained copy indices and proves that the assembled tensor entry vanishes.

### Block-diagonal boundary assembly
- **Pattern:** decompose membership in a finite supremum of open-boundary block spaces into
  finitely supported components, choose one boundary matrix per component, rescale by the
  inverse block weight, and reconstruct one block-diagonal boundary matrix.
- **Reuse:** `BlockSumGroundSpace.exists_blockDiagonal_boundary_of_mem_iSup_groundSpace` in
  `TNLean/MPS/ParentHamiltonian/BlockSumGroundSpace.lean` performs the construction without
  any BNT, dual-fixed-point, or simultaneous-word-span hypotheses.
- **Result:** four public wrappers in `BNTBlockDiagonalChain.lean`,
  `BNTBlockDiagonalSourceNormalization.lean`, and `RFP/NNCPHMultiSector.lean` retain their
  statements and specialized interfaces while delegating the shared construction to the
  neutral theorem. The Lean source loses 36 lines net.

### Injective one-site trace-pairing zero detection
- **Pattern:** put a matrix in the kernel of `MPSTensor.traceMulRightPi`, expand the
  map pointwise, and use `traceMulRightPi_ker_eq_bot` to conclude that the matrix is zero.
- **Reuse:** `MPSTensor.eq_zero_of_forall_trace_mul_right_eq_zero` in
  `TNLean/Algebra/TracePairing.lean` accepts the pointwise vanishing trace pairings directly.
- **Result:** all six known expansions now invoke the shared consequence of injectivity:
  the three public selected-sector visibility proofs, the injective invariant-projection
  argument, the per-block Gram-map injectivity proof, and the one-site boundary block-window
  reconstruction. Their public statements are unchanged.

### Matched BNT coefficient comparison with an eventual scalar
- **Pattern:** expand both sector decompositions in MPV state space, substitute a full matched
  `Q`-basis into the full `P`-basis, reindex along the basis equivalence, and compare exact
  coefficients using eventual BNT linear independence.
- **Reuse:** the private file-local lemma
  `coeff_identity_via_matched_mpv_phase_scalar` in
  `TNLean/MPS/FundamentalTheorem/SectorBNT/CoeffIdentity.lean` carries an arbitrary eventual
  length-dependent scalar through the comparison.
- **Result:** the equal theorem specializes the scalar to one, while the proportional theorem
  retains its selected eventually nonzero scalar. The two public theorem names and statements
  are unchanged, and the Lean source loses 58 lines net.

### Boundary-crossing trace-family reuse
- **Pattern:** choose boundary-crossing matrices independently for every interval and
  complementary word, then separate the trace identity blockwise using the corresponding
  simultaneous word span.
- **Reuse:** `MPSTensor.blockDiagonal_boundary_crossing_trace_decompositions_of_boundary`
  supplies the global family, and
  `MPSTensor.pgvwc07_fixed_complementary_word_compatibility_of_trace_decomposition`
  performs the blockwise comparison.
- **Result:** `blockDiagonal_boundary_crossing_pgvwc_comparison_of_chainGroundSpace`
  now composes these two existing theorems instead of repeating the interval assignment,
  local crossing configuration, and choice bookkeeping. Its public statement is unchanged,
  and the proof body loses 41 lines.

### MPS word-factor extension
- **Pattern:** extend a one-letter identity `Z a * A i = F a * Y` to a nonempty
  physical word by multiplying the witness by the remaining suffix product.
- **Reuse:** `MPSTensor.exists_evalWord_factor_of_letter_compatibility` in
  `TNLean/MPS/Core/WordFactor.lean` handles arbitrary index types and matrix families.
- **Result:** `ParentHamiltonian/BlockStrip.lean` and
  `ParentHamiltonian/ExtendRight.lean` use the neutral shared theorem instead of
  maintaining specialized inductions. The existing public parent-Hamiltonian statements
  are unchanged, and `ExtendRight.lean` does not import the larger `BlockStrip.lean` cone.

### Boundary-crossing word split
- **Pattern:** split `List.ofFn σ` at the boundary-crossing index `N - i` into the
  segment before the cut followed by the wrapped segment after the cut.
- **Reuse:** `MPSTensor.ofFn_eq_boundary_crossing_tail_append_head` in
  `TNLean/MPS/ParentHamiltonian/BNTBlockDiagonalCrossing.lean` records the index
  arithmetic once.
- **Result:** the crossing-matrix and crossing-trace proofs call the shared list
  identity. Their theorem statements and the Chapter 13 endpoints are unchanged.

### Dependent sector projections and structural map congruences
- **Pattern:** cyclic-sector proofs duplicated the same heterogeneous projection lemmas,
  local-operator constructions duplicated scalar compatibility, and three entropy modules
  wrapped equality rewriting solely to erase Hermiticity witnesses.
- **Reuse:** `PhysicalSectorFactorization.sectorIndex_fst_heq_of_heq` and
  `PhysicalSectorFactorization.sectorIndex_snd_heq_of_heq` now belong to the neutral
  sector-index API, while `MPOTensor.embedLocalOperator_smul` belongs to the defining
  local-embedding module. `Entropy.mutualInformation_congr` in the basic entropy API
  handles the proof-dependent Hermiticity witnesses for all mutual-information callers.
- **Result:** the two cyclic-active modules and the two local-embedding consumers retain their
  existing propositions and declaration names with one proof body per shared fact. The local
  wrappers in `LocalPurificationAreaLaw.lean` and `RFPViaTSSAL.lean` were removed, and the
  pre-existing third wrapper in `MutualInformationDataProcessing.lean` now also uses
  `Entropy.mutualInformation_congr`.

### MPDO pair-trace separation duality
- **Pattern:** use Hahn--Banach separation for a proper pair-matrix submodule,
  represent the separating functional as a pair trace, and contradict trace
  separation by proving the representing pair is zero.
- **Reuse:** the private file-local helper
  `pair_matrix_span_top_of_pair_trace_separating` in
  `TNLean/MPS/MPDO/BiCFDerivation/Core.lean`.
- **Result:** three copies in the homogeneous, cumulative, and all-word pair-span
  criteria now reduce to generator membership facts. Public theorem statements and
  trace-pairing order are unchanged.

### Martingale coefficient upper bound
- **Pattern:** prove `((1 : ℝ) / (4 * (L : ℝ))) ≤ 1` from `hL : 1 < L` by
  deriving positivity of `L`, casting `1 ≤ L`, and clearing the positive denominator.
- **Reuse:** the private file-local lemma `martingale_coefficient_le_one` in
  `TNLean/MPS/ParentHamiltonian/Martingale/Reduction.lean` uses Mathlib's
  `div_le_one` to reduce the estimate to `1 ≤ 4 * L`.
- **Result:** four explicit gap-bound reductions now share the same coefficient
  estimate. Public theorem statements and proof routes are unchanged.

### Vanishing-complement subtype sums
- **Pattern:** replace a finite sum by the sum over a predicate subtype after proving that every
  term outside the predicate is zero.
- **Reuse:** apply Mathlib's `Finset.sum_congr_set` directly, with reflexivity on the predicate
  and the existing proof that the summand vanishes off it.
- **Result:** the two private copies were deleted, and all four call sites now use the Mathlib
  theorem directly: three in `CyclicActiveAdjacentCoefficientExtraction.lean` and one in
  `CyclicActiveFourthRegionFormula.lean`. The complete diff has 23 insertions and 34 deletions
  across three files.

### Cyclic offset inverse identity
- **Pattern:** adding the residue `(b + N - a) % N` to `a` modulo `N` recovers `b`
  when `a` and `b` are both less than `N`.
- **Reuse:** the public lemma `MPSTensor.add_offset_mod_eq` in
  `TNLean/MPS/ParentHamiltonian/Defs.lean` records this inverse identity.
- **Result:** `MPOTensor.windowComplementEquiv` in `CommutingForm.lean` and the shared
  `MPSTensor.cyclicShiftEquiv` in `ParentHamiltonian/CyclicWindowIndex.lean` apply the lemma
  directly, as does its original `MPSTensor.replaceWindow_extractWindow` caller. The initial
  promotion reduced the Lean sources by 41 lines net (6 insertions and 47 deletions).

### Cyclic window index and product decomposition
- **Pattern:** two physical-product modules privately defined the same cyclic shift,
  window/complement index equivalence, its two evaluation lemmas, and the resulting
  product factorization.
- **Reuse:** `MPSTensor.cyclicShiftEquiv`, `MPSTensor.cyclicWindowIndexEquiv`,
  `MPSTensor.cyclicWindowIndexEquiv_inl`, `MPSTensor.cyclicWindowIndexEquiv_inr`, and
  `MPSTensor.prod_cyclicWindow_complement` in
  `TNLean/MPS/ParentHamiltonian/CyclicWindowIndex.lean` provide the shared API; the
  product theorem holds for every commutative monoid. Isolating these declarations from
  `ParentHamiltonian/Defs.lean` avoids invalidating its broad downstream import cone.
- **Result:** the exact call sites are `reindex_sitewisePhysicalMatrix_windowComplement`
  and `embed_twoSiteSectorProjection_eq_finKronecker` in
  `PhysicalSupportProductTransport.lean`, and
  `reindex_physicalCoordinateMatrixN_windowComplement` in
  `PhysicalSectorProductTransport.lean`. Across the four changed Lean files, including
  the generated ParentHamiltonian aggregator, the final diff is 90 insertions and 87
  deletions, a net increase of 3 lines.

### Product-marginal support kernel
- **Pattern:** the simultaneous marginal-support whitening proof and the
  mutual-information estimate both need the support inclusion
  $\ker(\rho_A\otimes\rho_B)\subseteq\ker\rho_{AB}$ for a positive
  semidefinite bipartite operator.
- **Reuse:** `Matrix.PosSemidef.productMarginals_kernel_le` in
  `TNLean/Channel/MarginalSupportAbsorption.lean` records this support-kernel
  fact once, using the two marginal support absorptions.
- **Result:** `MarginalSupportWhitenedChoi` and the new entropy theorem
  `Entropy.mutualInformation_le_log_operatorSchmidtRank` both use the shared
  semantic support statement instead of repeating support-projector algebra.
  The source-facing theorem `Matrix.product_marginal_support` used in the
  strong-subadditivity argument is a direct corollary of the same statement.

### Support-correct tensor logarithm
- **Pattern:** `TNLean/Channel/Schwarz/SSAEqualityDPI.lean` carried a local
  simultaneous-diagonalization proof of the support-correct tensor logarithm.
- **Reuse:** `Matrix.log_kronecker_posSemidef` in
  `TNLean/Analysis/CfcKronecker.lean` is the canonical low-layer theorem.
- **Result:** the duplicate proof was removed from
  `TNLean/Channel/Schwarz/SSAEqualityDPI.lean`; the faithful entropy comparison
  uses the Analysis declaration directly.

### Transpose covariance of the continuous functional calculus
- **Pattern:** `TNLean/Analysis/LiebConcavity.lean` carried a private copy of
  the conjugation star-algebra homomorphism and its functional-calculus
  covariance proof solely to commute real powers with transpose.
- **Reuse:** `Matrix.cfc_transpose` in `TNLean/Analysis/CfcConjugation.lean`
  supplies the public covariance theorem.
- **Result:** `rpow_transpose` keeps its private interface and now reduces to
  the public theorem after rewriting both powers as continuous functional
  calculi; the duplicated private conjugation stack was removed.

### Positive-semidefinite sandwich by real powers
- **Pattern:** three sandwiched Rényi proofs separately proved that a real power
  of the reference matrix is positive semidefinite and used Hermiticity to
  identify the resulting congruence with an equal-factor sandwich.
- **Reuse:** `_root_.Matrix.PosSemidef.rpow_mul_mul_rpow` in
  `TNLean/Analysis/SandwichedRenyiTwo.lean` proves
  `(ω ^ r * ρ * ω ^ r).PosSemidef` from `ρ.PosSemidef` and
  `ω.PosSemidef`, for arbitrary real `r`.
- **Result:** `sandwichedRenyiTwoTrace_nonneg`, `sandwichedRenyiTrace_nonneg`,
  and `sandwichedRenyiTrace_two` retain their statements and each obtain the
  sandwich positivity in one application.

### Hermitian spectral quadratic-form weights
- **Pattern:** two Jensen proofs separately diagonalized a Hermitian matrix, evaluated vector
  quadratic forms as eigenvalue-weighted sums, and proved that the squared eigenbasis
  coordinates of a unit vector form a probability distribution.
- **Reuse:** `Matrix.IsHermitian.spectralWeight`, `sum_spectralWeight`,
  `re_dotProduct_mulVec_eq_sum`, and `re_dotProduct_cfc_mulVec_eq_sum` in
  `TNLean/Analysis/SpectralQuadraticForm.lean` provide the basis-independent API used by both
  `SupportLogJensen.lean` and `Channel/Schwarz/DiagonalJensen.lean`.
- **Result:** the Channel proof imports the lowest-layer Analysis helper instead of carrying its
  own spectral calculation, while the support-aware logarithmic proof uses the same formulas and
  removes zero-eigenvalue terms explicitly through its support-weight vanishing lemma.

### Distinguished grouped reference corner
- **Pattern:** the horizontal BNT-refined and literal CPSV actual-grouped Figure~8 proofs
  both select the zero-index copy, use its identity gauge, and transport its physical corner
  through the equality of bond dimensions with a chosen copy.
- **Reuse:** `MPOTensor.exists_distinguished_grouped_reference_corner` in
  `TNLean/MPS/MPDO/GroupedReferenceCorner.lean` constructs the transported positive corner
  without any canonical-form hypothesis. The two Figure~8 theorems supply only their own
  pairwise marked-separation result.
- **Result:** the existing horizontal theorem keeps its statement, the literal theorem uses
  the same dimension-dependent construction, and neither canonical-form surface is adapted
  to the other.

### Grouped-sector Figure Eight and Gram rigidity
- **Pattern:** the horizontal BNT-refined and literal CPSV grouped-sector proofs repeated the
  distinguished-corner comparison and the subsequent normal-commutant argument, differing
  only in the theorem that equates two positive-corner Gram dressings.
- **Reuse:** `MPOTensor.HasGroupedCornerGramDressing`,
  `grouped_sector_gram_conj_eq_of_dressing`, and
  `grouped_sector_gram_eq_pos_smul_one_of_dressing` in
  `TNLean/MPS/MPDO/GroupedSectorGram.lean` isolate the predicate-neutral Figure Eight and
  Gram-rigidity steps.
- **Result:** both Figure Eight and Gram-normalization theorem families keep their exact public
  statements and independently supply their literal-CPSV or horizontal Gram-dressing theorem.
  No implication between the two canonical-form predicates is used.

### Positive-Gram provider for normalized grouped sectors
- **Pattern:** the horizontal BNT-refined and literal CPSV grouped-sector theorems
  differed only in how they obtained a positive scalar Gram identity for each
  copy gauge.
- **Reuse:** `MPOTensor.exists_normalized_grouped_sector_maps_of_gram` takes this
  positive-Gram provider as its sole canonical-form-specific input and proves the
  common isometry, orthogonality, intertwining, and exact reconstruction clauses.
- **Result:** `MPOTensor.IsMPDO.exists_normalized_grouped_sector_maps` and
  `MPSTensor.IsCPSVCanonicalForm.exists_normalized_grouped_sector_maps` remain
  separate public wrappers, each supplying its own Gram theorem without adapting
  one canonical-form hypothesis to the other.

### Vertical canonical form from grouped sectors
- **Pattern:** the literal CPSV and horizontal capstones both unpacked the same grouped BNT
  witness, built the vertical BNT, normalized its sector maps, and reindexed the same dependent
  double sum before applying the grouped-sector coisometry theorem.
- **Reuse:** `MPOTensor.verticalCF_of_grouping_and_gramDressing` in
  `TNLean/MPS/MPDO/VerticalCanonicalFormConstruction.lean` takes
  `HasVerticalBNTGroupingWithIsometry M` and `HasGroupedCornerGramDressing M`; it does not require
  an unused `IsMPDO M` hypothesis.
- **Result:** `verticalCF_of_cpsvCanonicalForm` and `verticalCF_of_horizontalCF` are thin,
  source-facing wrappers. Each independently supplies its own grouping theorem and pairwise
  Figure Eight theorem, preserving the strict separation of their canonical-form predicates.

### Canonical-form sector-compression separation
- **Pattern:** the horizontal BNT-refined and literal CPSV surfaces separately turned
  vanishing finite-chain compressions into zero first-site insertions, then converted
  the insertion equality back into vanishing vertical corners.
- **Reuse:**
  `MPOTensor.exists_sectorCompression_ne_zero_of_corner_of_insertedTensor_eq` accepts
  the original-space Lemma L provider; each canonical-form surface supplies its own
  insertion-equality theorem.
- **Result:** both public sector-compression separation statements are thin wrappers,
  and the shared argument uses no positivity, grouping, or weight normalization.

### Displaced-projector periodic contradiction
- **Pattern:** two canonical-form surfaces separately derived first-site insertion equality
  from hypothetical all-length commutation, then repeated the same periodic-vector
  contradiction at the resulting noncommuting length.
- **Reuse:** `MPOTensor.exists_not_commute_of_displaced_of_insertedTensor_eq` accepts the
  original-tensor Lemma L provider, and
  `MPOTensor.hasNoPeriodicVectors_verticalTensor_of_exists_not_commute_of_displaced` accepts
  the resulting displaced-idempotent noncommutation provider.
- **Result:** the horizontal BNT-refined and literal CPSV public theorems are thin wrappers;
  their statements and existential chain-length quantifiers are unchanged.

### Blocked-basis coercion reconstruction
- **Pattern:** blocked support-algebra coordinate proofs coerced finite sums
  into ambient matrices with unrestricted `simp`, which launched an expensive
  and irrelevant search for a `Nonempty` instance on the basis index.
- **Reuse:** `coe_reconstructFromBlockedCoefficients_apply` now transports the
  reconstruction equation through the subalgebra subtype map explicitly with
  `map_sum` and `map_smul`; the product formula composes the two reconstruction
  equations directly.
- **Result:** the worst reconstruction declaration falls from 1.68 seconds to
  below one second in the declaration profiler, and a clean full-source check
  completes in 15.39 seconds.

### Fourfold F-move entry normalization
- **Pattern:** five fourfold synthesis proofs separately took one matrix entry of
  `rightTripleSynthesis_mul_printedFMatrix` and ran the same dependent-sum
  normalization.
- **Reuse:** the private theorem
  `rightTripleSynthesis_mul_printedFMatrix_entry` records the normalized scalar
  identity once; each fourfold proof specializes it to the relevant subtree.
- **Result:** across five forced isolated rebuilds on one warm dependency cache,
  median Lake time falls from 5.60 to 5.50 seconds, wall time from 7.37 to
  7.24 seconds, and user CPU from 15.23 to 14.91 seconds.

### Bilinear closure of cumulative word spans
- **Pattern:** the cumulative-span multiplication proof expanded binary span
  induction into seven branches, then normalized linearity with broad `simp`
  calls.
- **Reuse:** `LinearMap.BilinMap.apply_apply_mem_of_mem_span` extends matrix
  multiplication from pairs of word generators to both spans; only the
  generator-product lemma remains local.
- **Result:** across five forced isolated rebuilds on one warm dependency cache,
  median Lake time falls from 4.40 to 2.80 seconds, wall time from 6.74 to
  4.55 seconds, and user CPU from 6.54 to 3.17 seconds. No event in the optimized
  file exceeds the profiler's 100-millisecond reporting threshold.

### Positive-congruence similarity evaluation
- **Pattern:** the spectral-radius proof repeatedly unfolded `similarityMap`
  and asked broad `simp` calls to rediscover the same inverse and Hermitian
  square-root identities.
- **Reuse:** the local `hsim_apply` equation records that evaluation once.
  The transformed eigenvector proof then cancels the two inverse pairs through
  an explicit matrix identity instead of normalizing the whole expression.
- **Result:** the main Wolf 6.3 declaration falls from 6.21 to 5.60 seconds in
  the declaration profiler, and the clean full-source check completes in
  15.34 seconds.

### Inverse physical action from a twisted companion
- **Pattern:** the virtual-unitary construction in `StringOrderAux.lean`
  combined scalar normalization, transfer-map scaling, and the full inverse
  physical-action calculation in one large proof.
- **Reuse:** `inverse_physical_action_of_twisted_companion` isolates the
  unitary change-of-basis calculation, while `transferMap_smul_apply` replaces
  the entrywise scaled-Kraus expansion.
- **Result:** `virtualUnitary_of_gaugePhaseEquiv_twisted` falls from 13.3 to
  6.7 seconds in the declaration profiler. The full profiled source check falls
  below 25 seconds locally, with every declaration below 7 seconds.

### Anticommuting-involution projective multiplication
- **Pattern:** split both `Z₂ × Z₂` inputs into sixteen cases, expand two concrete
  `2 × 2` matrices entrywise, and normalize every resulting scalar expression.
- **Reuse:** `mul_of_anticommuting_involutions` in `MPS/Examples/ZMod2.lean`
  proves the multiplication table once from the two involution laws and their
  anticommutation law. `clusterProjRep` now supplies only those three relations.
- **Result:** the concrete sixteen-case proof in `MPS/Examples/Cluster.lean`
  is replaced by one exact application; its previously profiled 31-second
  declaration falls below the 200-millisecond profiler threshold.

### Unit-norm complex scalars are nonzero
- **Pattern:** proofs repeatedly converted `h : ‖z‖ = 1` into `z ≠ 0` with
  `norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)`.
- **Reuse:** `Complex.ne_zero_of_norm_eq_one` in
  `TNLean/Algebra/ComplexPhasePositivity.lean` now states this scalar fact once.
- **Result:** a repository-wide semantic audit migrated 32 call sites across
  18 files, including nested `inv_ne_zero` uses and tactic-form contradiction
  proofs. No exact-hypothesis conversion from `h : ‖z‖ = 1` to `z ≠ 0`
  remains outside the shared lemma itself. The related proof from
  `star α * α = 1` in `PeripheralUnitary.lean` remains separate because its
  premise is not the helper's norm equality. All theorem statements and
  mathematical scopes are unchanged.

### Support left-right and relative-modular intertwining
- **Pattern:** `supportRelativeModular_sourceB_solution` and
  `supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular`
  each proved positive definiteness of
  `t • 1 + A ⊗ₖ hB.supportInvᵀ` and expanded the same matrix calculation
  \(S(1 \otimes P_B^{\mathsf T}) = (1 \otimes B^{\mathsf T})R\).
- **Reuse:** Both proofs now use `supportRelativeModular_resolvent_posDef` and
  `supportLeftRightSuperoperator_mul_supportProj_eq` from
  `Channel/Schwarz/SupportRelativeModular.lean`. The intertwining theorem only
  assumes positivity of `B`; positivity of `A` is confined to the positive-definiteness
  theorem.
- **Result:** The two Lean files have 49 insertions and 45 deletions: the repeated
  derivations are replaced by two source-facing algebraic lemmas and their call sites.
  All pre-existing public theorem statements and mathematical scope are unchanged.

### Concrete two-block injectivity through the standard matrix basis
- **Pattern:** prove that an arbitrary `2 × 2` matrix lies in a range span by
  expanding its four entries as a hand-written linear combination of matrix units.
- **Reuse:** `cluster_isNBlkInjective_two` and `aklt_isNBlkInjective_two` now use
  `Submodule.eq_top_iff_forall_basis_mem` with `Matrix.stdBasis`, discharging the
  four basis cases from their existing matrix-unit membership lemmas.
- **Result:** both theorem statements are unchanged, and their previously profiled
  multi-second declarations fall below the one-second profiler threshold.

### Blocked physical-dimension nonzeroness and explicit-gap specialization
- **Pattern:** four local calculations in `Martingale/BlockedGap.lean` repeated the same
  three-line construction of `NeZero (blockPhysDim d p)`, and the qualitative blocked-gap
  theorem repeated the anticommutator route already used by the preceding explicit-gap theorem.
- **Reuse:** `TNLean/MPS/Core/Blocking.lean` now provides the instance
  `MPSTensor.instNeZeroBlockPhysDim`, replacing exactly those four local calculations in
  `Martingale/BlockedGap.lean`.
  `IsPrimitiveMPS.exists_blockTensor_parentHamiltonianES_gapped` is now a thin
  corollary of `IsPrimitiveMPS.exists_blockTensor_parentHamiltonianES_gap_eighth`,
  using `1 / 8` as the positive gap witness.
- **Result:** The public theorem signatures and order in
  `TNLean/MPS/ParentHamiltonian/Martingale/BlockedGap.lean` are unchanged.

### Non-decaying-overlap dimension and gauge-phase dichotomy
- **Pattern:** The `hDim`/`hGPE` tails of
  `exists_state_scalar_of_nondecaying_overlap` (`MatchAux.lean`) and
  `exists_block_match_exact_of_eventuallyProportional`
  (`ProportionalMatch/Core.lean`) each re-ran the same two by-contradiction
  applications of the irreducible-TP overlap dichotomies
  (`mpvOverlap_tendsto_zero_of_dim_ne_of_irreducible_TP` and
  `mpvOverlap_tendsto_zero_of_not_gaugePhaseEquiv_cast_left_of_irreducible_TP`),
  about 22 lines verbatim in both files.
- **Reuse:** Both proofs now obtain `⟨hDim, hGPE⟩` from
  `dim_and_gaugePhase_of_nondecaying_overlap` in `SectorBNT/MatchAux.lean`,
  with the two `NeZero` instances moved inside the shared lemma.
- **Result:** 2 files changed, 22 insertions against 30 deletions (8 lines
  net). All public theorem statements and blueprint links are unchanged.

### Exact-sector matching through the proportional core
- **Pattern:** The equal-MPV sector matcher repeated the eventually-proportional
  matcher's fixed-length linear-independence and coefficient-comparison proof
  instead of specializing it at scalar `1`.
- **Reuse:** `exists_block_match_exact` now applies
  `exists_block_match_exact_of_eventuallyProportional` through
  `SameMPV₂Pos.toNonzeroProportionalMPV₂` and
  `NonzeroProportionalMPV₂.eventually`. The two low-level overlap lemmas used
  by the surviving proof live in `SectorBNT/MatchAux.lean`.
- **Result:** Across `ExactMatch.lean`, `ProportionalMatch/Core.lean`, and
  `MatchAux.lean`, the declaration count fell from 7 to 6. The
  exact-match-specific proof bodies fell from 195 lines to 2 lines, counting
  from the first tactic after `:= by` through the last tactic. Total source
  lines fell from 666 to 481 (185 lines net). The public theorem statement and
  blueprint link are unchanged.

### Bijective sector matching from directional existentials
- **Pattern:** The equal-MPV (`bijective_match_of_sameMPV`) and proportional
  (`bijective_match_of_eventuallyProportional`) bijection constructions each
  rebuilt the same injective-map-plus-cardinality argument (the `φ₀`-centred
  rebase, `Fintype.card_le_of_injective`, `Equiv.ofBijective`), about 75
  lines verbatim in both files.
- **Reuse:** Both theorems now call `bijection_from_matches` in
  `SectorBNT/MatchAux.lean`, parameterized by the forward and backward
  existential-match hypotheses. The equal-MPV existentials are obtained from
  the proportional matcher through
  `SameMPV₂Pos.toNonzeroProportionalMPV₂.eventually`, and the proportional
  matcher itself moved down to `ProportionalMatch/Core.lean` so both routes
  sit above it in the import graph.
- **Result:** `StrongMatch.lean` fell from 259 to 72 lines and
  `ProportionalMatch.lean` from 267 to 140; `MatchAux.lean` grew by 85 lines
  and `ProportionalMatch/Core.lean` by 34. Net 176 insertions against 320
  deletions (144 lines net). All public theorem statements and blueprint
  links are unchanged.

### Cyclic-sector compression transport
- **Pattern:** the transfer-intertwining branch in
  `exists_compressedTensor_of_supported_projection_with_letter_and_isometry`
  manually reopened both reindexed block coordinate systems to prove the
  per-letter identity.
- **Reuse:** prove the already-returned letter-expansion identity before
  packaging the existential, then compose `cornerCompressionExpand_mul` and
  `cornerCompressionExpand_conjTranspose`.
- **Result:** the theorem proof decreased from 421 to 362 lines (59 lines net),
  with no new declaration; the file diff is 18 insertions and 77 deletions.

### Three-way merge collapse through the regionMerge calculus
- **Pattern:** each of the three `triMerge` product lemmas re-proved the per-vertex
  read-back of a nested `mergeVirtualConfig` by hand: `Finset.prod_congr`,
  `congr 1; funext ie`, a `by_cases` ladder over each region's incidence, and
  `mergeVirtualConfig_of_pos`/`mergeVirtualConfig_of_neg` rewrites, with the
  crossing-agreement step inlined at each leaf.
- **Reuse:** `redProd_triMerge` is a one-line `regionProd_eq_merge` application
  (`triMerge` is definitionally the nest
  `regionMerge red (ζr, regionMerge blue (ζb, ζc))`); `blueProd_triMerge` chains
  `regionProd_eq_merge` with `regionProd_p2_eq_merge_of_incident_agree` at the red
  merge region, the agreement being `TripleAgrees.rb` through
  `isCrossing_rb_of_incident`; `complProd_triMerge` chains two
  `regionProd_p2_eq_merge_of_incident_agree` applications (blue, then red), the
  red step reading `ζc` from the inner merge via the new partition fact
  `not_isRegionIncidentEdge_blue_of_crossing_rc` (a red-to-complement
  crossing edge misses the blue region).
- **Result:** `RegionBlock/CoarseThreeSite5.lean` loses 2 source lines net
  (34 insertions, 36 deletions across two commits): the three product-lemma
  proofs fall from 33 tactic lines to 13 term lines while the new crossing lemma
  adds 18 lines. Every declaration name and statement, including the `triMerge`
  body, is unchanged; the `triFiber_card`, `agreeing_summand_eq`, and
  `agreeingTripleSum_collapse` consumers compile untouched.

### Gauge-extraction ladder packaged for matrix-algebra endomorphisms
- **Pattern:** three sites re-ran the same four-step gauge ladder —
  simplicity-bijectivity (`linear_mul_endomorphism_bijective`) →
  `linearMapToAlgHom` → `AlgEquiv.ofBijective` → `skolemNoether_matrix` → inner —
  plus per-site shims unwrapping the algebra equivalence back to the linear map:
  four `change`-shims in `fundamentalTheorem_singleBlock`
  (`MPS/FundamentalTheorem/Basic.lean`), a 7-line `f`↦`Φ` unwrap in
  `exists_conjugation_of_sameState` (`PEPS/CycleMPSChainOverlapInsertion.lean`),
  and three `show … from rfl` rewrites in
  `forward_det_one_implies_unitaryChannel`
  (`Channel/Determinant/UnitaryCharacterization.lean`). Two sites also
  duplicated a 5–6-line unital⇒nonzero inline proof.
- **Reuse:** `Matrix.exists_inner_of_linear_mul_endomorphism` relocated from
  `FundamentalTheorem/Basic.lean` to `Algebra/SkolemNoether.lean` beside its
  three ingredients; all three sites now obtain the gauge matrix in one
  `obtain`, and the unital⇒nonzero duplications use the new
  `Matrix.linearMap_ne_zero_of_map_one` (`T 1 = 1 → T ≠ 0`).
  `Chain/AlgebraIsomorphism.lean` now imports `Algebra.SkolemNoether` directly
  (its `FundamentalTheorem.Basic` import existed solely for the lemma).
- **Result:** 5 files changed, 51 insertions against 64 deletions (13 lines
  net; 29 lines net at the three migration sites). All theorem statements and
  blueprint links unchanged. This finishes #4595's migration and discharges
  the last open item of #4518 (ledger D2).

### UnionInjectivity ↔ UnionInjectivityGeneral2 mirror kill
- **Pattern:** three `NormalEdgeBlockingData`-parametrized theorems
  (`complCoeff_combination_eq_zero`,
  `regionBlockedWeight_complement_eq_smul_constrained`,
  `regionBlockedTensorInjective_union`) duplicated their
  bare-`ThreeBlockGeometry` twins in `UnionInjectivityGeneral2` as
  rename-identical 108/166/117-line proof bodies; the D-versions derive
  blue/compl injectivity internally, so the g-versions' injectivity arguments
  come for free.
- **Reuse:** `NormalEdgeBlockingData.toThreeBlockGeometry` (a structure literal
  whose projections reduce definitionally) plus re-proof of each D-theorem as a
  2–3-line wrapper over its `ThreeBlockGeometry` twin. All data conversions
  (`threeBlockComplPhysical`, `threeBlockComplCoeff` through the
  `swapBlueComplement` abbrev, `blueRedCrossingBondProd`) close by plain defeq —
  no bridge lemmas. Statements byte-identical, including the unused
  `_hblue`/`_hcompl` hypotheses.
- **Result:** `RegionBlock/UnionInjectivity.lean` drops from 906 to 244 lines
  (net −662), landed together in #4817 in two stages: the wrapper migration
  (906 → 628, +34/−312, net −278, 4 commits) and the deletion of the 12
  orphaned D-side helper declarations with their docstrings and the orphaned
  section docs (+7/−391, net −384). The sole external consumer
  `regionBlockedTensorInjective_compl_red` and the blueprint ch24 `\lean{}` tags
  are untouched; the two surviving docstring citations are re-pointed at the
  `ThreeBlockGeometry` twins.
- **Follow-up (#4822):** the two surviving wrappers were code-dead (no Lean
  consumers; all call sites use the `ThreeBlockGeometry` twins), so they were
  dropped together with their section docs, and the `IsBlueRedCrossingEdge` +
  `blueRedCrossingBondProd` D-side support chain cascaded with them (its only
  consumer was the deleted collapse wrapper; the live consumers all use the
  `ThreeBlockGeometry` versions). The vestigial `_hblue`/`_hcompl` hypotheses
  came off `regionBlockedTensorInjective_union`'s signature (the proof already
  re-derives both internally via `regionBlockedTensorInjective_blue`/
  `regionBlockedTensorInjective_complement`), and the sole consumer
  `regionBlockedTensorInjective_compl_red` stops passing them.
  `UnionInjectivity.lean` is now 133 lines (net −110 on the follow-up).

### Irreducibility transfer to the conjugate-transposed family
- **Pattern:** the MPS transfer-map proofs repeated the invariant-projection
  argument already proved for finite Kraus maps.
- **Reuse:** both MPS directions now combine the Form II tensor/map conversion
  lemmas with `Kraus.isIrreducibleMap_mapLM_conjTranspose` and its `iff`
  companion through `Kraus.mapLM_eq_transferMap`.
- **Result:** the two public MPS declarations retain their statements while their
  duplicated conjugate-transpose projection arguments are removed.

---

## Candidates

Seeded from `scripts/tactic_pattern_scan.py` (2026-07-18 scan; re-run for
current counts and full location lists).

### powers on an eigenspace — candidate
- **Pattern:** prove `(f ^ n) x = μ ^ n • x` from `x ∈ f.eigenspace μ`, either by induction
  using `Module.End.mem_eigenspace_iff` or by splitting on `x = 0` before applying
  `HasEigenvector.pow_apply`.
- **Seen:** 2 occurrences across `TNLean/Channel/Peripheral/WeightedCesaro.lean` and
  `TNLean/Channel/Peripheral/CesaroRecurrence.lean` (review on 2026-08-17).
- **Abstraction (proposed):** if a third occurrence appears, promote the private
  `pow_apply_of_mem_eigenspace` next to the shared `Module.End.eigenspace` API and refactor
  the case-split variant to use it.
- **Notes:** This is below the rule-of-three threshold. The induction handles the zero vector
  without constructing a `HasEigenvector`; keep the helper private until another independent
  consumer fixes the useful public location.

### quasi-local translation laws in automorphism-group form — candidate
- **Pattern:** convert translation composition, symmetry, and identity laws from
  `StarAlgEquiv.trans`, `StarAlgEquiv.symm`, and `StarAlgEquiv.refl` into group
  multiplication, inverse, and one before applying `Commute` closure lemmas.
- **Seen:** six short `StarAlgEquiv.aut_mul` / `aut_inv` / `aut_one` conversions
  at five call sites, all in `TNLean/QCA/TranslationCovariance.lean`, before the
  call-site simplification (2026-08-16).
- **Abstraction:** the reusable public laws `SpinChain.quasiLocalTranslation_mul`,
  `SpinChain.quasiLocalTranslation_inv`, and `SpinChain.quasiLocalTranslation_one`
  are available in `TNLean/QCA/QuasiLocalTranslation.lean`.
- **Notes:** automorphism multiplication reverses `StarAlgEquiv.trans`, so
  `quasiLocalTranslation d a * quasiLocalTranslation d b` translates by `b + a`.
  The five motivating call sites now use the public laws, but the pattern remains
  below the cross-file promotion threshold. Reconsider its ledger status only if
  the conversion recurs independently in another file.

### flattened-pair reconstruction from quotient and remainder — candidate
- **Pattern:** rewrite `ij : Fin (d * d)` as
  `finProdFinEquiv (ij.divNat, ij.modNat)` using
  `(finProdFinEquiv.apply_symm_apply ij).symm` before simplifying a flattened
  pair operation.
- **Seen:** 3 occurrences across `TNLean/MPS/MPDO/PhysicalAdjoint.lean` and
  `TNLean/MPS/MPU/PhysicalAdjointCanonicalForm.lean` after the physical-pair
  equivalence deduplication (2026-08-13); the latter contributes one occurrence.
- **Abstraction (proposed):** add a low-level simp lemma such as
  `finProdFinEquiv_divNat_modNat` near the shared flattened-index definitions,
  then replace all occurrences together.
- **Notes:** Promotion would require editing established MPDO code outside the
  narrow CFII review-fix scope. Record the repeated goal now and refactor the
  complete set in one low-level follow-up rather than adding a leaf-local helper.

### diagonal normalized-ancilla sum collapse — candidate
- **Pattern:** collapse the doubled sum for `normalizedDiagonalLift` by using
  `Finset.sum_eq_single` to retain the diagonal ancilla letter `(a, a)`, then
  cancel the resulting normalization with
  `(x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1` for `0 < x`.
- **Seen:** 2 occurrences in `TNLean/MPS/MPU/PhysicalAncilla.lean`:
  `MPOTensor.transferMap_normalizedDiagonalLift` (lines 198--220), for
  `A ij * X * (A ij)ᴴ`, and
  `MPOTensor.leftCanonical_normalizedDiagonalLift` (lines 262--283), for
  `(A ij)ᴴ * A ij`.
- **Abstraction (proposed):** if a third occurrence appears, extract the
  lowest-sufficient helper lemma shared by both matrix-product orientations;
  do not introduce a tactic solely for this pattern.
- **Notes:** Use when a sum over the normalized diagonal ancilla alphabet has
  off-diagonal terms that simplify to zero, every surviving diagonal term has
  the same matrix factor, and `0 < x` permits cancellation of the two
  inverse-square-root scalars against the ancilla cardinality. This is below
  the rule-of-three promotion threshold.

### positive-part support-projection trace estimate — candidate
- **Pattern:** for a positive linear map `T` and Hermitian `H`, decompose
  `T H = T H⁺ - T H⁻`, obtain the support projection `P` of `(T H)⁺`, and
  chain the trace estimate:
  ```lean
  have hTp : (T H⁺).PosSemidef := ...
  have hTm : (T H⁻).PosSemidef := ...
  have hX : (T H).IsHermitian := isHermitian_map_of_positive hpos hH
  have hdecomp : T H = T H⁺ - T H⁻ := ...
  obtain ⟨P, hPpsd, hPle, hPmul⟩ : ... := ...
  calc (((T H)⁺).trace).re
      = ((P * T H).trace).re := by rw [hPmul]
    _ = ((P * T H⁺).trace).re - ((P * T H⁻).trace).re := ...
    _ ≤ ((P * T H⁺).trace).re := ...
    _ ≤ ((T H⁺).trace).re := ...
  ```
- **Seen:** 2 occurrences in `TNLean/Analysis/TraceNormContractivity.lean`:
  `re_trace_posPart_map_le` (trace-preserving case) and
  `re_trace_posPart_map_le_of_scaledTrace` (scaled-trace case) before
  factoring (review on 2026-08-09).
- **Abstraction:** `Matrix.re_trace_posPart_map_le_aux` in
  `TNLean/Analysis/TraceNormContractivity.lean` isolates the shared
  projection-chaining estimate; both source-facing lemmas are now
  one-`calc`-block corollaries.
- **Notes:** the abstraction removes ~15 duplicated proof lines from each
  caller.  The two callers differ only in the final trace-identity step
  (trace preservation vs. scaled trace), which remains in the thin
  wrappers.  Mark as promoted if a third call site appears.

### shifted trace moments under matrix powers — candidate
- **Pattern:** turn a trace-moment hypothesis for exponents greater than one
  into an all-positive trace-moment hypothesis for a matrix power:
  ```lean
  intro k hk
  rw [← pow_mul]
  exact h (m * k) (hm.trans_le (Nat.le_mul_of_pos_right m hk))
  ```
- **Seen:** two occurrences: the target-one theorem
  `Matrix.forall_trace_pow_pow_eq_one_of_forall_trace_pow_eq_one_of_one_lt` in
  `TNLean/Algebra/ShiftedTracePowerSpectrum.lean` and the target-zero theorem
  `Matrix.forall_trace_pow_pow_eq_zero_of_forall_trace_pow_eq_zero_of_one_lt` in
  `TNLean/Algebra/ShiftedZeroTraceNilpotent.lean` (review on 2026-08-09).
- **Abstraction:** if a third occurrence appears, promote a lemma generalized
  over the common target value `c : ℂ`, then rewrite both current call sites.
- **Notes:** This is the second occurrence, below the rule-of-three promotion
  threshold; retain the explicit source-facing target-one and target-zero
  theorems until another consumer fixes the useful general statement.

### rectangular complement expansion — candidate
- **Pattern:** expand a rectangular remainder by associativity:
  `Q * (1 - L * Q) * L = Q * L - (Q * L) * (Q * L)`.
- **Seen:** two occurrences: `rectangular_remainder_eq_mul_sub_sq` in
  `TNLean/MPS/MPDO/ActiveSectorSpanningCounterexample.lean` and
  `caseI_rectangular_remainder_eq_zero_of_literal_ZCL` in
  `TNLean/MPS/MPDO/LemmaC5CaseI.lean` (review on 2026-08-08).
- **Abstraction:** if a third occurrence appears, promote the expansion to a
  general rectangular-matrix lemma over a nonunital nonassociative ring with
  the finite-index assumptions needed for matrix multiplication.
- **Notes:** Below the rule-of-three promotion threshold; keep the explicit
  calculation so each application exposes the relevant opposite product.

### stationary-sector rank-one physical probes — candidate
- **Pattern:** choose the trace-one stationary state of an irreducible
  left-canonical sector, realize rank-one inserted maps by physical
  observables, identify them by linear-map extensionality, and remove a
  complementary transfer gap by the stationary-state fixed-point equation.
- **Seen:** two occurrences in `TNLean/MPS/RFP/ZCLReverse.lean`, in
  `not_isPositiveGapPhysicalCID_basisDirectSum_of_basis_spectral_pair` and
  `exists_basis_physicalObservables_expectation_eq_trace_mul_transferMap_pow`
  (pattern scan and review on 2026-07-30).
- **Abstraction:** proposed helper lemma returning the two physical
  observables together with the composed direct-sum rank-one-map identity.
- **Notes:** this remains below the rule-of-three promotion threshold. The
  two callers use different terminal data: a spectral eigenmatrix in the
  contradiction argument and arbitrary trace-pairing probes in the
  zero-Jordan repair.

### positive-map resolvent distribution — candidate
- **Pattern:** distribute a positive linear map and a nonnegative real scalar
  through the shifted-resolvent difference, commute the scalar identity shift,
  and normalize the resulting module expression.
- **Seen:** 2 occurrences in
  `TNLean/Channel/Schwarz/OperatorJensenAux.lean`:
  `positiveMap_rpowIntegrand₀₁_jensen` and
  `positiveMap_rpowIntegrand₁₂_jensen`.
- **Abstraction:** a shared algebraic lemma parameterized by the exponent
  identities for the concave and convex integrands, if a third occurrence
  appears.
- **Notes:** Below the rule-of-three promotion threshold; keep the explicit
  rewrites until another consumer fixes the common statement's useful shape.

### active canonical-form block restriction — candidate
- **Pattern:** restrict a finite canonical-form block family to indices with
  nonzero weight, choose `Fintype.equivFin` coordinates for that subtype, and
  pull back the dependent bond dimensions and blocks along the equivalence.
- **Seen:** 2 occurrences, in
  `isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal`
  (`BNTCharacterization.lean`) and
  `CPSVCanonicalFormData.exists_isCPSVBasisOfNormalTensors`
  (`BNTExistence.lean`). This remains below the rule-of-three threshold.
- **Abstraction (proposed):** if a third occurrence appears, package the active
  subtype, finite equivalence, dimensions, and dependent block family in a
  reusable low-level construction.
- **Notes:** Any promotion must preserve the restriction to nonzero-weight
  blocks; it must not assert coverage of zero-weight listed blocks.

### invariant-subspace two-block fork — candidate
- **Pattern:** the general and strict invariant-subspace decompositions repeated the
  spectral split, block construction, and MPV calculation.
```
spectral split → block extraction → MPV calculation
spectral split → block extraction → MPV calculation → strict bounds
```
- **Seen:** 2 full proof paths in
  `TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`; no further occurrence is
  currently identified, so this remains below the promotion threshold.
- **Abstraction:** the implemented private semantic construction
  `exists_twoBlock_decomp_of_lowerZero_aux`; the strict public theorem adds only
  positivity and arithmetic for the strict dimension bounds.
- **Notes:** The local helper is retained because it removes two long proof paths without
  adding a public interface. Counting proof lines inclusively from `:= by` through the
  final proof line, the two public implementations had 307 + 243 = 550 lines. The shared
  construction and two projections have 342 + 4 + 8 = 354 lines, a net reduction of 196
  lines (35.6%). Both public theorem statements are unchanged.

### product_span_transport — candidate
- **Pattern:** transport membership in the span of fixed-length products through
  a linear map that preserves the identity and the relevant products, using
  `Submodule.span_induction` with separate generator, zero, addition, and scalar
  cases.
- **Seen:** 2 occurrences: the reindexing step in
  `IsPositiveMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`
  and the block-diagonal step in
  `IsPositiveDirectSumMap.tracePreserving_of_traceNonincreasing_of_fixed_product_span`
  (2026-07-19). This is below the rule-of-three promotion threshold.
- **Abstraction (proposed):** a lemma transporting a product-span membership
  statement through a linear map, parameterized by the product-compatibility
  equation. Scout Mathlib's `Submodule.map_span` and `Submodule.map_mono` API
  before introducing a project lemma.
- **Notes:** The two current instances use matrix reindexing and block-diagonal
  embedding. Record before a third coordinate-transport proof appears; confirm
  that their product-family goal shapes agree before promotion.

### clm_norm_instances — candidate
- **Pattern:**
  ```
  letI : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : SeminormedRing (V →L[ℂ] V) := ContinuousLinearMap.toSeminormedRing
  letI : NormedRing (V →L[ℂ] V) := ContinuousLinearMap.toNormedRing
  letI : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  letI : NormedAlgebra ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedAlgebra
  ```
- **Seen:** 5 occurrences (`TNLean/MPS/RFP/BNTOrthogonality.lean:423`,
  `TNLean/Spectral/MPVOverlapDecay.lean:174`,
  `TNLean/Spectral/PrimitiveOverlap.lean:101`,
  `TNLean/Spectral/TransferOperatorGap.lean:459`, +1).
- **Abstraction (proposed):** not a tactic — investigate why these instances
  need `letI` at all (likely an instance-resolution gap); either fix the
  underlying instance visibility once in a shared file, or provide a
  `clm_norm_instances` macro expanding to the block.

### filter_sum_split — candidate
- **Pattern:**
  ```
  · refine Finset.sum_congr rfl (fun η hη => ?_)
    rw [Finset.mem_filter] at hη
    rw [if_pos hη.2]
  · refine Finset.sum_eq_zero (fun η hη => ?_)
    rw [Finset.mem_filter] at hη
    rw [if_neg hη.2, smul_zero]
  ```
- **Seen:** 5 occurrences in `TNLean/PEPS/RegionBlock/`
  (`ThreeBlockResonate.lean:682`, `ThreeBlockResonate2.lean:452`,
  `UnionInjectivityGeneral.lean:505`, +2).
- **Abstraction (proposed):** a lemma of the shape
  `∑ η in s.filter p, (if p η then f η else 0) • g η = ...` — scout
  Mathlib's `Finset.sum_filter` / `Finset.sum_ite_of_true` family first.

### two_positive_bilinear_checks — candidate
- **Pattern:** alternating `· intro i / simp` and
  `· intro i u v / simp [mul_assoc, mul_add]` blocks discharging
  bilinearity side goals.
- **Seen:** 9 occurrences, all in `TNLean/Channel/Schwarz/TwoPositive.lean`
  (lines 359-396).
- **Abstraction (proposed):** single-file duplication — restructure the
  underlying definition to take a bundled bilinear map, or a local
  `macro`/`have` inside the file. Below cross-file threshold; promote only
  if the pattern escapes `TwoPositive.lean`. Note: `grind` is unlikely to
  close these directly (matrix multiplication is noncommutative and its
  ring solver is commutative); the bundled-bilinear-map restructuring is
  the better bet.

### region_cover_union_cases — candidate
- **Pattern:**
  ```
  rcases Finset.mem_union.mp hcover with hrb | hc
  · rcases Finset.mem_union.mp hrb with hr | hbl
  · exact absurd hr hwnotred
  ```
- **Seen:** 9 occurrences in `TNLean/PEPS/RegionBlock/`
  (`CoarseThreeSite3.lean:89`, `ThreeBlockReconcile.lean:244`,
  `ThreeBlockResonate.lean:96`, +6).
- **Abstraction (proposed):** a case-elimination lemma on the three-region
  cover (membership in red/blue/crossing regions) stated once in the
  RegionBlock development.

### spectral_double_sum_continuity — candidate
- **Pattern:**
  ```
  apply continuousOn_finsetSum Finset.univ
  intro i _
  apply continuousOn_finsetSum Finset.univ
  intro j _ t ht
  have ht0 : 0 < t := ht
  have hα : 0 < α i := hA.eigenvalues_pos i
  have hβ : 0 < β j := hB.eigenvalues_pos j
  have hden : α i + t * β j ≠ 0 := by positivity
  ```
- **Seen:** 3 occurrences in
  `TNLean/Analysis/RelativeEntropyResolventIntegral.lean` (lines 608, 637,
  and 846 in the initial scan).
- **Abstraction (proposed):** a local lemma reducing continuity of a finite
  spectral double sum on `(0, ∞)` to continuity of one summand, while supplying
  positivity of the two eigenvalues and nonvanishing of
  `α i + t * β j`.  The repetition is presently confined to one file, so
  retain it as a candidate rather than adding a general tactic.

### blocked_vertical_triple_sum_reassociation — candidate
- **Pattern:** reassociate the three finite sector sums in a blocked vertical expansion,
  then use `map_sum` for scalar multiplication to factor the inner coefficient sums:
  ```
  ∑ α, ∑ β, ∑ γ, c α β γ • O γ
    = ∑ γ, (∑ α, ∑ β, c α β γ) • O γ
  ```
- **Seen:** 2 occurrences in
  `TNLean/MPS/MPDO/BNTFusionTensorClauseFromRFP.lean` and
  `TNLean/MPS/MPDO/BNTAlgebraTensorClauseSpectrum.lean` (2026-07-22).
- **Abstraction (proposed):** first scout the finite-sum linear-map API for a general lemma
  factoring a doubly indexed scalar sum out of a fixed vector. This remains below the ordinary
  rule-of-three threshold, and no further occurrence is currently identified.
- **Notes:** Both uses combine `Finset.sum_comm` with two `map_sum` calls for
  `(smulAddHom ℂ _).flip`. Keep the explicit calculations until a third call site confirms that
  their coefficient and codomain shapes support a materially smaller shared statement.

### cpsv_matched_phase_coefficient_identity — candidate
- **Pattern:** rewrite two sector-decomposition state expansions through a matched phase
  bijection, then use eventual linear independence to identify their coefficients.
- **Seen:** 2 occurrences in
  `TNLean/MPS/FundamentalTheorem/SectorBNT/CoeffIdentity.lean` and
  `TNLean/MPS/MPDO/BNTAlgebraTensorClauseSpectrum.lean` (2026-07-22).
- **Abstraction (proposed):** generalize `coeff_identity_via_matched_mpv_phase` to accept
  eventual linear independence of the chosen basis directly, while retaining its current
  `IsBNTCanonicalForm` wrapper for existing consumers.
- **Notes:** The existing theorem cannot be reused by the MPDO spectrum proof: it requires
  `IsBNTCanonicalForm`, whose left-canonical and weight-normalization fields are absent from
  the source-faithful `IsCPSVBasisOfNormalTensors` contract. The MPDO proof already reuses the
  lower-level `coefficient_eventually_eq_of_eventually_linearIndependent` lemma. Keep this as
  a candidate until another consumer justifies widening the public coefficient-identity API;
  do not add stronger hypotheses merely to reuse the existing wrapper.

### square_interior_edge_translate — candidate
- **Pattern:** given `NormalSquareInteriorEdgeDatum e`, case-split horizontal/vertical,
  extract interior-margin hypotheses (`IsNormalSquareHorizontalEdgeInteriorMargins` /
  `IsNormalSquareVerticalEdgeInteriorMargins`), rewrite `e` to the translated-edge form
  (`normalSquareHorizontalTranslatedEdge` / `normalSquareVerticalTranslatedEdge`) via
  `normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge` /
  `normalSquareVerticalTranslatedEdge_sub_eq_upEdge`, and dispatch to the
  translated-edge version of the target statement.
- **Seen:** 2 occurrences (2026-07-24):
  `TNLean/PEPS/NormalSquareInteriorAbsorbedFamily.lean:84-104` (absorbing gauge),
  `TNLean/PEPS/NormalSquareFundamentalTheorem2.lean:118-190` (per-edge bond-dimension equality).
- **Abstraction (proposed):** a lemma of shape
  `NormalSquareInteriorEdgeDatum.translatedDispatch` taking the horizontal and vertical
  continuations, or a helper that rewrites the edge and exposes the translated-coordinate
  hypotheses.  Below the rule-of-three promotion bar.
- **Notes:** the two occurrences differ in the continuation: one calls the absorbing-gauge
  functions, the other constructs blocking data and applies `bondDim_apply_eq_of_blockingData`.
  Before promotion, verify that the resulting type families (gauge existence vs. bond-dimension
  equality) can be unified under a single dispatch lemma without bloating the argument list.

### disjoint-region crossing geometry case-split — candidate
- **Pattern:** for a crossing edge between two disjoint regions of a three-block
  partition, four-way `rcases` on the two boundary-edge disjunctions, dispatching the
  two same-endpoint impossible branches by `absurd` via partition disjointness and the
  two live branches by pinning each endpoint into the two crossing regions to exclude
  incidence to the third.
- **Seen:** ≥4 occurrences across ≥2 files (2026-07-25):
  `RegionBlock/CoarseThreeSite5.lean` (`isCrossing_rb_of_incident`,
  `isCrossing_rc_of_incident`, `isCrossing_bc_of_incident`,
  `not_isRegionIncidentEdge_blue_of_crossing_rc`),
  `RegionBlock/CoarseThreeSite9.lean:77` (`not_isRegionIncidentEdge_complement_of_crossing_rb`),
  plus the `UnionInjectivity.lean:337` / `UnionInjectivityGeneral2.lean:311` mirror pair
  (`not_isRegionIncidentEdge_complement_of_blueRedCrossing`).
- **Abstraction (proposed):** one lemma per shape over an abstract three-piece
  partition — `isCrossingEdge_of_incident` (incident to both of two disjoint regions ⇒
  crossing) and `not_isRegionIncidentEdge_of_isCrossingEdge` (crossing between two
  regions disjoint from a third ⇒ not incident to the third) — with the region-frame
  API (`IsRegionIncidentEdge`, `IsCrossingEdge`) already shared. Recorded rather than
  promoted in the triMerge migration PR: the `IsCrossingEdge`-hypothesis restate
  (sharing the `CoarseThreeSite9` derivation shape) was applied there, but unifying the
  six sites needs a partition-with-regions hypothesis bundle common to
  `CoarseThreeSite5/9` and the `UnionInjectivity*` geometry, which is a design
  decision for the #4522 interface arc.
- **Notes:** the incident⇒crossing and crossing⇒non-incident directions are mutually
  inverse facts about the same four-way case split; promote both directions together
  or not at all. The `UnionInjectivity*` sites may be subsumed by the planned
  `NormalEdgeBlockingData.toThreeBlockGeometry` mirror-kill (see #4522), which would
  change the occurrence count before any promotion.

### continuous nonnegative function with zero integral — candidate
- **Pattern:** on the open positive half-line, turn pointwise nonnegativity into an
  almost-everywhere inequality, use integrability and a zero integral to obtain
  almost-everywhere vanishing, then use continuity and
  `Measure.eqOn_open_of_ae_eq` to obtain pointwise vanishing.
- **Seen:** 2 occurrences across 2 files:
  `TNLean/Channel/Schwarz/WeylRelativeEntropyIntegral.lean` in
  `weyl_sourceB_defect_eq_zero_of_gap_eq_zero`, and
  `TNLean/Channel/Schwarz/SupportRelativeEntropyGap.lean` in
  `supportSourceBDefect_eq_zero_of_relativeEntropy_sum_eq` (2026-07-27).
- **Abstraction (proposed):** a measure-theoretic lemma taking `IntegrableOn f (Ioi 0)`,
  `ContinuousOn f (Ioi 0)`, nonnegativity on `Ioi 0`, and zero restricted integral,
  and returning `EqOn f 0 (Ioi 0)`.
- **Notes:** Below the rule-of-three threshold. Keep the application-specific integrand
  definitions and the subsequent arithmetic that isolates the source-\(B\) defect
  outside the eventual helper.

### right-support range witness for a left--right operator — candidate
- **Pattern:** factor the left--right operator through the right-support
  projection and the shifted relative-modular resolvent, construct
  `P R⁻¹ D y` for a `P`-fixed vector `y`, and use the witness to show that
  the support projection of the left--right operator fixes `y`.
- **Seen:** 2 occurrences in
  `TNLean/Channel/Schwarz/SupportLeftRightRelativeModular.lean`, in
  `supportRightProj_mul_supportLeftRightSupportProj_eq` and
  `supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular`
  (2026-07-27).
- **Abstraction (proposed):** a range-inclusion lemma stating that the range
  of `1 ⊗ P_Bᵀ` is contained in the range of
  `A ⊗ 1 + t(1 ⊗ Bᵀ)` for `t > 0`, with the projection-absorption identity
  and the one-pair source solution as consumers.
- **Notes:** Below the rule-of-three threshold. Keep the explicit witness in
  both proofs until another independent consumer establishes the promotion
  threshold; the surrounding conclusions and final generalized-inverse
  calculation differ.

### general cyclic-forward step offset — candidate
- **Pattern:** for `i : Fin N` and a step `r`, identify the offset of `i` from
  its `r`-step cyclic forward successor:
  ```lean
  (i.val + N - (MPSTensor.cyclicForwardSite i r).val) % N = (N - (r % N)) % N
  ```
- **Seen:** zero current call sites require `r > 1`; this candidate records a
  source- and blueprint-motivated generalization, not repeated unabstracted code.
- **Abstraction (proposed):** a `cyclicForwardSite_step_offset` lemma generalizing
  `MPSTensor.cyclicForwardSite_one_offset`, explicitly below the promotion threshold.
- **Notes:** the completed one-step lemma is the precedent already reused by
  `cyclicRestrictₗ_restrictFirst`, `replaceWindow_three_replaceWindow_two_right`,
  and `offset_from_finRotate`; these sites do not count toward this candidate's
  promotion. Under the offset convention in blueprint remark
  `rem:cyclic_window_operators`, the proposed identity is the offset of the old
  starting site from the new start of an `r`-step-shifted cyclic window:
  $\delta_{\mathrm{cyclicForwardSite}\,i\,r}(i)
  = (N - (r \bmod N)) \bmod N$.

### eventual near-spectral-radius geometric bound — candidate
- **Pattern:** from `spectralRadius ℂ a < r`, derive
  `∀ᶠ n in Filter.atTop, ‖a ^ n‖₊ < r ^ n` by combining Gelfand's formula
  `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius` with
  `filter_upwards` on `gelfand.eventually (eventually_lt_nhds hr)` and
  `Filter.eventually_gt_atTop 0`, then clearing the `n`-th root via
  `ENNReal.rpow_inv_lt_iff` and `ENNReal.rpow_natCast`.
- **Seen:** 2 occurrences: `have hev` in
  `geometric_bound_of_spectralRadius_lt_one` and `have hev` in
  `pow_tendsto_zero_of_spectralRadius_lt_one`, both in
  `TNLean/Analysis/SpectralRadiusPowerDecay.lean`, after their layer-0
  relocations (PR #6570 and issue #6585).
- **Abstraction (proposed):** an `eventually_nnnorm_pow_lt_pow_of_spectralRadius_lt`
  lemma in `TNLean/Analysis/SpectralRadiusPowerDecay.lean`, taking
  `{A : Type*} [NormedRing A] [CompleteSpace A] [NormedAlgebra ℂ A] (a : A) {r : ℝ≥0}
  (hr : spectralRadius ℂ a < r)` and returning the eventual bound; both current
  call sites would discharge their local `have` block with one application
  (the geometric-bound site at `A := V →L[ℂ] V`).
- **Notes:** below the rule-of-three threshold (two occurrences); promote on
  the next independent occurrence. Both current occurrences are already in
  `TNLean/Analysis/SpectralRadiusPowerDecay.lean`, so the deferral rests on the
  occurrence count alone, not on any import cost.
### star preserves the complex norm — candidate
- **Pattern:** `simpa only [RCLike.star_def, RCLike.norm_conj]` to close a goal of the
  form `‖star μ‖ = 1` or `‖star μ‖ ≤ 1` from `‖μ‖ = 1` or `‖μ‖ ≤ 1`.
- **Seen:** 5 occurrences in `TNLean/Channel/Peripheral/AdjointSpectrum.lean` before
  the 2026-08 adjoint-spectrum cleanup, 3 of them newly written in that PR.
- **Abstraction (proposed):** Mathlib's `norm_star : ‖star a‖ = ‖a‖` (a `simp` lemma on
  any `NormedStarGroup`, and `ℂ` is one) closes each of these directly; no new TNLean
  declaration is needed, only the call-site substitution.
- **Notes:** all five occurrences in `AdjointSpectrum.lean` were replaced by `norm_star`
  in the same cleanup. Two further call sites of the two-lemma idiom remain outside this
  file's scope, `TNLean/MPS/RFP/CPSVCanonicalForm.lean:124` and
  `TNLean/Channel/Determinant/HeisenbergDual.lean:103`; a follow-up sweep can retire this
  candidate once those are also converted to `norm_star`.

---

## Rejected

### matrix_entry_cases — rejected
- **Pattern:** matrix extensionality followed by a diagonal/off-diagonal split:
  `ext i j; by_cases hij : i = j; · subst hij`.
- **Seen:** 10 candidate occurrences across 8 files in the #4528 audit.
- **Reason:** The prototype macro hid only two idiomatic structural lines at each call site,
  required eight new imports and a new cross-cutting tactic module, and increased total
  source by nine lines (49 additions, 40 deletions). Its `try subst` implementation also
  violated the fail-fast rule for promoted tactics. The occurrences share no mathematical
  conclusion from which to extract a lemma, so keeping the explicit case split is clearer
  and more Mathlib-style.

### RFP structural semantic helper split — rejected
- **Pattern:** split `rfp_nt_structural_full_sqSum` into private matrix-unit
  realization and residual-tensor construction theorems, each with a large
  existential interface.
- **Seen:** one proof in `TNLean/MPS/RFP/StructuralFull.lean`; neither proposed
  helper has another caller.
- **Reason:** the split would move the existing linear proof into two one-use
  declarations without reducing its hypotheses or calculations. Instead,
  derive left canonicality directly from the already-proved pair-index
  orthogonality. This removes seven local constructions/proofs and reduces the
  theorem proof from 387 to 346 lines (41 lines net), with no new declaration.

### nonzero Kraus map via evaluation at the identity — resolved
- **Pattern:** show a finite Kraus map is nonzero by evaluating at `1`, reducing to
  `∑ᵢ Kᵢ Kᵢᴴ = 0`, and concluding each `Kᵢ = 0` from positive semidefiniteness of the
  summands via `Matrix.eq_zero_of_sum_mul_conjTranspose_eq_zero`.
- **Seen:** the generic proof in `Kraus.mapLM_ne_zero_of_exists_ne_zero`
  (`TNLean/Channel/KrausMap.lean`) and one former inline duplicate in
  `MPSTensor.exists_posDef_transferMap_eigenvector_of_irreducible`
  (`TNLean/MPS/CanonicalForm/ProjectorClosureSpectral.lean`).
- **Reuse:** the transfer-map theorem now applies
  `Kraus.mapLM_ne_zero_of_exists_ne_zero B hB` and rewrites the result with
  `Kraus.mapLM_eq_transferMap`.
- **Result:** the inline evaluation-at-identity proof is removed; no duplicate
  implementation remains.

## Retired

### block_words — retired
- **Pattern:** repeated `simp only [...]` lists normalizing direct/iterated
  blocking maps and `wordOfBlock` expressions.
- **Former abstraction:** `@[mps_block_words]` simp set + `block_words` macro
  (`TNLean/MPS/Tactic/Basic.lean`).
- **Audit:** #4535 found 18 annotations but zero tactic invocations. The natural
  consumers use individual blocking lemmas together with local definitions or
  unrelated algebraic rewrites, so replacing them by the macro would add proof
  steps rather than remove duplication.
- **Counts:** declarations 2 → 0; annotations 18 → 0; invocations 0 → 0;
  proof-body lines changed 0.
