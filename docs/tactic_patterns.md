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

### Single-qubit plus-state positivity — promoted (2026-10-08)

- **Pattern:** Identify the all-halves two-by-two density matrix with one half
  of the outer product of the vector `![1, 1]`, then apply
  `Matrix.posSemidef_vecMulVec_self_star` and nonnegative scalar multiplication.
- **Seen:** Three copies in `TNLeanTest/RegularizedPatchStationarity.lean`,
  `RegularizedPatchNoncommuting.lean`, and `RegularizedPatchZeroWeight.lean`.
- **Abstraction:** `TNLeanTest.SingleQubitConfig.plusDensity` and
  `plusDensity_posSemidef` in `TNLeanTest/Support/SingleQubitConfig.lean`.
  The three regressions use the shared density and positivity result directly.
- **Notes:** The former private `density`/`density_psd`,
  `secondDensity`/`secondDensity_psd`, and `plusDensity`/`plusDensity_posSemidef`
  pairs are removed. The singularity, noncommutation, first-variation, and
  zero-weight assertions are unchanged after unfolding the shared density.
  The four fixture files shrink by 14 lines. No new tactic or compatibility
  alias is introduced.

### Crossing edge on a walk that leaves a region — promoted (2026-10-09)

- **Pattern:** a walk in the induced domain starts in a region and ends outside it; take
  its boundary dart, cut the walk at the first endpoint of the dart, and show that the
  dart is an edge of the edge boundary no farther from the start than the walk is long.
- **Seen:** `subset_of_isSafe` in `TNLean/PEPS/AreaLaw/BufferedRectangles.lean`,
  `card_crossingTerms_le_edgeBoundary` in `TNLean/PEPS/AreaLaw/TailParameter.lean`, and
  `TNLean/PEPS/AreaLaw/Scan/SupportLocalization.lean`.
- **Abstraction:** the lemma `TNLean.PEPS.AreaLaw.exists_edgeBoundary_of_walk` in
  `TNLean/PEPS/AreaLaw/FiniteDomain.lean` returns the boundary edge, its endpoint in the
  region and the shortened walk; the three call sites use it.
- **Notes:** `exists_cut_edge_near` in `TNLean/PEPS/AreaLaw/CrossingBudget.lean` is the
  analogue for an arbitrary graph in the extended graph distance.

### Rectangular sandwich of a matrix product operator word — promoted (2026-10-08)

- **Pattern:** replace every letter `U i j` of a nonempty word by `A * U i j * B` with
  `B * A = 1` and telescope, so that the word evaluation is `A * evalWord U is js * B`.
- **Seen:** `evalWord_padBond` (an isometry and its adjoint) and `evalWord_virtualSandwich`
  (a bond similarity) in `TNLean/MPS/MPU/`, beside the Kraus form
  `Kraus.evalWord_compress_of_left_absorb`.
- **Abstraction:** `MPOTensor.evalWord_sandwich` in `TNLean/MPS/MPU/WordSandwich.lean`, for
  rectangular `A` and `B`.
- **Refactor:** `evalWord_padBond` and `evalWord_virtualSandwich` are one-line instances.

### Rank from a factorization and an identity minor — promoted (2026-10-08)

- **Pattern:** prove `rank M = k` from `M = P * Q` through `k` (upper bound) and a `k × k`
  submatrix equal to the identity (lower bound).
- **Seen:** four cut-rank proofs in `TNLean/MPS/MPU/Examples/ControlledZ.lean` and
  `leftRank_oddRingTensor` in `TNLean/MPS/MPU/Examples/OddRing.lean`.
- **Abstraction:** `Matrix.rank_eq_card_of_eq_mul_of_submatrix_eq_one` in
  `TNLean/Algebra/MatrixRankOfFactor.lean`.
- **Refactor:** all five call sites use the lemma; the private helpers are deleted.

### Functional calculus under a unitary conjugation — promoted (2026-10-08)

- **Pattern:** `f (x * A * xᴴ) = x * f A * xᴴ` for a unitary `x` and Hermitian `A`, and the same
  for `PosSemidef.supportInvSqrt`.
- **Seen:** general `Matrix` lemmas that had been placed in `TNLean/MPS/MPU/SourceFactorChoice.lean`.
- **Abstraction:** `Matrix.IsHermitian.cfc_eq_of_eq_unitary_conj`,
  `Matrix.PosSemidef.supportInvSqrt_eq_of_eq_unitary_conj` and
  `Matrix.conjTranspose_mul_unitary` in `TNLean/Algebra/MatrixUnitaryConjCFC.lean`.
- **Refactor:** the MPU module imports the algebra module.

### Connectivity from two run-support memberships — promoted (2026-10-08)

- **Pattern:** Convert membership of two fan slots in one run's support into
  equality of their connected-component identifiers before applying colour
  constancy.
- **Seen:** Three transfers in `BeltRunInterfaces.lean` and one in
  `DummyRunInterfaces.lean`.
- **Abstraction:** Mathlib already provides
  `SimpleGraph.ConnectedComponent.reachable_of_mem_supp` and
  `SimpleGraph.ConnectedComponent.eq`. Their composition replaces all four
  manual pairs of support-membership equalities. No additional theorem or
  tactic is needed.
- **Notes:** The two existing belt-interface statements are unchanged. Both
  receive fresh whole-file verification with the dummy-interface contribution.

### Boundary geometry of an elementary side — promoted (2026-10-07)

- **Pattern:** Derive nondegeneracy and the constant square-boundary coordinate
  of an elementary side, allowing arbitrary midpoint subdivisions.
- **Seen:** The two opposing-region existence cases in
  `ElementarySideOpponents.lean` and the opposing-region uniqueness proof in
  `ElementarySideOpponentUniqueness.lean`.
- **Abstraction:** `cellFan_elementary_geometry` promotes the existing private
  statement and proof unchanged in `ElementarySideOpponents.lean`. The two
  existing callers and the new uniqueness proof use this common theorem.
- **Notes:** No compatibility alias or additional hypothesis is introduced.
  The existing existence statement is unchanged; its complete source file
  receives fresh verification with the two new declarations.

### Four orientations of fine-cell endpoints — promoted (2026-10-07)

- **Pattern:** Identify the ordered whole-side endpoints from the cell center
  and side vectors, then recognize the two endpoints as binary cell corners.
- **Seen:** The coordinate calculation in `CellContacts`, the full-mesh
  witnesses in `DummyCorners`, and the corner witnesses in `ActualSideMatching`.
- **Abstraction:** `cellFan_unsplit_endpoints_coordinates` and
  `cellFan_unsplit_endpoints_are_corners` in `SideEndpoints.lean`. The existing
  coordinate statement and proof move unchanged to their shared owner; the
  corner witnesses follow from that formula.
- **Refactor:** All three callers use the shared lemmas. The promotion removes
  38 net lines from `CellContacts`, 30 from `DummyCorners`, and the 25-line
  private corner table from `ActualSideMatching`; the shared owner has 88
  lines. The five older public statements stay unchanged.
- **Notes:** A scoped pattern scan of the five completed proof modules finds
  the remaining whole-side and half-side rectangle conversions only within
  `CellContacts`, below the threshold across two files. No new tactic or
  compatibility alias is introduced.

### Actual fine-cell containment in a layer — promoted (2026-10-07)

- **Pattern:** Rewrite the exact union over actual fine-layer indices and insert
  the indexed cell as one summand.
- **Seen:** Three copies in `NonbeltPrimaries.lean`,
  `FineMarkSeparation.lean` and `SideSubdivision.lean`.
- **Abstraction:**
  `TNLean.PEPS.AreaLaw.Geometry.dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices`
  in `LayerPartition.lean`. It requires only the aligned exponents and actual
  index membership, including empty layers and arbitrary origins and radii.
- **Refactor:** All three callers use the lemma. The closure callers apply
  `closure_mono` to the same containment conclusion. No theorem statement changes.

### Quasi-local MPS expectation on an interval — promoted (2026-10-07)

- **Pattern:** Rewrite the quasi-local MPS expectation of an interval
  observable by unfolding the interval inclusion, applying the interval
  formula, and cancelling the coordinate equivalence.
- **Seen:** Six parent-Hamiltonian modules repeated the same three-step
  rewrite.
- **Abstraction:** `MPSTensor.quasiLocalExpectation_quasiLocalIntervalObservable`
  in `LocalObservableQuasiLocalState`, next to the interval formula it uses.
- **Refactor:** All known callers use the lemma.

### A positive binary measurement from an orthogonal projector — promoted (2026-10-03)

- **Pattern:** Derive Hermiticity, positivity, idempotence, orthogonality and
  completeness for a projector and its complement.
- **Occurrences:** The return measurement in `PEPS/RegularChargePair.lean`,
  the physical charge measurement in `PEPS/RegularTwoSitePhysicalChargeMeasurement.lean`,
  and the physical transport in `Algebra/ScaledProjectionTransport.lean`.
- **Abstraction:** `Matrix.binaryProjectionFamily_complete` in
  `Algebra/BinaryProjectionFamily.lean`; all three calculations use this lemma.
- **Related reuse:** `Matrix.scaledProjectionTransport_properties` replaces the
  private transported-projection calculation in the two-site charge measurements.
  It proves positivity and the coefficient-map intertwiner from the explicit
  scaled Gram identity, support identity and commuting virtual projector.

### Absorption of the regional regular projector — promoted (2026-10-03)

- **Pattern:** Expand the product physical map, apply local absorption of the
  regular averaging projector, and reassemble the product to obtain AP=A.
- **Abstraction:** `regionPhysicalProductMatrix_mul_regularLocalProjector` in
  `PEPS/RegularPhysicalUnitaryTransport.lean` states this regional identity once.
- **Reuse:** The physical charge-pair image proof and original-spin return
  measurement use it directly. The two-site local data calculation already uses
  `regularSiteMap_projector_coefficients`, the same underlying local identity.
  The return measurement also uses `Matrix.exists_binaryProjectionFamily_transport`
  for the complete positive measurement on the full physical space.

### Column selection identified with a fixed-input contraction — promoted (2026-10-07)

- **Pattern:** Select a nonzero column with
  `exists_column_ne_zero_of_traceNorm_sub_pure_le`, rewrite it as the
  contraction of the network with the input fixed, and repackage.
- **Seen:** Two sites in `TNLean/PEPS/Approximation/VectorColumn.lean` and two
  in `TNLean/PEPS/Approximation/SquareGridColumn.lean`.
- **Abstraction:** `exists_eq_column_ne_zero_of_traceNorm_sub_pure_le` in
  `ColumnSelection`, taking a family `ψ z` identified with the columns `σ|z⟩`.
- **Refactor:** Both square-grid sites use it. The two `VectorColumn` sites
  already state their conclusion for the column itself and take the base lemma
  directly, with no rewrite step.

### Periodic norm as transfer trace — promoted (2026-10-06)

- **Pattern:** Apply the physical expectation trace identity to the identity
  observable and simplify its action to obtain the periodic squared norm.
- **Seen:** The canonical norm limit and two finite full-ring proofs repeated
  the same calculation, in addition to the existing `WindowClustering` lemma.
- **Abstraction:** The existing public
  `MPSTensor.inner_mpvState_self_eq_trace` is moved unchanged to its lower owner
  `WindowCorrelator`; no alias or second declaration is added.
- **Refactor:** All three new callers use the existing identity. The clustering
  owner still imports it transitively through `WindowOperatorSupport`.


### Canonical purity consequences — promoted (2026-10-05)

- **Pattern:** From a faithful canonical stationary density and the simple
  peripheral eigenspace property, derive irreducibility and peripheral
  primitivity before applying a twisted-transfer theorem.
- **Seen:** The source spectral theorem and physical selection rule repeated
  this reduction; finite physical endpoints need the same consequences.
- **Abstraction:** `MPSTensor.pureCanonical_isIrreducibleMap_and_isPrimitive`
  in `PureTwistedSpectrum`; the existing two consumers and the new canonical
  endpoint theorem use it without altering their mathematical hypotheses.
- **Notes:** Actual-import validation of the combined analytic refactor is
  recorded separately in the String Order integration audit.


### Logarithmic normalization cutoff — promoted (2026-10-05)

- **Pattern:** Turn `(log K - log ε) / r ≤ x` into `K exp(-rx) ≤ ε`.
- **Seen:** The three eventual-nonvanishing proofs in
  `InhomogeneousMixingPreparation`, `VaryingReferencePreparation`, and
  `RectangularPreparation`.
- **Abstraction:** `mul_exp_neg_mul_le_of_div_log_le` in
  `InjectivityCutoff`, using the existing exponential threshold theorem.
- **Refactor:** Three copied arithmetic blocks become calls to the shared bound.


### Sites in a one-block partition — promoted (2026-10-05)

- **Pattern:** Proving that the site map of a singleton partition is the identity
  by finite-index extensionality and unfolding the block offset.
- **Seen:** Five uses in `RectangularPreparation`, `VaryingReferencePreparation`,
  `InhomogeneousMixingPreparation`, and `OrderedMixingPairRate`.
- **Abstraction:** `MPSPreparation.blockSite_singleton` in `BlockSites`.
- **Refactor:** All five consumers use the shared identity.


### Uniform Gram/transfer reshuffling — promoted (2026-10-05)

- **Pattern:** Reshuffle the transfer-matrix error into the physical Gram
  error, bound the reshuffling by its operator norm, and reverse the same
  involution when starting from a Gram estimate.
- **Seen:** `InhomogeneousOverlap`, `VaryingReferenceOverlap`, and
  `InhomogeneousChoiResidual` repeated this fixed-dimensional argument.
- **Abstraction:** `MPSTensor.exists_norm_gram_transferMatrix_sub_le` in
  `PositivePartRate` proves both directions with one constant chosen before
  the physical dimension, tensor, and positive semidefinite reference.
- **Notes:** Both polar estimates and the actual-site/window Choi consumers
  use the same comparison; the fixed-reference inverse wrapper is removed.
  No generic channel definition or new import is introduced.


### Transported-reference Choi residual estimate — promoted (2026-10-05)

- **Pattern:** Subtract trace-preparation terms from actual block channels,
  compose the completely positive residuals, and bound their normalized Choi
  traces before reshuffling to the physical Gram matrix.
- **Seen:** `InhomogeneousPositivePartRate` and `WindowMixing` previously needed
  the same residual/trace bookkeeping with different reference hypotheses.
- **Abstraction:**
  `MPSPreparation.norm_gram_blockTensor_sub_transport_le_of_choi_domination`
  in `InhomogeneousChoiResidual` handles varying strengths and minorizers.
- **Notes:** This is a substantive transported-reference estimate, not a new
  tactic. The common faithful theorem preserves its signature and exponent;
  the new fixed-window consumer supplies its own compatible references.

### Simultaneous permutation invariance of matrix entries — promoted (2026-10-03)

- **Pattern:** Convert simultaneous invariance of matrix entries into commutation
  with the associated permutation matrix.
- **Seen:** Regular cycle flux creation, two-site charge-projector commutation,
  and regional charge-reference preparation.
- **Abstraction:** `Matrix.commute_permMatrix_of_entry_invariant` in
  `TNLean/Algebra/PermutationMatrixCommutation.lean`, over an arbitrary semiring.
- **Refactor:** The old private theorem is removed, and all three consumers
  use the shared entry argument.

### Induced walks after extension by exterior operators (promoted, 2026-10-03)

`regularRegionInternalOperators_bondExtension` restricts an extended assignment
back to its original internal operators. `regularWalkHolonomy_induced_bondExtension`
then evaluates an induced-region walk directly with the original assignment.
They are defined in `TNLean/PEPS/RegularInsertedWalkHolonomy.lean` and replace
repeated restriction proofs in the two-plaquette joint measurement, the
three-plaquette output measurement, and the routed reunion measurement.

### Local projector commutation from independent vertex translations — promoted (2026-10-02)

- **Pattern:** Express the product of local regular averaging projectors as the
  scalar average of independent vertex translations, then move commutation
  through the finite sum and scalar action.
- **Seen:** `RegularCycleControlledSupport.lean`,
  `RegularTwoCyclePhysicalFluxMove.lean`, and
  `RegularCyclePhysicalFluxCreation.lean`.
- **Abstraction:** `commute_regionLocalProjector_of_vertexTranslation` in
  `TNLean/PEPS/RegularCycleControlledSupport.lean` gives the mathematical
  commutation criterion for the actual regional projector.
- **Notes:** All three consumers retain their derived translation commutation.
  The helper adds no state or Gram assumption, and all public signatures remain
  unchanged.

### Adjoint of dependent block diagonals (promoted, 2026-10-02)

- **Pattern:** Expand dependent block-diagonal entries to move conjugate
  transpose through the block construction.
- **Occurrences:** `Algebra/FiniteGroupCommutant.lean`,
  `QICLean/Algebra/ScalarCommutant.lean`, and
  `QICLean/Algebra/DependentBlockDiagonal.lean`.
- **Promotion:** Reuse Mathlib's `Matrix.blockDiagonal'_conjTranspose`.
  The finite-group commutant proof removes its private entrywise copy and
  rewrites directly with this theorem; the companion-library consumers
  already use it.
- **Notes:** No new helper or tactic is needed.

### Weighted isotypic scalar action (promoted, 2026-10-02)

- **Pattern:** Expand a weighted character-projector sum on an irreducible
  summand, replace each projector by its character-equality indicator,
  and retain the weight of that summand.
- **Occurrences:** `RepresentationDelta.deltaOperator_apply_of_mem`,
  `CharacterProjectorTwirl.averageMap_linHom_rep`, and the reciprocal
  coefficient in `RepresentationDeltaInverse.deltaOperatorInverse_apply_of_mem`.
- **Promotion:** `Representation.sum_smul_charProjector_apply_of_mem` in
  `TNLean/Algebra/CharacterProjectorWeighted.lean`. All three calculations
  use this mathematical helper. The same module proves that every such
  isotypic scalar operator commutes with the group action.
- **Notes:** The helper imports only the character-projector foundation,
  so the weighted trace operator and its inverse share it without an
  import cycle. The two earlier calculations lose their indicator-sum proofs.

### Positivity of weighted character projectors (promoted, 2026-10-02)

- **Pattern:** Express a weighted sum through occurring irreducible characters,
  obtain the corresponding subrepresentation, inherit unitarity there, and
  sum its positive character projectors with nonnegative coefficients.
- **Occurrences:** `RepresentationDeltaPositive.isPositive_deltaOperator_of_unitary`
  and `RepresentationThetaPositive.isPositive_thetaOperator_of_unitary`.
  Positive representation weights require the same argument in subsequent
  bond constructions.
- **Promotion:** `Representation.isPositive_sum_smul_charProjector_of_nonneg`
  in `TNLean/Algebra/RepresentationDeltaPositive.lean`. Both calculations use
  this lemma and retain only their scalar nonnegativity arguments.
- **Notes:** This is a mathematical positivity statement, not a tactic wrapping
  finite-sum induction; the orthogonal character-projector argument is proved once.

### Equality on irreducible summands (promoted, 2026-10-02)

- **Pattern:** Choose Maschke's internal direct sum, compare endomorphisms
  on each summand, and install its irreducibility instance from the atom witness.
- **Occurrences:** `CharacterProjector.sum_charProjector_irreducibleCharacters`,
  `CharacterProjectorWeighted.sum_smul_charProjector_commute` and
  `charProjector_mul_self`, `CharacterProjectorTwirl.averageMap_linHom_rep`,
  `RepresentationDeltaInverse.deltaOperatorInverse_mul`,
  `SemiRegularGroupAlgebra.isSemiRegular_of_linearIndependent`, and
  `RepresentationTheta.thetaOperator_pow_four`.
- **Promotion:** `Representation.linearMap_ext_on_irreducible` in
  `TNLean/Algebra/CharacterProjector.lean`; the listed calculations use this
  finite-dimensional mathematical extensionality lemma.
- **Notes:** The chosen-decomposition calculation in
  `exists_mem_character_eq_of_mem_irreducibleCharacters` remains on the existing
  `DirectSum.IsInternal.linearMap_ext`: its hypothesis concerns that specific
  family, not every irreducible subrepresentation. Replacing it by the stronger
  quantified criterion would require the character-occurrence theorem being proved.

### Product maps on coherent finite sums — promoted (2026-10-02)

- **Helper:** `TNLean.PEPS.physicalProductMap_sum_prod` in
  `TNLean/PEPS/TorusPhysicalCoherentMap.lean`.
- **Use:** apply one rectangular coefficient matrix independently to the
  factors of a finite coherent sum. Interchange the configuration sum and
  coherent-label sum, then use Mathlib `Fintype.prod_sum` once.
- **Consumers:** actual multiplicity restoration of the weighted torus state
  and transport of coherent bond coefficients between orthonormal coordinates.

### Transport of coherent bond products — promoted (2026-10-02)

- **Pattern:** Rewrite the coherent contraction, transform every one-bond
  vector, and reconstruct the finite sum of bond products.
- **Seen:** Six coefficient calculations across
  `PEPS/TorusMultiplicityBondState.lean`,
  `PEPS/GraphMultiplicityBondState.lean`,
  `PEPS/TorusBondCoordinateTransport.lean`, and
  `PEPS/GraphBondCoordinateTransport.lean`.
- **Abstraction:** `physicalProductMap_sum_prod_eq` in
  `PEPS/PhysicalCoherentTransport.lean` reduces each consumer directly to its
  mathematical single-bond vector identity. It reuses
  `physicalProductMap_sum_prod` and replaces the repeated product congruence.
- **Related helper:** `physicalProductMap_eq_on_inclusion_range` in the same
  module extends equality after one inclusion to the product inclusion range.
  The torus and general-graph full-domain isometry proofs use this shared lemma.
- **Notes:** No custom tactic is needed. The remaining coefficient-level
  congruences outside transport use Mathlib's `congr!` where appropriate.

### Weighted blocks and actual torus multiplicity restoration — promoted (2026-10-02)

- **Pattern:** rewrite the coherent dressed-state expansion, reconstruct weighted
  diagonal blocks with matching-sector inclusion, and apply the multiplicity map
  to each factor of every vertex-label summand.
- **Sites:** the orthonormal-sector and explicit fourth-root block constructions
  in `PEPS/TorusMultiplicityBondState.lean` and
  `PEPS/TorusBlockMultiplicityState.lean` contained four repeated congruence blocks.
- **Promotion:** `torusBondRegrouping_dressedAveragingSite_of_weightedBlocks`
  proves support and the actual state equality from the single-bond matrix identity.
  Both constructions derive that identity and commutation before using the helper;
  their duplicated coherent-state arguments have been removed.

### Common bond operators outside a region — promoted (2026-10-02)

- **Pattern:** show an incident edge at an exterior vertex is not internal,
  derive equality of exterior twisted site tensors, and apply the identity
  vertex gauge to obtain one common crossing-boundary transport.
- **Seen:** the global movement and coherent global creation arguments in
  `PEPS/RegularTwoCycleGlobalFluxMove.lean` and
  `PEPS/RegularCycleGlobalFluxCreation.lean`; four incident-edge exclusions
  and three twisted-site expansions in the 130-file PEPS scan.
- **Abstraction:**
  `regularTwistedSite_regularRegionBondExtension_eq_outside` and
  `openRegionWeight_regularTreeCycleBondExtension` in the global movement
  module. Both movement and creation consumers apply these shared identities;
  their public statements are unchanged.
- **Notes:** the boundary transport is independent of the internal cycle
  assignment. It is derived from the actual crossing operators, rather than
  supplied as a contraction hypothesis. No new tactic is needed.

### Uniform open-column action on an actual cut — promoted (2026-10-02)

- **Pattern:** obtain the same scalar action on every boundary column, assemble
  the open-region matrix identity, and multiply by the complementary matrix.
- **Seen:** the private plaquette measurement argument in
  `PEPS/TorusPlaquetteFluxMeasurement.lean` and the joint-flux measurement in
  `PEPS/TorusJointFluxMeasurement.lean`; the cycle-permutation global consumer
  requires the same actual cut implication.
- **Abstraction:**
  `mul_regularPhysicalCutMatrix_eq_smul_of_openRegion_eigen` in
  `PEPS/RegularPhysicalCutColumnAction.lean` proves the implication from the
  actual cut factorization. Both measurement consumers now use it.
- **Notes:** this is a mathematical statement about all actual boundary columns,
  not an assumed global eigenstate identity. No unitarity hypothesis is needed.

### Combining commuting representation weights — promoted (2026-10-02)

- **Pattern:** move a power of a commuting weight past a representation factor,
  then combine the two representation factors.
- **Seen:** `PEPS/TorusThetaBondState.lean`, `PEPS/GraphAveragingBondState.lean`,
  and `PEPS/GraphOpenAveragingBondState.lean`.
- **Abstraction:** `MonoidHom.mul_commuting_pow_mul` and its adjacent-weight
  specialization `MonoidHom.mul_weight_mul_weight_mul` in
  `Algebra/MonoidHomCommutingWeight.lean`; all three callers use these results.
- **Notes:** the proof uses the existing commutation and homomorphism laws.
  No additional representation or contraction hypothesis is introduced.

### Conjugation leaves the conjugacy-class quotient unchanged — promoted (2026-10-02)

- **Pattern:** exhibit the conjugating element, use symmetry of conjugacy,
  and conclude equality in the conjugacy-class quotient.
- **Seen:** the former private class calculation in
  `PEPS/RegularCycleFluxMeasurement.lean` and the two component class
  calculations in `PEPS/RegularThreePlaquetteDoubleExchange.lean`.
- **Abstraction:** `ConjClasses.mk_conjugate` in
  `Algebra/ConjClassesConjugation.lean` proves the group identity once.
  The measurement module uses it at both former call sites; the exchange
  module uses it on the two derived conjugate component formulas.
- **Notes:** the result requires only a group, with no finiteness or
  representation hypothesis. The former private helper is removed.

### Ordered non-tree bonds under graph isomorphisms — promoted (2026-10-02)

- **Pattern:** split the two possible sorted endpoint orders, cancel the
  graph isomorphism, and contradict adjacency in the original tree.
- **Seen:** the native chord constructions in
  `PEPS/TwoPlaquetteGeometry.lean`,
  `PEPS/TranslatedTwoPlaquetteGeometry.lean`, and
  `PEPS/ThreePlaquetteGeometry.lean`.
- **Abstraction:** `Edge.comap_adj_map_iff` in
  `PEPS/EdgeMapSubgraph.lean` proves the adjacency equivalence for any
  transported graph. All three certificate proofs now use its negation.
- **Notes:** the result requires only the ordered vertex sets and the graph
  isomorphism, with no finiteness or tree hypothesis. The endpoint sorting
  argument is removed from every known caller; no auxiliary tactic is needed.

### Conditional group-column action on the actual cut — promoted (2026-10-02)

- **Pattern:** encode group-valued boundary configurations, introduce the common
  indicator scalar, and transport a conditional column identity to the cut.
- **Seen:** `PEPS/TorusPlaquetteFluxMeasurement.lean`,
  `PEPS/TorusJointFluxMeasurement.lean`, and
  `PEPS/TorusThreePlaquetteOutputMeasurement.lean`.
- **Abstraction:** `mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen` in
  `PEPS/RegularPhysicalCutColumnAction.lean` derives the numbering and scalar
  internally from the existing uniform scalar action theorem. All three
  consumers now apply the conditional implication directly.
- **Notes:** the condition is uniform over actual group-valued boundary labels.
  Neither unitarity nor a nonzero global-state assumption is needed. Public
  measurement statements are unchanged; their repeated numbering and scalar
  calculations are removed.

### Coherent weighted-block multiplicity restoration (promoted, 2026-10-02)

- Pattern: derive matching-sector support and multiplicity restoration from a
  coherent product of square-root weighted diagonal matrix blocks.
- Promotion: `coherentWeightedBlocks_support_restore` and
  `exists_isometric_coherentWeightedBlocks` in
  `TNLean/PEPS/CoherentMultiplicityTransport.lean`.
- Consumers: the actual graph and torus weighted-state support theorems, and
  the actual group-inserted closed-graph isometry theorem. The ordinary matrix
  hypothesis remains distinct from an assumed contraction identity; every
  actual-state consumer derives its coherent expansion.

### Native plaquette transport — promoted (2026-10-02)

- **Pattern:** unfold the four actual plaquette steps, reverse the top and left
  transports, and evaluate the resulting ordered group product.
- **Seen:** `PEPS/TorusPlaquetteFluxMeasurement.lean`,
  `PEPS/TorusTwoPlaquetteFluxHolonomy.lean`,
  `PEPS/TorusJointFluxGeometry.lean`, and
  `PEPS/TorusThreePlaquetteFluxGeometry.lean`; both orientations are also
  required by the four-endpoint string calculation.
- **Abstraction:** `regularWalkHolonomy_torusPlaquetteWalk` and
  `regularWalkHolonomy_torusPlaquetteWalk_reverse` beside the defining walk
  in the measurement module. The native consumers use the common formulas.
- **Notes:** each directed edge is retained, including seam reversals. The
  formulas require a group, with no finite-group, physical-state, or supplied
  holonomy hypothesis. The outer six-step walks still have their own ordered
  products. No tactic or separate compatibility module is needed.

### Sorted-edge endpoint comparison — promoted (2026-10-02)

- **Pattern:** compare the two endpoint orders of native sorted edges, or
  distinguish them by a coordinate constant on one pair of endpoints.
- **Seen:** repeated plaquette and translated-movement edge inequalities in
  `PEPS/TorusPlaquetteFluxMeasurement.lean` and
  `PEPS/TorusTranslatedFluxMove.lean`; the vertical movement needs the same
  endpoint comparison.
- **Abstraction:** `Edge.ofAdj_eq_iff_endpoints` and
  `Edge.ofAdj_ne_of_endpoint_coordinates` in `PEPS/EdgeMapSubgraph.lean`.
  Both former private coordinate helpers are removed and their callers use
  the common result.
- **Notes:** the coordinate function is arbitrary. The argument does not
  impose a lattice orientation or a finite vertex set.

### Sparse cycle assignments — promoted (2026-10-02)

- **Pattern:** reconstruct an internal assignment from identity on a spanning
  tree and a small explicit list of non-tree bonds.
- **Seen:** the two private horizontal support proofs in
  `PEPS/TorusTranslatedFluxMove.lean` and
  `PEPS/TorusTwoPlaquetteFluxHolonomy.lean`, and the vertical movement proof.
- **Abstraction:** `regularTreeCycleAssignment_eq_of_support` and its
  two-bond specialization `regularTreeCycleAssignment_twoSupport`, beside
  the defining assignment in `PEPS/RegularTwoCycleFluxMove.lean`.
- **Notes:** the support conditions concern the actual bond assignment,
  rather than a supplied contraction identity. The single-flux consequence
  `regularTwoCycleMove_single` is also public in the defining module and is
  used by horizontal and common-gauge vertical movement. Its former private
  name is removed; no compatibility alias is retained.

### Native seven-edge transport reconstruction — promoted (2026-10-03)

- **Pattern:** compare the seven directed transports of a two-plaquette
  induced graph, then recover its ordered bond coefficients.
- **Seen:** the first rightward physical string step and the two upward
  physical crossing steps in `TorusInitialStringRightPhysicalStep.lean`,
  `TorusInitialStringPhysicalCrossing.lean`, and
  `TorusSecondStringPhysicalCrossing.lean`.
- **Abstraction:** `twoPlaquette_internal_eq_of_edgeTransports` compares
  the abstract seven-edge graph once. Its horizontal and vertical
  corollaries use the actual induced-graph isomorphisms. The helpers in
  `RegularInternalGaugeTransport.lean` recover coefficients from directed
  transports and extend equality across one actual regional cut.
- **Refactor:** all three consumers supply only their seven scalar
  transport equalities. The two upward reconstruction proofs lose 175
  and 185 lines; the rightward module loses 27 lines. The geometry and
  the actual group coefficients remain explicit.
- **Validation:** the shared table and all three consumers pass the
  package Lean options at the default heartbeat limit. Their theorem
  audits use only the ordinary logical axioms.

### Physical coordinate permutations from translation equivariance — promoted (2026-10-03)

- **Pattern:** Conjugate a coordinate permutation by the actual spanning-tree
  equivalence, transport its vertex-translation commutation, and apply the
  permutation-matrix homomorphism. Average the translations to obtain
  commutation with the product local invariant projector.
- **Seen:** The controlled-boundary argument in
  `PEPS/RegularCycleControlledSupport.lean`, the cycle argument in
  `PEPS/RegularCyclePermutation.lean`, and the charge-reference operation in
  `PEPS/RegularChargeFluxCoordinateTransport.lean`.
- **Abstraction:** `regularRegionCoordinatePhysicalPermutation` and its
  `_commute_vertexTranslation` and `_commute_localProjector` theorems in
  `PEPS/RegularCycleControlledSupport.lean`. All three consumers supply only
  their derived coordinate equivariance.
- **Notes:** This is the rule-of-three promotion. The two existing proof bodies
  decrease from 33 to 7 nonblank lines, excluding the shared theorem and the
  newly added charge consumer. Their public signatures remain unchanged.
  The criterion supplies no Gram or contraction assumption and introduces no
  import cycle.
### Averaged left inverse of a G-injective MPS tensor (promoted, 2026-10-02)

- **Pattern:** Extract the invariant tensor and its averaged left inverse from
  general G-injectivity, then rewrite map invariance as conjugation invariance
  of every physical tensor coefficient.
- **Seen:** The concatenation proof in `PEPS/GInjectiveMPS.lean`, both original
  intersection and closure proofs in `PEPS/GInjectiveMPSIntersection.lean`,
  and the inhomogeneous intersection proof in
  `PEPS/GInjectiveStripIntersection.lean`.
- **Abstraction:** `IsGInjective.exists_mpsLeftInverse` in
  `TNLean/PEPS/GInjectiveMPS.lean` combines the existing general left-inverse
  theorem with the conjugation-invariance characterization.
- **Notes:** All four consumers use this mathematical helper. The repeated
  conjugation rewrite is removed; the helper adds no mathematical hypothesis
  and does not require a finite physical alphabet.

### Regional PEPS subspace inclusion by open contraction columns — promoted (2026-10-02)

- **Pattern:** Rewrite the regional ground space as the span of its actual
  open contraction columns, apply `Submodule.span_le`, and extract each
  crossing configuration from the generator range.
- **Seen:** Twice in `PEPS/ParentHamiltonian/RegularRegionFlatness.lean`
  (exposure into canonical coordinates and recovery through the inverse),
  and once in `RegularRegionBondRightInvariance.lean`
  (exposed shared-bond right invariance).
- **Abstraction:** `TNLean.PEPS.regionGroundSpace_le_iff` in
  `TNLean/PEPS/ParentHamiltonian/RegionGroundSpace.lean` gives the universal
  subspace property of the actual regional contraction.
- **Notes:** All three consumers use this mathematical equivalence. It
  composes Mathlib's `Submodule.span_le` and `Set.range_subset_iff`, adds no
  hypotheses, and leaves the consumer theorem signatures unchanged.

### Finite linear combinations in a supported subspace — promoted (2026-10-02)

- **Pattern:** prove membership of a sum by `Submodule.sum_mem`, then prove
  each scalar multiple belongs by `Submodule.smul_mem`.
- **Seen:** regional support transport in
  `PEPS/ParentHamiltonian/RegionPhysicalGroundSpaceTransport.lean`,
  `VertexInverseRegionSlice.lean`, and `VertexVirtualParentTransport.lean`.
- **Abstraction:** existing Mathlib `Submodule.sum_smul_mem`; all three
  consumers now apply it directly. No new lemma or tactic is needed.
- **Notes:** the summands are actual regional slices, transformed by regional
  site maps or site inverses. The scalar coefficients come from the
  complementary region; no positivity assumption is involved.

### injectivity under translations of a torus region — promoted
- **Pattern:** transport blocked-region injectivity along a torus translation,
  then replace the transported tensor by the original translation-invariant tensor.
- **Seen:** four uses in `TorusWitnessTranslate.lean`,
  `TorusTranslatedScalarComparison.lean`, and `TorusWindowGaugeUniqueness.lean`.
- **Abstraction:** the existing `regionBlockedTensorInjective_translate` now lives in
  `TorusTranslationInvariant.lean`, so the witness, scalar and uniqueness arguments
  can use it without importing the later torus Fundamental Theorem.
- **Notes:** the statement and proof are unchanged. Four duplicated uses are replaced;
  the move has no line cost, consumer proofs lose five lines, and the necessary
  `RegionTransport` import adds one line (net Lean line delta: -4).


### propagation of two PEPS reference witnesses — promoted
- **Pattern:** translate horizontal and vertical coefficient witnesses to every edge,
  absorb their boundary gauges, and prove covariance by composition of translations.
- **Seen:** the rectangle construction in `PEPS/TorusCovariantAbsorbedFamily.lean`
  and the normal-window construction in `PEPS/TorusArcWindowGaugeExistence.lean`.
- **Abstraction:** `exists_torusCovariantAbsorbedGaugeFamily_of_edgeReferenceWitnesses`
  in `PEPS/TorusReferenceAbsorbedFamily.lean` accepts arbitrary witnessing regions.
- **Notes:** both constructions use the same proof; the rectangle module loses
  139 lines while retaining its theorem statement.

### Integer-cell collar offset decomposition (promoted, 2026-10-02)

- **Pattern:** Split the displacement from an occupied integer center into
  two equal offsets; use one in the closed unit cell and one in the
  radius-three-quarters enlargement.
- **Occurrences:** `PEPS/IntegerCellExteriorCollar.lean` and
  `PEPS/TorusRegionBoundaryLift.lean`, formerly the private
  `unitStep_mem_collar` placement proof. Actual edge and boundary-endpoint
  geometry both need the same numerical placement.
- **Promotion:** `mem_integerClosedCell_add_of_abs_le_one` in
  `TNLean/PEPS/IntegerCellExteriorCollar.lean`. The generic theorem already
  serves edge-segment containment and the integer-center collar
  characterization; the torus boundary-lift consumer uses it after reducing
  its unit-step hypothesis to coordinate distance at most one.
- **Notes:** The scanner does not identify this mathematical repetition:
  one proof begins with absolute coordinate bounds and the other with
  unit-step cases. The shared theorem avoids repeating the offset split.

### continuous argument along slit-plane paths — promoted (2026-10-02)

- **Pattern:** Reduce continuity of a principal-argument path to continuity at
  each point, use `Complex.continuousAt_arg`, and compose with the path.
- **Seen:** three angular-branch constructions in `PEPS/IntegerCellNoHoles.lean`.
- **Abstraction:** Mathlib's `Complex.continuousOn_arg.comp_continuous`.
- **Notes:** all three constructions now use the existing composition theorem
  directly. No new helper or tactic is introduced.

### Flat spectral entropy reduction (promoted, 2026-10-02)

- **Pattern:** Apply a quadratic matrix identity to a nonzero eigenvector,
  cancel the vector coefficient, and conclude that each eigenvalue is zero
  or the reciprocal flatness parameter.
- **Occurrences:** The von Neumann calculation in `Algebra/FlatDensityEntropy`
  and the spectral real-power trace calculation in
  `Algebra/FlatDensityRenyiEntropy`; the same spectral argument would otherwise
  precede each Rényi order and each boundary-density specialization.
- **Promotion:**
  `Matrix.IsHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul` in
  `TNLean/Algebra/FlatDensityEntropy.lean`. Both entropy calculations consume
  this lemma, with no repeated eigenvector cancellation proof.

### finite compact cell quotients — promoted (2026-10-02)

- **Pattern:** Map a finite disjoint union of compact locally path connected
  cells continuously onto its realized union, use compactness and the Hausdorff
  property to obtain a closed quotient map, and pass local path connectedness
  to the quotient.
- **Seen:** the original torus-cell proof in
  `PEPS/TorusRegionRealization.lean` and the planar integer-cell construction in
  `PEPS/IntegerCellNoHoles.lean`.
- **Abstraction:** `locallyPathConnectedSpace_iUnion_range` in
  `PEPS/FiniteCellTopology.lean`. Both geometric instances now use the shared
  theorem; the torus instance no longer repeats the quotient argument.
- **Notes:** the hypothesis is a genuine finite family of compact continuous
  cell images, not a collar connectivity or disk hypothesis. No tactic is added.

### Integer unit-step seam arithmetic (promoted, 2026-10-02)

- **Pattern:** Split an integer unit step into its four orientations; apply
  Euclidean division at a seam, and negate the crossing pair for reverse steps.
- **Occurrences:** Exterior walk approximation in
  `PEPS/TorusExteriorPathApproximation.lean` and boundary endpoint lifting in
  `PEPS/TorusRegionBoundaryLift.lean`; the four-case argument is shared by
  exterior walks and native boundary crossings.
- **Promotion:** `torusIntegerDeckCoordinate` and
  `torusDirectedWinding_eq_of_integerUnitStep` in
  `PEPS/TorusIntegerStepWinding.lean`. The exterior approximation now uses
  this lemma, and the boundary endpoint theorem uses the same arithmetic.
  No region or path assumption enters the shared step identity.

### Fixed complementary walk control (promoted, 2026-10-02)

- **Pattern:** Reread each crossing edge from the complementary side, evaluate
  the cycle word of its fixed native walk, and conjugate the resulting boundary
  permutation into the original physical half-edge basis.
- **Occurrences:** `RegularCycleControlledBoundary`,
  `RegularControlledBoundaryFactor`, `TorusComplementDisentangling`, and
  `TorusControlledBoundaryFactor`; the same construction appeared in matrix
  definitions, native contraction identities, and sector-independent unitary
  witnesses.
- **Promotion:** `regularComplementWalkControlMatrix` and
  `regularComplementWalkControlMatrix_mem_unitaryGroup` in
  `TNLean/PEPS/RegularCycleControlledBoundary.lean`. The matrix depends only on
  the fixed trees and actual walks, before any bond assignment or closure label.
  Known consumers use this definition directly; there is no compatibility alias.

### integer fibers and affine lifts of additive circles — promoted
- **Pattern:** extract an integer fiber from `AddCircle.coe_eq_zero_iff`,
  or compare a continuous lift of a projected affine interval path with
  the affine lift by `IsCoveringMap.eq_of_comp_eq`.
- **Seen:** the two coordinate constructions in
  `PEPS/TorusRegionRealization.lean` and
  `PEPS/TorusRegionLiftRealization.lean` (2026-10-02); the integer-fiber
  proofs were identical, and the affine-lift proofs differed only in
  their final use of function extensionality.
- **Abstraction:** `exists_intCast_eq_of_addCircle_eq_zmod_val` and
  `eq_affine_of_addCircle_eq` in `PEPS/TorusRegionRealization.lean`.
- **Notes:** both modules now use the shared mathematical lemmas. The
  integer statement uses the explicit standard residue representative;
  the affine statement allows any real period and is available to
  subsequent plane-path lifting arguments. No tactic is introduced.

### products of finite indicator sums — promoted
- **Pattern:** after separating scalar factors, expand a product of sums by
  `Fintype.prod_sum` and collapse each product of zero-one indicators by
  `Fintype.prod_boole`.
- **Seen:** `regularProjectorOpenRegionMatrix_apply`,
  `regularProjectorTwistedRegionMatrix_apply`, and
  `prod_torusSiteGram_eq_sum_translation` in the corresponding three PEPS
  modules (2026-10-02).
- **Abstraction:** `Fintype.prod_sum_boole` in
  `TNLean/Algebra/FiniteIndicatorSum.lean`, for dependent finite choice types
  over an arbitrary commutative semiring.
- **Notes:** all three proofs now use the combined counting identity. The
  abstraction is a lemma rather than a tactic or a new simplification rule.

### equality of labels under a boundary numbering — promoted
- **Pattern:** prove equality of two functions on a numbered boundary by
  evaluating an equality of their pullbacks at the inverse numbering, and
  prove the converse by function extensionality.
- **Seen:** three occurrences in
  `PEPS/RegularRegionGram.lean`, `PEPS/RegularTwistedRegionGram.lean`, and
  the private projector-numbering lemma in
  `PEPS/RegularRegionInjectivity.lean` (2026-10-02).
- **Abstraction:** Mathlib's `Function.Surjective.right_cancellable`,
  applied to the surjective boundary equivalence.
- **Notes:** all three proofs now use this equivalence directly, with
  `Function.comp_def`, `Pi.smul_apply`, and `smul_eq_mul` identifying
  precomposition and simultaneous regular translation. No additional
  theorem or tactic is required.

### recovering site coefficients from a composed site map — promoted
- **Pattern:** apply `LinearMap.toMatrix'` to a composition identity, expand
  the matrix of the four-leg site map, and read one physical and virtual entry.
- **Seen:** the former forward local inverse and reverse projector action in
  `PEPS/RegularGInjectiveTorus.lean`, and their generalization to arbitrary
  virtual representations in `PEPS/GInjectiveTorusProjector.lean`
  (2026-10-02).
- **Abstraction:** `siteMap_injective` and
  `physicalMapSite_eq_iff_siteMap_comp` in
  `PEPS/GInjectiveTorusProjector.lean` recover coefficient equality from
  equality or physical composition of site maps.
- **Notes:** both general physical-map identities now use the composition
  equivalence and the existing `siteMap_physicalMapSite`; the repeated
  coefficient-extraction proofs in the regular module were removed.

### equality of boundary functions under incident-edge indexing — promoted
- **Pattern:** compare boundary functions after pulling them back to the
  boundary subtype of incident edges, then recover their equality by
  function extensionality at the canonical incident-edge inclusion.
- **Seen:** four occurrences in `PEPS/RegularRegionCounting.lean` and
  `PEPS/RegularTwistedRegionCounting.lean`, detected by the tactic pattern
  scan on 2026-10-02.
- **Abstraction:** `regionBoundaryLabel_eq_iff` in
  `PEPS/RegularRegionCounting.lean`.
- **Notes:** both the fixed-boundary condition and the translated-boundary
  condition now use the same equality lemma; all four copies were removed.

### finite sums supported on constant functions — promoted
- **Pattern:** when a summand indexed by vertex labels vanishes unless the
  label function is constant, replace the sum by a sum over its common value.
- **Seen:** `sum_regionLabelCompatible_eq_sum_translation` in
  `PEPS/RegularRegionConnectivity.lean`,
  `sum_torusClosureCompatible_eq_sum_intertwiner` in
  `PEPS/RegularTorusCompatibility.lean`, and
  `sum_twistedRegionLabelCompatible_eq_sum_translation` in
  `PEPS/RegularTwistedRegionConnectivity.lean` (2026-10-02).
- **Abstraction:** Mathlib's `Fintype.sum_of_injective`, applied to the
  constant-function injection. All three proofs already use it.
- **Notes:** nonemptiness of the vertex set makes the injection faithful;
  no uniqueness from an incident edge is required, so isolated singletons
  remain covered. No additional tactic or local sum theorem is needed.

### Finite contour winding gradients — promoted (2026-10-02)

- **Pattern:** Sum a finite signed vertical edge flow along a horizontal ray,
  then compute its east and north increments by finite telescoping.
- **Occurrences:** `PEPS/IntegerContourRayPotential.lean` and the actual exposed
  orbit flow in `PEPS/IntegerCellBoundaryContour.lean`. The contour proof's
  former specialized horizontal and vertical contribution calculations have
  been removed.
- **Promotion:** `integerContourRayPotential_east` and
  `integerContourRayPotential_north`; the actual contour constructs its finite
  horizontal and vertical flows, proves conservation from successor endpoint
  continuity, and applies these shared mathematical identities.
- **Notes:** The shared statements concern finite integer flows. They do not
  assume contour connectivity or a geometric boundary relation.

### Functions constant on graph edges — promoted (2026-10-02)

- **Pattern:** Induct on a graph walk to propagate equality of a function at
  adjacent vertices. Two such inductions occurred for occupied and missing
  cells in the exposed-contour proof.
- **Promotion:** Mathlib's
  `Relation.reflTransGen_le_of_equivalence_of_le`, applied to the kernel
  equivalence of the function, together with
  `SimpleGraph.reachable_iff_reflTransGen`. The contour module has one private
  application of these existing results, reused for both cell graphs.
- **Notes:** No new public graph API or tactic is introduced; the two walk
  inductions were removed.

### compact finite-volume kernel gaps — promoted
- **Pattern:** obtain a positive lower norm bound on a finite-dimensional
  kernel complement at each parameter, preserve half of it in a neighborhood
  using continuity of the operator and its kernel projection, and pass to a
  finite subcover of a compact parameter set.
- **Seen:** the finite-volume argument in
  `TNLean/MPS/ParentHamiltonian/PeriodicShortGapContinuity.lean` and the
  fixed-injectivity-length extension in
  `TNLean/MPS/ParentHamiltonian/CompactNormalParentGap.lean`, the multiblock
  fixed-volume theorem in `BlockPeriodicGroundSpaceContinuity.lean`, and the
  local positive-interaction comparison in `CompactParentInteractionGap.lean`
  (2026-10-02).
- **Abstraction:**
  `ContinuousLinearMap.exists_uniform_norm_gap_of_compact` in
  `TNLean/Algebra/CompactKernelGap.lean`.
- **Notes:** the bound follows from finite dimensionality; positivity,
  self-adjointness, and a supplied pointwise gap are unnecessary.

### scalar cancellation in the fixed-point physical action — promoted
- **Pattern:** replace an invertible virtual matrix by a nonzero scalar
  multiple in `Wᵀ ⊗ W⁻¹`; the scalar and its reciprocal cancel.
- **Seen:** three uses across two files: the identity and multiplication
  proofs of `sptFixedPointAction` in `SPTFixedPoint.lean`, and
  `sptFixedPointAction_eq_of_forall_eq_smul` in
  `CohomologousFixedPointPath.lean`, under `TNLean/MPS/Symmetry/`.
- **Abstraction:** `MPSTensor.sptKron_eq_of_eq_smul` was already the private
  helper for the first two uses. It is now public and serves the third use.
- **Notes:** no new cancellation proof or tactic is needed.

### Gram left inverses of injective matrix sections — promoted
- **Pattern:** cancel the product of an injective section with its Hermitian
  Gram left inverse.
- **Seen:** quotient algebra recovery, letter-coordinate recovery, and
  continuous range frames.
- **Abstraction:** `Matrix.gramLeftInverse_mul` in
  `TNLean/Algebra/MatrixGramLeftInverse.lean`.
- **Notes:** all three proofs use the common lemma.

### Continuity of Gram left inverses — promoted
- **Pattern:** prove continuity of `(Cᴴ * C)⁻¹ * Cᴴ` for a continuous injective
  rectangular matrix family.
- **Seen:** trace-quotient multiplication coordinates, reconstructed letter
  coordinates, and continuous range frames.
- **Abstraction:** `Matrix.continuous_gramLeftInverse` in
  `TNLean/Algebra/MatrixGramLeftInverse.lean`.
- **Notes:** all three proofs use the common lemma. Inversion is handled by
  `Matrix.nonsing_inv_eq_ringInverse` and `NormedRing.inverse_continuousAt`.
  The local-unit argument uses those Mathlib results directly as well.

### Bilinear maps in pair-indexed coordinates — promoted
- **Pattern:** expand a bundled bilinear map into the matrix acting on
  coordinates `(a,b) ↦ x a * y b`.
- **Seen:** quotient algebra recovery, continuous quotient units, and
  continuous primitive elements.
- **Abstraction:** `Matrix.toLinearMap₂'_apply_mulVec_prod` in
  `TNLean/Algebra/MatrixBilinearCoordinates.lean`.
- **Notes:** the three private coordinate-expansion proofs are removed.

### Restricting continuous data to an open subtype neighborhood — promoted
- **Pattern:** transfer an open neighborhood in an open subtype to its image
  in the ambient space, then restrict the chosen continuous data.
- **Seen:** continuous quotient units, continuous canonical normalization,
  continuous range frames, and minimal tensor reconstruction.
- **Abstraction:** Mathlib's `IsOpen.isOpenMap_subtype_val` and
  `Topology.IsInducing.subtypeVal.continuousOn_image_iff`.
- **Notes:** the repeated ambient-intersection constructions are removed;
  no additional theorem or tactic is required.

### Associativity and units from an injective multiplicative map — promoted
- **Pattern:** transfer associativity and the two unit identities through a
  bijective coordinate identification with a matrix algebra.
- **Seen:** the associative product in
  `TNLean/MPS/Structure/TraceQuotientAlgebraRecovery.lean` and both unit
  identities in `TNLean/MPS/Structure/ContinuousTraceQuotientUnit.lean`.
- **Abstraction:** install the coordinate product as a local `Mul` and the
  recorded unit as a local `One`. Use Mathlib's
  `Function.Injective.semigroup` and `Function.Injective.mulOneClass`, then
  `mul_assoc`, `one_mul`, and `mul_one`. No additional transport lemma is needed.
- **Refactor:** these three identities use the existing Mathlib transfers.

### bilinear extension from spanning tensor letters — promoted
- **Pattern:** extend an identity on pairs of tensor letters first in one
  matrix argument and then in the other.
- **Seen:** four successive single-argument extensions in the two proofs
  `MPS/Structure/LinearExtension.lean` and
  `MPS/Structure/FiniteRingTraceAlgebra.lean` (2026-10-02).
- **Abstraction:** Mathlib's `LinearMap.mul`, `LinearMap.compr₂`,
  `LinearMap.compl₁₂`, and two nested `LinearMap.ext_on_range` calls express
  the identity as equality of bundled bilinear maps.
- **Notes:** both proofs use the existing Mathlib operations. No new tactic
  or helper theorem is needed; the original theorem signatures are unchanged.


### physical-matrix covariance from tensor letters — promoted
- **Pattern:** rewrite the physical rotation as left multiplication of
  the physical matrix, then vectorize the two bond factors; for a unitary
  general linear factor, replace its inverse by its adjoint.
- **Seen:** seven occurrences across
  `MPS/Symmetry/PolarDeformation.lean`,
  `MPS/Symmetry/PolarFrameEmbedding.lean`,
  `MPS/Symmetry/PolarFixedPointEmbedding.lean`,
  `MPS/Symmetry/CommonPhysicalEndpointPaths.lean`, and
  `MPS/Symmetry/CommonPhysicalExactPhase.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.physicalMatrix_covariance_of_rotatePhysical`
  in `MPS/Symmetry/PolarDeformation.lean`, with
  `MPSTensor.physicalMatrix_mul_eq_sptKron_of_unitary_covariance` in
  `MPS/Symmetry/PhysicalMatrixBondCovariance.lean` for unitary virtual actions.
- **Notes:** all seven callers use the common lemmas. The general identity
  allows arbitrary left and right bond matrices; neither requires the
  physical action matrix to be unitary.

### summing on-site symmetric local interactions — promoted
- **Pattern:** expand the periodic interaction Hamiltonian, prove that each
  embedded two-site term commutes with the full on-site tensor power, and
  sum the commutation identities.
- **Seen:** four occurrences in `MPS/Symmetry/CanonicalInjectiveGappedPath.lean`,
  `MPS/Symmetry/WeightedMatrixUnitParentPath.lean`, and
  `MPS/Symmetry/CommonPhysicalFixedPointPath.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.interactionHamiltonian_commute_onSiteTensorPow`
  in `MPS/Symmetry/InteractionHamiltonianSymmetry.lean`.
- **Notes:** all four callers use the common lemma. The on-site matrix need
  not be unitary; local commutation alone gives commutation of the sum.


### orthogonal matrix projections as symmetric linear projections — promoted
- **Pattern:** map a star projection through the orthonormal matrix-coordinate
  equivalence, then apply
  `LinearMap.isStarProjection_iff_isSymmetricProjection`.
- **Seen:** three occurrences in
  `MPS/Symmetry/BondProductParentHamiltonian.lean`,
  `MPS/Symmetry/PhysicalInteractionGap.lean`, and
  `MPS/Symmetry/PhysicalInteractionGroundSpace.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.bondMatrixEquiv_symm_isSymmetricProjection` in
  `MPS/Symmetry/BondProductParentHamiltonian.lean`.
- **Notes:** all three callers use the shared conversion. Mathlib supplies
  the projection equivalence; the helper supplies its matrix-coordinate
  application. No mathematical assumptions are added.

### reindexing an orthogonal matrix projection — promoted
- **Pattern:** transport idempotence by the matrix reindexing equivalence
  and self-adjointness by the conjugate-transpose reindexing identity.
- **Seen:** three uses in `MPS/Symmetry/TwoSiteBondInteraction.lean`,
  `MPS/Symmetry/FixedPointGappedPath.lean`, and
  `MPS/Symmetry/PhysicalInteractionGap.lean` (2026-10-02).
- **Abstraction:** `Matrix.isStarProjection_reindex` in
  `Algebra/MatrixProjectionReindex.lean`.
- **Notes:** all three callers use the shared lemma. It applies to matrices
  over any additive commutative monoid with multiplication and a star;
  no decidable-equality hypothesis is needed in its statement.

### inverse of a unitary general linear matrix — promoted
- **Pattern:** identify the general linear inverse with the matrix inverse,
  then use the unitary adjoint as a left inverse.
- **Seen:** three uses in `MPS/Symmetry/SPTFixedPoint.lean`,
  `MPS/Symmetry/CommonPhysicalEndpoints.lean`, and
  `MPS/Symmetry/CommonPhysicalEndpointPaths.lean` (2026-10-02).
- **Abstraction:** `Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup`
  in `Algebra/UnitaryGeneralLinearInverse.lean`.
- **Notes:** all callers use the shared matrix identity; the virtual gauge
  convention is unchanged.

### Unit-vector inner-product deficit — promoted
- **Pattern:** expand a squared distance, substitute both unit norms, and
  orient the real inner product to obtain its quadratic deficit.
- **Seen:** three checked uses in `MPS/Preparation/SecondOrderOverlap.lean:337`,
  `MPS/Preparation/SecondOrderBlockOverlap.lean:357`, and
  `MPS/Preparation/PolarCompression.lean:95` (2026-10-03).
- **Abstraction:** `one_sub_re_inner_eq_norm_sub_sq_div_two` in
  `MPS/Preparation/SecondOrderOverlap.lean:55` specializes Mathlib's
  `norm_sub_sq` to two unit vectors over a real or complex inner-product
  space. All three callers use the same identity.
- **Notes:** no custom tactic or positivity hypothesis is needed. The
  abstraction and three substitutions add ten lines, including the helper's
  mathematical documentation; future uses require one application.

### positivity of the cyclic step-orbit length — promoted
- **Pattern:** derive `0 < m / m.gcd p` from `0 < m`.
- **Seen:** four uses across `FinStepOrbit.lean`, `SectorPhaseWord.lean`, and
  `StepOrbitSectors.lean` (2026-09-29).
- **Abstraction:** the core Lean theorem `Nat.div_gcd_pos_of_pos_left p hm`
  (`Init/Data/Nat/Gcd.lean`) provides the result directly; the phase
  construction and prescribed-blocking sectors use it.
- **Notes:** no local theorem or extra positivity hypothesis is needed.

### fixed-volume C3 from a physical open-chain bound — promoted
- **Pattern:** split a martingale index into `n < l`, `n = l`, and `l < n`;
  the first two products vanish, while the last is bounded by its physical
  open-chain representative after adjoining the right spectator sites.
- **Seen:** the original threshold theorem in
  `TNLean/MPS/ParentHamiltonian/Martingale/FixedAmbientMartingaleBound.lean`
  and the prescribed-gap theorem in
  `TNLean/MPS/ParentHamiltonian/Martingale/PrescribedGap.lean` (2026-09-28).
- **Abstraction:** `fixedAmbient_martingaleDifference_norm_le_of_openChain`
  in `FixedAmbientMartingaleBound.lean` retains the chosen nonnegative bound
  without tying it to the threshold `1 / sqrt (l + 1)`.
- **Notes:** both uses share the original three-case proof; no new tactic is
  needed.

### passing a scalar grading through a matrix word — promoted
- **Pattern:** move a grading matrix through each letter and multiply the
  letter-dependent scalars.
- **Seen:** three occurrences across `MPS/ParentHamiltonian/Basic.lean`,
  `MPS/Examples/MajumdarGhoshGroundSpace.lean`, and
  `MPS/Examples/MultiBlock/ParityAmplitudes.lean`.
- **Abstraction:** `MPSTensor.mul_evalWord_of_mul_eq_smul_letter` in
  `MPS/Core/WordGrading.lean`; the constant-scalar theorem is a specialization.
- **Notes:** all three matrix-word inductions now share one proof. The parity
  example only retains the scalar identity combining occupation signs.
  The promotion adds 21 Lean lines including the helper module and imports.

### virtual-leg cancellation in source-gate contractions — promoted
- **Pattern:** cancel the adjacent factors $z^\dagger z=I$ between two
  rectangular matrices, leaving the site-specific Kronecker expansions intact.
- **Seen:** three occurrences across two files: `transported_source_u_contraction`
  in `TNLean/MPS/MPU/VirtualSourceFactorTransport.lean`, and `rawU_virtual_cancel`
  and `rawV_virtual_cancel` in `TNLean/MPS/MPU/SelectedSourceGateVirtualGauge.lean`.
- **Abstraction:** `Matrix.mul_unitary_adjoint_mul_cancel` in
  `TNLean/Algebra/UnitaryContraction.lean`.
- **Notes:** all three sites use the helper. Net Lean line delta: -2, including
  the helper module and its imports.

### bilinear identities on operators with disjoint supports — promoted
- **Pattern:** prove an identity `f A B = g A B`, bilinear in operators `A`, `B` acting on
  sets of sites `S`, `S'`, by nested `Submodule.span_induction` on
  `A ∈ supportedOperators d S` and `B ∈ supportedOperators d S'`: a product-generator case
  `finKronecker m`, `finKronecker m'` settled site by site, and eight zero, addition and
  scalar cases.
- **Seen:** 4 occurrences in 3 files (2026-09-27): `commute_of_mem_supportedOperators`
  and `expect_productVector_mul` in `TNLean/Circuit/LocalCircuit.lean`,
  `trace_rectKronecker_mul_mul` in `TNLean/Circuit/Channel/Layer.lean`,
  and `OnsiteChannel.dual_mul` in
  `TNLean/Circuit/Channel/Conversion.lean`.
- **Abstraction:** `QuantumCircuit.eq_of_mem_supportedOperators₂` in
  `TNLean/Circuit/LocalCircuit.lean`: two bilinear maps
  `f g : M →ₗ[ℂ] M →ₗ[ℂ] P` agree on supported pairs once they agree on pairs of product
  generators (`LinearMap.eqOn_span'` applied in each argument). A call site builds the two
  maps from `LinearMap.mul`, `LinearMap.compr₂` and `LinearMap.compl₁₂`, then proves only the
  product-generator case after a `change`.
- **Notes:** all four call sites are refactored (2026-09-28).

### injectivity lengths below the error cutoff — promoted
- **Pattern:** in an error bound `ε ≤ C u e^{C u}` with `u = M x^q`, dispose of
  `C u ≥ 1` by `ε ≤ 1`, then derive `x < 1` and `L_j ≤ q` for every injectivity
  length `L_j` from `C u < 1` and `C ≥ 1 + ∑ⱼ x^{-L_j}`.
- **Seen:** three occurrences across three files (2026-09-27):
  `exists_approximationError_le` in `ApproximationError.lean` (one length),
  `exists_approximationError_le_blockSum` in `OrthogonalBlockError.lean`, and
  `exists_approximationError_le_repeatedBlockSum` in `RepeatedBlockError.lean`,
  all under `TNLean/MPS/Preparation/`. The last two are now corollaries of the
  repeated-overlapping bound in `BlockSumError.lean` and no longer use the cutoff.
- **Abstraction:** `le_mul_mul_exp_of_forall_le` (the whole case split, built
  on `lt_one_and_forall_le_of_mul_mul_pow_lt_one`) and
  `Real.exp_neg_mul_div_eq_pow` (the rewrite `e^{-γ q/ξ} = (e^{-γ/ξ})^q`), in
  `TNLean/MPS/Preparation/InjectivityCutoff.lean`; the single-length site
  instantiates the index type with `Unit`.
- **Notes:** all three call sites are refactored. The block-by-block bound
  `C₁ u e^{S₁ u} + K₅ u` that follows is still duplicated between the two
  block-sum files and is a candidate for the same treatment.

### error from a logarithmic block-length threshold — promoted
- **Pattern:** close `K * (M * Real.exp (-x)) ≤ ε` from a threshold
  `log K + log M - log ε ≤ x` by a hand-written `calc` through
  `Real.exp_log`, `Real.exp_add`/`Real.exp_sub` and `Real.exp_le_exp`.
- **Seen:** three occurrences across three files (2026-09-30):
  `DepthLogBound.lean`, `LogDepthPreparation.lean` and `TreeMERA.lean`, all
  under `TNLean/MPS/Preparation/`.
- **Abstraction:** `mul_mul_exp_neg_le_of_log_le` in
  `TNLean/MPS/Preparation/InjectivityCutoff.lean`.
- **Notes:** all three call sites use the helper; each now proves only the
  threshold inequality.

### error from a block-length threshold with a logarithmic offset — promoted
- **Pattern:** from `a log(M q/ε) + b ≤ q` with `b ≥ a max(log K, 0)`, expand
  `log(M q/ε)`, discard `a log q ≥ 0`, and pass `log K + log M - log ε ≤ q/a`
  to `mul_mul_exp_neg_le_of_log_le`.
- **Seen:** two occurrences across two files (2026-10-01):
  `DepthLogBound.lean` and `NonNormalMeasurementPreparation.lean`, under
  `TNLean/MPS/Preparation/`.
- **Abstraction:** `mul_mul_exp_neg_div_le_of_le` in
  `TNLean/MPS/Preparation/InjectivityCutoff.lean`.
- **Notes:** promoted at two sites because the second copy was verbatim; the
  remaining threshold steps in `LogDepthPreparation.lean` and `TreeMERA.lean`
  have different offsets and keep `mul_mul_exp_neg_le_of_log_le`.

### depth from the window of block lengths — promoted
- **Pattern:** from `q ≤ 2 (a log(N/ε) + b)`, `N ≥ 2`, `0 < ε ≤ 1`, `b ≥ 1`,
  a `calc` through `log(N/ε) ≥ log 2` giving
  `C q ≤ C (2a + 2b/log 2) log(N/ε)`.
- **Seen:** two verbatim occurrences across two files (2026-10-01):
  `DepthLogBound.lean` and `NonNormalMeasurementPreparation.lean`.
- **Abstraction:** `MPSPreparation.natCast_mul_le_mul_log_of_le_two_mul` in
  `TNLean/MPS/Preparation/DepthLogBound.lean`.
- **Notes:** both call sites are one line.

### gap of the transfer map of a normal tensor — promoted
- **Pattern:** `uniform_eigenvalue_gap_of_finite_lt_one` with
  `Kraus.isChannel_mapLM … |>.eigenvalue_norm_le_one` and
  `primitive_transfer.unique_peripheral`, then `t := max (1 - δ) (1 / 2)`.
- **Seen:** three occurrences across three files (2026-10-01):
  `ApproximationError.lean`, `DepthLogBound.lean` and
  `NonNormalMeasurementPreparation.lean`, under `TNLean/MPS/Preparation/`.
- **Abstraction:** `MPSTensor.exists_eigenvalue_norm_le_of_isNormal` in
  `TNLean/MPS/Preparation/ApproximationError.lean`; the family version
  `MPSPreparation.exists_forall_eigenvalue_norm_le` takes the maximum over the
  blocks.
- **Notes:** all three call sites use the helper.

### kernel projection under a right-spectator fiberwise conjugacy — promoted
- **Pattern:** from a right-spectator conjugacy `U G U⁻¹ = rightFiberwiseMap H`,
  conclude `U P_{ker G} U⁻¹ = rightFiberwiseMap P_{ker H}` by combining
  `ker_starProjection_conj_linearIsometryEquiv` with
  `ContinuousLinearMap.ker_starProjection_rightFiberwiseMap` and a `change`.
- **Seen:** five occurrences across two files:
  `openPrefixGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`,
  `openPrefixWholeGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`,
  and `openIntervalGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`
  in `TNLean/MPS/ParentHamiltonian/Martingale/SpectatorTransport.lean`, and
  both `hP` and `hQ` in
  `norm_suffixGroundProjection_comp_prefixDifference_le_active` in
  `TNLean/MPS/ParentHamiltonian/Martingale/GroupedSpectatorNorm.lean`.
- **Abstraction:** `MPSTensor.ker_starProjection_conj_of_rightFiberwiseMap` in
  `SpectatorTransport.lean`, stated in the composition form of the Hamiltonian
  conjugacy lemmas; each call site is one application. The grouped estimate
  ascribes the `LinearEquiv.conj` form, which is definitionally equal.

### common positive simple blocking of two or three MPUs — promoted
- **Pattern:** choose a positive simple blocking for each MPU, add the chosen
  lengths, and use persistence of simplicity at every later direct blocking.
- **Seen:** three occurrences across three developments (2026-09-26):
  `IsMPUCanonicalFormII.index_eq_of_mpo_eq` in `RepresentativeIndex.lean`
  (two tensors), `IsMPUCanonicalFormII.index_tensorProduct` in
  `TensorProductIndex.lean` (three tensors), and
  `IsMPUCanonicalFormII.index_eq_add_of_mpo_eq_mulTensor` in
  `CompositionIndex.lean` (three tensors).
- **Abstraction:** `MPOTensor.IsMPU.exists_common_blockTensor_isMPUSimple`
  and `MPOTensor.IsMPU.exists_common_blockTensor_isMPUSimple_three` in
  `TNLean/MPS/MPU/SimpleBlocking.lean`.
- **Notes:** the two- and three-tensor forms allow different physical and bond
  dimensions without an indexed-family abstraction. All three known call
  sites are refactored on their respective dependent branches: representative
  index at `008464fc4`, tensor-product index at `86217104a`, and composition
  index at `4a9bbc2f5`. No fourth copy is introduced.

### fixed-range block parent gap from an open-chain kernel identity — promoted
- **Pattern:** obtain a gapped range `W ≥ 2 * R` for a primitive block sum, then transfer the
  gap to range `R` through the open-chain kernel identity at `W`; the uniform form then
  converts the eventual gap into a gap for every chain length with
  `Filter.Eventually.exists_forall_of_atTop` and `parentHamiltonianES_gap_of_eventual_gap`.
- **Seen:** the transfer step three times, in
  `TNLean/MPS/ParentHamiltonian/Martingale/PrimitiveBlockGapAtC1Range.lean`,
  `TNLean/MPS/ParentHamiltonian/Martingale/PrimitiveBlockGapThreshold.lean`, and
  `TNLean/MPS/ParentHamiltonian/Martingale/BlockGapAtSimultaneousInjectivity.lean`; the
  eventual-to-uniform step twice, in
  `TNLean/MPS/ParentHamiltonian/Martingale/PrimitiveBlockUniformGap.lean` and
  `BlockGapAtSimultaneousInjectivity.lean`.
- **Abstraction:** `exists_parentHamiltonianES_toTensorFromBlocks_gap_of_ker_openParentHamiltonianES_eq`
  and its uniform companion
  `exists_parentHamiltonianES_toTensorFromBlocks_uniform_gap_of_ker_openParentHamiltonianES_eq`
  in `PrimitiveBlockGapThreshold.lean`. Both take the primitive block data, a positive range
  `R`, and `∀ W, R ≤ W → ker (openParentHamiltonianES B R W) = groundSpaceES B W`; each call
  site supplies only its kernel identity.

### every list is a `List.ofFn` — promoted
- **Pattern:**
  ```lean
  obtain ⟨L, u, rfl⟩ : ∃ L, ∃ u : Fin L → Fin (d * d), w = List.ofFn u :=
    ⟨_, _, (List.ofFn_get w).symm⟩
  ```
- **Seen:** eight occurrences across two files: four in
  `TNLean/MPS/Core/ReductionComposition.lean` (the `kronId`/`idKron` lifts of reductions and
  dressed proportionality) and four in `TNLean/MPS/MPDO/ActionTensorReduction.lean` (the
  action-tensor lifts).
- **Abstraction:** `List.exists_eq_ofFn` in `TNLean/Algebra/ListOfFn.lean`; call sites write
  `obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w`.
- **Notes:** used before rewriting with `evalWord_ofFn`-style lemmas that are stated on
  `List.ofFn` words. The `l = List.ofFn (fun k ↦ l[k])` variants in
  `ResidualAlgebra.lean`, `ThreeFormSpan.lean`, and `ReductionResidual.lean` keep the explicit
  indexing function and are not refactored.

### operator identity from a word-trace identity — promoted
- **Pattern:**
  ```lean
  rw [← MPOTensor.mpo_mulTensor]
  ext σ τ
  have hw : (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) ≠ [] := by
    simp only [ne_eq, List.ofFn_eq_nil_iff]
    omega
  have h := ‹trace identity› (List.ofFn fun k => finProdFinEquiv (σ k, τ k)) hw
  unfold ‹stack› ‹targets› at h
  rw [MPOTensor.evalWord_toMPSTensor_pairConfig, ...] at h
  simpa [MPOTensor.mpoMatrixEntry] using h
  ```
- **Seen:** six occurrences across four files (2026-09-17): `fibonacci_fusion_rule` in
  `TNLean/MPS/Examples/Fibonacci/Fibonacci.lean`, `mpo_uu` and `mpo_dd` in
  `Examples/Z3Anomalous/Z3AnomalousFusion.lean`, `mpo_ud` and `mpo_du` in
  `Examples/Z3Anomalous/Z3AnomalousInverseFusion.lean`, `mpo_defect_mul_defect` in
  `Examples/Z3Anomalous/Z3AnomalousDefectCompression.lean`.
- **Abstraction:** `MPOTensor.mpo_apply_toMPSTensor`, `MPOTensor.ofFn_pairConfig_ne_nil`,
  `MPOTensor.mpo_eq_of_trace_evalWord` and `MPOTensor.mpo_mul_eq_of_trace_evalWord` in
  `TNLean/MPS/MPDO/OperatorFromWordTrace.lean`.
- **Notes:** a fusion rule with a single target is one application of
  `mpo_mul_eq_of_trace_evalWord`; sums or scalar multiples of operators rewrite the matrix
  elements with `mpo_apply_toMPSTensor` and apply the trace identity entrywise. All call sites
  are refactored; each loses six to nine lines.

### span of all matrix units is everything — promoted
- **Pattern:**
  ```lean
  refine top_unique fun X _ => ?_
  rw [Matrix.matrix_eq_sum_single X]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using T.smul_mem (X i j) (hunit i j)
  ```
- **Seen:** seven occurrences across six files (2026-09-17):
  `TNLean/MPS/Examples/CZX/CZXTensor.lean`, `Examples/Fibonacci/Fibonacci.lean`
  (twice), `Examples/MultiBlock/ParityGraded.lean`, `Examples/KramersWannier/KramersWannier.lean`,
  `Examples/MultiBlock/StackedPairGauge.lean`, `Examples/Rings/EisensteinCertificates.lean`.  A later sweep
  (2026-09-19) found nine further occurrences outside the `Reduction/Examples` directory that
  the promotion had missed: `Examples/Rings/Zsqrt2Ring.lean`, `Examples/Rings/GoldenCompression.lean`,
  `Examples/MultiBlock/OneSlotGauge.lean`, `TNLean/MPS/MPDO/CZXTensorInjectivity.lean`,
  `TNLean/MPS/MPDO/BondTwoSingletonGramBoundary.lean`,
  `TNLean/MPS/MPDO/BiCFDerivation/DiagonalRestrictionCounterexample.lean`,
  `TNLean/MPS/MPDO/PositiveMinimalRealizationCounterexample.lean`,
  `TNLean/MPS/RFP/BellPairCIDObstruction.lean` and
  `TNLean/PEPS/TorusRowColumnReductionObstruction.lean`.
- **Abstraction:** `Submodule.eq_top_of_forall_single_mem` in
  `TNLean/Algebra/MatrixSingleSpan.lean`.
- **Notes:** the goal is `T = ⊤` for a submodule `T` of matrices, or `Kraus.IsInjective A`
  unfolded to it; the hypothesis is membership of every matrix unit.  The 2026-09-17 entry
  claimed that every call site had been refactored, which was wrong for the nine sites listed
  above; those were refactored on 2026-09-19, after which the claim holds.  A site loses
  between three and nine lines.

### simplicity with the recorded canonical fixed pair — promoted
- **Pattern:** specialize supplied-witness `simple2` to the canonical transfer
  power at `max (D * D - 1) 1`, deriving physical nonvanishing from canonical
  form II and using the recorded vectorized right boundary and identity left boundary.
- **Seen:** three occurrences across three files (2026-09-06):
  `IsMPUCanonicalFormII.sourceV_isIsometry` in
  `TNLean/MPS/MPU/SourceVCompleteNetwork.lean`,
  `IsMPUCanonicalFormII.doubleLayer_boundary_contractions` in
  `TNLean/MPS/MPU/AdjointSimpleContraction.lean`, and
  `IsMPUCanonicalFormII.oneLetter_physical_contraction` in
  `TNLean/MPS/MPU/SourceYPhysicalContractions.lean`.
- **Abstraction:** `MPOTensor.IsMPUCanonicalFormII.simple2_recorded_fixed_pair`
  in `TNLean/MPS/MPU/SuppliedFixedWitnesses.lean`.
- **Notes:** all three callers use the helper; the source-V proof retains its
  explicit transpose-symmetry conversion. The boundary-contraction proof gives
  the local hypothesis its original vector-shaped type to preserve rewriting
  through the local `ρ` and `Φ` definitions. No new imports, structures, or
  `simple1` wrapper are introduced; caller proof bodies lose one line overall.

### reciprocal scalar cancellation across a matrix product — promoted
- **Pattern:** move scalars out of a matrix product and cancel nested actions
  by a nonzero scalar and its inverse, in either order.

  ```lean
  simp (disch := exact hβ) only [matrix_reciprocal_smul]
  ```
- **Seen:** three declarations across three files (2026-09-04):
  `MPSTensor.IsReduction.reciprocal_smul` in `TNLean/MPS/Core/Reduction.lean`
  (two goals), `MPSTensor.reductionResidual_reciprocal_smul` in
  `TNLean/MPS/Core/ReductionResidual/Basic.lean`, and
  `MPSTensor.IsReductionExteriorBufferLength.reciprocal_smul_iff` in
  `TNLean/MPS/Core/ReductionBlocking.lean`.
- **Abstraction:** the `matrix_reciprocal_smul` simp set, registered in
  [`TNLean/Tactic/Attr.lean`](../TNLean/Tactic/Attr.lean) and populated in
  [`TNLean/Tactic/MatrixReciprocalSmul.lean`](../TNLean/Tactic/MatrixReciprocalSmul.lean)
  with Mathlib's `Matrix.smul_mul`, `Matrix.mul_smul`, `inv_smul_smul₀`, and
  `smul_inv_smul₀`. No new cancellation theorem or tactic is needed.
- **Notes:** all three declarations now use the set (four proof lines removed).
  An explicit discharger supplies the nonzero premise to the conditional
  cancellation lemmas; `simp only [matrix_reciprocal_smul, hβ]` alone does not
  discharge it on the pinned toolchain. Do not add `smul_smul`: the intended
  normal form preserves nested actions until reciprocal pairs cancel.

### source-rank nonvanishing from a trace equation — promoted
- **Pattern:** derive `rank ≠ 0` from `htrace : coefficient * rank = d` and
  `hd : d ≠ 0` by assuming the rank is zero and simplifying the trace equation.
- **Seen:** four occurrences across three files (2026-09-06):
  `IsMPUCanonicalFormII.sourceY₁_mul_conjTranspose` in
  `TNLean/MPS/MPU/SourceYOneNormalization.lean`,
  `IsMPUCanonicalFormII.sourceY₂_weighted_mul_conjTranspose` in
  `TNLean/MPS/MPU/SourceYTwoNormalization.lean`, and
  `IsMPUCanonicalFormII.sourceX₁_physical_contraction` and
  `IsMPUCanonicalFormII.sourceX₂_physical_contraction` in
  `TNLean/MPS/MPU/SourceXPhysicalNormalization.lean`.
- **Abstraction:** existing Mathlib `right_ne_zero_of_mul`, applied as
  `right_ne_zero_of_mul (htrace.trans_ne hd)`.
- **Notes:** resolved by direct library reuse at all four sites, removing twelve
  proof lines. No new helper, tactic, import, or public statement is needed.

### nested finite-sum congruence under two binders — promoted
- **Pattern:** two successive `apply Finset.sum_congr rfl` steps, each
  followed by an index and membership introduction.
- **Seen:** the 2026-09-05 scan at `00ff0ec40` reports 11 literal
  three-line `i`/`_` prefixes across six surviving files, and seven fully
  literal `i`/`j` four-line blocks across those same files. The deleted
  `ReflectedTransferKernel.lean` is excluded. Counting alpha-renamed
  four-line windows using the scanner's consecutive runs gives 77 windows
  across 40 files; overlapping windows in three-binder descents count twice.
- **Abstraction:** `Finset.sum_congr₂` in
  `TNLean/Algebra/FinSumPermutation.lean`, with
  `{κ : ι → Type*}`, `{t : (i : ι) → Finset (κ i)}`, and an
  `AddCommMonoid` codomain. Both the inner index type and its finite set may
  depend on the outer index. Two applications of Mathlib's `sum_congr`
  prove it; no macro, product API, or additional typeclass is needed.
- **Result:** 19 nonoverlapping descents replaced across the six primary
  files: `CompleteZipperFusionPentagon.lean` (10), including its dependent
  fusion multiplicities; `CPSVBlockingChannelCounterexample.lean` (3);
  `VerticalCF.lean` (1); `ReflectedMarkedChain.lean` (2);
  `TwoSitePrefixReflectedMarkedChain.lean` (2); and
  `MPU/DoubleLayerContraction.lean` (1). All 11 primary literal sites are
  covered. No adjacent two-descent block remains in these files; intervening
  rewrites and single descents remain explicit. The global alpha-renamed
  window count is now 53 across 34 files, outside this bounded refactor.
- **Notes:** caller proofs shrink by 38 lines; four direct imports and the
  general helper/documentation give a net Lean reduction of 20 lines.
  All existing declarations and paper anchors are unchanged. The related
  commutation-first pattern still uses `Finset.sum_comm`; this lemma only
  replaces two adjacent congruence descents after any permutation.


### three-block configuration extensionality — promoted
- **Pattern:** prove equality of vectors indexed by a concatenated three-block
  configuration by splitting an arbitrary configuration through the canonical
  three-block equivalence.
- **Seen:** five occurrences in
  `TNLean/MPS/ParentHamiltonian/FNWProjectorDefect.lean` before promotion
  (2026-09-02).
- **Abstraction:** the private theorem `euclideanSpace_threeBlock_ext` in
  `TNLean/MPS/ParentHamiltonian/FNWProjectorDefect.lean`.
- **Notes:** callers now provide the pointwise equality on the three separate
  blocks; the helper performs the repeated extensionality and configuration
  decomposition.

### torus-translation bond uniformity — promoted
- **Pattern:** use a translation carrying one right (respectively up) edge to
  another to prove constancy of a bond-dimension function, then reduce an
  arbitrary horizontal or vertical edge to the corresponding reference edge.
- **Seen:** six occurrences across two files before promotion (2026-08-31):
  the right-edge, up-edge, and orientation-uniformity proofs in
  `TNLean/PEPS/TorusTranslationInvariant.lean` and
  `TNLean/PEPS/TorusStateTranslationInvariant.lean`.
- **Abstraction:** `bondDim_torusRightEdge_const_of_translate`,
  `bondDim_torusUpEdge_const_of_translate`, and
  `torusUniformBondDim_of_translate` in
  `TNLean/PEPS/TorusTranslationInvariant.lean`.
- **Notes:** the helpers assume only invariance of the bond-dimension function
  under every torus translation.  Both the tensor-level and state-level
  wrappers now supply their respective translated-edge equality theorem.

### torus shift of a product over sites — promoted
- **Pattern:** reindex a product over torus sites by `Equiv.addRight (1, 0)`
  (or `(0, 1)`), rewrite `u + (1, 0)` as `(u.1 + 1, u.2)` and cancel with
  `add_sub_cancel_right`, turning factors on the left (or down) leg of each
  site into factors on the right (or up) leg of its neighbour.
- **Seen:** six occurrences across three files before promotion (2026-09-26):
  `TNLean/PEPS/Examples/Cluster.lean` (`stateCoeff_clusterPEPS`),
  `TNLean/PEPS/Examples/AKLT.lean` (`stateCoeff_akltPEPS`), and
  `TNLean/PEPS/Examples/RVB.lean` (`stateCoeff_rvbPEPS`), one horizontal and
  one vertical shift each.
- **Abstraction:** `TNLean.PEPS.prod_torus_sub_fst` and
  `TNLean.PEPS.prod_torus_sub_snd` in `TNLean/PEPS/TorusSiteTensor.lean`.
- **Notes:** pass the two-site factor `f` explicitly, since the product
  `∏ v, f v (v.1 - 1, v.2)` is not a higher-order pattern; a symmetric factor
  written in the other order needs one `Finset.prod_congr` with `mul_comm`.

### permutation-matrix unitarity — promoted
- **Pattern:** unfold unitary-group membership, rewrite the conjugate transpose
  of a permutation matrix as the inverse permutation matrix, and reduce their
  product to the identity permutation.
- **Seen:** three occurrences before promotion (2026-08-30):
  `TNLean/MPS/MPU/Examples/Shift.lean` (`rightShiftTensor_isMPU`),
  `TNLean/MPS/FundamentalTheorem/SectorBNT/FundamentalCoord.lean`
  (`permGL_mem_unitaryGroup`), and
  `TNLean/MPS/MPU/Examples/ShiftTilde.lean`
  (`shiftPhysicalSwap_mem_unitaryGroup`).
- **Abstraction:** `Equiv.Perm.permMatrix_mem_unitaryGroup` in
  `TNLean/Algebra/PermutationMatrixUnitary.lean`.
- **Notes:** all three call sites now use the common theorem; the
  fundamental-theorem consumer simplifies the coercion of `permGL` to its
  underlying permutation matrix.

### non-injectivity from an annihilating linear functional — promoted
- **Pattern:** exhibit a matrix outside the span of a finite Kraus family by
  running `Submodule.span_induction` over an entrywise linear condition
  (`M 0 1 = 0`, `M 0 0 = M 1 1`), discharging the `zero`, `add`, and `smul`
  cases by `simp`/`linear_combination`, then contradicting the membership of a
  chosen witness supplied by `span_eq_top ▸ Submodule.mem_top`.
- **Seen:** eight occurrences before promotion (2026-08-26):
  `TNLean/MPS/Examples/AKLT.lean` (`aklt_not_isInjective`),
  `TNLean/MPS/Examples/GHZ.lean` (`ghz_not_isInjective`),
  `TNLean/MPS/Examples/Cluster.lean` (`cluster_not_isInjective`),
  `TNLean/MPS/Examples/EvenParity.lean` (`evenParity_span_diag_eq` and
  `evenParity_not_isInjective`),
  `TNLean/MPS/Examples/MajumdarGhosh.lean` (`majumdarGhosh_not_isInjective`,
  `majumdarGhosh_not_isNBlkInjective_of_odd`,
  `majumdarGhosh_not_isNBlkInjective_of_even`), and
  `TNLean/MPS/MPDO/BiCFDerivation/DiagonalRestrictionCounterexample.lean`
  (`diagBlock_diagonalRestrictionUnits_not_isNormal`).
- **Abstraction:** `Kraus.not_isInjective_of_linearMap` and
  `Kraus.not_isNBlkInjective_of_linearMap` in
  `QICLean/Kraus/Injectivity.lean`.
- **Notes:** the caller supplies the functional (typically a signed sum of
  `Matrix.entryLinearMap`), the vanishing proof on the generators, and one
  witness on which the functional is nonzero; the span induction disappears.
  Both lemmas are channel-generic finite-Kraus results and are owned by
  QICLean's injectivity file.

### Kronecker product of matrix isometries — promoted
- **Pattern:** expand `Matrix.IsIsometry`, commute conjugate transpose and
  multiplication with the Kronecker product, and substitute the two constituent
  isometry identities.
- **Seen:** two source-factor proofs in
  `TNLean/MPS/MPU/SourceFactorsTensorProduct.lean`, private copies in
  `TNLean/MPS/MPDO/IsometricAdjacentBondTransport.lean` and
  `TNLean/MPS/MPDO/CPSVExample410Spectrum.lean`, and reindexed hand proofs in
  `TNLean/MPS/MPDO/BNTRightTripleFusion.lean` and
  `TNLean/MPS/MPDO/BNTLeftTripleFusion.lean` before promotion (2026-08-24).
- **Abstraction:** `Matrix.IsIsometry.kronecker` in
  `TNLean/Algebra/MatrixIsometryKronecker.lean`.
- **Notes:** the theorem is rectangular and assumes only the finite row
  coordinates and decidable column coordinates required by the two complex
  matrix isometry identities. All cited copies now use the common theorem; the
  four first- and second-stage fusion proofs compose it with
  `Matrix.IsIsometry.reindex`.

### rectangular isometry entries — promoted
- **Pattern:** extract either scalar-product orientation of column
  orthonormality from `Vᴴ * V = 1` by applying the matrix equality at two
  column indices and unfolding matrix multiplication, conjugate transpose,
  and the identity matrix.
- **Seen:** nineteen entry extractions across fourteen TNLean files before
  promotion (2026-08-29): `PhysicalIndexMixing.lean`,
  `PhysicalIsometricEmbedding.lean`, `SitewisePhysicalMatrix.lean`,
  `PhysicalSectorCoordinateTransport.lean`,
  `PhysicalSectorBondTransport.lean`, `RFP/Defs.lean`,
  `RFP/StructuralFull.lean`, `RFP/BeigiLoopInjectivity.lean`,
  `Symmetry/StringOrderAux.lean`, `MPU/MatchingContractions.lean`,
  `MPU/SourceFactors.lean`, `Periodic/Applications.lean`,
  `MPDO/LemmaC5CaseI.lean`, and
  `MPDO/NonCartesianActiveSectorObstruction.lean`.
- **Abstraction:**
  `Matrix.sum_star_mul_eq_ite_of_conjTranspose_mul_eq_one` and
  `Matrix.sum_mul_star_eq_ite_of_conjTranspose_mul_eq_one` in
  `QICLean/Algebra/MatrixIsometryEntries.lean` (QICLean dependency).
- **Notes:** both complex scalar orientations are owned by QICLean's generic
  rectangular matrix layer. All cited TNLean consumers now invoke them
  directly; no MPS- or MPO-specific wrapper is retained.

### rectangular coisometry entries — promoted
- **Pattern:** extract either scalar-product orientation of row
  orthonormality from `V * Vᴴ = 1` by applying the matrix equality at two row
  indices and unfolding matrix multiplication, conjugate transpose, and the
  identity matrix.
- **Seen:** eight entry extractions across seven TNLean files before promotion
  (2026-08-29): `MPU/MatchingContractions.lean`,
  `MPU/SourceFactorContraction.lean`, `MPDO/BNTFixedFinalUnitarity.lean`,
  `MPDO/PhysicalSectorCoordinateTransport.lean`,
  `MPDO/NonCartesianActiveSectorObstruction.lean`,
  `MPDO/NonCartesianActiveSectorRigidity.lean` (two extractions), and
  `MPDO/BlockedCompleteZipper.lean`.
- **Abstraction:**
  `Matrix.sum_mul_star_eq_ite_of_mul_conjTranspose_eq_one` and
  `Matrix.sum_star_mul_eq_ite_of_mul_conjTranspose_eq_one` in
  `QICLean/Algebra/MatrixIsometryEntries.lean` (QICLean dependency).
- **Notes:** both complex scalar orientations are owned by QICLean's generic
  rectangular matrix layer. All eight TNLean consumers now invoke the public
  row-entry API directly; no tensor-network-specific wrapper is retained.

### positive-definite trace pairing with a nonzero positive matrix — promoted
- **Pattern:** prove `0 < Matrix.trace (A * B)` or its cyclic orientation from
  `A.PosDef`, `B.PosSemidef`, and `B ≠ 0` by combining nonnegativity with
  faithfulness of the positive-definite weighted trace.
- **Seen:** three occurrences across two TNLean files before promotion
  (2026-08-23): two in
  `TNLean/MPS/MPDO/NonCartesianActiveSectorCounterexample.lean` and one in
  `TNLean/MPS/CanonicalForm/NormalTensorGauge.lean`. QICLean also contained
  two private copies before the upstream promotion.
- **Abstraction:** `Matrix.PosDef.trace_mul_pos_of_posSemidef_of_ne_zero` and
  `Matrix.PosSemidef.trace_mul_pos_of_ne_zero_of_posDef` in
  `QICLean/Algebra/MatrixAux.lean` (QICLean dependency).
- **Notes:** QICLean owns the canonical statement and derives the cyclic
  product orientation by trace commutativity. All three TNLean derivations
  now use the public theorem directly; no companion API is duplicated locally.

### matrix-reindex entry transport — direct
- **Pattern:** package an entrywise formula as a `Matrix.reindex` equality with
  `ext` and `Matrix.reindex_apply`, or restate an entry in the reindexing
  coordinates by destructuring both index arguments through `Equiv.surjective`
  and discharging the inverse equivalences with `Equiv.symm_apply_apply`.
- **Seen:** four coordinate-restatement proofs in
  `TNLean/MPS/MPU/Examples/ShiftSourceBlockedFormulas.lean` (lines 25, 44, 121,
  and 140). Locations re-derived 2026-09-03 after the source-cut file split and
  recounted 2026-09-04: the eight packaging proofs formerly counted in the
  mixed-kernel example module went with its deletion.
- **Abstraction:** none. The former project wrappers were retired with
  `QICLean.Algebra.MatrixReindex`; the direct extensionality and evaluation
  proofs are the canonical pattern.
- **Notes:** the source-gate call sites retain the paper's four-spin coordinate
  order explicitly in their local arguments.

### multiplication of compatibly reindexed matrices — Mathlib API
- **Pattern:** replace the product of two `Matrix.reindex` operations with one
  reindexing of the matrix product along the common middle equivalence.
- **Seen:** eight occurrences in
  `TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` and four in
  `TNLean/MPS/MPU/SourceFactorsTensorProduct.lean`.
- **Abstraction:** Mathlib's `Matrix.reindexLinearEquiv_mul`; instantiate the
  row, middle, and column equivalences explicitly and use
  `Matrix.coe_reindexLinearEquiv` when coercion normalization is needed.
- **Notes:** the source-factor call sites keep all three equivalences explicit,
  so the source-cut orientations remain visible and no searching tactic is
  used. The former `Matrix.reindex_mul_reindex` wrapper is retired.

### blocked-coordinate transport of a channel — promoted
- **Pattern:** relabel the source matrix index along one equivalence, conjugate
  by a rectangular isometry, and relabel the target index back along a second
  equivalence; then assemble trace-preserving complete positivity from the two
  reindexings and the single-Kraus conjugation.
- **Seen:** four defining occurrences and four accompanying positivity proofs
  in `TNLean/MPS/MPDO/PhysicalSectorPhysicalTransport.lean` before promotion
  (2026-08-27).
- **Abstraction:** the private `blockTransportMap` and
  `blockTransportMap_isKrausCPTP` at the head of that file.
- **Notes:** the four blocked physical-sector transports and their inverses now
  differ only in the two coordinate equivalences and the isometry, so the
  blocking convention stays explicit at each call site.

### periodic operator entry along a forced bond configuration — promoted
- **Pattern:**
  ```lean
  rw [MPOTensor.mpo_apply, MPOTensor.mpoMatrixEntry, MPOTensor.evalWord_ofFn]
  have h := MPSTensor.trace_evalWord_eq_sum_cyclic M.toMPSTensor
    (fun n ↦ finProdFinEquiv (s n, t n))
  rw [MPSTensor.evalWord_ofFn_eq_prod] at h
  have h' : ... := by simpa only [MPOTensor.toMPSTensor, ...] using h
  rw [h', Fintype.sum_eq_single g0]
  ...
  · intro g hg
    obtain ⟨n, hn⟩ := Function.ne_iff.mp hg
    refine Finset.prod_eq_zero (Finset.mem_univ n) ?_
  ```
- **Seen:** seven occurrences across seven files: `mpo_czxTensor_apply` in
  `TNLean/MPS/Examples/CZX/CZXUnitary.lean`,
  `mpo_reviewCZXTensor_apply` in `Examples/CZX/CZXReviewTensor.lean`,
  `mpo_czxDecoratedTensor_apply` in `Examples/CZX/CZXDecoratedTensor.lean`,
  `mpo_uTensor_apply` in `Examples/Z3Anomalous/Z3AnomalousUnitary.lean`, `mpo_symTensor_apply` in
  `Examples/AnomalousCondensation/AnomalousCondensationZ2Z2Unitary.lean`, `mpo_tensor_apply` in
  `TNLean/MPS/MPDO/CZXTensor.lean`, and `mpo_rightShiftTensor_apply` in
  `TNLean/MPS/MPU/Examples/Shift.lean`.
- **Abstraction:** `MPOTensor.mpo_apply_eq_sum_cyclic` and
  `MPOTensor.mpo_apply_eq_prod_of_forced_bond` in `TNLean/MPS/MPDO/OperatorCyclicSum.lean`;
  for monomial tensors, `MPOTensor.mpo_apply_of_forced_right_bond` and
  `MPOTensor.mpo_apply_of_forced_left_bond` in the same file.
- **Notes:** the caller of `mpo_apply_eq_prod_of_forced_bond` supplies the surviving bond
  configuration `g₀` and, for every other configuration, one site with a vanishing entry. When
  the entry has the form `if i = π j ∧ r = β i j then φ i j l else 0` (or `l = β i j` with
  phase `φ i j r`), the forced-bond lemmas take the tensor's `_apply` lemma as their only
  hypothesis and return `if s = π ∘ t then ∏ n, ... else 0`; the caller only rewrites its phase
  exponent as a sum. The six monomial call sites above and `mpo_tensor_apply` in
  `TNLean/MPS/MPU/GroupCocycleMPO.lean` use these, each in two to five lines (net about
  `-150` lines). The shift uses only `mpo_apply_eq_sum_cyclic`, because its surviving
  configuration is the input configuration and exists only when the output is its rotation.

### SAL nonvanishing of the physical-trace transfer — promoted
- **Pattern:** contradict the positive-length trace clause in `IsSAL` at one
  site by rewriting the periodic trace as the trace of the vertical loop and
  then setting the physical-trace transfer equal to zero.
- **Seen:** two duplicated proofs in `TNLean/MPS/MPDO/BNTSectorAreaLaw.lean`
  and `TNLean/MPS/MPDO/RFPViaTSSAL.lean`; the literal-idempotence bridge in
  `TNLean/MPS/MPDO/SALTraceTransfer.lean` supplied the third use at promotion
  (2026-08-21).
- **Abstraction:** `MPOTensor.IsSAL.physTraceTransfer_ne_zero` in
  `TNLean/MPS/MPDO/SALTraceTransfer.lean`.
- **Notes:** the two duplicated proofs now use the common theorem. The same
  module records the immediate bridge from SAL and literal idempotence to
  source zero correlation length.

### Powers on an eigenspace — promoted
- **Pattern:** prove `(f ^ n) x = μ ^ n • x` from `x ∈ f.eigenspace μ`, either by induction
  using `Module.End.mem_eigenspace_iff` or by splitting on `x = 0` before applying
  `HasEigenvector.pow_apply`.
- **Seen:** 3 occurrences across `TNLean/Channel/Peripheral/WeightedCesaro.lean`,
  `TNLean/Channel/Peripheral/CesaroRecurrence.lean`, and
  `TNLean/Kraus/Wielandt/Primitivity/VectorSpreadToPrimitive.lean`.
- **Abstraction:** `Module.End.pow_apply_of_mem_eigenspace` in
  `QICLean/Algebra/EigenspaceMap.lean` (QICLean dependency) handles the zero vector directly and is used by all
  three consumers.

### finite-Kraus transfer-power trace pairing — promoted
- **Pattern:** expand a Kraus-map or MPS transfer-map power as a sum over words,
  distribute matrix multiplication through the sum, reduce multiplication by a
  matrix unit to entries, and identify the resulting product of diagonal sums
  with a trace times its complex conjugate.
- **Seen:** two exact proofs, each over 90 lines, in
  `TNLean/Kraus/Wielandt/Primitivity/StronglyIrreducibleToFullWordSpan.lean` and
  `TNLean/Wielandt/Primitivity/TracePairing.lean` before promotion (2026-08-20).
- **Abstraction:** `Kraus.sum_normSq_trace_conjTranspose_mul_evalWord` in
  `QICLean/Kraus/TracePairing.lean` (QICLean dependency).
- **Notes:** the Kraus theorem owns the generic identity. The established
  `MPSTensor.sum_normSq_trace_conjTranspose_mul_evalWord` statement is a direct
  reformulation by definitional equality; the primitive full-word-span
  proof applies the Kraus theorem directly.

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
  in `QICLean/Analysis/TwoProjectionCompressionSpectrum.lean` (QICLean dependency).
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
  `QICLean/Analysis/IdempotentEndomorphism.lean` (QICLean dependency).
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
  `QICLean/Analysis/EntropyMarkovReverse.lean` (QICLean dependency).
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
  `QICLean/Channel/SingleKrausPositivity.lean` (QICLean dependency).
- **Notes:** both consumer modules now invoke the two matrix identities directly;
  the private helper copies were removed.

### finite-sum submatrix distribution — promoted
- **Pattern:** prove that taking a submatrix commutes with a finite sum by
  extensionality and entrywise simplification.
- **Seen:** duplicate 6-line helpers in `TNLean/MPS/RFP/BNTOrthogonality.lean`
  and `TNLean/MPS/RFP/PhysicalObservableRealization.lean` before promotion
  (2026-08-10).
- **Abstraction:** `Matrix.submatrix_sum` in `QICLean/Algebra/FinSum.lean` (QICLean dependency).
- **Notes:** the theorem is polymorphic over the entry additive commutative
  monoid. Its four motivating calls now share the neutral matrix identity.

### transfer-map irreducibility in Kraus-map notation — promoted
- **Pattern:** use the definitional equality of `Kraus.transferMap` and `Kraus.mapLM` to view
  `IsIrreducibleMap (MPSTensor.transferMap F)` as
  `IsIrreducibleMap (Kraus.mapLM F)` before applying generic peripheral
  theorems.
- **Seen:** the five transfer-map compatibility declarations in
  `TNLean/Channel/Peripheral/{ClosureFixedPoint,CyclicGroup}.lean` (2026-08-09).
- **Abstraction:** no conversion theorem is needed: `Kraus.transferMap` and
  `Kraus.mapLM` are definitionally equal.
- **Notes:** generic theorems use `Kraus.mapLM`; transfer-map hypotheses are
  passed directly to them without an equality rewrite or compatibility wrapper.

### Transfer-map spectral arguments in Kraus-map notation — promoted
- **Pattern:** prove eigenvector, fixed-point, and channel-power statements for
  `MPSTensor.transferMap` by repeating the same argument already available for
  `Kraus.mapLM`.
- **Seen:** eleven compatibility declarations in
  `TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducibleAux.lean` duplicated
  the channel argument in
  `TNLean/Kraus/Wielandt/Primitivity/VectorSpreadToPrimitive.lean` before
  promotion (2026-08-20).
- **Abstraction:** the reusable channel statements are public in
  `Kraus.Wielandt.Primitivity.VectorSpreadToPrimitive`; the established MPS
  declarations apply them directly by definitional equality.
- **Notes:** construction details for Hermitian parts remain private to the
  channel theorem. Only the compound MPS conclusion remains; exact pass-through declarations were removed.

### weighted word traces of a compression — promoted
- **Pattern:**
  ```lean
  have h := P.trace_evalWord_eq_sum w hw
  have hs : ∀ s, Matrix.trace (Kraus.evalWord (μ s • A s) w) =
      μ s ^ w.length * Matrix.trace (Kraus.evalWord (A s) w) := by
    intro s
    rw [show μ s • A s = fun i => μ s • A s i from rfl,
      Kraus.evalWord_smul, Matrix.trace_smul, smul_eq_mul]
  rw [h, show S = Finset.univ from rfl, Fin.sum_univ_two, hs 0, hs 1]
  ```
- **Seen:** at least ten occurrences of the `Kraus.evalWord_smul, Matrix.trace_smul,
  smul_eq_mul` step after `MultiBlockCompression.trace_evalWord_eq_sum` across the worked
  examples (2026-09-25), among them `Examples/RFP/TwistedDimer.lean`,
  `Examples/RFP/OneLabelCandidate.lean`, `Examples/Ising/IsingWeightedTwist.lean`,
  `Examples/MultiBlock/OneSlotGauge.lean` and `Examples/KramersWannier/KramersWannier.lean`.
- **Abstraction:** `MPSTensor.MultiBlockCompression.trace_evalWord_eq_sum_smul` in
  `TNLean/MPS/FundamentalTheorem/Reduction/MultiBlockTrace.lean`: a compression onto weighted
  blocks `μ_s • A_s` gives `tr(B^w) = ∑_s μ_s^{|w|} tr(A_s^w)`.
- **Notes:** the two RFP example sites now call it directly. The remaining example sites can
  switch when next edited; the one-block form `MPSTensor.trace_evalWord_smul` in
  `MPDO/OperatorProduct.lean` covers a single rescaled tensor.

### CFC square-root Hermiticity — promoted
- **Pattern:** derive `(CFC.sqrt ρ)ᴴ = CFC.sqrt ρ` from `CFC.sqrt_nonneg`,
  `Matrix.nonneg_iff_posSemidef`, and positive-semidefinite Hermiticity.
- **Seen:** six occurrences across `Channel/FixedPoint/Corollaries.lean`,
  `MaximalRank.lean`, and `WeightedCornerFixedPoints.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Matrix.conjTranspose_cfc_sqrt` in
  `QICLean/Analysis/MatrixSqrt.lean` (QICLean dependency).
- **Notes:** the helper needs no positivity hypothesis because `CFC.sqrt_nonneg`
  is unconditional. All six motivating proofs are now one-line applications;
  the caller files lose fifteen lines.

### positive-definite CFC square-root determinant unit — promoted
- **Pattern:** combine `CFC.isUnit_sqrt_iff`, `Matrix.PosDef.isUnit`, and
  `Matrix.isUnit_iff_isUnit_det` to prove `IsUnit (CFC.sqrt ρ).det`.
- **Seen:** four occurrences across `Channel/FixedPoint/Corollaries.lean` and
  `WeightedCornerFixedPoints.lean` before promotion (2026-08-09).
- **Abstraction:** `Matrix.PosDef.isUnit_det_cfc_sqrt` in
  `QICLean/Analysis/MatrixSqrt.lean` (QICLean dependency).
- **Notes:** the theorem retains the caller's `DecidableEq` instance so the
  determinant does not require proof-irrelevance transport. The four proof
  blocks become one-line applications.

### transfer-map trace-adjoint pairing — promoted
- **Pattern:** rewrite a linear map equality `E = transferMap K`, apply the
  finite-Kraus trace-adjoint identity, and unfold the adjoint transfer family.
- **Seen:** three occurrences across `Channel/Irreducible/FromSpectral.lean`,
  `PerronFrobenius.lean`, and `SpectralRadius.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Kraus.trace_mul_mapLM_adjoint` in
  `QICLean/Channel/KrausMap.lean` (QICLean dependency).
- **Notes:** transfer-map callers use this canonical finite-Kraus theorem directly,
  relying on the definitional equality of `Kraus.mapLM` and `Kraus.transferMap`.

### matrix-family irreducibility in transfer-map notation — promoted
- **Pattern:** convert between irreducibility of a finite matrix family and
  irreducibility of its MPS transfer map by passing through the definitionally equal `Kraus.mapLM`.
- **Seen:** nine forward conversions and three converse conversions across
  `MPS/Irreducible/FormII.lean`, `Spectral/TransferOperatorGap{NT,Injective}.lean`,
  and `Wielandt/Primitivity/{PrimitiveBridge,ToNormal}.lean` before promotion
  (2026-08-20).
- **Abstraction:**
  `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` and
  `Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM` in
  `QICLean/Kraus/InvariantProjection.lean` (QICLean dependency).
- **Notes:** QICLean owns the equivalence canonically in `mapLM` notation.
  Transfer-map callers use it directly by definitional equality, without an
  equality conversion or compatibility wrapper.

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
  `QICLean/Channel/Peripheral/Spectrum.lean` (QICLean dependency).
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
  `QICLean/Algebra/PosSemidefSupport.lean` (QICLean dependency).
- **Notes:** the lemma isolates the dependent proof transport that ordinary
  rewriting does not resolve directly.

### mpv_ext — promoted
- **Pattern:** `intro N σ` / `intro N hN σ` prelude for `SameMPV₂` /
  `SameMPV₂Pos` goals.
- **Abstraction:** `mpv_ext` (elab tactic, `TNLean/MPS/Tactic/Basic.lean`).
- **Notes:** elab rather than macro because it inspects the goal to
  distinguish the two predicate forms.

### rho-weighted matrix instance preamble — promoted
- **Pattern:** open a statement or a proof body with the three-line or
  four-line `letI` block activating the rho-weighted normed group, seminormed
  group, inner-product space, and (in the four-line form) norm instances on
  the virtual matrix algebra:

  ```lean
  letI : NormedAddCommGroup Mat := Matrix.toMatrixNormedAddCommGroup ρ hρ
  letI : SeminormedAddCommGroup Mat :=
    (Matrix.toMatrixNormedAddCommGroup ρ hρ).toSeminormedAddCommGroup
  letI : InnerProductSpace ℂ Mat := Matrix.toMatrixInnerProductSpace ρ hρ.posSemidef
  letI : Norm Mat := (Matrix.toMatrixNormedAddCommGroup ρ hρ).toNorm
  ```

- **Seen:** 122 blocks across eight modules before the refactor
  (`TNLean/MPS/ParentHamiltonian/`): `FNWOverlapCoordinates.lean` (28),
  `FNWLowerBoundary.lean` (23), `FNWOverlapEstimate.lean` (20),
  `FNWAggregateOrthogonality.lean` (16), `FNWProjectorDefect.lean` (13),
  `WeightedVirtualHilbert.lean` (12), `FNWTransferDecay.lean` (6), and
  `FNWBoundaryEstimate.lean` (4).
- **Abstraction:** the `weighted_matrix_instances` and
  `weighted_matrix_norm_instances` macros in
  `TNLean/MPS/ParentHamiltonian/WeightedVirtualHilbert.lean`. Each is declared
  twice, once in term position (`weighted_matrix_instances ρ hρ in` prefixing a
  statement) and once in tactic position, because the block is repeated in both
  the statement and the proof of nearly every weighted-norm theorem. The norm
  variant expands to the plain one followed by the norm binding, so the two
  stay in step.
- **Notes:** a macro rather than a lemma or a simp set, because activating a
  non-global instance is a binding, not a rewrite; the instances cannot be made
  global without changing every matrix norm in every importing file. The
  expansion is textual, and it ascribes the instance types with a placeholder
  matrix type, so the elaborated statements are unchanged from the hand-written
  blocks. All 122 blocks were refactored in the same change. Two shorter
  prefixes of the pattern remain hand-written where they occur: the single
  normed-group binding (22 sites) and the normed-group-plus-seminormed-group
  pair (8 sites, all in `FNWOverlapCoordinates.lean`).

### transfer_simp — promoted
- **Pattern:** unfolding `transferMap A X` to `∑ i, A i * X * (A i)ᴴ`.
- **Abstraction:** `@[mps_transfer]` simp set + `transfer_simp` macro
  (`TNLean/MPS/Tactic/Basic.lean`).

### generalize_decide — promoted
- **Pattern:** abstract finitely many finite-type values occurring inside a
  goal (`x 0`, `(s j).1.1`, `γ k`) into fresh variables, revert them, and
  close the closed bit identity by `decide`:

  ```lean
  generalize x 0 = x0
  generalize x 1 = x1
  generalize x 2 = x2
  generalize x 3 = x3
  revert x0 x1 x2 x3
  decide +revert
  ```

- **Seen:** fourteen occurrences across four files before promotion
  (2026-09-03): the phase-table rows and bar-flip exponent identities in
  `TNLean/MPS/MPDO/CZXGaussCircuitTuple.lean`, the involution, holonomy, fiber
  coordinate, and label lemmas in
  `TNLean/MPS/MPDO/CZXGaussInvariantSubspace.lean`, hypercube connectivity in
  `TNLean/Algebra/HypercubePhasePotential.lean`, and the characteristic-two
  identity in `TNLean/Algebra/MonomialFixedSubspace.lean`.
- **Mathlib replacement:** the characteristic-two identity in
  `MonomialFixedSubspace.lean` now uses `CharTwo.add_self_eq_zero` pointwise;
  finite-case automation is no longer needed at that call site.
- **Abstraction:** `generalize_decide t₁, …, tₙ` macro
  (`TNLean/Algebra/GeneralizeDecide.lean`); the terms are abstracted in order
  and `decide +revert` quantifies over the fresh variables.
- **Notes:** all call sites now use the macro. The macro is meant for goals
  whose only free data are values in small finite types with decidable
  equality (`ZMod 2`, `ZMod 4`); a goal that still depends on other free
  variables after abstraction fails with the usual `decide` message.

### finite-sum common-left-factor normalization — promoted
- **Pattern:** a finite sum differs from a factored form only by pulling one
  index-independent left factor through summands of the form `a * f i * g i`.
  The original proofs used `rw`, `simp_rw`, or `simp only` with
  `Finset.mul_sum`, a `Finset.sum_congr` binder (tactic, functional, or
  semicolon form), and `ring`.
- **Seen:** 25 current call sites across 20 files. The promotion pass
  recorded 37 sites across 27 files; of those, eight moved to QICLean with
  the quantum-channel extraction and two were deleted as dead weight, while
  three further files adopted the lemma afterwards. Current consumers:
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
  `TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean`,
  `TNLean/MPS/RFP/AppendixBTwoSiteBasicSupport.lean`,
  `TNLean/MPS/RFP/BellPairCIDObstruction.lean`,
  `TNLean/MPS/RFP/CPSVCIDNotRFPExample.lean`,
  `TNLean/MPS/RFP/StructuralFull.lean` and
  `TNLean/PEPS/TorusWindowChain4.lean`.
- **Abstraction:** `Fintype.sum_mul_mul_eq_mul_sum_mul` in
  `QICLean/Algebra/FinSum.lean` (QICLean dependency).
- **Result:** every call site uses the shared lemma, and all 20 current
  consumer files import `QICLean.Algebra.FinSum` directly. The promotion's
  broad final passes found 18 sites in 13 then-new files, including
  functional binders, one-line semicolon proofs,
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
  step, such as `TorusWindowChain4.lean`. The indicator expansion in
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
  `QICLean/Algebra/FinSum.lean` (QICLean dependency).
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
  in `QICLean/Algebra/FinSum.lean` (QICLean dependency).
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
  `CyclicActiveAdjacentCoefficientExtraction.lean` before promotion.
- **Abstraction:**
  `PhysicalSectorFactorization.reindex_reducedBlockState_add_eq_suffixSectorContraction`
  in `TNLean/MPS/MPDO/CyclicActiveFourthRegionContraction.lean`.
- **Notes:** the arbitrary suffix length is the mathematical parameter; the
  source-facing three-suffix theorem is a specialization.

### partial trace under product reindexing — promoted
- **Pattern:** split a simultaneous relabelling of both tensor factors into
  left- and right-factor submatrices, change the summation index in the traced
  factor, and compose the resulting submatrices.
- **Seen:** three occurrences across `PartialTrace.lean`,
  `RelativeEntropyDataProcessing.lean`, and `StrongSubadditivityPosDef.lean`
  before promotion.
- **Abstraction:** `Matrix.partialTraceRight_submatrix_prod_equiv` in
  `QICLean/Channel/PartialTrace.lean` (QICLean dependency).
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
  `QICLean/Analysis/Entropy.lean` (QICLean dependency).
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

### critical-scalar uniqueness for positive-definite fixed points — promoted
- **Pattern:** given two positive-definite fixed points $\rho$ and $\sigma$ of
  the same linear map, choose a critical scalar $c$, set
  $\tau=\sigma-c\rho$, and use the hypothesis that every nonzero
  positive-semidefinite fixed point is positive definite to force $\tau=0$.
- **Seen:** three occurrences in
  `TNLean/Channel/Irreducible/FixedPointUniqueness.lean`, theorem
  `posSemidef_fixedPoint_unique_of_irreducible_cp`, and
  `QICLean/Kraus/Wielandt/Primitivity/VectorSpreadToPrimitive.lean`, theorem
  `Kraus.posSemidef_pow_fixedPoint_unique`, and
  `TNLean/Wielandt/Primitivity/ImpliesStronglyIrreducibleAux.lean`, before direct reuse
  (2026-08-20).
- **Abstraction:**
  `exists_smul_eq_of_posDef_fixedPoints_of_fixedPoint_posDef`
  in `QICLean/Channel/Irreducible/FixedPointUniqueness.lean` (QICLean dependency).
- **Notes:** the shared theorem includes the load-bearing hypothesis that every
  nonzero positive-semidefinite fixed point is positive definite; without this
  hypothesis the proportionality statement is false for the identity map. The
  three callers establish it respectively from irreducibility or from
  fixed-length vector spreading.

### off-edge delta collapse to the consistent-off-`e` subtype — promoted
- **Pattern:** a sum over all open local configurations of a three-factor
  summand whose first factor is the product of the per-edge consistency deltas
  away from a distinguished edge, collapsed by `prod_off_delta_eq` into an
  `if … then … else 0`, then re-expressed as a sum over the subtype of
  configurations consistent off that edge via `Finset.sum_ite` followed by
  `Finset.sum_subtype_eq_sum_filter`.
- **Seen:** four occurrences across `PEPS/FundamentalTheorem/GaugeAction.lean`
  (`edgeInsertedCoeff_eq_sum_local`),
  `PEPS/FundamentalTheorem/EdgeInsertion.lean` (`open_gauge_sum_over_outer`),
  `PEPS/FundamentalTheorem/OneVertexComparison.lean`
  (`edgeInsertedCoeff_eq_doubled`), and `PEPS/RegionBlock/GaugeBridge.lean`
  (`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`) before promotion — four
  files, clearing the rule of three.
- **Abstraction:** `TNLean.PEPS.sum_off_delta_eq_sum_consistentOff` in
  `TNLean/PEPS/FundamentalTheorem/GaugeAction.lean`. The trailing factor is
  taken as an arbitrary function of the configuration, which is what lets the
  four callers pass their own per-vertex tensor product, gauge-matrix product,
  or region-assembled component product.
- **Notes:** the decidability of consistency off the edge is an explicit
  `DecidablePred` instance argument rather than an `open scoped Classical in`
  on the lemma; this is load-bearing, since each caller derives its own
  instance from a `classical` in its proof and those must unify with the
  lemma's. Each call site collapses a twenty-odd-line `calc` to a two- to
  five-line term. Net source delta over the four sites: −69 lines against +37
  for the lemma.

### bit-indexed Kraus support fibre sums — promoted
- **Pattern:** a Kraus operator supported on the indicator of a condition
  prescribing some bits of a bit-encoded physical index; a sum against it is
  rewritten into the indicator of the fibre condition by `ite_eq_left` /
  `ite_eq_right` under `Finset.sum_congr`, and the fibre sum is then collapsed
  to the single index (all bits prescribed) or to a sum over the free bits.
- **Seen:** four occurrences across two files (2026-09-02):
  `MPS/MPDO/TwistedDimerRefine.lean` (`refineKraus_col_sum`, `refineKraus_row_sum`) and
  `MPS/MPDO/TwistedDimerViaTS.lean` (`coarseKraus_row_sum`, `coarseKraus_res_term`).
- **Abstraction:** `MPOTensor.TwistedDimer.one_site_fiber_sum`,
  `left_fiber_sum`, `right_fiber_sum`, and `pair_fiber_sum` in
  `TNLean/MPS/MPDO/TwistedDimerRefine.lean`, all stated for an arbitrary
  summand so that each caller supplies its own Kraus amplitude and contracted
  vector.
- **Notes:** the pair version is proved from the two one-index versions rather
  than by expanding sixty-four terms, which keeps its proof independent of the
  prescribed bits. The one-index versions are proved by transporting the sum
  along the bit encoding (`sum_fin_eight`) and deciding the eight resulting
  cases.

---

### twisted-dimer bit-encoding destructuring — promoted
- **Pattern:** rewriting an index of the eight-valued physical or bond
  alphabet of the twisted dimer as its bit encoding before case analysis:
  ```lean
  obtain ⟨p, p', k, rfl⟩ : ∃ p p' k, a = physIdx p p' k := ⟨_, _, _, (physIdx_bits a).symm⟩
  ```
- **Seen:** 4 occurrences across 2 files before promotion
  (`TNLean/MPS/MPDO/TwistedDimerFlagSectors.lean`,
  `TNLean/MPS/MPDO/TwistedDimerHorizontalCF.lean`).
- **Abstraction:** `MPOTensor.TwistedDimer.exists_eq_physIdx`
  (`TNLean/MPS/MPDO/TwistedDimer.lean`); call sites read
  `obtain ⟨p, p', k, rfl⟩ := exists_eq_physIdx a`.
- **Notes:** the inline existential statement and its witness are removed at
  every call site; one line each.

### ground-space invariance under nonzero tensor rescaling — promoted
- **Pattern:** identify the local MPS spaces of `ζ • A` and `A` for `ζ ≠ 0`
  by rewriting `groundSpaceMap (ζ • A) L X` as
  `groundSpaceMap A L ((ζ ^ L) • X)`, then use multiplication by
  `ζ ^ L` and its inverse for the two range inclusions.
- **Seen:** three occurrences before promotion (2026-09-04): the private
  `groundSpace_smul_eq` in
  `TNLean/MPS/ParentHamiltonian/CoisometricReconstruction.lean`, the private
  `groundSpace_smul_eq_of_ne_zero` in
  `TNLean/MPS/ParentHamiltonian/CPSVOriginalRange.lean` (both 2026-08-31), and
  the normalized primitive gauge of a normal tensor in
  `TNLean/MPS/ParentHamiltonian/PrimitiveGaugeExistence.lean`.
- **Abstraction:** `MPSTensor.groundSpace_smul_eq` in
  `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`, placed beside
  `MPSTensor.GaugeEquiv.groundSpace_eq` so that the scalar and the gauge half
  of the normalization are available together.
- **Notes:** both private copies are deleted and their call sites now pass the
  nonzero scalar to the public theorem; the third consumer chains it with the
  gauge half to identify the local MPS spaces of a tensor and of its
  normalized representative.

### bond-space product and action of tensors over a ring — promoted
- **Pattern:** an example defines the bond-space product of two matrix product
  operator tensors over an exact ring,
  `(M · N)^{ik} = ∑_j M^{ij} ⊗ N^{jk}` in the bond order of `finProdFinEquiv`,
  or the bond-space action `(M · A)^i = ∑_j M^{ij} ⊗ A^j`, and then reproves
  that it commutes with the entrywise image of the ring in the complex numbers,
  so that a stacked product tensor over the complexes reduces to a decidable
  identity between matrices over that ring.
- **Seen:** first three occurrences over the integers (2026-09-17): a public
  copy in `TNLean/MPS/Examples/CZX/CZXTensor.lean`, a
  private copy in
  `TNLean/MPS/Examples/KramersWannier/KramersWannier.lean`, and a
  third needed by the renormalization fixed points of
  `TNLean/MPS/Examples/MultiBlock/StackedPairGauge.lean`; then
  one copy per example ring, over the integers, over `ℤ√2`, over `ℤ[σ]` and over
  `ℤ[ω]`, each with its own product, action and compatibility lemma.
- **Abstraction:** `MPSTensor.mulTensorR` and `MPSTensor.actTensorR` over an
  arbitrary commutative ring, with `MPSTensor.mulTensor_complexOfRing`, its
  rescaled form `MPSTensor.mulTensor_smul_complexOfRing` and
  `MPSTensor.actTensor_complexOfRing`, in
  `TNLean/MPS/FundamentalTheorem/Reduction/RingEmbedding.lean`, beside
  the entrywise image `MPSTensor.complexOfRing` of
  `TNLean/Algebra/ComplexOfRing.lean` that they belong to.
- **Notes:** the rescaled form is what the P6 fixed points need, since their
  tensors are integer matrices divided by a common denominator; the unscaled
  form is the instance at one. Each ring keeps only a one-line abbreviation of
  the general product or action, and the compatibility lemmas are used in their
  general form, since their left sides are headed by the complex product and
  action rather than by the entrywise image. A new example ring therefore
  contributes its ring homomorphism, two abbreviations and the one-line
  instantiations of the arithmetic lemmas its proofs rewrite with.

### exact-ring layer: word evaluation, gauge inverses and matrix-unit certificates — promoted
- **Pattern:** each example ring re-proved the entrywise `Matrix.map` ladder
  (`_mul`, `_one`, `_zero`, `_sub`, `_transpose`, `_injective`,
  `_blockDiagonal'`), defined its own word evaluation with its own
  compatibility lemma, turned a decided `G * H = 1` into the complex identity by
  `rw [← complexOfR_mul, h, complexOfR_one]`, and repeated the span argument
  that makes a tensor normal from a decided table of scaled matrix units.
- **Seen:** the golden and Eisenstein rings (`Examples/Rings/GoldenRing.lean`,
  `Examples/Rings/EisensteinRing.lean`), the golden action tensor of
  `Examples/Rings/GoldenCompression.lean`, the two normality certificates of
  `GoldenCompression.lean` and `EisensteinCertificates.lean`, and about thirty
  gauge-inverse rewrites across the CZX, Ising, multi-block, Fibonacci and
  `ℤ[ω]` examples.
- **Abstraction:** `MPSTensor.complexOfRing_sub`, `_transpose`,
  `_blockDiagonal'`, `_injective`, `_ne_zero` and
  `MPSTensor.complexOfRing_mul_eq_one` in
  `TNLean/Algebra/ComplexOfRing.lean`; `MPSTensor.evalWordR` with
  `MPSTensor.evalWord_complexOfRing`, and the certificates
  `MPSTensor.isNBlkInjective_of_complexOfRing_smul_single` and
  `MPSTensor.isNormal_of_complexOfRing_smul_single`, in
  `TNLean/MPS/FundamentalTheorem/Reduction/RingEmbedding.lean`.
- **Notes:** `complexOfGolden` and `complexOfEisenstein` are now same-name
  `abbrev`s of `complexOfRing`, and `evalWordGolden` and `mulGoldenTensor` of
  `evalWordR` and `mulTensorR`, so their blueprint tags and statements stay;
  the ring-specific lemmas the proofs rewrite with are one-line instances. A
  term such as `complexOfRing_mul_eq_one _ hG` elaborates against a goal
  stated with the abbreviation, because the abbreviation unfolds reducibly;
  a forward `rw` with a general lemma does not match the abbreviated head, so
  rewriting keeps the ring-specific names. Kernel `decide` costs are unchanged,
  since the general definitions have the same recursion as the ones they
  replace.

### golden compression datum from a decided gauge — promoted
- **Pattern:** an example over `ℤ[σ]` records the letters of the source and of
  the targets, a change of bond coordinates and its inverse, and the conjugated
  letters as explicit matrices, decides `G G⁻¹ = 1`, `B^i G⁻¹ = G⁻¹ K^i` and the
  block structure of every `K^i`, and then assembles the multi-block
  compression datum by transporting each decided identity along
  `complexOfGolden` in the three structure fields, and separately reproves that
  the remainder vanishes from the block diagonality of the `K^i`.
- **Seen:** seven occurrences (2026-09-17): the `τ ⊗ τ` datum of
  `TNLean/MPS/Examples/Fibonacci/Fibonacci.lean`, the three
  unit laws of `Examples/Fibonacci/FibonacciUnit.lean`, and the three action tensors of
  `Examples/Fibonacci/FibonacciAction.lean`.
- **Abstraction:** `MPSTensor.MultiBlockCompression.ofGolden` in
  `TNLean/MPS/Examples/Rings/GoldenCompression.lean`, since 2026-09-25 an
  instance of the ring-generic `MPSTensor.MultiBlockCompression.ofRing` of
  `TNLean/MPS/FundamentalTheorem/Reduction/ExplicitGauge.lean` (see the entry
  on the ring-generic compression datum), with `MPSTensor.unitOrd` and
  `MPSTensor.unitCoord` for the block ordering and bond coordinates of a datum
  with one target placed before the zero slots.
- **Notes:** each example now supplies only its matrices and four decided
  identities; the matched clause is stated with the target indices quantified
  before the letter (`revert i; revert p q; decide +kernel`), since with the
  letter first the instance search for the decidability of the clause fails on
  the first-order unification of the target family against a matrix. The
  triangular clause is read off the off-diagonal one by
  `MultiBlockCompression.triangular_of_offDiag`, and the remainder by
  `MultiBlockCompression.remainder_ofRing` after unfolding the datum.

### ring-generic compression datum — promoted
- **Pattern:** a worked example of the multi-block compression theorem
  hand-builds `MultiBlockCompression` field by field: a gauge, its conjugation
  lemma, and the triangular, matched and unmatched clauses each transported
  from a decided identity over `ℤ`, `ℤ√2`, `ℤ[σ]` or `ℤ[ω]` along the entrywise
  embedding; the remainder is then reproved from block diagonality or by
  expanding the single-slot sum `Finset.sum_eq_single_of_mem`.
- **Seen:** `ofGolden`, `ofEisenstein`, `ofConjMatrix`, `ofScalarFlagFour`,
  the Kramers–Wannier data `kwSquare_compression`, `plusCompression`,
  `kwGHZCompression`, `czxPlusIdentity_compression`, the Ising data
  `isingCompression` and `sectorCompression`, the seven Fibonacci data,
  `parityGraded_compression` and `czxSquare_compression` (2026-09-25).
- **Abstraction:** `MPSTensor.MultiBlockCompression.ofRing` (any gauge whose
  conjugation of every letter is the image of a matrix `K i` over `R`,
  relabelled along `τ`; a scaled gauge such as the Kramers–Wannier `G/2`
  enters through its own conjugation lemma), `ofRingBlockDiagonal` (the
  conjugated letters are the image of one block-diagonal matrix),
  `remainder_ofRing`, `remainder_ofRingBlockDiagonal`,
  `remainder_eq_zero_of_offDiag`, `remainder_oneSlot`, `triangular_of_offDiag`,
  `MPSTensor.gaugeOfRingMatrix` and `MPSTensor.conjMatrix_gaugeOfRingMatrix` in
  `TNLean/MPS/FundamentalTheorem/Reduction/ExplicitGauge.lean`, together with
  the single-slot set `MPSTensor.oneSlot`.
- **Notes:** `remainder_ofRing` takes the proof arguments of the datum
  implicitly; elaborating it against a named datum leaves them unassigned
  (proof irrelevance closes the unification without assigning them), so unfold
  the named datum first. `ParityGraded.parityGraded_compression` and
  `CZXCompression.czxSquare_compression` are migrated too, and the `ℤ₃` fusion
  examples and `CZXSquare` use `MPSTensor.oneSlot`/`MPSTensor.oneSlotMem` for
  their single slot.

### normality from a golden matrix-unit table — promoted
- **Pattern:** a tensor over `ℤ[σ]` is shown normal by deciding, for every
  matrix unit, a combination of words of one positive length with coefficients
  in `ℤ[σ]`, transporting the identity along `complexOfGolden`, and closing the
  span argument by `Matrix.matrix_eq_sum_single`.
- **Seen:** four occurrences (2026-09-17): the two blocks of
  `TNLean/MPS/Examples/Fibonacci/Fibonacci.lean` and the two
  normal states of `Examples/Fibonacci/FibonacciAction.lean`.
- **Abstraction:** `MPSTensor.isNormal_of_complexOfRing_single` in
  `TNLean/MPS/FundamentalTheorem/Reduction/RingEmbedding.lean`, the unscaled
  instance of `MPSTensor.isNormal_of_complexOfRing_smul_single`, applied along
  `goldenToComplex` (the golden-specific wrapper was removed on 2026-09-25).
  The single-letter certificates `P6Compression.isNormal_of_single_eq_smul`
  and `MPSTensor.isNormal_of_single_eq_smul_zsqrt2` are instances of
  `MPSTensor.isNormal_of_complexOfRing_letter_eq_smul_single`, which keeps the
  complex prefactor.
- **Notes:** the words are given as functions `Fin ℓ → Fin d` so that the
  length is fixed by the type; the two former proofs of the Fibonacci blocks
  became one-line applications, for a net loss of about forty lines.
### stacked-letter lookup-table identification by kernel decision — promoted
- **Pattern:** identify the pair-alphabet stacked-letter function of two
  integer tensors, `stackedInt A B`, with an explicit sixteen-entry lookup
  table `C`, for a private `Fin 16`-indexed theorem `stackedInt A B b = C b`,
  by reverting the index and deciding the resulting closed proposition by
  kernel reduction:

  ```lean
  revert b
  decide +kernel
  ```

- **Seen:** sixteen occurrences across two files (2026-09-17): `xX_int`,
  `xXy_int`, `xyX_int`, `xyXy_int` in
  `TNLean/MPS/Examples/AnomalousCondensation/AnomalousCondensationZ2Z2NonSplit.lean`,
  and `eE_int`, `eY_int`, `eX_int`, `eXy_int`, `yE_int`, `yY_int`, `yX_int`,
  `yXy_int`, `xE_int`, `xyE_int`, `xY_int`, `xyY_int` in
  `TNLean/MPS/Examples/AnomalousCondensation/AnomalousCondensationZ2Z2Split.lean`.
  Each theorem differs only in its statement, never in its proof.
- **Abstraction:** the `revert_decide_kernel x₁, …, xₙ` tactic macro, in
  `TNLean/Algebra/GeneralizeDecide.lean` beside the sibling `generalize_decide`
  macro it is modeled on.
- **Notes:** all sixteen call sites now read `revert_decide_kernel b`. The
  macro is deliberately narrower than `generalize_decide`: it reverts a
  named local hypothesis already in context (a bound table index) rather
  than generalizing a term occurring inside the goal, and it decides with
  the kernel evaluator, needed here because plain `decide` elaboration is
  slow on the sixteen-entry tables.

### no sitewise intertwiner from a certificate over an exact ring — promoted
- **Pattern:** show that `X = 0` whenever `B i * X = X * C i` for all letters
  (or `Y * B i = C i * Y`, or the bond-one vector forms `B i *ᵥ v = C i 0 0 • v`
  and `u ᵥ* B i = C i 0 0 • u`) by expanding the entrywise equations and
  eliminating the unknowns by hand:

  ```lean
  have h₀ := congrFun (congrFun (hX 0) p) q
  have h₁ := congrFun (congrFun (hX 1) p) q
  simp [Matrix.mul_apply, Fin.sum_univ_succ, ...] at h₀ h₁ ...
  linear_combination ... * h₀ + ... * h₁ + ...
  ```

- **Seen:** six hand-written eliminations across three files before promotion
  (2026-09-25, #8092): `ParityGraded.parNeg_right_intertwiner_eq_zero` and
  `parNeg_left_intertwiner_eq_zero` in
  `TNLean/MPS/Examples/MultiBlock/ParityGraded.lean` (about 110 lines),
  `MPSTensor.ghzC0_right_intertwiner_eq_zero` and
  `ghzC0_left_intertwiner_eq_zero` in
  `TNLean/MPS/Examples/MultiBlock/GHZSectors.lean`, and
  `CZXCompression.czxSquare_right_intertwiner_eq_zero` and
  `czxSquare_left_intertwiner_eq_zero` in
  `TNLean/MPS/Examples/CZX/CZXSquare.lean`.
- **Abstraction:** `MPSTensor.right_intertwiner_eq_zero_of_ringCertificate`,
  `MPSTensor.left_intertwiner_eq_zero_of_ringCertificate`,
  `MPSTensor.mulVec_eq_zero_of_ringCertificate` and
  `MPSTensor.vecMul_eq_zero_of_ringCertificate` in
  `TNLean/MPS/FundamentalTheorem/Reduction/AssemblyLemmas.lean`, wrapping
  `right_intertwiner_eq_zero_of_certificate` and
  `left_intertwiner_eq_zero_of_certificate`.
- **Notes:** the letters are given as images `complexOfRing f (BR i)` of
  matrices over a ring `R` with `f : R →+* ℂ` (usually `Int.castRingHom ℂ`),
  and the certificate is a matrix `N` over `R` with
  `N * (sitewiseEqMatrix BR CR).submatrix rows id = c • 1` and `f c ≠ 0`, where
  `rows` selects a full-rank set of the sitewise equations; the identity `hN`
  is closed by `decide` over `R`. The right forms
  (`right_intertwiner_eq_zero_of_ringCertificate`,
  `mulVec_eq_zero_of_ringCertificate`) take a certificate of
  `sitewiseEqMatrix BR CR`; the left forms
  (`left_intertwiner_eq_zero_of_ringCertificate`,
  `vecMul_eq_zero_of_ringCertificate`) take one of the transposed letters.
  Compute `N` offline by exact rational
  inversion of the selected equations and clear denominators into `c`. All six
  call sites use the wrappers; the helper evaluation lemmas they needed were
  deleted.

### Ising fusion rule from a signed-permutation gauge — promoted
- **Pattern:** a fusion rule `O_L(X) O_L(Y) = O_L(T)` of the Ising
  fusion-tree tensors, proved by applying
  `MPSTensor.mpo_mul_eq_of_zsqrt2_conj` to an orthogonal gauge `G` over `ℤ√2`,
  reducing the letter identity to the sectors of the middle label with
  `isingConj_of_rho_eq`, and expanding the stacked letters as short sums with
  `mul_mulTensorR_mul_transpose_eq_list`.
- **Seen:** eight copies of this proof body across three files before
  promotion (2026-09-25, #8092): four in
  `TNLean/MPS/Examples/Ising/IsingFusionAlgebraOnePsi.lean`, two in
  `IsingFusionAlgebraOneSigma.lean`, two in `IsingFusionAlgebraPsiSigma.lean`.
- **Abstraction:** `IsingTwist.isingFusion_of_signedPerm` in
  `TNLean/MPS/Examples/Ising/IsingFusionAlgebra.lean`.
- **Notes:** the caller supplies the scaled-matrix-unit form of each letter
  (`*_eq_smul_single`), a duplicate-free list `next h` containing every right
  label `h'` at which the first factor's coefficient `a h h'` may be nonzero
  (any such superset of the support works; labels outside it must have
  `a h h' = 0`), the vanishing of the letters across the middle
  label, the gauge `G` with `G * Gᵀ = 1` and `Gᵀ * G = 1`, and the sector
  identity `hdiag`; the last three are `decide +kernel` checks over `ℤ√2`.
  The lemma is specific to the ten fusion-tree labels of the Ising category;
  a fusion rule of other tensors related by a bond similarity uses
  `mpo_mul_eq_of_zsqrt2_conj` directly.

### normality from a table of two-letter words — promoted
- **Pattern:** prove `IsNormal A` for a small complex tensor by showing that
  every matrix unit `E_ij` is a combination of two words of length two, via a
  chain of private product lemmas `A i * A j = ...` and matrix-unit
  identities, and then concluding with a span argument.
- **Seen:** four call sites across two directories (2026-09-25):
  `CZXDecoratedTensor.lean`, `CZXReviewTensor.lean` and `CZXTensor.lean` in
  `TNLean/MPS/Examples/CZX/`, and `ParityGraded.parA_isNormal` in
  `TNLean/MPS/Examples/MultiBlock/ParityGraded.lean` (which dropped eight
  private product and matrix-unit lemmas in #8092).
- **Abstraction:** `MPSTensor.isNormal_of_single_eq_two_words` in
  `TNLean/MPS/Core/NormalityFromTwoWords.lean`.
- **Notes:** the caller supplies, for each pair `(i, j)`, letters `a, b, c, e`
  and scalars `u, v` with
  `Matrix.single i j 1 = u • (A a * A b) + v • (A c * A e)`, typically by
  `fin_cases` on `(i, j)` or through one table decided over the integers and
  transported by `complexOfRing`. When more words or another length are
  needed, use `MPSTensor.isNormal_of_complexOfRing_single` instead.

### inner product of combinations of orthogonal sequences — promoted
- **Pattern:**
  ```lean
  rw [sum_star_sum_mul_sum (fun j τ => a j * F j τ) (fun j τ => b j * G j τ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j]
  · calc _ = star (a j) * b j * ∑ τ, star (F j τ) * G j τ := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun τ _ => by rw [star_mul']; ring
      _ = _ := ...
  ```
- **Seen:** eight occurrences across two files (2026-09-26): six in
  `TNLean/MPS/Preparation/OrthogonalBlockError.lean` (the norm, target-norm and
  overlap sums of `norm_nonNormalApproxOverlap_blockSum`, diagonal and cross terms)
  and two in `TNLean/MPS/Preparation/DiagonalPolar.lean`.
- **Abstraction:** `MPSTensor.sum_star_mul_mul_mul`, `MPSTensor.sum_star_mul_mul`
  (scalars out of `∑_τ conj(a F τ) (b G τ)`), and
  `MPSTensor.sum_star_sum_mul_sum_of_orthogonal` (the whole inner product
  `∑ⱼ conj(aⱼ) bⱼ cⱼ` from `⟨Fⱼ, Gⱼ'⟩ = δⱼⱼ' cⱼ`) in
  `TNLean/MPS/Preparation/DiagonalPolar.lean`.
- **Notes:** all eight call sites are refactored; the three sums of
  `norm_nonNormalApproxOverlap_blockSum` each became two lines. That lemma and
  `OrthogonalBlockError.lean` were later deleted, when the orthogonal-block bound
  became a corollary of the repeated-overlapping bound.

## Completed refactors

### Literal one- and two-bond assignment specialization — resolved (2026-10-02)

- **Pattern:** specialize the literal-to-tree-cycle assignment identity at
  `false` and `true`, normalize the Boolean conditions, and rewrite both
  actual contractions with the resulting assignments.
- **Seen:** the local and global consumers in
  `PEPS/TorusTranslatedFluxMove.lean`,
  `PEPS/TorusTwoPlaquettePhysicalFluxMove.lean`, and
  `PEPS/TorusTwoPlaquetteGlobalFluxMove.lean`; four occurrences in the
  124-file PEPS scan at window three, count three.
- **Reuse:** the existing literal-to-tree-cycle assignment theorems contain
  the common mathematical identity. All four consumers now normalize both
  specialized equalities in one `simp only` step, then rewrite the actual
  contractions with those equalities. Public statements are unchanged.
- **Notes:** simplification stays on the assignment equalities: simplifying
  the entire dependent contraction exceeds the default heartbeat allowance.
  A new helper wrapping Boolean simplification would not add a mathematical
  assertion. The repeated two-step normalization block is removed.

### Weighted projector calculations with constant-weight recovery — resolved (2026-10-03)

- **Pattern:** Expand the actual regional projector into independent vertex
  translations and solve the compatibility equations in spanning-tree
  coordinates, retaining a scalar weight on the incident labels.
- **Seen:** The original and weighted formulas in
  `PEPS/RegularProjectorTwistedRegion.lean` and
  `PEPS/RegularTwistedRegionProjectorCoordinates.lean`.
- **Reuse:** `regularProjectorWeightedTwistedRegionMatrix_apply` and
  `_coordinates` prove the general weighted identities once. Both former
  unweighted formulas follow by setting the weight to one. The reconstructed
  incident labels are the public `regularRegionTreeReferenceLabels`.
- **Notes:** The generalized calculation replaces the existing calculation;
  its long proof is not copied. There is no remaining repeated weighted
  compatibility argument requiring a candidate or a tactic. Literal scalar
  weights are retained; diagonal insertions are not inferred from a span of
  group-representation matrices.

### Appending a tuple endpoint under `List.ofFn`
- **Pattern:** four proofs expanded `List.ofFn (Fin.snoc f x)` by repeating the
  same `List.ofFn_succ'`, `Fin.snoc_castSucc`, and `Fin.snoc_last` calculation.
- **Reuse:** `List.ofFn_snoc` in `TNLean/Algebra/ListOfFn.lean` owns the generic
  list identity.
- **Result:** the parent-Hamiltonian word lemmas and FNW boundary estimate import
  the layer-0 result, while `MPOTensor.evalWord_ofFn_cons_snoc` uses it for both
  endpoint words. Across Lean sources the refactor adds 31 lines and removes 21,
  for a net increase of 10 lines.

### Successor under one-step finite rotation
- **Pattern:** both closed-chain MPO calculations proved that `finRotate (N + 1)`
  sends `i.castSucc`, for `i : Fin N`, to `i.succ` by the same cast-heavy
  specialization of `finRotate_of_lt`.
- **Reuse:** `Fin.finRotate_succ_castSucc` in
  `TNLean/Algebra/FinCyclicInduction.lean` is the shared finite-index lemma.
- **Result:** the public example-specific lemma and the duplicated local proof
  are removed; both closed-chain calculations use the algebra lemma.

### Full support across tensor-equality casts
- **Pattern:** `PhysicalAncilla.lean` and `TensorProductCanonicalForm.lean` each
  carried the same local proof that casting canonical-form-II witness data along
  an equality of ambient tensors preserves the retained-dimension sum.
- **Reuse:** `CPSVCanonicalFormIIData.hasFullSupport_cast` in
  `TNLean/MPS/MPU/CanonicalForm.lean` is the single canonical-form
  infrastructure lemma used by both constructions.
- **Result:** both five-line local proofs are removed, and each caller states
  only its operation-specific tensor equality and full-support witness.

### Continuous-linear-map extensionality via Mathlib
- **Pattern:** nine call sites used `ContinuousLinearMap.coe_injective`,
  `DFunLike.ext`, and `intro` to prove equality of continuous linear maps.
- **Refactor:** use Mathlib's `ContinuousLinearMap.ext`, followed by `intro`.
- **Scope:** one site in `C3CorrectionBounds.lean`, one in
  `Martingale/SpectatorTransport.lean`, and seven in
  `SpectatorBoundaryGram.lean`.
- **Result:** the scanner no longer reports this pattern; no project-specific
  tactic was introduced.

### Nonempty products in generated subsemigroups
- **Pattern:** induct over subsemigroup closure to express each element as a
  nonempty list product of generators.
- **Reuse:** `Subsemigroup.exists_nonempty_list_prod_of_mem_closure` in
  `TNLean/Algebra/ListProduct.lean` replaces the three local proofs in the MPU
  residual algebra, MPU three-form span, and MPS reduction-residual modules.

### Four-site composition sum normalization
- **Pattern:** expand a four-site product cut into eight finite indices, permute
  those indices once, and compare only the resulting scalar summands modulo
  associativity and commutativity of multiplication.
- **Reuse:** the private `sum_eight_cut_factorization` lemma in
  `TNLean/MPS/MPU/CompositionRanks.lean` performs the distributivity step on
  abstract scalar functions.  Its proof descends through all eight sums by
  explicit congruences and closes the scalar identity with `ac_rfl`; the
  concrete source-cut composition proof now instantiates this lemma without
  constructing a distributed matrix-entry expression.
- **Performance:** the cached target build before the refactor reported 25 s.
  Profiler-reported cumulative module-elaboration totals fell from 16,129,355
  heartbeats before the refactor to 13,899,455 after it, a 13.8% reduction.
  These are module-level cumulative measurements, not per-proof costs.
  Post-refactor local wall runs reported 72--89 s while unrelated checkouts were
  rebuilding dependencies and saturating the host, so they are not comparable;
  the heartbeat reduction projects the uncontended target below 22 s, with the
  isolated PR check serving as the authoritative verification of the 25 s limit.

### Block entropy from real characteristic roots
- **Pattern:** derive a block entropy from a known real multiset of characteristic roots.
- **Reuse:** `MPOTensor.blockEntropy_of_charpoly_roots_eq` in
  `TNLean/MPS/MPDO/AreaLaw.lean` owns the shared entropy argument.
- **Result:** both CPSV16 Example 4.10 and 4.11 entropy modules reuse the theorem instead of
  duplicating private wrappers around the matrix entropy API.

### Reversing `List.ofFn` by `Fin.rev`
- **Seen:** five former proofs in `Kraus.Blocking`, `Kraus.Wielandt.RankOne.Construction`,
  `Kraus.Wielandt.RectangularSpan.Basic`, `MPS.MPDO.Defs`, and the MPU
  reflected-kernel module deleted on 2026-09-04.
- **Abstraction:** `List.ofFn_reverse` in `QICLean/Kraus/Word.lean` (QICLean dependency).
- **Result:** the four surviving consumers use the shared theorem directly.

### Finite Kraus setup for channels
- **Seen:** 2 occurrences in `Channel/Peripheral/IrreducibleChannel.lean` and
  `Channel/Semigroup/Primitivity/Helpers.lean` before promotion (issue #6576).
- **Abstraction:** `IsChannel.exists_kraus_map_eq_and_normalized` in
  `QICLean/Channel/KrausMap.lean` (QICLean dependency) packages a finite Kraus family, the equality with
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
  `QICLean/MPS/Core/Injectivity.lean` (QICLean dependency) supplies the literal span equality.
- **Call sites:** the odd- and even-length Majumdar-Ghosh obstructions and the
  diagonal-restriction non-normality counterexample.

### Euclidean linear-map multiplicativity
- **Pattern:** prove that `Matrix.toEuclideanLin (A * B)` is the composition of the
  Euclidean linear maps represented by `A` and `B` by expanding both sides through
  `Matrix.toLin_mul` in the standard orthonormal basis.
- **Reuse:** `Matrix.toEuclideanLin_mul` in `QICLean/Analysis/TraceNormAbs.lean` (QICLean dependency) is the shared
  layer-0 statement.
- **Result:** `QICLean/Analysis/MatrixReducedProjection.lean` uses the shared theorem directly,
  and `PositiveOnAbelian.Internal.toEuclideanLin_mul` remains as a compatibility wrapper for
  its three existing QICLean Channel call sites. The two-copy candidate was promoted early as required
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
- **Result:** the call sites in `TNLean/MPS/MPDO/VerticalCopyBlocks.lean` and
  `TNLean/MPS/MPDO/VerticalProductRetainedBlocks.lean` now invoke the shared owner
  directly; the private forwarders that formerly stood between them and it have been
  removed.
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
  `TNLean/MPS/Core/TracePairing.lean` accepts the pointwise vanishing trace pairings directly.
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
- **Further evidence (2026-08-27):** four more copies of the same matrix-entry
  congruence — `cyclicActiveLeftBoundary_entry_eq_of_heq` and
  `cyclicActiveRightBoundary_entry_eq_of_heq` in `CyclicActiveCutRegrouping.lean`,
  `rightTensor_eq_of_heq` and `leftTensor_eq_of_heq` in
  `CyclicActiveFourthRegionContraction.lean` — were replaced by the single
  index-family lemma `Matrix.entry_eq_of_heq` in
  `TNLean/MPS/MPDO/PhysicalSectorFactorization.lean`. The family goes in as an
  explicit lambda, so the per-boundary weight or virtual-index argument is
  captured rather than threaded through the lemma signature.
  `neighboringOperator_entry_eq_of_heq` stays: its conclusion is indexed by a
  sector pair, not a single index family.
- **Upstream reuse (2026-10-05):** the unchanged generic `Matrix.entry_eq_of_heq`
  now belongs to `QICLean/Algebra/MatrixDependentEntries.lean`. The original MPDO
  module imports it, preserving the same name and binders for every existing consumer.
  Actual varying-bond interval identification uses the same coordinate transport.

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
- **Update (2026-09-19):** the representation step is no longer proved from matrix
  units. `Matrix.exists_trace_representation` is now the inverse of the linear equivalence with the
  dual space induced by the nondegenerate trace form
  (`Matrix.traceBilinForm`, `Matrix.traceBilinForm_nondegenerate`, and Mathlib's
  `LinearMap.BilinForm.toDual`), and the pi- and pair-indexed corollaries are
  three-line consequences of it. The separation step itself still runs by hand,
  because no nondegeneracy statement exists yet for the pi-indexed or product trace
  form; once one does, `Matrix.family_submodule_eq_top_of_trace_separating` and
  `pair_matrix_span_top_of_pair_trace_separating` become one-line consequences.
- **Update (2026-10-02):** the ordinary representation, finite-family
  representation, and family span criterion are public in
  `MPS/SharedInfra/MatrixFamilyTracePairing.lean`. The MPDO criteria and
  the prescribed-length converse for the joint parent boundary map reuse
  these proofs. No parallel product bilinear form is needed.
- **Candidate (2026-09-19):** "a trace pairing that vanishes on a generating set
  vanishes on its span" now appears twice as `Submodule.span_le` into the kernel of
  the trace functional: `pair_trace_zero_on_span` in
  `TNLean/MPS/MPDO/BiCFDerivation/Core.lean` and
  `block_matrices_eq_zero_of_wordTupleSpanTop_trace` in
  `TNLean/MPS/SharedInfra/WordTupleGauge.lean`. A third occurrence should be
  abstracted into a single lemma over an indexed family of trace forms.

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
- **Result:** the exact call sites are the shared public lemma
  `MPOTensor.reindex_sitewisePhysicalMatrix_windowComplement` in
  `PhysicalSectorProductTransport.lean`, used from both that file and
  `PhysicalSupportProductTransport.lean`, and
  `embed_twoSiteSectorProjection_eq_finKronecker` in
  `PhysicalSupportProductTransport.lean`. Across the four changed Lean files, including
  the generated ParentHamiltonian aggregator, the final diff is 90 insertions and 87
  deletions, a net increase of 3 lines.

### Product-marginal support kernel
- **Pattern:** the simultaneous marginal-support whitening proof and the
  mutual-information estimate both need the support inclusion
  $\ker(\rho_A\otimes\rho_B)\subseteq\ker\rho_{AB}$ for a positive
  semidefinite bipartite operator.
- **Reuse:** `Matrix.PosSemidef.productMarginals_kernel_le` in
  `QICLean/Channel/MarginalSupportAbsorption.lean` (QICLean dependency) records this support-kernel
  fact once, using the two marginal support absorptions.
- **Result:** `MarginalSupportWhitenedChoi` and the new entropy theorem
  `Entropy.mutualInformation_le_log_operatorSchmidtRank` both use the shared
  semantic support statement instead of repeating support-projector algebra.
  The source-facing theorem `Matrix.product_marginal_support` used in the
  strong-subadditivity argument is a direct corollary of the same statement.

### Support-correct tensor logarithm
- **Pattern:** `QICLean/Channel/Schwarz/SSAEqualityDPI.lean` carried a local
  simultaneous-diagonalization proof of the support-correct tensor logarithm.
- **Reuse:** `Matrix.log_kronecker_posSemidef` in
  `QICLean/Analysis/CfcKronecker.lean` (QICLean dependency) is the canonical low-layer theorem.
- **Result:** the duplicate proof was removed from
  `QICLean/Channel/Schwarz/SSAEqualityDPI.lean`; the faithful entropy comparison
  uses the Analysis declaration directly.

### Transpose covariance of the continuous functional calculus
- **Pattern:** `TNLean/Analysis/LiebConcavity.lean` carried a private copy of
  the conjugation star-algebra homomorphism and its functional-calculus
  covariance proof solely to commute real powers with transpose.
- **Reuse:** `Matrix.cfc_transpose` in `QICLean/Analysis/CfcConjugation.lean` (QICLean dependency)
  supplies the public covariance theorem.
- **Result:** `rpow_transpose` keeps its private interface and now reduces to
  the public theorem after rewriting both powers as continuous functional
  calculi; the duplicated private conjugation stack was removed.

### Positive-semidefinite sandwich by real powers
- **Pattern:** three sandwiched Rényi proofs separately proved that a real power
  of the reference matrix is positive semidefinite and used Hermiticity to
  identify the resulting congruence with an equal-factor sandwich.
- **Reuse:** `_root_.Matrix.PosSemidef.rpow_mul_mul_rpow` in
  `QICLean/Analysis/SandwichedRenyiTwo.lean` (QICLean dependency) proves
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
  `QICLean/Analysis/SpectralQuadraticForm.lean` (QICLean dependency) provide the basis-independent API used by both
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
- **Result:** the Figure Eight and Gram-normalization steps are stated once, over the
  Gram-dressing property, and each canonical form supplies that property through
  `MPOTensor.IsHorizontalCF.hasGroupedCornerGramDressing` or
  `MPSTensor.IsCPSVCanonicalForm.hasGroupedCornerGramDressing` in
  `TNLean/MPS/MPDO/VerticalBNTGrouping.lean`. No implication between the two canonical-form
  predicates is used.

### Positive-Gram provider for normalized grouped sectors
- **Pattern:** the horizontal BNT-refined and literal CPSV grouped-sector theorems
  differed only in how they obtained a positive scalar Gram identity for each
  copy gauge.
- **Reuse:** `MPOTensor.exists_normalized_grouped_sector_maps_of_gram` takes this
  positive-Gram provider as its sole canonical-form-specific input and proves the
  common isometry, orthogonality, intertwining, and exact reconstruction clauses.
- **Result:** `MPOTensor.exists_normalized_grouped_sector_maps_of_dressing` is the single
  public statement; it takes the Gram-dressing property, which each canonical form supplies
  on its own, so neither canonical-form hypothesis is adapted to the other.

### Vertical canonical form from grouped sectors
- **Pattern:** the literal CPSV and horizontal capstones both unpacked the same grouped BNT
  witness, built the vertical BNT, normalized its sector maps, and reindexed the same dependent
  double sum before applying the grouped-sector coisometry theorem.
- **Reuse:** `MPOTensor.verticalCF_of_grouping_and_gramDressing` in
  `TNLean/MPS/MPDO/VerticalCanonicalFormConstruction.lean` takes
  `HasVerticalBNTGroupingWithIsometry M` and `HasGroupedCornerGramDressing M`; it does not require
  an unused `IsMPDO M` hypothesis.
- **Result:** `verticalCF_of_cpsvCanonicalForm` and `verticalCF_of_horizontalCF` are thin,
  source-facing wrappers over `MPOTensor.HasVerticalBNTGroupingInputs`, the pair of grouping
  and Gram-dressing inputs defined in `TNLean/MPS/MPDO/VerticalBNTGrouping.lean`. Each
  canonical form proves that pair from its own grouping theorem and pairwise Figure Eight
  theorem, preserving the strict separation of their canonical-form predicates.

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
  unitary change-of-basis calculation, while `transferMap_smul` replaces
  the entrywise scaled-Kraus expansion.
- **Result:** `virtualUnitary_of_gaugePhaseEquiv_twisted` falls from 13.3 to
  6.7 seconds in the declaration profiler. The full profiled source check falls
  below 25 seconds locally, with every declaration below 7 seconds.

### Unit-norm scalar invariance of the transfer map
- **Pattern:** three modules separately expanded `transferMap_smul` and proved
  that the factor $c\overline c$ is one from `‖c‖ = 1`.
- **Reuse:** `MPSTensor.transferMap_smul_eq_of_norm_eq_one` in
  `MPS/SharedInfra/Scaling.lean` states the map equality once.
- **Result:** periodicity transport, periodic repeated-block spectrum
  comparison, and Beigi-loop transfer idempotence now use the shared theorem.

### Anticommuting-involution projective multiplication
- **Pattern:** split both `Z₂ × Z₂` inputs into sixteen cases, expand two concrete
  `2 × 2` matrices entrywise, and normalize every resulting scalar expression.
- **Reuse:** `mul_of_anticommuting_involutions` in `MPS/Examples/ZMod2.lean`
  proves the multiplication table once from the two involution laws and their
  anticommutation law. `clusterProjRep` now supplies only those three relations.
- **Result:** the concrete sixteen-case proof in `MPS/Examples/Cluster.lean`
  is replaced by one exact application; its previously profiled 31-second
  declaration falls below the 200-millisecond profiler threshold.

### Scalar invariance of the MPU double layer — promoted
- **Pattern:** expand the double layer of a scalar multiple entrywise and
  cancel the scalar against its conjugate.
- **Reuse:** `MPOTensor.physicalAdjointTensor_smul` and
  `MPOTensor.doubleLayerTensor_smul_of_star_mul_self` reduce this to
  `mulTensor_smul_smul`. The parity witness specializes the latter at `-1`.
- **Result:** the parity example no longer splits over physical and bond
  coordinates. Its identity simplicity proof and the shift identity proof
  share `MPOTensor.isMPUSimple_idTensor` in `MPS/MPU/Simple.lean`.
  Net Lean line delta: -6 across the four changed modules.

### Unit-norm complex scalars are nonzero
- **Pattern:** proofs repeatedly converted `h : ‖z‖ = 1` into `z ≠ 0` with
  `norm_ne_zero_iff.mp (by rw [h]; exact one_ne_zero)`.
- **Reuse:** `Complex.ne_zero_of_norm_eq_one` in
  `QICLean/Algebra/ComplexPhasePositivity.lean` (QICLean dependency) now states this scalar fact once.
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
- **Reuse:** QICLean's `Kraus.instNeZeroBlockPhysDim` provides the instance,
  replacing exactly those four local calculations in `Martingale/BlockedGap.lean`.
  The former TNLean instance `MPSTensor.instNeZeroBlockPhysDim` was an exact
  duplicate and has been retired; `MPSTensor.blockPhysDim` is an abbreviation
  of `Kraus.blockPhysDim`, so the canonical instance applies directly.
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
- **Reuse:** callers use `Kraus.isIrreducibleMap_mapLM_conjTranspose`, its `iff`
  companion, and `Kraus.traceAdjointMap_mapLM_eq_mapLM_conjTranspose` directly.
- **Result:** the two MPS pass-through declarations and their duplicated
  conjugate-transpose projection arguments are removed.

### Closed-sector rectangular trace factorization
- **Pattern:** three MPDO proofs promoted a physical-sector isometry to a unitary,
  expanded `physTraceTransfer` as a closed-sector sum, and identified that sum
  with a rectangular product of sector-trace matrices. The active-sector proofs
  additionally filtered away zero-weight sectors.
- **Reuse:** `physTraceTransfer_eq_leftTraceMatrix_mul_rightTraceMatrix` owns the
  all-sector factorization, while the layer-0 lemma
  `Finset.sum_eq_sum_subtype_ne_zero` owns the filtered-sum step.
- **Result:** the duplicated `hphys` blocks in
  `ActiveSectorTraceMatrixZCL.lean` and `LemmaC5CaseI.lean` are short
  specializations of these two lemmas. This completes the promotion tracked in
  issue #6931.

### Complex squares of real square roots
- **Pattern:** finite matrix computations repeatedly converted
  $((\sqrt{x}:\mathbb R):\mathbb C)^2$ back to $x$ through
  `Complex.ofReal_pow` and `Real.sq_sqrt`.
- **Reuse:** the layer-0 lemma `Complex.ofReal_sqrt_sq` owns the coercion and
  nonnegative-square-root identity.
- **Result:** the five occurrences in the corrected CPSV16 Example 4.10 tensor
  and spectrum proofs, together with the two older AKLT helpers, now reuse the
  same lemma.

### Complex inverse squares of real square roots
- **Pattern:** small example modules each proved the scalar identity
  $((\sqrt{x}:\mathbb R):\mathbb C)^{-1}\cdot((\sqrt{x}:\mathbb R):\mathbb C)^{-1}
  = (x:\mathbb C)^{-1}$ at $x = 2$, in six different spellings of $1/\sqrt 2$.
- **Reuse:** the layer-0 lemma `Complex.ofReal_sqrt_inv_mul_self` owns the
  identity; each spelling is one `simpa [one_div]` away from it.
- **Result:** the six private lemmas in `Cluster.lean`, `EvenParity.lean`,
  `MajumdarGhosh.lean`, `LocalPurificationRFP.lean`,
  `CaseIIAbsorptionCounterexample.lean` and `CPSVCIDNotRFPExample.lean` now have
  one- or two-line bodies, and the two normalized-ancilla cancellations of
  `TNLean/MPS/MPU/PhysicalAncilla.lean` route through the owner lemma as of
  2026-09-23.  The three private constants naming $1/\sqrt 2$ and the
  general-`d` `sourceSqrt` cancellations of
  `TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` are retained: they have
  different carriers or fixed associativity shapes and are consumed as rewrite
  rules in their own spellings.  The two pass-throughs
  `sourceSqrt_mul_inv`/`sourceSqrt_inv_mul` of that family, plain
  `mul_inv_cancel₀` wrappers outside the owner lemma's shape, were retired on
  2026-09-23.

### Scalar identity matrix positivity and trace
- **Pattern:** proofs repeatedly derived positivity or positive-definiteness of
  `c • (1 : Matrix n n R)` from the corresponding scalar order hypothesis and
  computed its trace by rewriting `Matrix.trace_smul` and `Matrix.trace_one`.
- **Reuse:** the generic lemmas `Matrix.PosSemidef.smul_one`,
  `Matrix.PosDef.smul_one`, and `Matrix.trace_smul_one` in
  `TNLean/Algebra/MatrixScalarIdentity.lean` own these arguments under the
  weakest assumptions used by the underlying Mathlib results.
- **Result:** the repeated proofs in `Theorem49RepeatedCopyCounterexample.lean`,
  `AKLTStringOrder.lean`, `Cluster.lean`, and
  `ShiftPaperSourceFactors.lean` now use the shared matrix API.

---

### Orthogonal-resolution multiplication table — promoted
- **Pattern:** split equality of two indices; use idempotence in the equal
  case and `orthogonalProjection_mul_eq_zero_of_sum_eq_one` otherwise.
- **Seen:** three occurrences in `stepOrbitProjection_mul_original`,
  `hasEigenvalue_adjoint_compressed_stepOrbit`, and the private
  `exists_root_of_orbit_phase`, in `StepOrbitSectors.lean`,
  `BlockingEigenvalues.lean`, and `OrbitUnitary.lean` under
  `TNLean/MPS/Periodic/` (2026-09-30).
- **Abstraction:** `orthogonalProjection_mul_eq_ite_of_sum_eq_one` in
  `TNLean/Algebra/OrthogonalResolution.lean` gives the full multiplication
  table. All three consumers use it; no custom tactic is needed.

### finite-volume continuity from the local interaction — promoted
- **Pattern:** express a translated parent term as the finite average of
  restriction–interaction–adjoint products, prove each product continuous,
  and sum the terms over the chain.
- **Seen:** the injective-family and direct-sum-family continuity theorems in
  `MPS/ParentHamiltonian/GroundSpaceMapContinuity.lean` and
  `MPS/ParentHamiltonian/BlockGroundSpaceMapContinuity.lean` (2026-10-02).
- **Abstraction:** `continuous_parentInteractionES_family_of_groundProjection`,
  `continuous_localTermES_family_of_groundProjection`,
  `continuous_openParentHamiltonianES_family_of_groundProjection`, and
  `continuous_parentHamiltonianES_family_of_groundProjection` take
  continuity of the local ground-space projection as their analytic input.
- **Notes:** both tensor-family arguments use the same finite-volume proof;
  the injectivity and simultaneous-word-span conditions are confined to
  the construction of the local projector.

### contracting a two-site bond penalty — promoted
- **Pattern:** reindex the two-site configuration sum by `twoSiteBondEquiv`,
  contract the two exterior identity factors, and evaluate the remaining
  middle-register sum.
- **Seen:** three contractions across `BondProductEndpointGroundSpace.lean`,
  `FixedPointParentIdentification.lean`, and `WeightedMatrixUnitParent.lean`,
  under `TNLean/MPS/Symmetry/`.
- **Abstraction:** `twoSiteBondInteraction_mulVec_apply` gives the coefficient
  formula for an arbitrary two-site vector. Its separable specialization
  `twoSiteBondInteraction_mulVec_separable` and the unit-vector consequence
  `twoSiteBondPenalty_mulVec_separable` are in `TwoSiteBondContraction.lean`.
- **Refactoring:** both earlier contractions and the weighted contraction
  use these lemmas. The two earlier files lose 33 lines in total, while the
  shared module contributes 87 lines, including documentation and four
  declarations: net +54 lines. The exterior-index reduction now occurs once.
- **Notes:** the existing boundary-coefficient formulas remain local; the
  arbitrary-vector formula also handles the complementary projection without
  assuming separable coefficients.

### canonical-parent comparison with a normalized bond interaction — promoted

- **Pattern:** compare positive two-site projections, identify the bond
  Hamiltonian's periodic ground line with the tensor's periodic vector,
  and apply affine interpolation with common zero modes and endpoint symmetry.
- **Seen:** the weighted comparison in `MPS/Symmetry/WeightedMatrixUnitParentPath.lean`
  and the two embedded endpoint comparisons in `MPS/Symmetry/EmbeddedFixedPointParent.lean`.
- **Abstraction:** `normalizedBondCanonicalParentComparisonPath`, with the
  periodic-vector comparison in
  `ker_interactionHamiltonian_normalizedBondInteraction_le_parent_of_mpv_eq`
  and the local comparison in
  `twoSiteBondInteraction_le_parentInteraction_of_groundSpaceMap`.
- **Notes:** the three constructors share the spectral and symmetry proof.
  Bond dimension may differ from the dimension of the normalized bond.
  No injectivity assumption is used in the comparison itself.

### gauge covariance along the polar deformation — promoted

- **Pattern:** regard a unitary bond matrix as an invertible matrix and
  apply the preserved polar covariance letter by letter.
- **Seen:** the parent-symmetry proof in `MPS/Symmetry/PolarDeformationGap.lean`
  and the path constructors in `MPS/Symmetry/PolarGappedInteractionPath.lean`
  and `MPS/Symmetry/EmbeddedInjectiveGappedPath.lean`.
- **Abstraction:** `gaugeEquiv_polarDeformation_of_unitary_covariance`
  in `MPS/Symmetry/PolarDeformation.lean`.
- **Notes:** the same virtual matrix implements the covariance at every
  parameter. All three uses now share the conversion to gauge equivalence.

### boundary spaces under rectangular physical maps — promoted

- **Pattern:** expand the rotated letters, collect the product of their
  physical coefficients, and identify the boundary space as the range
  of the tensor power composed with the original boundary map.
- **Seen:** the three square-map boundary identities in
  `MPS/ParentHamiltonian/PhysicalDeformation.lean` and their rectangular
  counterparts in `MPS/ParentHamiltonian/PhysicalEmbedding.lean`.
- **Abstraction:** `groundSpaceMap_rotatePhysical_rectangular`,
  `groundSpace_rotatePhysical_rectangular`, and
  `groundSpaceES_rotatePhysical_rectangular`.
- **Notes:** the square-map statements now use these shared results.
  Neither invertibility nor injectivity is required for boundary transport.
  Isometric projection transport additionally uses
  `LinearIsometry.starProjection_map_eq_comp_adjoint`.

### adjoint transfer along a stationary support — promoted

- **Pattern:** stationary support invariance makes expansion of a compressed
  matrix intertwine the two adjoint transfer maps.
- **Helper:** `MPSTensor.adjointMap_compression_lift` in
  `TNLean/MPS/Symmetry/StationarySupportedDensityPhaseInvariance.lean`.
- **Call sites:** normalized stationary uniqueness in that module, and
  adjoint eigenvector lifting in
  `TNLean/MPS/Symmetry/StationarySupportPreparation.lean` (2026-10-03).
- **Decision:** expose the existing mathematical identity and remove its
  duplicate proof. No new tactic or additional hypothesis is needed.

### normalized adjoint fixed-matrix uniqueness — promoted

- **Pattern:** trace-adjoint duality identifies a one-dimensional adjoint fixed space;
  a trace-one fixed matrix spans it, and traces determine the scalar of any other
  trace-one fixed matrix.
- **Helper:** `MPSTensor.normalized_adjoint_fixed_unique_of_transfer_fixed_finrank_one`
  in `MPS/Symmetry/StationarySupportLimitIdentification.lean`.
- **Call sites:** stationary-support identification in that module and the convergent
  sequence argument in `MPS/Symmetry/CompactSupportedSequenceClass.lean` (2026-10-03).
- **Decision:** expose the existing proof unchanged and reuse it. Positivity of the
  comparison matrix is not needed.

### reordering words of a party layout — promoted

- **Pattern:** a word of exchanges of tensor factors, built by recursion or
  composition, gets a lemma that it is allowed, uses any given parties and has
  no pair source, followed by three one-line projections.
- **Helper:** the predicate `PairEffect.Word.IsReordering` with the simp lemmas
  `isReordering_id`, `isReordering_swap`, `isReordering_comp_iff`,
  `isReordering_frame_iff`, `isReordering_frameList_iff` and the projections
  `IsReordering.isAllowed`, `IsReordering.usesOnly` and
  `IsReordering.sourceCount_eq`, in
  `TNLean/PEPS/Approximation/SiteRegisters.lean`.
- **Call sites:** `SiteRegisters.lean`, `RegisterReordering.lean`,
  `FrameRegisters.lean`, `TwoSheetRegisters.lean` and
  `FrameBoundedChanges.lean` (2026-10-09). A composite of reorderings closes
  by `simp [w]`; a word with local maps passes the projections to `simp` as
  conditional rewrites.
- **Notes:** when a recursive word's type differs from the type of its
  unfolding only up to definitions such as `siteRegs`, `simp` cannot match
  `isReordering_comp_iff`; apply `IsReordering.comp` as a term instead.

## Candidates

### Operator norm in orthonormal coordinates — candidate (2026-10-07)

- **Pattern:** Identify matrix multiplication in orthonormal coordinates with
  the underlying continuous linear map, then use preservation of norms by the
  coordinate isometries to transfer an operator-norm bound.
- **Seen:** Two occurrences:
  `PEPS/Approximation/PreparedMatrixNorm.lean`,
  `Word.norm_preparedMatrix_le_one`, and
  `PEPS/Approximation/SourceBlockMatrix.lean`,
  the private `Word.norm_toMatrix_eval_le_one`.
- **Abstraction:** If another independent use arises, first check Mathlib for
  the corresponding orthonormal-coordinate norm identity, then supply a general
  lemma if needed. No further copy is currently required: the proper-frame
  bound uses the complete free-source matrix bound through a fixed map word.
- **Notes:** The predecessor proof and its exact-source verification remain
  unchanged. The focused scan of the five new modules and `PreparedMatrixNorm`
  found these two occurrences and no pattern occurring three times. This entry
  remains below the promotion threshold.

### sitewise Kronecker power in configuration coordinates — candidate
- **Pattern:** the matrix `fun a b => ∏ n, A (a n) (b n)` on `Fin N → ι` with its product,
  identity, conjugate-transpose and unitarity lemmas.
- **Seen:** two copies (2026-10-06): `siteProduct` (index `Fin ℓ × Fin r`) in
  `TNLean/MPS/MPU/FundamentalTheoremGates.lean` and the private `chainPower` (index `Fin d`) in
  `TNLean/MPS/MPU/Examples/ShiftStrictEquivalence.lean`.
- **Abstraction:** one definition over an arbitrary fintype; a third copy promotes it.

### simplicity of a tensor with diagonal rank-one double-layer letters — candidate
- **Pattern:** `isMPUSimple_of_rankOne_diagonal` (`TNLean/MPS/MPU/SimpleRankOne.lean`,
  2026-10-06) proves simplicity from three scalar pairings; the shift's own simplicity proof
  (`rightShiftTensor_isMPUSimple`) has this form and could be replaced by it.

### Endpoint witness for a closed dyadic neighborhood — candidate (2026-10-07)

- **Pattern:** Choose one cell in the finite closed neighborhood union, then
  an endpoint in its occupied neighboring cell, and apply the closed-cell
  distance bound.
- **Seen:** The private neighborhood witness in `DistanceLayers.lean` and
  the public `dyadicNeighborhood_exists_dist_le` in `DummyContacts.lean`.
- **Current reuse:** New consumers use the public theorem. The earlier verified
  module is preserved; this is the second occurrence, below the promotion
  threshold.
- **Promotion trigger:** If a third occurrence is needed, use the public
  theorem and replace the earlier private copy in one separately verified
  contribution.

### Entropy bounds from boundary counts — candidate (2026-10-07)

- **Pattern:** Cast a cardinal comparison to the reals, multiply by the
  nonnegative entropy constant, and compose with the assumed entropy bound.
- **Seen:** Two occurrences in `PEPS/AreaLaw/VertexBoundaryCorollaries.lean`,
  for the inner boundary and the set of both endpoints.
- **Abstraction:** Both proofs already use Mathlib's cast and multiplication
  lemmas. A third occurrence in another module should extract the common
  inequality argument into a lemma, with the comparison factor explicit.

### Simultaneous weighted sector coordinates — candidate (2026-10-02)

- **Sites:** `ThetaBondCoordinates` and `ThetaBondOrthonormalCoordinates`.
- **Pattern:** restrict the family containing both ρ(g) and Θ²ρ(g) to the
  irreducible summands, then collect the sector coordinates simultaneously.
- **Current reuse:** the direct-sum matrix and collected-orthonormal-basis
  theorems are Mathlib results; only the scalar restriction calculation is
  repeated between the linear and orthonormal versions.
- **Promotion trigger:** a third occurrence should extract that scalar
  restriction identity, preserving the distinction between linear and
  orthonormal coordinates.

### Closure of unitary generators under adjoints — candidate (2026-10-02)

- **Sites:** invariant-subspace and restricted-intertwiner correspondences in
  `Algebra/UnitaryRepresentationAlgebra.lean`.
- **Pattern:** use `Algebra.adjoin_induction` on the generators together with
  their adjoints; replace an adjoint generator by the inverse group element.
- **Current reuse:** Mathlib supplies the algebra induction, while the common
  inverse-adjoint identity is proved once in the same module. The product step
  uses invariance in different ways for vectors and intertwiners.
- **Promotion trigger:** a third use in another file should first seek a
  common generated-algebra statement. Two distinct inductions in one file do
  not justify a new tactic.

### Orthonormal rows as subrepresentation bases — candidate (2026-10-02)

- **Sites:** `Algebra/UnitaryRepresentationBlocks.lean` and
  `PEPS/RegularFourier.lean`.
- **Pattern:** use `Basis.span` on an orthonormal subfamily, transport it to a
  named invariant subspace with `LinearEquiv.ofEq`, and identify the underlying
  row vectors.
- **Current reuse:** the basis construction and transport are existing Mathlib
  abstractions. The Fourier calculation additionally inherits orthonormality
  and uses `Basis.toOrthonormalBasis`; the multiplicity calculation only needs
  the linear basis.
- **Promotion trigger:** another use requiring the same transported
  orthonormal basis should extract a mathematical basis construction, rather
  than a tactic wrapping these existing operations. The four new Fourier
  modules have no repeated tactic blocks at window five, count two.

### Expanding a controlled cycle contraction — candidate (2026-10-02)

- **Pattern:** expand the actual region projector as a sum of vertex translations,
  distribute the two surrounding matrices over that sum, and compare each term.
- **Sites:** `RegularCycleControlledSupport.lean` and
  `RegularCycleFluxMeasurement.lean`, with two occurrences at window five in
  the combined 103-module PEPS scan.
- **Current reuse:** both use
  `regionPhysicalProductMatrix_regularLegProjector_eq_sum_vertexTranslation`
  and Mathlib's finite-sum congruence. Their termwise conclusions differ.
- **Promotion trigger:** a third use should extract the shared contraction
  identity if it eliminates the termwise calculation; a wrapper around the
  existing sum expansion alone is not needed.

### Six-site vertex-label evaluations — candidate (2026-10-03)

- **Pattern:** unfold the vertex-label assignment, distinguish its two
  rows, and evaluate a fixed local column.
- **Seen:** seven short occurrences in
  `TorusInitialStringRightPhysicalStep.lean`; the pattern scan identifies
  their common three-line opening.
- **Current treatment:** the coordinate calculations remain in one file.
  Their dependent edge enumeration has already been replaced by the
  shared seven-edge transport theorem.
- **Promotion trigger:** reuse of the same vertex-label family in another
  module. Prefer pointwise value lemmas for that family.
### boundary-weighted physical twists — candidate
- **Pattern:** expand the trace of an ordered product of linear combinations, then match
  each coefficient with the corresponding Kronecker-power matrix entry.
- **Seen:** the ket and bra twists, with and without a boundary, in
  `TNLean/MPS/Symmetry/MPDO/Vectorized.lean` (four occurrences in one file, 2026-10-02).
- **Existing abstraction:** `Matrix.trace_prod_ofFn_sum_smul` and
  `Matrix.trace_mul_prod_ofFn_sum_smul` perform the trace expansion. The remaining entry
  arguments are short and distinguish left multiplication from right multiplication.
- **Decision:** retain these proofs; no further abstraction is warranted before this
  pattern occurs in another file.

### Physical insertion congruence and identity insertions — candidate
- **Pattern:** a finite physical insertion transforms by congruence under a
  bond similarity; insertion of the identity on `n` sites gives the same
  covariance for the `n`th transfer power.
- **Seen:** the insertion and connected-contraction proofs in
  `TNLean/MPS/SharedInfra/PhysicalObservableGauge.lean` (2026-10-02).
- **Reuse:** `MPSTensor.physicalObservableTransfer_congruence_of_gauge`
  proves the word-sum calculation once. The transfer-power identity follows
  from the existing `MPSTensor.physicalObservableTransfer_one`, and the
  connected contraction uses these equations with trace cyclicity.
- **Notes:** the arbitrary-gauge decay proof transports the already proved
  trace-preserving contraction instead of repeating complementary powers and
  fixed-point projection calculations. No custom tactic is needed.

### centering physical insertions carried by transfer eigenvectors — candidate
- **Pattern:** trace preservation and a transfer eigenvalue different from one
  imply that the eigenvector is traceless; the fixed-state projection then
  vanishes on the inner physical insertion, including the zeroth transfer power.
- **Seen:** two occurrences across two files (2026-10-02):
  `DecayingCorrelations.lean` and `DecayingCorrelationBound.lean`, under
  `TNLean/MPS/Preparation/`.
- **Abstraction:** the existing
  `MPSTensor.trace_eq_zero_of_transferMap_eq_smul` supplies tracelessness;
  a Hermitian-vector realization now records this property in its conclusion.
- **Notes:** the physical two-point identity and positive-separation reduction
  are proved once in `DecayingCorrelations.lean`. The finite-size and clustering
  arguments use the reduction lemma instead of repeating the projection algebra.

### Exponential error converted to polynomial accuracy — candidate
- **Pattern:** bound the number of blocks by the chain length, compare the
  exponential rate using the logarithmic block-length threshold, and use
  `Real.exp_add`, `Real.exp_log`, and `Real.rpow_def_of_pos` to obtain
  the factor `N ^ (-η)`.
- **Seen:** private `mul_exp_le_polynomial` in
  `TNLean/MPS/Preparation/PolynomialAccuracy.lean` and private
  `polynomial_error_factor` in
  `TNLean/MPS/Preparation/AllLengthPolynomialAccuracy.lean` (2026-10-03).
- **Notes:** there are two implementations. The former derives `M ≤ N`
  from uniform blocks; the latter accepts that inequality for the
  remainder-absorbing construction. At a third occurrence, extract the
  common scalar inequality. The promoted logarithmic-threshold helpers
  address a prescribed error tolerance rather than this polynomial form.

### Ceiling block lengths and logarithmic circuit depth — candidate
- **Pattern:** apply `Nat.le_ceil` and `Nat.ceil_lt_add_one` to the
  prescribed block length, then absorb the additive one using
  `log N ≥ log 2` to bound circuit depth by a multiple of `log N`.
- **Seen:** the block-length choice in
  `TNLean/MPS/Preparation/LogDepthPreparation.lean` and private
  `polynomialBlockLength_bounds` in
  `TNLean/MPS/Preparation/AllLengthPolynomialAccuracy.lean` (2026-10-03).
- **Notes:** these are two related arguments with different logarithmic
  thresholds. The new polynomial argument also proves a lower bound
  uniform in the accuracy exponent. The existing promoted depth helper
  uses a logarithmic offset and does not cover that lower-bound argument.
  Retain the local proofs until a third occurrence identifies a common
  assertion.

### Finite group fibers in local tensor isometries — candidate
- **Pattern:** parameterize all preimages of a virtual label by one group
  coordinate, use that coordinate as the inverse in a finite-sum bijection,
  and evaluate the resulting weighted sum or fiber cardinality.
- **Seen:** the dual tensor's `siteMap_quantumDoubleDualTensor_apply_spins`
  argument in `TNLean/PEPS/Examples/QuantumDouble.lean` and the private
  `primalLabels_fiber_sum` argument in
  `TNLean/PEPS/Examples/ToricCodePrimal.lean` (2026-10-03).
- **Notes:** these two occurrences have different label maps. The primal
  parameterization is already shared by its weighted sum and fiber count;
  no further abstraction is needed before a third distinct occurrence.

### linearity of a recovered bond operation — candidate
- **Pattern:** apply injectivity of the boundary-insertion map, rewrite the
  virtual operations by their physical realizations, and use linearity of the
  physical operation and boundary insertion.
- **Seen:** two occurrences in
  `TNLean/PEPS/TorusWindowCrossTensorAlgebra.lean`, in
  `staircaseCrossTensorVirtualOperation_add` and
  `staircaseCrossTensorVirtualOperation_smul` (2026-10-02).
- **Abstraction:** a linear recovery map from realized physical operations,
  if a third use in another module needs the same argument.
- **Notes:** the two current proofs use `bondInsertedRegionInsert_injective`
  and the existing realization identities; no tactic is needed at this count.

### Remainder-absorbing block lengths — candidate
- **Pattern:** write `N / q = m + 1`, take `m` blocks of length `q` and one
  of length `q + N % q`, and prove the sum is `N` by separating the last
  summand, summing the constants, and applying `Nat.div_add_mod`.
- **Seen:** two production occurrences in
  `TNLean/MPS/Preparation/LogDepthPreparation.lean:152` and
  `TNLean/MPS/Preparation/ZeroSubleadingPreparation.lean:120` (2026-10-03).
- **Abstraction:** at a third occurrence, a partition lemma for arbitrary
  `N,q,m` with `N / q = m + 1` can supply the sum and the lower/upper bounds
  from `Nat.mod_lt`, using the existing `Fin.sum_univ_castSucc` and
  `Finset.sum_const`.
- **Notes:** Mathlib already supplies the finite-sum and division identities;
  no general partition lemma was found. The two production occurrences are
  below the rule-of-three threshold.

### One-site doubled-alphabet transport — candidate
- **Pattern:** identify the doubled alphabet of one-site MPO blocking with
  the original ket-bra alphabet, then transport the physical-trace contraction
  along the one-site equivalence.
- **Seen:** two occurrences of each identity across two files:
  `TNLean/MPS/MPDO/Simple.lean:IsSimpleCanonicalForm.isSimple` and
  `TNLean/MPS/MPDO/TwistedDimerBondSimple.lean` (2026-10-02).
- **Abstraction:** the bond-factor proof uses private generic identities
  `blockTensor_one_toMPSTensor` and
  `doubledPhysTraceTransfer_reindex_singleBlock`. At a third occurrence,
  move the equivalence and identities to the physical-blocking API and
  refactor the existing simplicity proof.
- **Notes:** the generic form also avoids unfolding the concrete four-level
  matrix-unit tensor during alphabet comparison. The count remains below
  the rule-of-three threshold.

### native endpoint equations in spanning-tree coordinates — candidate
- **Pattern:** specialize a half-edge compatibility identity at both endpoints
  of one internal edge, then rewrite the two inverse coordinate formulas.
- **Seen:** two occurrences in
  `PEPS/RegularRegionProjectorCoordinates.lean:118` and
  `PEPS/RegularTwistedRegionProjectorCoordinates.lean:53`, found by the
  deduplicated changed-module scan with `--min-window 5 --min-count 2`
  (2026-10-02).
- **Abstraction:** the mathematical synchronization is already shared through
  `regularRegionCoordinates_rootLabels_of_tree_compatibility`; the endpoint
  identities themselves use the public tail and head reconstruction lemmas.
- **Notes:** below the three-occurrence threshold. No third endpoint
  specialization is currently identified. The untwisted and twisted
  compatibility hypotheses differ, and combining the existing endpoint
  lemmas into a conjunction would only shorten the specialization step.
  Keep this candidate until another independent application needs the same
  derived endpoint statement.

### dependent boundary half-edge identification — candidate
- **Pattern:** identify the boundary vertex, prove equality of the associated
  dependent half-edge pair using `Sigma.ext` and `Subtype.heq_iff_coe_eq`,
  then transport the reconstructed coefficient through that equality.
- **Seen:** the tail and head boundary reconstruction proofs in
  `PEPS/RegularRegionCoordinates.lean:422` and `:450`, detected by the
  same scan (2026-10-02).
- **Abstraction:** if another application appears, consider a native
  boundary-half-edge equality lemma, preserving the dependence of the
  incident-edge type on its vertex.
- **Notes:** two occurrences in one file, with no further use currently
  identified. The scanner's fifth line starts the subsequent coefficient
  transport, so its five-line window is not one uniform mathematical step.
  No additional helper is introduced at this stage.

### incident vertices from an unordered endpoint equation — candidate
- **Pattern:** combine the two possible endpoint orientations of an edge
  with its two possible incidences to conclude that the incident vertex
  is one of the original ordered endpoints.
- **Seen:** horizontal and vertical cases in
  `PEPS/RegularTorusEntropy.lean:49` and `:66`, detected by the same
  changed-module scan (2026-10-02).
- **Abstraction:** if further applications appear, first look for an
  existing incidence characterization for `Edge.ofAdj`; otherwise use a
  graph-theoretic endpoint lemma rather than a tactic.
- **Notes:** two occurrences in one file. No additional occurrence is
  currently expected, so the promotion criteria are not met.

### semi-regularity through an injective intertwiner — candidate
- **Pattern:** compose each nonzero irreducible intertwiner with an injective
  intertwining map, then use injectivity to preserve nonvanishing.
- **Seen:** `IsSemiRegular.of_equiv` in
  `Algebra/SemiRegularEquiv.lean` and `IsSemiRegular.tprod_of_mem_invariants`
  in `Algebra/RepresentationTensorProduct.lean` (2026-10-02). The latter
  proves injectivity of the fixed-factor tensor inclusion by a dual pairing.
- **Abstraction:** if another occurrence arises, a semi-regularity transport
  theorem for injective intertwining maps would include equivalences and
  invariant tensor inclusions in one statement.
- **Notes:** the equivalence case is already centralized in
  `IsSemiRegular.of_equiv`; the native regular coordinate bridge uses it
  directly, so it adds no repeated occurrence proof.

### normalization from the physical boundary density trace — candidate
- **Pattern:** rewrite the squared norm of a physical bipartite boundary
  vector as the trace of its Schmidt coefficient matrix times its adjoint,
  identify the reduced density, and use its unit trace.
- **Seen:** the positive cut normalization in
  `PEPS/RegularRegionEntropy.lean` and the superposition normalization in
  `PEPS/RegularClosureSuperposition.lean` (2026-10-02).
- **Abstraction:** a physical-boundary norm lemma taking the two invariant
  Gram identities would remove the two identical reductions if another
  direct use appears.
- **Notes:** both proofs already use Mathlib's
  `Matrix.star_dotProduct_eq_trace_conjTranspose_mul`; the candidate is
  the subsequent identification with the physical boundary density.

### positive interaction subfamilies — candidate (2026-10-02)

- **Pattern:** Express an interval interaction sum as a filtered sum, then
  apply `Finset.sum_le_sum_of_subset_of_nonneg` and
  `LinearMap.nonneg_iff_isPositive` to bound it by the full interaction sum.
- **Seen:** two instances in
  `ParentHamiltonian/Martingale/OverlappingIntervalGap.lean`, for the prefix
  and terminal interval Hamiltonians.
- **Abstraction:** Mathlib already supplies the finite-sum comparison. If
  more interval shapes require this argument, isolate the common positive
  subfamily comparison rather than repeating the filter conversion.
- **Notes:** Both occurrences are in one module; no new tactic is needed.

### Gram products of vertically stacked matrices — candidate
- **Pattern:** reduce the Gram product of a matrix formed by `Matrix.fromRows`
  to the sum of the two block Gram products, using
  `Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose` and
  `Matrix.fromCols_mul_fromRows`.
- **Seen:** three proofs in `TNLean/MPS/MPU/ProjectionPhaseIsometries.lean`:
  `projectionPrefixMap_isIsometry`, `projectionInteriorMap_isIsometry`, and
  `projectionSuffixMap_isIsometry` (2026-10-02).
- **Abstraction:** combine the two existing Mathlib identities into a helper
  lemma if a second file uses the same reduction.
- **Notes:** three occurrences in one file; below the two-file promotion
  threshold. The following projection algebra differs between the proofs.

### adjoints of left polar identities — candidate (2026-10-02)

- **Pattern:** Apply `congrArg Matrix.conjTranspose` to a matrix product
  identity, then simplify `conjTranspose_mul` and the Hermitian factors.
- **Seen:** four instances in `ParentHamiltonian/LeftPolar.lean`: the
  support factorization used for positivity, the support action on the
  partial isometry, and the two identities identifying the physical range.
- **Abstraction:** The existing `Matrix.conjTranspose_mul` supplies the
  algebraic operation. A more specific reusable lemma would need to remove
  repeated Hermitian-factor arguments in a second module.
- **Notes:** These instances occur in one module and prove distinct polar
  identities. No additional tactic or matrix predicate is introduced.

### quadratic bounds for commuting periodic projections — candidate
- **Pattern:** convert matrix translates to symmetric linear projections,
  use nonnegative cross terms, and specialize the common quadratic-form
  bound with unit gap and zero overlap.
- **Seen:** `MPS/Symmetry/BondProductParentHamiltonian.lean` and
  `MPS/Symmetry/PhysicalInteractionGap.lean` (2026-10-02).
- **Abstraction:** both already use
  `ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`;
  the remaining periodic-translate conversion may be shared if another
  caller needs it.
- **Notes:** two occurrences; no additional tactic is needed at present.

### coordinate restriction at the two bond endpoints — candidate

- **Pattern:** expand a weighted matrix unit, select the occupied summand,
  and reduce its endpoint weight to the corresponding inverse square root.
- **Seen:** the two physical embedding identities in
  `MPS/Symmetry/EmbeddedFixedPointTensor.lean`.
- **Abstraction:** a general weighted matrix-unit compression lemma if a
  third use appears in a second module.
- **Notes:** currently two occurrences in one module. Isometric inclusions,
  boundary transport, and covariance restriction already use shared lemmas.

### relabeling normalized source factors into a standard form — candidate
- **Pattern:** pull source factors back along intermediate-rank equivalences,
  use the supplied gate entry formulas, and rewrite both finite sums along
  those equivalences to inherit the open source-factor contraction.
- **Seen:** `shiftExampleU₂BlockedStandardForm` and
  `shiftExampleU₃BlockedStandardForm` in `Examples/ShiftStandardForms.lean`.
- **Notes:** their weighted and ordinary isometry identities are transported
  along the same column equivalences. Consider a shared constructor when a
  third tensor requires this exact combination of data.


### rescaling a source cut to normalize its virtual weight — candidate
- **Pattern:** scale the first cut's `X₁` and `Z₁` by a nonzero real scalar,
  scale `Y₁` inversely, and divide the virtual weight by the scalar's square.
- **Seen:** `rightShiftPaperSourceFactors` in `Examples/ShiftSourceFactors.lean`
  and `normalizeProductShiftSourceFactors` in `Examples/ShiftNormalizedSourceFactors.lean`.
- **Reuse:** the latter helper already serves both counterpropagating families.
  A third distinct proof should extract the general scalar-weight operation.


### delta-contraction standard-form witnesses — candidate
- **Pattern:** reindex a finite bond sum by `finProdFinEquiv`, expand tensor
  entries, and contract Kronecker deltas with `simp`; finish reordered
  equality tests with `split_ifs` and `simp_all`.
- **Seen:** the unblocked third-family and swap-transformed second-family
  witnesses in `TNLean/MPS/MPU/Examples/ShiftStandardForms.lean`. The direct
  identity witness has the trivial bond `Fin 1`, so it contracts deltas without
  any bond reindexing and is not an occurrence.
- **Normalization:** the unblocked third family and transformed second family
  also evaluate Gram sums after the same bond reindexing, with reciprocal
  square-root scalings. Both occurrences remain in this one module.
- **Decision:** the two blocked families now use normalized source factors and
  the shared open-contraction theorem instead. Keep the remaining explicit
  gate-specific expansions while the pattern is confined to one module; if
  another example repeats it, first seek a finite-sum lemma rather than a tactic.


### finite three-cocycle entry elimination — candidate
- **Pattern:** specialize the cocycle equation at a concrete quadruple, reduce its group
  products, and simplify using entries already known to be one.
- **Seen:** 18 specializations in `eq_one_of_klein_entries`, in
  `TNLean/Algebra/KleinCocycleCompleteness.lean` (2026-09-30).
- **Abstraction:** no new tactic yet; these are the entries of one finite calculation.
  If a second group needs the pattern, prefer a general cocycle determination lemma
  before automating the table elimination.

### weighted W-state rows across a cut — candidate
- **Pattern:** rewrite a weighted sum of traces of two word products as a
  scalar multiple of the W amplitude on the concatenated configuration, then
  use `wIndicator_append_mem_span` to put the cut row in the two-dimensional
  span of the vacuum and single-excitation indicators.
- **Seen:** two occurrences in one file (2026-09-28):
  `lt_of_sum_mpv_eq_smul_wIndicator` and
  `lt_of_sum_mpv_eq_smul_wIndicator_asymmetric` in
  `TNLean/MPS/Examples/WStateCanonicalBound.lean`.
- **Abstraction:** if another cut-rank application repeats this conversion,
  state a row-membership lemma taking the weighted W-state identity and the
  two cut lengths.
- **Notes:** below the promotion threshold. The shared long-side spanning
  argument is already extracted as
  `blockTracePairing_range_le_of_forall_mem` in
  `TNLean/MPS/ParentHamiltonian/PGVWC07CutRank.lean` and used in both cut-rank
  estimates.

### Positive local terms with prescribed kernels

For two finite families of positive operators with equal kernels term by
term, rewrite each kernel of a sum with
`WeightedPositiveKernel.ker_sum_eq_iInf`, then substitute the pointwise kernel
equalities. This proves equality of the two total kernels without comparing
the operators in order.

Occurrences: `BlockGroundSpaceAtInjectivityLength.lean` and
`CanonicalBlockGroundSpaceAtInjectivityLength.lean`. Both use the existing
QICLean kernel-of-sum theorem. A further occurrence would justify a direct
kernel-equality corollary there; no new tactic is needed.

### Scalar-valued norms and equal ambient lengths

When a linear map acts on a Hilbert space indexed by an arithmetic expression,
rewriting an equality of lengths inside the map can introduce dependent casts.
First express the entire operator norm as a scalar-valued function of the
ambient length and interval endpoints. A `change` then exposes ordinary natural
number arguments, and `rw` transports the scalar expression without transporting
the underlying Hilbert space explicitly.

Example: `GroupedProjectorEstimate.lean`, in
`grouped_martingaleDifference_norm_le_of_projector_defect`, uses
`F N a b : ℝ` for the norm of a suffix projection composed with a difference of
prefix projections. This permits the active-volume identity and spectator bound
to be combined using ordinary arithmetic equalities. Candidate helper pattern;
currently one occurrence, so no general declaration is warranted.

### telescoping trace bound near an idempotent mixed transfer matrix — candidate
- **Pattern:** bound `‖Tr(T^M) - 1‖` for a mixed transfer matrix `T = Ψ(P)` with
  `‖T - T_∞‖ ≤ K₃ K₁ x^q`, where `T_∞ = Ψ(P_∞)` is idempotent of trace one: apply
  `norm_prod_range_sub_pow_le_of_isIdempotentElem` with `c = ‖1‖ + ‖T_∞‖`, rewrite
  `Tr(T^M) - 1` through `Matrix.traceLinearMap`, then close the chain
  `K₄ c ((1 + cδ)^M - 1) ≤ … ≤ C u e^{C u}` with `one_add_pow_sub_one_le_mul_exp`.
- **Seen:** two occurrences across two files (2026-09-30):
  `exists_norm_trace_prod_range_transferMatrix_sub_one_le` in
  `TNLean/MPS/Preparation/ApproximationError.lean` and
  `exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le` in
  `TNLean/MPS/Preparation/OverlappingBlockOverlap.lean` (2026-10-01: there `T_∞ = t R` with
  `R` idempotent, through `norm_prod_range_sub_pow_le_of_forall_norm_pow_le`).
- **Notes:** a third occurrence would justify a lemma taking the power-bounded `T_∞`,
  its trace, and the linear bound `‖T - T_∞‖ ≤ δ` as hypotheses.

### off-diagonal constants chosen with a dummy diagonal value — candidate
- **Pattern:** `have hoff : ∀ j k, ∃ K, 0 ≤ K ∧ (j ≠ k → ∀ n, ‖f j k n‖ ≤ K * x ^ n)`,
  proved by `by_cases j = k` with `⟨0, le_rfl, …⟩` on the diagonal, then `choose`, and
  a split `∑ⱼ ∑ₖ = ∑ⱼ (diagonal + ∑_{k ∈ univ.erase j})` by `Finset.add_sum_erase`.
- **Seen:** two occurrences across two files (2026-09-30):
  `exists_norm_gram_blockTensor_blockSum_sub_le` in
  `TNLean/MPS/Preparation/OverlappingBlockGram.lean` and
  `exists_abs_norm_mpvState_blockSum_weight_sq_sub_le` in
  `TNLean/MPS/Preparation/OverlappingBlockOverlap.lean`.

### second-order trace bound for an element compressed by an idempotent — candidate
- **Pattern:** for `T` with `e T e = α e`, `e` idempotent of trace one, `‖T - e‖ ≤ δ` and
  `1 - α` (or `1 - ‖α‖`) at most a multiple of `δ²`: put `Z = α⁻¹ T - e`, prove `e Z e = 0`,
  `T = α (e + Z)` and `‖Z‖ ≤ c₄ δ`, bound the blocks of `Z` by `z = c₅ (c₄ δ) c₅` with
  `c₅ = ‖e‖ + ‖1 - e‖`, apply `IsIdempotentElem.norm_trace_add_pow_sub_le_of_le`, and absorb
  `α^M` through `one_add_mul_le_pow`, with constants `zc = c₅⁴ c₄²` and
  `E₀ = K (‖e‖ + 3 ‖1 - e‖)`.
- **Seen:** two occurrences across two files (2026-10-02):
  `exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq` in
  `TNLean/MPS/Preparation/SecondOrderOverlap.lean` (complex `α`, conclusion on
  `1 - ‖tr T^M‖`) and `IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq` in
  `TNLean/Algebra/IdempotentTracePerturbation.lean` (real `α ≤ 1`, conclusion on
  `‖tr T^M - 1‖`).
- **Notes:** the second is the abstracted form for real `α`. Generalizing it to complex `α`
  with `‖α‖ ≤ 1`, `1 - ‖α‖ ≤ δ²` and `‖1 - α‖ ≤ δ`, concluding on `1 - ‖tr T^M‖`, would let
  the normal case call it and remove the first copy.

### Adjoint reversal of an orthogonal-projector error — candidate
- **Pattern:** replace the norm of a projector product minus a self-adjoint
  projector by the norm of its adjoint, reverse the product, and reverse the
  sign of the difference.
- **Occurrences:** `norm_projector_defect_adjoint` in
  `TNLean/MPS/ParentHamiltonian/BlockIntervalDefectDecay.lean` and
  `norm_projection_difference` in
  `TNLean/MPS/ParentHamiltonian/Martingale/WholeIncrementSpectatorTransport.lean`.
- **Count:** two occurrences across two files. The second also removes a
  nested projection using subspace containment. If another use appears,
  separate the common adjoint identity into a submodule helper theorem.

### Spectator ranges of block sums — factored
- **Pattern:** identify a spectator boundary map as a coordinate map composed
  with the pointwise extension of the local boundary map, then distribute its
  range over a sum of local ground spaces.
- **Seen:** the left and tail boundary ranges in
  `TNLean/MPS/ParentHamiltonian/BlockSumIntervalSpaces.lean`.
- **Abstraction:** the private `pi_univ_iSup_const` lemma follows from Mathlib's
  `Submodule.iSup_map_single`, `Submodule.map_iSup`, and `iSup_comm`.
  Both range calculations use `LinearMap.range_compLeft`; the Hilbert-space
  statements follow by mapping the same submodule identities.
- **Notes:** two occurrences in one file. No new tactic or general simp set is
  needed; promote the submodule lemma only if another file needs it.


### Uniform decay of whole-increment block errors — factored
- **Pattern:** combine the geometric FNW estimate with the vanishing rational
  coefficient, then choose a common overlap length independently of the two
  exterior intervals.
- **Occurrences:** the single-block numerical threshold in `C3Threshold.lean`
  and the finite-block decay argument.
- **Status:** `IsPrimitiveMPS.eventually_wholeIncrement_groundProjection_defect_le`
  states the uniform estimate once. Finite-family assembly distributes the
  requested tolerance among the overlap correction and the individual blocks;
  no new tactic is needed.

### Preserving overlap bounds under finite orthogonal sums — promoted
- **Pattern:** expand the inner product over fixed spectator configurations,
  apply the pointwise overlap bound, and finish with finite Cauchy–Schwarz.
- **Occurrences:** the two nested restrictions to a middle interval in
  `TNLean/MPS/ParentHamiltonian/SpectatorOverlap.lean`, and the aggregate
  estimate `norm_inner_overlap_sub_inner_aggregates_le` in
  `TNLean/MPS/ParentHamiltonian/FNWOverlapEstimate.lean`, which ran the same
  chain `norm_sum_le`, `Finset.sum_le_sum`, `Finset.mul_sum`,
  `Real.sum_mul_le_sqrt_mul_sqrt` over the spectator configurations.
- **Abstraction:** `Finset.norm_sum_le_mul_sqrt_mul_sqrt` in
  `TNLean/Algebra/FinsetNormSumCauchySchwarz.lean`: termwise bounds
  `‖z i‖ ≤ c * a i * b i` with `0 ≤ c` give
  `‖∑ i ∈ s, z i‖ ≤ c * (√(∑ a i ^ 2) * √(∑ b i ^ 2))`.
- **Status:** promoted; the fiber bound in `SpectatorOverlap.lean` and the
  FNW aggregate estimate both close with it. The transport along a
  configuration equivalence stays private in `SpectatorOverlap.lean`, and the
  three-interval evaluation of the right boundary map is shared with
  `FNWProjectorDefect.lean` through `SpectatorBoundaryCoordinates.lean`.

### Lower Gram bounds and off-diagonal pairings — locally factored
- **Pattern:** turn a lower Gram bound into an upper bound on the Euclidean
  norm of the component norms, then apply a bilinear matrix estimate.
- **Occurrences:** three uses of `norm_norms_le_of_lower_bound` in
  `TNLean/MPS/ParentHamiltonian/BlockSubspaceOverlap.lean`.
- **Status:** factored into a private lemma. The two projector-pairing
  expansions in `BlockProjectorSum.lean` likewise share private lemmas
  for removing the diagonal and bounding the remaining finite sum.
  No new tactic is needed.

### diagonal bond similarity with nowhere-zero entries — candidate
- **Pattern:**
  ```lean
  have hGH : Matrix.diagonal g * Matrix.diagonal g⁻¹ = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext p
    exact mul_inv_cancel₀ (hg p)
  have hHG : Matrix.diagonal g⁻¹ * Matrix.diagonal g = 1 := by
    ...
  exact MPOTensor.mpo_eq_of_conj hGH hHG hconj L
  ```
- **Seen:** four occurrences in `TNLean/MPS/Examples/Fibonacci/FibonacciGSymbol.lean`
  (`mpo_fibStringNetEdgeTau`, `mpo_fibStringNetTensor`, `mpo_fibReviewTensor`, and the
  configuration-space variant in `isMPOFusionAlgebra_fibReviewWeightedTensor`), found in review
  before merge; the first three already call `mpo_eq_of_diagonal_conj`.
- **Status:** four occurrences in one file; the rule of three needs a second file before promotion. The helper lemmas below already live in a general module, per the reuse rule, and are the target once a second file needs them.
- **Abstraction (available):** `Matrix.diagonal_mul_diagonal_inv`, `Matrix.diagonal_inv_mul_diagonal` and
  `MPOTensor.mpo_eq_of_diagonal_conj` in `TNLean/MPS/MPDO/BondSimilarity.lean`.
- **Notes:** `mpo_eq_of_diagonal_conj g hg hconj L` takes a nowhere-zero `g` and the letterwise
  identity `diag g * M i j * diag g⁻¹ = N i j`; the two `Matrix` lemmas cover diagonal
  inverses on any index type, such as the configuration space of a fusion-rule transfer.


### Wielandt block-injectivity length below the uniform square bound — candidate
- **Pattern:**
  ```lean
  calc (dim k ^ 2 - Kraus.krausRank K + 1) * dim k ^ 2
      ≤ (D ^ 2 + 1) * D ^ 2 := Nat.mul_le_mul (by omega) hd
    _ ≤ (D ^ 2 + 1) ^ 2 := by nlinarith
  ```
- **Seen:** 2 occurrences (`TNLean/MPS/Examples/WStateCanonicalBound.lean:376`,
  `TNLean/MPS/Examples/WStatePrimeLengthBound.lean:149`).
- **Abstraction:** proposed lemma bounding the Wielandt length
  `(m ^ 2 - r + 1) * m ^ 2 ≤ (D ^ 2 + 1) ^ 2` for `m ≤ D`, stated over `ℕ`.
- **Notes:** promote at a third occurrence, for example a reduction at composite length.

### Decomposing membership in a finite sum of subspaces — promoted
- **Pattern:** obtain vectors in the individual subspaces from membership in
  their finite supremum using `Submodule.mem_iSup_finset_iff_exists_sum`, then
  apply a norm or inner-product estimate to their sum.
- **Occurrences:** three proofs across two files:
  `Submodule.norm_inner_le_iSup_of_overlapMatrix` and
  `Submodule.iSup_overlap_bound_of_uniform`
  (`TNLean/MPS/ParentHamiltonian/BlockSubspaceOverlap.lean`), and the
  private lemma `norm_inner_sum_starProjection_sub_le` in
  `TNLean/MPS/ParentHamiltonian/BlockProjectorSum.lean`.
- **Abstraction:** `Submodule.exists_sum_eq_of_mem_iSup` in
  `TNLean/MPS/ParentHamiltonian/BlockSubspaceOverlap.lean` turns
  `u ∈ ⨆ i, V i` over a finite index type into a family `v : ∀ i, V i` with
  `∑ i, (v i : M) = u`, absorbing the `(s := Finset.univ)` instantiation and
  the `simpa` coercion from the indexed supremum.
- **Status:** promoted; all three call sites now read
  `obtain ⟨v, rfl⟩ := exists_sum_eq_of_mem_iSup V hu`.

### carrying a boundary through one Kronecker factor of a letter sum — candidate
- **Pattern:** unfold `kronId`/`idKron`, collapse the boundary into the index space of the
  `finProdFinEquiv` submatrix with `Matrix.submatrix_mul_equiv` (twice), distribute with
  `Matrix.mul_sum`/`Matrix.sum_mul`, then `congr 1`, `Finset.sum_congr rfl`, and push the
  boundary onto one factor with `← Matrix.mul_kronecker_mul` (twice) and
  `Matrix.one_mul`/`Matrix.mul_one`.
- **Seen:** six occurrences across three files: `MPSTensor.IsReduction.mulTensor_kronId` and
  `mulTensor_idKron` (`TNLean/MPS/Core/ReductionComposition.lean`),
  `MPOTensor.mulTensor_mul_kronId_of_intertwine` (`TNLean/MPS/MPDO/OperatorProduct.lean`),
  and `MPSTensor.IsReduction.actTensor_idKron`, `actTensor_kronId` and
  `MPOTensor.actTensor_mul_kronId_of_intertwine`
  (`TNLean/MPS/MPDO/ActionTensorReduction.lean`).
- **Abstraction:** a lemma stating
  `(X ⊗ 1) * (∑ j, A j ⊗ B j) * (Y ⊗ 1) = ∑ j, (X * A j * Y) ⊗ B j` and its `1 ⊗ X`
  mirror, in the `finProdFinEquiv` bond order; the intertwiner lemmas are the cases
  `Y = 1` and `X = 1`.
- **Notes:** past the rule of three. Promotion rewrites the three call sites in
  `ReductionComposition.lean` and `OperatorProduct.lean` as well, so it is left to a
  separate refactor rather than folded into the action-tensor PR.

### classical choice of a nonzero proportionality scalar — candidate
- **Pattern:**
  ```lean
  if hz : ∃ z : ℂ, z ≠ 0 ∧ MPSTensor.IsDressedProportional B X Y z
  then Units.mk0 hz.choose hz.choose_spec.1 else 1
  ```
- **Seen:** three occurrences across two files: `FusionData.omega` (through
  `IsAssociator`) and `FusionData.relativeScalar`
  (`TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`), and `ActionData.lSymbol`
  (`TNLean/MPS/Symmetry/MPOSymmetry/AnomalyObstruction.lean`).
- **Abstraction:** a definition
  `MPSTensor.IsDressedProportional.chooseScalar B X Y : Units ℂ` with the lemma that it
  satisfies the relation whenever some nonzero scalar does; `omega`, `relativeScalar`
  and `lSymbol` then specialize it.
- **Notes:** at the rule of three. Promotion changes the definitions of `omega` and
  `relativeScalar` on `main` and the lemmas that unfold them, so it needs a Lean build and
  is left to a separate refactor.

### reassociating a triple Kronecker sum by `mulTensorAssocEquiv` — candidate
- **Pattern:** four `finProdFinEquiv.surjective` peels on the row and column indices, the
  three-stage `simp only` with `mulTensorAssocEquiv`, `Equiv.prodAssoc_apply`,
  `Matrix.kroneckerMap_apply`, `Matrix.sum_apply`, `Matrix.kronecker_apply`, then
  `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_comm`, and `mul_assoc` under
  `Finset.sum_congr`.
- **Seen:** two occurrences: `MPOTensor.mulTensor_assoc`
  (`TNLean/MPS/MPDO/OperatorProduct.lean`) and `MPOTensor.actTensor_mulTensor`
  (`TNLean/MPS/MPDO/ActionTensorReduction.lean`).
- **Abstraction:** a lemma stating that
  `(∑ j, (∑ m, X m ⊗ Y m j).submatrix e e ⊗ Z j)` is the `mulTensorAssocEquiv`-reindex of
  `∑ m, X m ⊗ (∑ j, Y m j ⊗ Z j).submatrix e e`, for arbitrary families of matrices.
- **Notes:** below the rule of three; promote on the next occurrence.

Seeded from `scripts/tactic_pattern_scan.py` (2026-07-18 scan; re-run for
current counts and full location lists).

### ambient left-canonical normalization from a unique full-support MPU block — candidate
- **Pattern:** from the shifted transfer-trace identity, obtain the sole
  canonical-form-II block and its unit-modulus weight; use full support to make
  the block inclusion unitary, then transport the block's left-canonical sum
  through the intertwining relation to the ambient tensor.
- **Seen:** two occurrences across two files (2026-09-26): the local
  `hweightedLeft`/`hAleft` argument in
  `TNLean/MPS/MPU/TransferStabilization.lean` and
  `IsMPUCanonicalFormII.isLeftCanonical_normalizedFlattening` in
  `TNLean/MPS/MPU/VirtualUnitaryGauge.lean`.
- **Abstraction:** the new public theorem
  `IsMPUCanonicalFormII.isLeftCanonical_normalizedFlattening` is reusable for
  full-support canonical-form-II data. A later refactor can replace the local
  argument in `TransferStabilization.lean` once its supplied CFII data are
  presented in that theorem's type.
- **Notes:** the existing transfer-stabilization theorem requires `1 < D`, so
  it cannot establish ambient left canonicity for the general positive-bond
  case. The virtual-gauge proof uses no such extra dimension hypothesis. Two
  occurrences do not yet meet the three-occurrence promotion threshold for a
  further generic block-inclusion abstraction.

### integer-matrix verification of an explicit compression datum — promoted
- **Pattern:** define every matrix of a worked example as the entrywise
  coercion of an integer matrix, push the coercion through the bond-space
  product and through conjugation by the gauge, and discharge the resulting
  finite identity with `decide` on integer matrices.

  ```lean
  rw [gauge_def, conjMatrix_gaugeOfMatrix, tensor_eq, ← complexOfInt_mul,
    ← complexOfInt_mul, conj_int]
  ```
- **Seen:** three occurrences across three files (2026-09-17):
  `CZXCompression.czxSquare_eq` in
  `TNLean/MPS/Examples/CZX/CZXTensor.lean`,
  `CZXCompression.czxSquare_conjMatrix` in
  `TNLean/MPS/Examples/CZX/CZXSquare.lean`, and
  `CZXCompression.czxPlusIdentity_conjMatrix` in
  `TNLean/MPS/Examples/CZX/CZXPlusIdentity.lean`.
- **Abstraction:** the entrywise image `MPSTensor.complexOfRing` along a ring
  homomorphism into the complex numbers, with `complexOfRing_mul`,
  `complexOfRing_one` and `complexOfRing_neg` in
  `TNLean/Algebra/ComplexOfRing.lean`, whose instantiation at the integer cast
  is the coercion `MPSTensor.complexOfInt` of
  `TNLean/Algebra/ComplexOfInt.lean` with its one-line `complexOfInt_mul`,
  `complexOfInt_one` and `complexOfInt_neg`, together with
  `MPSTensor.gaugeOfMatrix` and `MPSTensor.conjMatrix_gaugeOfMatrix` in
  `TNLean/MPS/FundamentalTheorem/Reduction/ExplicitGauge.lean`.
- **Notes:** the payoff is that block triangularity, the matched diagonal
  blocks and the vanishing zero blocks of a nine-dimensional example all become
  decidable statements about integer matrices, verified in seconds; without the
  coercion the same checks are complex-number `simp` calls over several
  thousand products. The image is stated for arbitrary index types so that
  rectangular gauge rows and columns are covered as well, and for an arbitrary
  ring so that the exact arithmetic of an example in `ℤ√2`, `ℤ[σ]` or `ℤ[ω]`
  uses the same lemmas as the integer examples.

### nested finite-sum binder permutation — promoted
- **Pattern:** permute the binders of three to five nested finite sums over
  `Finset.univ` by folding them into one sum over an iterated product type,
  transporting along an explicit component permutation with
  `Fintype.sum_equiv`, and unfolding again with `Fintype.sum_prod_type`.
- **Seen:** five used private helpers and one unused helper across
  `TNLean/MPS/MPU/SourceUCompleteNetwork.lean`,
  `TNLean/MPS/MPU/SourceVCompleteNetwork.lean`, and the range-transport module
  deleted on 2026-09-04 (recorded 2026-09-03).
- **Abstraction:** the `Fintype.sum_reverse_three`,
  `Fintype.sum_last_two_first_four`, `Fintype.sum_last_first_four`,
  `Fintype.sum_last_two_first_five`, and `Fintype.sum_permute_five` helper
  theorems in `TNLean/Algebra/FinSumPermutation.lean`.
- **Notes:** the four surviving call sites use the shared results, and the
  unused sixth private helper was removed. Specific theorem statements are the
  lowest sufficient abstraction for the permutations needed; no elaborator
  tactic or arity-indexed framework is introduced. After the 2026-09-04
  mixed-kernel deletion `Fintype.sum_last_two_first_five` has no remaining call
  site.

### cycle-edge virtual-configuration sum reindexing — candidate
- **Pattern:** identify assignments on the edges of a cycle with assignments
  indexed by its sites using `cycleEdgeEquiv`, then, when a cyclic product is
  required, rotate the site-indexed assignment by one step so that the two
  incident virtual indices become `g v` and `g (v + 1)`.
- **Seen:** the site-to-edge reindexing occurs in
  `Tensor.stateCoeff_reindexMPSChain` in
  `TNLean/PEPS/CycleMPSConstantDescription.lean`,
  `stateCoeff_cycleTensorOfMPS` in `TNLean/PEPS/CycleMPSTensor.lean`, and the
  blocked-region calculation in `TNLean/PEPS/CycleMPSInjectivity.lean`
  (2026-08-31). The subsequent one-step rotation occurs in the first two of
  these proofs.
- **Abstraction (proposed):** if a third proof needs the full two-stage
  reindexing, extract a cycle-graph sum lemma parameterized by the local
  factor. Keep the factor-specific incident-edge and blocked-arc identities
  at their call sites.
- **Notes:** `Fintype.sum_equiv` already owns the common first stage; its three
  remaining congruence obligations have different mathematical content. The
  exact two-stage proof occurs twice, so it remains below the promotion
  threshold rather than introducing a wrapper around the existing finite-sum
  equivalence.

### one-site blocking by canonical physical reindexing — candidate
- **Pattern:** identify the doubled physical alphabet after one-site blocking
  with the original doubled alphabet, prove that blocking is the resulting
  physical relabeling, and reindex the diagonal physical-trace sum to preserve
  each representative's transfer matrix.
- **Seen:** 2 occurrences: the general implication
  `MPOTensor.IsSimpleCanonicalForm.isSimple` in
  `TNLean/MPS/MPDO/Simple.lean` and the four-letter specialization
  `MPOTensor.RescalingStableLengthDependentRFP.R_isSimple` in
  `TNLean/MPS/MPDO/RescalingStableSimple.lean` (post-merge review of PR #7533,
  2026-08-31).
- **Abstraction (proposed):** if a third occurrence appears, extract the
  dimension-parametric one-site doubled equivalence together with lemmas for
  the blocked-tensor relabeling and invariance of the doubled physical-trace
  transfer. Specialize the existing proofs to those lemmas.
- **Notes:** below the rule-of-three promotion threshold. Do not add a one-use
  wrapper or duplicate predicate surface merely to merge these two proofs.

### supplied paper-gate indicator entries — completed refactor
- **Pattern:** multiply two source-entry indicator functions, combine their
  two pairs of physical-index equalities, and cancel the shift normalization.
- **Seen:** six paper-gate entry proofs in
  `TNLean/MPS/MPU/Examples/ShiftSourceGateFormulas.lean` and the two four-spin
  matrix entry proofs in
  `TNLean/MPS/MPU/Examples/ShiftSourceFactors.lean` (recounted 2026-09-04 after
  deleting the mixed-kernel examples).
- **Abstraction:** Mathlib's `ite_zero_mul_ite_zero` combines the two indicator
  factors into one conjunction.  The source-specific scalar identities
  `shiftSourceScale_square_cancel` and
  `shiftSourceScale_inv_square_cancel` record the two remaining normalization
  calculations.
- **Result:** all eight proofs use `ite_zero_mul_ite_zero`; the six gate proofs
  reuse the scalar lemmas, and no four-equality case-split chain remains.  The
  different paper-coordinate permutations stay visible at the call sites.

### factor pairing under a two-index finite sum — candidate
- **Pattern:** before collapsing a two-index finite sum, use `simp_rw` with a
  pointwise identity proved by `ring` to pair corresponding scalar factors from
  two products, then factor the independent index sums.
- **Seen:** three occurrences in the private proofs `VFour_collapse_one`,
  `VThree_collapse_one`, and `VTwo_collapse_one` in
  `TNLean/MPS/MPDO/CPSVExample410Spectrum.lean` (2026-08-23).
- **Abstraction:** a possible file-local lemma that combines the pointwise ring
  rearrangement with `sum_two_four_factors` for products of varying lengths.
- **Notes:** the three products have different numbers and kinds of factors, so
  the shared finite-sum factorization is generic while the ring identities stay
  explicit. No occurrence in a second file is known, so this remains below the
  promotion threshold.

### transport of diagonal spectral identities — candidate
- **Pattern:** diagonalize a Hermitian matrix as a unitary conjugate of its
  eigenvalue diagonal, prove a scalar or polynomial identity on that diagonal,
  and transport the identity back through the conjugation algebra
  automorphism.
- **Seen:** three occurrences in
  `TNLean/Algebra/HermitianTracePower.lean` and
  `TNLean/Algebra/TracePurity.lean` (two occurrences), recorded 2026-08-21.
- **Abstraction:** a proposed Hermitian spectral-transport lemma exposing the
  diagonalization equality and preserving polynomial identities through the
  conjugation algebra automorphism.
- **Notes:** the three conclusions differ: a trace-power formula, scalarity
  from constant eigenvalues, and idempotency from idempotent eigenvalues. A
  useful abstraction should remove the repeated diagonalization argument
  without hiding these distinct mathematical steps.

### projector-selected sector closure assembly — candidate
- **Pattern:** expand a closure as a finite sum of sector closures, distribute
  a projector-controlled sum of linear maps over it, use the orthogonal
  selector identity to retain the matching sector, and finish with the
  sectorwise closure equation.
- **Seen:** four call sites in
  `TNLean/MPS/MPDO/BNTChannelComposition.lean`, one coarse-graining/refinement
  pair in each of `exists_chainCoordinateRFP_of_projectiveSectorDecomposition`
  and `exists_chainCoordinateRFP_of_orthogonalSectorDecomposition`
  (2026-08-20).
- **Abstraction (file-local):** the private theorem
  `sum_comp_singleKrausMap_firstSiteMatrix_properties` (lines 445--513)
  extracts all four copies. It is parametrized by `n` and `m`, corresponding
  to input and output chain lengths `n + 1` and `m + 1`, the sectorwise maps
  `F`, and their closure equation.
- **Notes:** all call sites remain in one file, and no further occurrences are
  identified, so the pattern remains below the promotion threshold. The
  parameters `n` and `m` retain the opposite matrix orientations of the
  coarse-graining and refinement maps explicitly.

### explicit finite-generator word-tuple spanning — candidate
- **Pattern:** unfold `MPSTensor.WordTupleSpanTop`, place one or more explicit
  word tuples in the span by `Submodule.subset_span`, express an arbitrary
  block tuple as their scalar linear combination, and conclude by closure
  under scalar multiplication and addition.
- **Seen:** two direct occurrences: `sectors_wordTupleSpanTop_one` in
  `TNLean/MPS/MPDO/CaseIIAbsorptionCounterexample.lean` and
  `scalarBNT_wordTupleSpanTop` in
  `TNLean/MPS/MPDO/Theorem49RepeatedCopyCounterexample.lean`, together with
  the related finite-generator reconstruction in
  `TNLean/MPS/MPDO/ActiveSectorSpanningCounterexample.lean`
  (`sectorMatrix_span_eq_top`) (2026-08-20).
- **Abstraction (proposed):** first determine whether a small finite-generator
  span criterion can cover both dependent block tuples and ordinary matrix
  families without requiring application-specific coefficient functions.
- **Notes:** the two word-tuple proofs use different numbers of generators,
  while the related matrix proof has a different codomain. Record the common
  reconstruction pattern now; retain the explicit proofs until another
  direct word-tuple occurrence identifies a materially smaller theorem.

### rational negMulLog prime-logarithm expansion — candidate
- **Pattern:** rewrite `Real.negMulLog (a / b)` for an explicit rational into a
  linear combination of logarithms of small primes: unfold `negMulLog`, split
  the quotient with `Real.log_div`, express `b` (and composite `a`) as prime
  powers, apply `Real.log_pow`/`Real.log_mul`, then `push_cast` and `ring`.
- **Seen:** eight private lemmas in
  `TNLean/MPS/MPDO/CPSVExample410CorrelatedFlip.lean`
  (`negMulLog_quarter` through `negMulLog_nine_128ths`) (2026-08-21).
- **Abstraction (proposed):** one lemma computing
  `negMulLog ((a : ℝ) / 2 ^ k)` from the prime factorization of `a`, or a
  small simp set bundling `negMulLog`, `Real.log_div`, `Real.log_pow`, and
  `Real.log_mul` with the needed positivity side conditions.
- **Notes:** all occurrences are presently in one file, below the two-file
  promotion threshold. The sibling exact-entropy statements in
  `TNLean/MPS/MPDO/CPSVExample411Entropy.lean` keep `negMulLog` values
  unexpanded, so no second file uses the pattern yet.

### Hermitian extraction from a finite-order channel eigenvector — candidate
- **Pattern:** from `E X = μ • X`, `X ≠ 0`, `μ ≠ 1`, and `μ ^ p = 1`,
  use trace preservation and the Hermitian parts `X + Xᴴ` and
  `Complex.I • (Xᴴ - X)` to obtain a nonzero Hermitian trace-zero fixed point
  of `E ^ p`.
- **Seen:** 2 occurrences before compatibility reduction (2026-08-20):
  `Kraus.exists_hermitian_ne_zero_trace_zero_pow_fixedPoint` and
  `MPSTensor.exists_hermitian_ne_zero_trace_zero_pow_fixedPoint`.
- **Abstraction (proposed):** retain the channel-native Kraus theorem as the
  proof owner; the transfer-map statement is definitionally the same and adds only the positive-semidefinite
  consequence required by its established conclusion.
- **Notes:** the generic theorem keeps the Hermitian-part construction private.
  The compatibility reduction should preserve the public MPS statement while
  removing its second implementation.

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

### concrete numeric gauge with an explicit inverse — candidate
- **Pattern:** a concrete invertible numeric matrix is packaged as an element of
  `GL n ℂ` through `Matrix.GeneralLinearGroup.mkOfDetNeZero`, after which the
  inverse coordinate is recovered by building a second `mkOfDetNeZero` for the
  inverse, proving the product is one through `Units.ext`, and rewriting with
  `inv_eq_of_mul_eq_one_right`.
- **Seen:** 2 occurrences (2026-09-19), in
  `TNLean/MPS/MPDO/BondTwoSingletonGramBoundary.lean` and
  `TNLean/MPS/MPDO/PositiveMinimalRealizationCounterexample.lean`; both now use
  the structure form below.  Seven further `mkOfDetNeZero` gauges in
  `TNLean/MPS/Examples/` keep their present form, where the saving is at most one
  or two lines.
- **Abstraction (proposed):** no new declaration is needed.  Supply the inverse
  directly, `where val := M; inv := N; val_inv := h; inv_val := mul_eq_one_comm.mp h`,
  after which both coordinate lemmas are `rfl` and no determinant lemma is
  required.
- **Notes:** scoped to concrete numeric gauges.  Where the matrix is abstract and
  only its determinant is known, as in the renormalization fixed-point modules,
  `mkOfDetNeZero` remains the only available construction.

### diagonal normalized-ancilla sum collapse — candidate
- **Pattern:** collapse the doubled sum for `normalizedDiagonalLift` by using
  `Finset.sum_eq_single` to retain the diagonal ancilla letter `(a, a)`, then
  cancel the resulting normalization with
  `(x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1` for `0 < x`,
  closed by `Complex.ofReal_sqrt_inv_mul_self` since 2026-09-23.
- **Seen:** 2 occurrences in `TNLean/MPS/MPU/PhysicalAncilla.lean`:
  `MPOTensor.transferMap_normalizedDiagonalLift` (lines 160--182), for
  `A ij * X * (A ij)ᴴ`, and
  `MPOTensor.leftCanonical_normalizedDiagonalLift` (lines 224--245), for
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
  `QICLean/Analysis/TraceNormContractivity.lean` (QICLean dependency) isolates the shared
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
  `QICLean/Channel/Schwarz/OperatorJensenAux.lean`:
  `positiveMap_rpowIntegrand₀₁_jensen` and
  `positiveMap_rpowIntegrand₁₂_jensen`.
- **Abstraction:** a shared algebraic lemma parameterized by the exponent
  identities for the concave and convex integrands, if a third occurrence
  appears.
- **Notes:** Below the rule-of-three promotion threshold; keep the explicit
  rewrites until another consumer fixes the common statement's useful shape.

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
- **Seen:** 4 occurrences (`TNLean/Spectral/QuantitativeGap.lean:94`,
  `TNLean/Spectral/MPVOverlapDecayRect.lean:48`,
  `TNLean/MPS/RFP/BNTOrthogonality.lean:453`,
  `TNLean/MPS/Symmetry/StringOrderDefs.lean:230`, the last with the carrier
  spelled out instead of abbreviated).
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
- **Seen:** 2 verified occurrences in `TNLean/PEPS/`
  (`RegionBlock/UnionInjectivityGeneral.lean:492`,
  `TorusWindowChain4.lean:242`).
- **Abstraction (proposed):** a lemma of the shape
  `∑ η in s.filter p, (if p η then f η else 0) • g η = ...` — scout
  Mathlib's `Finset.sum_filter` / `Finset.sum_ite_of_true` family first.

### two_positive_bilinear_checks — candidate
- **Pattern:** alternating `· intro i / simp` and
  `· intro i u v / simp [mul_assoc, mul_add]` blocks discharging
  bilinearity side goals.
- **Seen:** 9 occurrences, all in `QICLean/Channel/Schwarz/TwoPositive.lean`
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
- **Seen:** surviving examples in `TNLean/PEPS/RegionBlock/`
  (`CoarseThreeSiteCoherentFrame.lean:381`,
  `UnionInjectivityGeneral.lean:95`, `UnionInjectivityGeneral.lean:121`).
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
  `TNLean/PEPS/NormalSquareUnconditionalFundamentalTheorem.lean:118-190` (per-edge bond-dimension equality).
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
  `QICLean/Channel/Schwarz/WeylRelativeEntropyIntegral.lean` in
  `weyl_sourceB_defect_eq_zero_of_gap_eq_zero`, and
  `QICLean/Channel/Schwarz/SupportRelativeEntropyGap.lean` in
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
  `QICLean/Channel/Schwarz/SupportLeftRightRelativeModular.lean`, in
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

### physical-slice support equality at tensor entries — candidate
- **Pattern:** pass from a matrix identity involving `physicalSlice K β α` to
  the corresponding identity of tensor-valued sums by applying the matrix
  equality at physical indices and simplifying `Matrix.mul_apply`:
  ```lean
  ext β α
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  simpa [physicalSlice, Matrix.mul_apply] using
    congrFun (congrFun (hP β α) i) j
  ```
- **Seen:** 3 occurrences in
  `TNLean/MPS/MPDO/BNTChannelComposition.lean`, in the proofs of
  `firstSiteMatrix_mul_physCloseN_of_mul_physicalSlice`,
  `firstSiteMatrix_mul_physCloseN_eq_zero_of_mul_physicalSlice_eq_zero`, and
  `physCloseN_mul_firstSiteMatrix_of_physicalSlice_mul`.
- **Abstraction (proposed):** left- and right-multiplication lemmas expressing
  the entries of a physical-slice identity as sums of scalar multiples of the
  tensor matrices. The zero conclusion should be a specialization of the left
  lemma rather than a separate argument.
- **Notes:** the three occurrences lie in one file. Promote when a second file
  needs the same entry-extraction step, choosing the weakest pair of algebraic
  lemmas that covers both multiplication orientations.

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

### closed-chain Schur factorization of a matrix product operator — candidate
- **Pattern:** prove positivity of the operator generated on a ring by an
  explicit tensor by (i) defining the cyclic bond-matching condition together
  with its rank-one indicator matrix, proved positive semidefinite as an outer
  product of the indicator vector with itself; (ii) proving an entrywise
  closed-chain formula in which the indicator multiplies a product of one-site
  factors; (iii) proving that the corresponding Kronecker power is positive
  semidefinite by induction, peeling the last site off with the
  last-coordinate equivalence and using that a Kronecker product of positive
  semidefinite matrices is positive semidefinite; and (iv) assembling with the
  Schur product theorem and a nonnegative scalar.
- **Seen:** 2 occurrences: `R_isMPDO` in
  `TNLean/MPS/MPDO/RescalingStableLengthDependentRFP.lean` and `T_isMPDO` in
  `TNLean/MPS/MPDO/TwistedDimerMPDO.lean` (2026-09-02).
- **Abstraction (proposed):** if a third such tensor appears, extract a
  positivity criterion parameterized by the local bond-matching relation and
  the local factor, and specialize the existing proofs to it.
- **Notes:** the two current instances differ in the shape of the local factor
  (a single two-by-two matrix against a sum of two four-by-four Kronecker
  powers proved positive semidefinite together with their difference), so a
  common criterion would have to abstract over that as well.  Below the
  rule-of-three promotion threshold.

### matrix-unit tensor word and closed-chain expansions — candidate
- **Pattern:** multiply a matrix-unit tensor letter into a matrix unit, induct
  along two words using the open bond-matching condition, then take the trace
  and split on the wraparound match to obtain a cyclic closed-operator entry
  formula.
- **Seen:** 2 occurrences across `TNLean/MPS/MPDO/TwistedDimerMPDO.lean`
  (`T_mul_single_sum`, `evalWord_T_ofFn`, `mpo_T_entry_formula`) and
  `TNLean/MPS/MPDO/TwistedDimerFlagSectors.lean` (`unitTensor_mul_single`,
  `evalWord_unitTensor_ofFn`, `mpo_unitTensor_apply`) (2026-09-02).
- **Abstraction (proposed):** if a third occurrence appears, extract a generic
  closed-chain formula for block-disjoint matrix-unit tensors and derive both
  existing calculations from it.
- **Notes:** the twisted-dimer tensor sums over two block labels, whereas a flag
  sector has one matrix unit per letter. A shared statement must retain this
  distinction rather than identifying the two tensor shapes. Below the
  rule-of-three promotion threshold.

### trace-one ambient block fixed matrix — candidate
- **Pattern:** from canonical-form-II data with one retained block and full
  support, rescale the block's diagonal positive fixed matrix to trace one,
  use the unit weight forced by the shifted transfer traces, and transport the
  rescaled matrix along the ambient block inclusion to a positive trace-one
  right fixed matrix of the ambient transfer map.
- **Seen:** two occurrences,
  `TNLean/MPS/MPU/TransferStabilization.lean` (the stabilized-power theorem)
  and `TNLean/MPS/MPU/ReducedCanonicalRepresentative.lean` (the reduced
  representative in the ambient diagonal gauge), recorded 2026-09-04.
- **Abstraction:** proposed lemma on canonical-form-II data producing the
  normalized block matrix together with its weighted-block fixed-point
  equation, leaving each call site to choose the ambient coordinates.
- **Notes:** below the promotion threshold at two occurrences. The two call
  sites differ in their conclusion: one keeps the original ambient
  coordinates and therefore cannot assert diagonality, while the other
  changes gauge to the block coordinates and can. Only the shared normalized
  block matrix and its fixed-point equation should be factored out.

---

### scalar multiple preserves block injectivity — candidate
- **Pattern:** rewrite `Kraus.IsNBlkInjective` as `wordSpan = ⊤`, run
  `Submodule.span_induction` on a matrix of the original span, and absorb the
  scalar `z ^ N` of `Kraus.evalWord_smul` with `inv_smul_smul₀`.
- **Seen:** 2 occurrences across 2 files: the private
  `isNBlkInjective_smul_of_ne` in
  `TNLean/MPS/Periodic/Overlap/SectorMatch/Basic.lean` and
  `MPSTensor.isNBlkInjective_smul` in
  `TNLean/MPS/CanonicalForm/TranslationInvariantUniqueness.lean`
  (recorded 2026-09-05).
- **Abstraction:** one public theorem next to
  `MPSTensor.isNBlkInjective_of_gaugeEquiv` in `TNLean/MPS/Defs.lean`, with
  `isNormal_smul` as its normality corollary; both call sites then drop their
  local copies.
- **Notes:** below the rule of three. The promotion was deferred because a
  change to `TNLean/MPS/Defs.lean` rebuilds the whole library; do it in a
  dedicated cleanup.

### rectangular reduction from local compression data — candidate
- **Pattern:** prove `MPSTensor.IsReduction B A V W` by
  `refine ⟨hVW, fun w ↦ ?_⟩` followed by `induction w` with `nil`, singleton,
  and `cons i (cons j w)` cases, the last one rewriting `B i * W * V * B j`
  to `B i * B j` and then splitting the caps off the two factors.
- **Seen:** one occurrence, in `MPOTensor.CZX.fusion_isReduction`
  (`TNLean/MPS/MPDO/CZXFusionTensors.lean`), recorded 2026-09-07.
- **Abstraction:** `MPSTensor.IsReduction.of_local_compression` in
  `TNLean/MPS/Core/Reduction.lean`, taking `V * W = 1`, per-letter
  compression, and the two-letter reinsertion identity.
- **Notes:** below the rule of three, but the abstraction now sits beside the
  definition it constructs, so a second local-compression reduction reuses it
  instead of repeating the word induction.
  `MPOTensor.CZX.dressedAction_isReduction`
  (`TNLean/MPS/MPDO/CZXActionTensors.lean`) is not an occurrence: it obtains
  the all-word equation by absorbing the dressing into a nonempty acted word,
  not from per-letter data.

### periodic vector of a doubled-index view at an arbitrary pair letter — candidate
- **Pattern:** rewrite a periodic vector of `MPOTensor.toMPSTensor` at an arbitrary
  configuration of the pair alphabet into a matrix entry of the periodic operator, by first
  proving `(fun n => finProdFinEquiv ((ρ n).divNat, (ρ n).modNat)) = ρ` and then rewriting with
  `MPSTensor.mpv_toMPSTensor_pairConfig`.
- **Seen:** `MPOTensor.GroupFamily.IsRepresentation.sameMPV₂Pos_mulTensor` in
  `TNLean/MPS/MPU/GroupRepresentation.lean`, `TNLean/MPS/MPU/DaggerInverse.lean`,
  `TNLean/MPS/MPU/ReducedCanonicalRepresentative.lean`,
  `TNLean/MPS/MPDO/NormalizedMPOProportionality.lean`,
  `TNLean/MPS/MPDO/BNTLayerOrthogonality.lean`,
  `TNLean/MPS/MPDO/FixedBondProductTensor.lean` (recorded 2026-09-17).
- **Abstraction:** `MPOTensor.mpv_toMPSTensor` in
  `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`, which states the identity for an
  arbitrary pair configuration and needs no auxiliary equality of configurations.
- **Notes:** above the rule of three, but the existing call sites all sit upstream of the
  module where the general statement is first needed. Promoting means moving the statement
  beside `MPOTensor.toMPSTensor` in `TNLean/MPS/MPDO/Defs.lean` and refactoring the six sites;
  that rebuild is large enough to deserve its own change.

### canonical form of normalized one-dimensional blocks — candidate
- **Pattern:** certify `IsBNTCanonicalForm` for a `SectorDecomposition` whose blocks are
  normalized tensors of bond dimension one with unit weights: linear independence of the block
  states from `mpv_of_dim_one` evaluated on constant words, `basis_distinct` by
  `not_gaugePhaseEquiv_of_dim_one` after a `cast_eq`, then `totalDim_*`, bijectivity of the
  copy coordinates by `sigma_eq_of_copyCoord_eq`, the ordering `(Equiv.ofBijective _ _).symm`,
  and `reindex_toTensor_*` by `toTensor_copyCoord` / `toTensor_copyCoord_of_ne`.
- **Seen:** 2 occurrences, `TNLean/MPS/Preparation/RepeatedBlockCounterexample.lean` and
  `TNLean/MPS/Preparation/OverlappingBlockCounterexample.lean` (recorded 2026-09-27).
- **Abstraction:** proposed lemma giving `IsBNTCanonicalForm` for a sector decomposition of
  normalized one-dimensional blocks with unit weights whose letters are pairwise distinguished
  by their zero patterns.
- **Notes:** below the rule of three; the two copies differ only in the literals.

### parent interaction from an explicit symmetric idempotent — candidate
- **Pattern:** identify a spin-chain local term, shifted and rescaled, with
  `parentInteraction A n`: prove a coordinate formula by `fin_cases` over the window,
  deduce from it that the operator is symmetric for the \(\ell^2\) pairing and idempotent
  (both by `ring` on the coordinates), match its kernel with `groundSpace A n` through the
  explicit constraint characterization, and close with
  `Submodule.eq_starProjection_of_mem_orthogonal` and `inner_withLpLinearEquiv_symm`.
- **Seen:** `MPSTensor.majumdarGhoshTerm_shift_eq_parentInteraction`
  (`TNLean/MPS/Examples/MajumdarGhoshLowerBound.lean`) and
  `MPSTensor.akltBondTerm_shift_eq_parentInteraction`
  (`TNLean/MPS/Examples/AKLTPolynomialHamiltonian.lean`) (recorded 2026-09-27).
- **Abstraction (proposed):** a lemma `parentInteraction_eq_of_symm_idem_ker` taking a
  linear endomorphism `Q` of `NSiteSpace d n` that is symmetric for the coefficient
  pairing, idempotent, and has kernel `groundSpace A n`, and concluding
  `Q = parentInteraction A n`.
- **Notes:** two occurrences in two files, below the rule of three. The chain-level
  consequences that both examples also need (positivity of \(H+c\), the eigenvalue bound
  \(\mu\ge-c\), and the ground eigenspace as the parent kernel, from
  \(H+c=s\,H_{\mathrm{parent}}\)) are already shared lemmas in
  `TNLean/MPS/ParentHamiltonian/ShiftedParentHamiltonian.lean`, and the exchange
  interaction is the operator-family-generic `MPSTensor.spinExchange` of
  `TNLean/MPS/Examples/SpinOperator.lean`.

### endpoint contraction through a physical pairing — candidate
- **Pattern:** after `ext` and `simp only [leftAct, leftEndpoint, …]` (or the right-endpoint
  analogue), move the physical sum inside the two virtual sums and regroup the product so
  that the pairing `∑ c, Â c α β * C c γ δ` appears as a factor:

  ```lean
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun β _ ↦ Finset.sum_congr rfl fun c _ ↦ by ring
  ```

- **Seen:** 4 occurrences in one file, in `leftAct_leftEndpoint`,
  `leftAct_leftEndpoint_eq_zero`, `rightAct_rightEndpoint` and
  `rightAct_rightEndpoint_eq_zero`
  (`TNLean/MPS/Symmetry/MPOSymmetry/DomainWallString.lean`, lines 163, 186, 207 and 227;
  reported by `scripts/tactic_pattern_scan.py`, recorded 2026-09-27).
- **Abstraction (proposed):** a lemma rewriting
  `∑ c, (∑ α, ∑ β, x α β * Â c α β) * y c` as `∑ α, ∑ β, x α β * ∑ c, Â c α β * y c`, or
  one endpoint lemma parametrized by the value of the pairing, from which the four
  endpoint theorems follow by `simp`.
- **Notes:** all occurrences are in one file, below the rule of three (which asks for at
  least two files). Promote when a second module contracts an endpoint tensor against a
  physical pairing in the same way.

### canonical local space as the representative block sum — factored
- **Pattern:** compose `CPSVCanonicalFormData.groundSpace_eq_iSup_representatives` with the
  symmetric form of `groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1) B (by simp) L`.
- **Seen:** 2 occurrences, in
  `TNLean/MPS/ParentHamiltonian/CanonicalBlockGroundSpaceAtInjectivityLength.lean` and
  `TNLean/MPS/ParentHamiltonian/Martingale/CanonicalGapAtSimultaneousInjectivity.lean`.
- **Abstraction:** `CPSVCanonicalFormData.groundSpace_eq_toTensorFromBlocks_representatives`
  in `CanonicalBlockGroundSpaceAtInjectivityLength.lean`, the first file that needs it. The
  parent-Hamiltonian identity then follows from `parentHamiltonianES_eq_of_groundSpace_eq`.

### GHZ zero-image non-injectivity witnesses — candidate

- **Pattern:** choose virtual labels forcing one physical label to equal both 0 and 1,
  then use the resulting zero basis image to disprove injectivity.
- **Occurrences:** `ghzSiteTensor_not_linearIndependent` and
  `ghzPEPS_not_isVertexInjective` in `TNLean/PEPS/Examples/GHZ.lean`.
- **Count:** two occurrences in one file; below the promotion threshold.
- **Possible abstraction:** a bridge from linear independence of the four-leg
  site tensor to vertex injectivity of its torus realization, if another example
  repeats the construction.

### Transposed Kronecker gauge inverses — candidate

- **Pattern:** reduce block-diagonal inverse products to Kronecker products,
  combine factors with `Matrix.mul_kronecker_mul` and `Matrix.transpose_mul`,
  and cancel unit-valued gauges.
- **Occurrences:** the two pair-gauge inverse identities and four left/right
  tree-gauge inverse identities in `TNLean/MPS/MPDO/CompleteZipperFusionGauge.lean`.
- **Count:** six occurrences in one file; the two-file promotion threshold
  has not been reached.
- **Possible abstraction:** a transposed Kronecker inverse-pair lemma if a
  second module needs the same cancellation pattern.

### root-of-unity powers across a cyclic successor — candidate
- **Pattern:** simplify `Fin.val_add` and `Fin.val_one'`, then use
  `pow_eq_pow_mod`, `pow_succ`, and commutativity to prove
  `z ^ (k + 1).val = z * z ^ k.val` from `z ^ q = 1`.
- **Seen:** two occurrences in two files: `Fin.exists_stepOrbit_phases` in
  `TNLean/Algebra/FinStepOrbit.lean` and the private `map_cyclic_sum` in
  `TNLean/MPS/Periodic/BlockingEigenvalues.lean` (2026-09-30).
- **Abstraction (proposed):** a cyclic-successor power lemma over a commutative
  monoid; below the three-occurrence promotion threshold.

### Unitary transport of left-canonical sums — candidate
- **Pattern:** expand the conjugate transpose of `U * A i * Uᴴ`, cancel the
  middle unitary pair, move the outer matrices through the finite sum, and
  use the original left-canonical identity.
- **Seen:** two occurrences in two files: the normalization proof in
  `exists_isLeftCanonical_blockTensor_eq_of_unitary_conj` in
  `TNLean/MPS/Periodic/SectorPhaseBlocking.lean`, and
  `leftCanonical_of_unitary_block_intertwining` in
  `TNLean/MPS/MPU/VirtualUnitaryGauge.lean`.
- **Abstraction (proposed):** a left-canonical transport lemma for a unitary
  matrix intertwining two tensor families, if a third occurrence arises.
- **Notes:** the periodic application uses the inverse unitary orientation.
  Below the three-occurrence promotion threshold; no custom tactic introduced.

### Selecting and flattening prescribed orbit blocks — candidate
- **Pattern:** choose the prescribed periodic decomposition separately for each
  original block, flatten `(original block, orbit)` with `finSigmaFinEquiv`,
  and transport the weighted MPV identity through that enumeration.
- **Seen:** two occurrences in `IsIrreducibleForm.block` in
  `TNLean/MPS/Periodic/IrreducibleFormBlocking.lean` and
  `weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos` in
  `TNLean/MPS/Periodic/RefinementNormalization.lean` (2026-09-30).
- **Abstraction (proposed):** a family-level decomposition lemma returning
  the chosen blocks and dimension identities if a third consumer appears.
  The shared weighted-sum refinement is already a separate theorem.

### measurement-assisted GHZ protocol on two site layouts — candidate
- **Pattern:** the Example 1 protocol of arXiv:2103.13367 written twice: the
  outcome-consistency lemma, the corrections by outcomes and partial sums, and
  the product-state bookkeeping.
- **Seen:** two occurrences (2026-10-01):
  `TNLean/Circuit/Measurement/GHZ.lean` (interleaved single qudits of
  an open chain, `forall_succ_eq_iff`, `forall_add_ghzCorrection_eq_iff`) and
  `TNLean/MPS/Preparation/WindowGHZ.lean` (registers of `r₁` sites inside
  blocks of a ring, `forall_cyclic_eq_zero_iff`).
- **Abstraction:** proposed: one protocol over an injective embedding of the
  system and ancilla sites and a label type `Cfg d r₁`, in an open and a
  cyclic form, with the outcome-consistency lemma over an additive group
  indexed by `Fin M`. The partial sums already share `Fin.partialSum`.
- **Notes:** below the rule of three; the layouts differ in the controlled
  shift between a register and its ancilla, which spans a block in
  `WindowGHZ.lean`.


### Scalar word-trace identities for Ising compression — candidate

- **Pattern:** introduce a local identity
  `trace (evalWord (c • A) w) = c ^ w.length * trace (evalWord A w)`
  by `Kraus.evalWord_smul`, `Matrix.trace_smul`, and `smul_eq_mul`, then
  use it to simplify the traces of the weighted target family.
- **Seen:** the local `hs` in `IsingWeightedTwist.lean` and `hscale` in
  `IsingThreeObjectTwist.lean` (2026-10-02).
- **Abstraction (proposed):** a word-trace form of the existing scalar word
  evaluation lemma, in QICLean beside `Kraus.evalWord_smul` if another
  development needs the same statement.
- **Notes:** two occurrences in two files, below the promotion threshold.
  The three-object calculation also needs simplification of the finite
  dependent dimensions before rewriting the trace expressions.

### finite block coordinates with zero complements — candidate
- **Pattern:** split active and zero block labels, decide the active label,
  derive the coordinate bounds with `omega`, and simplify the block inclusions
  and projections before proving the scalar entry identity.
- **Seen:** three coordinate cases in
  `TNLean/MPS/Examples/Ising/IsingThreeObjectGauge.lean` (2026-10-02).
- **Abstraction:** a coordinate lemma for regrouping active direct sums with
  one-dimensional zero complements, if a second example requires the same
  construction.
- **Notes:** bounds should be supplied before simplifying dependent matrix
  indices; exhaustive enumeration of all bond-coordinate pairs is unnecessary.

## Rejected

### Elementary set and finite-sum proof structure — rejected (2026-10-02)

- **Pattern:** The three-line sequences `ext x; constructor; intro hx` and
  `rw [Finset.sum_comm]; apply Finset.sum_congr rfl; intro θ _`.
- **Seen:** Three occurrences of each in the completed PEPS geometry and
  physical-density batch, across `IntegerCellNoHoles`, `TorusRegionRealization`,
  `RegularPhysicalCutTransfer`, and `TorusControlledBoundaryDensity`.
- **Reason:** Set extensionality, sum exchange, and elementwise sum equality
  are already expressed by the standard tactics and Mathlib lemmas. The
  subsequent arguments have different mathematical hypotheses and conclusions.
  Bundling these elementary steps would hide proof structure without sharing
  a mathematical assertion. The longer geometry and spectral arguments have
  separate promoted lemmas recorded above.
- **Creation-inclusive review:** a fresh 126-file scan also finds nested
  `Prod.ext` with reflexive unchanged coordinates in
  `RegularCyclePhysicalFluxCreation` and `RegularTwoCyclePhysicalFluxMove`,
  and `unfold openRegionWeight; apply Finset.sum_congr rfl; intro η _`
  in the coherent global transport, twisted recovery, and global flux move.
  These use existing product extensionality and finite-sum congruence; their
  subsequent mathematical identities differ. No further wrapper is needed.
- **Joint-measurement check:** the fresh 131-file scan at window three,
  count three found only the already covered set-extensionality and finite-sum
  congruence patterns. The actual uniform-column-to-cut implication has its
  own promoted mathematical theorem; no further wrapper is needed.
- **Three-plaquette review:** the fresh 140-file mirror at window three,
  count three contains the same set and finite-sum patterns, the already
  resolved encoded boundary comparison, and extensionality followed by a
  single selected-coordinate case split. The subsequent identities differ;
  no further mathematical abstraction is justified. The repeated sorted
  non-tree certificate is separately promoted as `Edge.comap_adj_map_iff`.

### scalar-unit equality by coercion and field cancellation — rejected
- **Pattern:** reduce an equality in `Units ℂ` to an equality in `ℂ` with
  `apply Units.ext; push_cast`, then cancel the nonzero scalar denominators
  with `field_simp`.
- **Seen:** seven occurrences across
  `TNLean/Algebra/CocycleCohomology.lean`,
  `TNLean/Algebra/ScalarThreeCocycle.lean`,
  `TNLean/Algebra/ScalarThreeCocycleInversion.lean`, and
  `TNLean/Algebra/GeneralizedCocycle.lean` in the 2026-08-29 scan.
- **Reason:** `Units.ext` is already the semantic abstraction. The remaining
  two tactics expose the standard passage to the ambient field and a
  goal-specific cancellation; a macro would merely hide three idiomatic lines
  without sharing any mathematical conclusion or simplifying hypotheses.

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
  `Kraus.mapLM_ne_zero_of_exists_ne_zero B hB` directly by definitional equality.
- **Result:** the inline evaluation-at-identity proof is removed; no duplicate
  implementation remains.

### indicator-weight case split — candidate
- **Pattern:** prove a pointwise identity or inequality between coordinate
  weights built from `if` on index arithmetic by `split_ifs <;> first |
  (exfalso; omega) | norm_num`: the arithmetically impossible branches close by
  `omega` on the accumulated index hypotheses and the remaining branches are
  numeric.
- **Seen:** five occurrences in
  `TNLean/MPS/ParentHamiltonian/Martingale/NachtergaeleLowerEndpoint.lean`
  (2026-09-04), all inside one refuting model.
- **Abstraction (proposed):** none yet. The rule of three asks for occurrences
  across at least two files; if a second coordinate model needs the same
  split, extract a `weight_split` macro next to the diagonal-operator helpers
  rather than a general tactic.

### CZX phase-table entry evaluation — rejected
- **Pattern:** evaluate one transported four-qubit monomial operator at one
  computational basis vector by naming the two decidable facts that hold there
  and closing the scalar arithmetic:

  ```lean
  have hperm : barFlip ![1, 1, 0, 0] = ![0, 0, 0, 0] := by decide
  have hphase : hExponent ![1, 1, 0, 0] = 0 := by decide
  rw [<operator basis action>, hperm, hphase]
  norm_num [show ((1 : ZMod 2)).val = 1 from rfl]
  ```

- **Seen:** eight occurrences across two files (2026-09-07): the six
  `matterMatrix_{w,tildeLambda,tildeLambdaStar}_mulVec_matterKet_{zero,one}`
  proofs in `TNLean/MPS/MPDO/CZXCompletion.lean`, and the two
  `matterMatrix_lambda_mulVec_defectVector_{zero,one}` proofs in
  `TNLean/MPS/MPDO/CZXUnmodifiedFusion.lean`.
- **Reason:** the shared step is already abstracted. Every occurrence reaches
  `MPOTensor.CZX.matterMatrix_monomial_mulVec_matterKet`, directly or through
  the per-operator wrappers `matterMatrix_w_mulVec_matterKet` and
  `matterMatrix_tildeLambda_mulVec_matterKet`, and that lemma carries the whole
  mathematical content of the step. What is left at each site is the site's own
  data: which bit string the permutation sends where, and what the sign
  exponent is there. The eight sites use four different operators, four
  different exponent functions, three different scalar prefactors, and eight
  different bit strings, so they share no conclusion from which a further lemma
  could be extracted; they are eight entries of a phase table.
- **Prototype:** a helper `(hperm : σ x = y) → (hphase : φ x = c) →
  matterMatrix (monomial σ φ) *ᵥ matterKet x = c • matterKet y` was written out
  on paper, in full for one site of each of the three shapes that occur and by
  shape for the remaining five. It does not shorten them. The permutation fact
  survives verbatim as an explicit argument; the exponent fact does not,
  because `φ x` is a complex number and `φ x = c` is undecidable, so each site
  must wrap its `decide` inside a `norm_num` proof of the sign, which is longer
  than the `have` it replaces. Each of the eight proof bodies grows by one line
  and the helper adds nine, for about seventeen lines net. The prototype was
  not compiled.
- **Notes:** the one fragment genuinely shared by the sites is the closing
  `show ((1 : ZMod 2)).val = 1 from rfl`, an inlined shadow of Mathlib's
  `ZMod.val_one`. Replacing it is a Mathlib-reuse cleanup across the three CZX
  files rather than a tactic abstraction, and is recorded here so it is not
  confused with this pattern.

### red/blue window membership case split — promoted
- **Pattern:**
  ```lean
  rcases hRed with ⟨hr, hrn⟩ | ⟨hrn, hr⟩ <;>
    rcases hBlue with ⟨hb, hbn⟩ | ⟨hbn, hb⟩ <;>
    (simp only [not_and, not_lt] at hrn hbn; omega)
  ```
  with a second form that adds `⊢` to the `simp only` location list, for a goal that is
  itself a conjunction of coordinate bounds.
- **Seen:** twenty-four occurrences before the 2026-09-19 torus edge-coordinate cleanup
  (twelve in `TNLean/PEPS/TorusEdgeBlockingCrossing.lean`, ten in
  `TNLean/PEPS/TorusWindowRegion.lean`, two in
  `TNLean/PEPS/NormalEdgeSingleCrossing.lean`); five afterwards, once the per-step copies
  inside the coordinate-pinning blocks collapsed into one call each and the unused vertical
  staircase pair was removed. Three of the five were the first form, verbatim, across two
  files, and two were the goal-normalizing form.
- **Abstraction:** the tactic `crossing_blocks hRed hBlue`, with the form
  `crossing_blocks hRed hBlue ⊢` for the goal-normalizing variant, in
  `TNLean/PEPS/TorusEdgeBlockingCrossing.lean`. All five sites are refactored. Net Lean
  delta of the promotion itself: +31 / -15, since the five sites lose two lines each while
  the two forms with their documentation and section note cost about twenty-five; the
  duplication rather than the line count is what it removes.
- **Notes:** the two membership hypotheses are passed as arguments, since the hypotheses
  introduced inside a macro are not the caller's; the four branches differ only in which
  endpoint lies in which block, and `omega` reads the coordinate ranges of the blocks from
  the context, so one closing call serves every branch. The tactic sits beside the crossing
  arguments whose hypothesis shapes it is written for rather than in a general tactic
  module. The two occurrences in `TNLean/PEPS/NormalEdgeSingleCrossing.lean` are a
  different shape — the open-lattice memberships need no negation normalization and the
  branches close by `omega` alone — and are left as they are.



### encoded boundary conditions inside region sums — resolved
- **Pattern:** apply `Finset.sum_congr`, introduce the incident configuration,
  and replace its encoded boundary condition by the corresponding group-label
  condition.
- **Seen:** three occurrences in `RegularProjectorOpenRegion.lean` and
  `RegularProjectorTwistedRegion.lean` (2026-10-02): forward physical access,
  reverse physical recovery, and twisted forward access.
- **Reuse:** all three use `regionIncidentBoundaryLabel_regularGroup_iff`,
  which already contains the common mathematical argument. The remaining
  `Finset.sum_congr` steps compare the different local products required by
  their respective identities. A further wrapper would merely combine this
  existing lemma with the generic finite-sum congruence theorem.

### unitary adjoint identities in matrix coordinates — candidate

- **Pattern:** Extract `Uᴴ * U = 1` or `U * Uᴴ = 1` from membership in the
  unitary group, then reassociate a matrix product to cancel adjacent factors.
- **Occurrences:** Four extractions in
  `TNLean/MPS/Symmetry/UniformProjectiveRigidity.lean`, in the unitary
  conjugation norm, orbit-to-intertwiner, and Choi orbit arguments.
- **Existing results:** Mathlib `Matrix.mem_unitaryGroup_iff` and its primed
  form supply the identities. The promoted
  `Matrix.mul_unitary_adjoint_mul_cancel` in `Algebra/UnitaryContraction.lean`
  handles the rectangular contraction when its statement applies.
- **Decision:** The occurrences lie in one file, below the two-file promotion
  threshold. No new tactic or theorem is needed; further uses should first
  consult the existing identities and contraction lemma.

### the spectrum after quotienting by a simple fixed line — candidate

- **Pattern:** identify the maximal generalized eigenspace at one with its
  eigenspace from algebraic simplicity, then exclude one from the quotient
  spectrum while retaining every other eigenvalue.
- **Seen:** the private fixed-line quotient arguments in
  `TNLean/MPS/Symmetry/FixedLineLimitSimplicity.lean` and
  `TNLean/MPS/Symmetry/PeriodicMPSNormLowerBound.lean` (2026-10-03).
- **Abstraction:** a finite-dimensional linear-map lemma for the spectrum of
  the quotient by a simple fixed line would contain the common argument.
- **Notes:** two occurrences across two modules; below the promotion threshold.

### one-sided letter invariance from adjoint stationarity — candidate

- **Pattern:** apply stationary support invariance to the adjoint Kraus
  letters, then take adjoints to obtain
  `P * B i * (1 - P) = 0` for the stationary support projection.
- **Seen:** `prepare_stationary_support_compression` and
  `exists_dim_eq_gaugePhase_of_unital_stationary_support_overlap`, in
  `StationarySupportPreparation.lean` and
  `StationarySupportLimitIdentification.lean` (2026-10-03).
- **Abstraction:** a Kraus-family support identity for an adjoint fixed
  positive matrix would contain the common argument.
- **Notes:** two occurrences across two modules; below the promotion threshold.

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

### one-site MPO blocking as a physical reindexing — candidate
- **Pattern:** prove that blocking one physical site is reindexing by
  `Kraus.singleBlockEquiv`, by matrix extensionality and simplification of
  `wordOfBlock` at length one.
- **Seen:** two private helper proofs in
  `TNLean/MPS/MPU/IdentityIndex.lean` and
  `TNLean/MPS/MPU/InjectiveSourceIndex.lean` (2026-10-02).
- **Abstraction:** promote `blockTensor_one_eq_reindexPhysical` to
  `TNLean/MPS/MPDO/PhysicalBlocking.lean` if a third proof is needed.
- **Notes:** both uses identify source ranks after one-site blocking; no
  custom tactic is required.

### Normalization of finite character coefficient vectors — candidate

- **Pattern:** Write the finite squared norm as a dot product, move the
  scalar normalization outside using `star_smul`, `dotProduct_smul`, and
  `smul_dotProduct`, then apply translated character orthogonality.
- **Occurrences:** The initial and flux-inserted pair norms and their
  mixed overlap in `PEPS/RegularChargePair.lean`.
- **Status:** Three occurrences in one module. A common normalization
  lemma is appropriate if a second module repeats the calculation.

### Charge motion by exchange of internal reference labels — candidate

- **Pattern:** Reindex the actual weighted projector column by an internal
  reference exchange, prove equivariance under independent vertex
  translations, and lift through the local scaled-isometry Gram identity.
- **Occurrence:** `PEPS/RegularPhysicalChargeMotion.lean`; the exchange moves
  a literal bond diagonal, with its parameter transported by the derived
  rooted tree gauge.
- **Status:** The coordinate permutation and physical lift reuse the
  general helpers in `PEPS/RegularChargeFluxPhysicalTransport.lean`.
  The remaining column calculation depends on the actual exchanged weight.

### Literal diagonal weights under vertex gauges — candidate

- **Pattern:** Change the actual tail labels by the vertex gauge, retain
  each scalar diagonal weight in the finite sum, and restrict the bijection
  to the actual open boundary.
- **Occurrences:** The closed graph and open-region identities in
  `PEPS/RegularWeightedGaugeTransport.lean`; the translated torus consumer
  uses these identities directly.
- **Status:** Two calculations in one module, below the promotion threshold.
  Correlated charge-pair weights are handled by specialization of the
  arbitrary-weight identity.

### A unique surviving labeling in a finite tensor contraction — candidate

- **Pattern:** Rewrite each local coefficient as its indicator, identify
  the joint support with one explicit internal labeling and a condition
  on the retained indices, and collapse the finite sum.
- **Occurrences:** `PEPS/KitaevCheckerboardBlocking.lean`, for the four
  elementary checkerboard tensors and their eight exterior binary legs;
  `PEPS/KitaevGlobalCheckerboardBlocking.lean`, for the globally paired
  crossing labels on a periodic tiling.
- **Status:** Two contractions. Mathlib's `Fintype.sum_of_injective` and
  equivalence lemmas handle the global support restriction directly.
  Nested bond-sum congruences reuse the promoted `Finset.sum_congr₂`.
### Full logical unitary implementation in an initialized packet — promoted (2026-10-02)

- **Pattern:** Include a complete logical unitary in prescribed physical basis
  coordinates, extend its orthonormal columns to a physical unitary, synthesize
  that unitary, and retain the equality on every logical input.
- **Seen:** `MPU/LeafIntervalCircuit.lean`, `MPU/BondDilationCircuit.lean`, and
  `MPU/CompatibleBondDilationCircuit.lean`.
- **Abstraction:**
  `QuantumCircuit.exists_isPairProduct_isCleanImplementation` in
  `TNLean/Circuit/CleanUnitaryImplementation.lean` derives the actual circuit and
  its full logical-space clean identity. `IsCleanImplementation.embedOp` in
  `TNLean/Circuit/CleanImplementationPlacement.lean` places this identity into a
  larger shared scratch pool.
- **Notes:** All three local constructions use the common existence theorem.
  Cleanup on selected physical-input columns alone is insufficient for an
  inverse call; the full logical identity is retained. The synthesis bound is
  polynomial in the packet Hilbert dimension and is used only on packets of
  logarithmic width in the bond bound.

### Orthogonal projection in matrix coordinates — candidate (2026-10-02)

- **Pattern:** Transport a finite-dimensional invariant subspace to Euclidean
  coordinates, represent its orthogonal projection by `Matrix.toEuclideanLin.symm`,
  and prove matrix Hermiticity, idempotence and invariant-range identities.
- **Seen:** two constructions: QICLean `Kraus/IrreducibleAction.lean`
  (`isIrreducibleAction_of_isIrreducibleFamily`) and TNLean
  `MPS/FundamentalTheorem/Reduction/StationarySplitting.lean`
  (`isSemisimpleModule_wordModule_of_hasInvariantProjectorClosure`).
- **Abstraction:** a matrix-coordinate orthogonal-projection helper with
  invariant-range equivalence, preferably in QICLean's projection algebra.
- **Notes:** below the three-occurrence promotion threshold. The new construction
  reuses Mathlib's star-projection facts; no custom tactic is needed.

### nonzero matrix eigenvectors lie orthogonal to the kernel — candidate
- **Pattern:** use self-adjointness to identify the orthogonal complement
  of the kernel with the range, then exhibit the inverse eigenvalue times
  the eigenvector as a preimage.
- **Seen:** `Matrix.spectrum_separated_of_orthogonal_quadratic_gap` in
  `Algebra/CommonKernelSpectralGap.lean` and
  `spectrum_separated_of_orthogonal_norm_gap` in
  `MPS/Symmetry/CanonicalInjectiveGappedPath.lean` (2026-10-02).
- **Abstraction:** a nonzero-eigenvalue membership lemma for symmetric
  linear maps would remove the repeated range argument.
- **Notes:** two occurrences across two files; below the promotion threshold.

### Orthogonal projections are Hermitian — promoted (2026-10-02)

- **Pattern:** obtain the Hermitian matrix identity from an orthogonal projection.
- **Seen:** the two projected-Gram arguments in
  `Circuit/UniformPostselection.lean` and the flag projection in
  `Circuit/UniformSuccessAttenuation.lean`.
- **Abstraction:** the existing Mathlib results `IsSelfAdjoint.isHermitian`
  and `Matrix.IsHermitian.eq` give the identity directly.
- **Result:** all three arguments use `hP.isSelfAdjoint.isHermitian.eq`;
  the repeated conversion of the matrix star is removed. No new tactic or
  additional mathematical hypothesis is needed.

### adjoint Perron eigenvalue from trace duality — candidate
- **Pattern:** pair a positive definite adjoint eigenvector with a positive
  definite right eigenvector, apply `Kraus.trace_mul_mapLM_adjoint`, and
  cancel the nonzero trace pairing to identify the two eigenvalues. For a
  unital tensor the right eigenvector is the identity and its eigenvalue is one.
- **Seen:** two occurrences across
  `TNLean/MPS/CanonicalForm/NormalTensorGauge.lean` and
  `TNLean/MPS/Symmetry/UnitaryVirtualGauge.lean` (2026-10-02).
- **Abstraction:** a lemma identifying eigenvalues from a nonzero trace
  pairing would contain the common algebraic step; the existing promoted
  trace-duality theorem already contains the matrix expansion.
- **Notes:** the new unital case takes only four lines after choosing the
  adjoint eigenvector. No new tactic is needed.

### matrix products after a common bond conjugation — candidate
- **Pattern:** expand the matrix coefficients of general-linear-group products,
  reassociate, and cancel the adjacent inverse-basis factors.
- **Seen:** two occurrences in
  `TNLean/MPS/Symmetry/ProjectiveGaugeTransport.lean`, in the projective
  multiplication law and transported virtual covariance (2026-10-02).
- **Abstraction:** use the group conjugation identities before taking matrix
  coefficients when possible; a matrix conjugation linear equivalence may
  contain the common cancellation when a scalar action is also present.
- **Notes:** both occurrences are in one module, below the promotion threshold.

### positivity and unit bounds for the two-block square root — candidate
- **Pattern:** use `u² + v² = 1` and the nonnegativity of the two square-root
  coefficients to obtain `u ≤ 1` and `v ≤ 1`, then use `2uv = s`.
- **Seen:** three occurrences in
  `MPS/Preparation/OverlappingBlockCounterexample.lean`: the two normalized
  state-error bounds and the polar matrix lower bound (2026-10-03).
- **Abstraction:** a small conjunction lemma for these scalar inequalities
  could replace the repeated derivations if a second file uses the pattern.
- **Notes:** the occurrences currently lie in one file; the promotion
  criterion of at least two files is not met.

### algebraic simplicity from a positive unital fixed line — promoted
- **Pattern:** identify the generalized eigenspace at one with the fixed
  space by excluding peripheral Jordan blocks, then identify the algebraic
  multiplicity with the dimension of that space.
- **Seen:** `simple_fixedEigenvalue_of_unital_positive` in
  `MPS/Symmetry/PeriodicMPSNormLowerBound.lean`, reused by the periodic norm
  estimate and `MPS/Symmetry/CompactMinimalClassStability.lean` (2026-10-03).
- **Abstraction:** expose the existing fixed-eigenvalue lemma; the compact
  sequence proof uses it without repeating the Jordan-block argument.
- **Notes:** a theorem suffices; no additional tactic is required.

### Positive half-chain spectral comparison — candidate (2026-10-04)

- **Pattern:** Rewrite a positive matrix characteristic polynomial as the product
  over its eigenvalues, sort the real roots in decreasing order, and compare
  finite eigenvalue lists after appending zeros.
- **Seen:** `HalfChainSpectralComparison.lean`, ordered monotone functional
  calculus and padded characteristic-polynomial comparison (two occurrences).
- **Abstraction:** Existing Mathlib characteristic-root and sorted-list APIs do
  most of the work. `paddedEigenvalues_eq_of_charpoly` is the physical consumer's
  common statement; no additional tactic is warranted below the rule of three.
- **Notes:** Weyl monotonicity and CFC square roots are reused from QICLean and
  Mathlib. The local perturbation/padding results compose those public APIs;
  no QICLean implementation is copied into TNLean.

### Coherent GHZ seed and cyclic correction — promoted (2026-10-05)

- **Pattern:** Repeat the prescribed seed-column unitary construction and the
  cyclic difference-measurement calculation when changing only the routing.
- **Seen:** `MPS/Preparation/WindowGHZ.lean` and
  `MPS/Preparation/SparseWindowGHZ.lean`.
- **Abstraction:** `exists_windowGHZSeedUnitary`,
  `windowGHZDifference_eq_mulVec`, and `exists_windowGHZCorrectionRound`
  keep the seed and coherent cyclic algebra in one place. The correction
  scalar is quantified before the arbitrary label amplitudes.
- **Notes:** The one-round SWAP protocol and the constant-depth multi-round
  protocol have different physical resource claims, so neither replaces the
  other. Both now consume the same algebra instead of copying its proof.

### Remainder-absorbing preparation blocks — promoted (2026-10-05)

- **Pattern:** Split a ring into `N / q` blocks, enlarge the final block by
  `N % q`, prove their sum is `N`, and bound every length between `q` and `2q`.
- **Seen:** `AllLengthPolynomialAccuracy.lean`, `OrderedMixingPairRate.lean`,
  and `AllLengthPrescribedSlope.lean` under `MPS/Preparation/`.
- **Abstraction:** `RemainderBlocks.lean` owns `remainderBlockLengths`,
  `sum_remainderBlockLengths`, `le_remainderBlockLengths`, and the stronger
  strict upper bound `remainderBlockLengths_lt_two_mul`. The definition and
  sum theorem were moved without renaming; the three consumers share them.
- **Notes:** The scalar rate conversion likewise reuses
  `mul_mul_exp_neg_le_of_log_le` through `mul_pow_mul_exp_neg_le_of_le`;
  the original uniform-rate proof no longer repeats that arithmetic.

### Finite periodic quotient error — candidate (2026-10-06)

- **Pattern:** Bound a normalized periodic expectation by rewriting
  `a / b - s = ((a - s) + s * (1 - b)) / b` and using `‖b‖ ≥ 1/2`.
- **Seen:** The fixed-support quantitative expectation proof and its simpler
  full-ring contracting case in `MPS/Symmetry/PeriodicStringBounds`.
- **Abstraction:** None yet. The fixed-support proof bounds a centered
  numerator, while the full-ring proof has target zero. Existing norm and
  division inequalities keep both arguments short.
- **Notes:** The two occurrences do not justify another exported quotient
  wrapper; the underlying estimates stay with the actual periodic observables.

### Bilinear identities for two pair sources — candidate (2026-10-07)

- **Pattern:** Reduce an identity involving two arbitrary bipartite source
  vectors to pure tensors by two tensor-product inductions. Linearity handles
  the additive cases; tensor associators and exchanges then evaluate explicitly.
- **Seen:** `eval_combineSources` in
  `TNLean/PEPS/Approximation/PartyLayout.lean` and
  `eval_expandCombinedPair` in
  `TNLean/PEPS/Approximation/PairSourceExpansion.lean` (two occurrences).
- **Abstraction:** At the next occurrence, consider a bilinear extensionality
  lemma for maps on two tensor products. The existing `clm_ext_tmul` and
  `clm_ext_tmul₃` already handle identities between continuous linear maps
  with one tensor-product input; use those whenever the map has that form.
- **Notes:** The endpoint-reversal identity uses `clm_ext_tmul`. Exchanging
  complete source blocks reuses the preparation tensor identity and the
  register-block exchange theorem. Neither requires another double induction.

### Tensor maps under equal filtered layouts — candidate (2026-10-07)

- **Pattern:** Identify equal owner-filtered memories, transport their tensor
  maps, and compare the resulting operators or their values on vectors.
- **Seen:** `PartyTensorMaps.mapL_heq` and
  `PartyFactorization.mapL_apply_heq` under `PEPS/Approximation` (two local
  helpers across two files).
- **Abstraction:** Canonical conjugation already uses the shared
  `Layout.conj_memCongr_heq`, `Layout.norm_conj_memCongr`, and
  `Layout.eq_conj_memCongr_of_heq`. The remaining two helpers distinguish
  equality of tensor maps from equality after evaluation. A further occurrence
  should use one tensor-map equality lemma followed by evaluation.
- **Notes:** Associator and exchange identities use the existing
  `clm_ext_tmul₃`; no additional tactic is needed.
- **Scan:** The focused approximation scan also found five instances of
  eliminating the two layout equalities by `cases` and closing by reflexivity,
  all in `WordRestriction.lean`. These express the defining equations of the
  equality transport; there is no repeated proof argument across files.

### Congruence after identifying layout memories — reuse (2026-10-07)

- **Pattern:** After identifying two equal register layouts, apply the same
  dependent construction to heterogeneously equal vectors.
- **Seen:** The focused scan found `cases h; cases hxy; rfl` in
  `SourcePreparation.eval_source_heq`, `Word.eval_castInput_of_heq`, and the
  new `SourcePreparationCoordinates.assocL_tmul_heq` under
  `TNLean/PEPS/Approximation` (three occurrences across two files).
- **Decision:** Reuse core `congrArg`, `eq_of_heq`, and `heq_of_eq` in the new
  associator helper after identifying the layouts. These are defining
  equations of three distinct dependent constructions, not repeated tensor
  calculations. A new generic congruence lemma would restate the existing
  equality lemmas, so no additional theorem or tactic is promoted. Previously
  audited source-preparation proofs are unchanged.
- **Relation to the tensor-map candidate:** The two existing private
  `mapL_heq` and `mapL_apply_heq` helpers concern tensor products of two maps
  with four changing spaces. The new helper instead compares an associator
  applied to a fixed pair vector and a changing spectator vector; obtaining
  a tensor-map identity first would require additional equalities without
  simplifying the proof. The common mathematical operation is ordinary
  congruence after the memory types have been identified.


### Cons-source preparation under fixed slot layouts — candidate (2026-10-07)

- **Pattern:** Identify the vector-independent slot layout with an actual source
  inventory, then express preparation of a nonempty list as preparation of the
  tail followed by its head source.
- **Seen:** `prepareSlots_cons_heq` in `SourceSlotMaps.lean` and
  `SelectiveSourcePreparation.lean` under `PEPS/Approximation` (two occurrences).
- **Abstraction:** Before a third consumer, export the cons identity from a
  shared preparation module. Tensor calculations already reuse
  `eval_frameList_prepare`; the remaining argument identifies equal layouts.
- **Notes:** Short equality transports follow the existing congruence decision
  above. No additional tactic is needed.

### Grouped operators and spectator memories — candidate (2026-10-07)

- **Pattern:** Evaluate an operator on a block tensored with an untouched memory,
  and transport both layouts through the canonical owner-grouping isometries.
- **Seen:** `localMap_owner_naturality` in `WordOwnerMap.lean` and
  `eval_groupedBlockMap` in `GroupedBlockMap.lean` under `PEPS/Approximation`.
- **Abstraction:** Both calculations use `Layout.mapOwnerIso_append_tmul` and
  `clm_ext_tmul`. At a third occurrence, move the block-operator identity to a
  lower-level lemma, then derive the local and aggregate cases from it.
- **Notes:** The aggregate case permits several original owners on the block;
  it retains the full operator after those owners are grouped together.

### Weighted ket–bra matrix sums — candidate (2026-10-08)

- **Pattern:** Distribute a matrix product through two finite weighted sums,
  conjugate the bra coefficients, and exchange the two summations.
- **Seen:** `sum_density_expansion` in `SourceGateDensity.lean` and
  `density_eval_eq_sum_partialWord` in `PartialSourceDensity.lean` under
  `PEPS/Approximation` (two occurrences).
- **Abstraction:** Before a third consumer, expose the rectangular matrix
  identity as a shared lemma. Its two coefficient families and output index
  types should remain independent.
- **Scan:** The full repository scan was run. A focused scan of the eight
  chronological-expansion modules with minimum count two found no repeated
  tactic blocks at the default window lengths.

### Exterior ownership of a placed block — candidate (2026-10-08)

- **Pattern:** If no participant of a placed gate is affected, every register
  in its transported layout has the exterior owner.
- **Seen:** `exterior_layout` in `DistributedSourceComposition.lean` and
  the corresponding local assertion in `PartialSourceEvaluation.lean` under
  `PEPS/Approximation` (two occurrences).
- **Abstraction:** A third consumer should use one public layout-membership
  lemma. The existing `affectedOwner_eq_none` already supplies the pointwise
  fact; no new tactic is needed.
### Complementary-slice reconstruction — candidate (2026-10-07)

- **Pattern:** Choose one inside vector for each outside configuration and
  reconstruct the global vector by composing with the regional configuration
  equivalence. Applying a slice reduces to the equivalence's inverse law.
- **Seen:** `range_dependentRegionOperatorLift` and the two summands in
  `dependentRegionCylinder_sup`, all in `PEPS/AreaLaw/Cylinder`.
- **Abstraction:** None yet; these three occurrences are in one file. Reuse the
  existing configuration equivalence before introducing another reconstruction
  map if a second file needs the same argument.
- **Notes:** This argument permits an empty complementary configuration type;
  it never cancels an identity extension or assumes that the outside factor is
  nonzero. The scoped tactic-pattern scan found no exact repeated blocks at
  its default thresholds.

### Dyadic refinement cardinality bounds — candidate (2026-10-07)

- **Pattern:** Rewrite an exact refined-cell cardinality as the coarse count
  times the number of descendants, multiply a coarse-cell bound by that
  nonnegative factor, and rearrange the scalar factors.
- **Seen:** `card_fineLayerIndices_le` and
  `card_fineLayerIndices_boundary_le` in
  `PEPS/AreaLaw/Geometry/DyadicRefinement.lean` (two occurrences).
- **Abstraction:** `card_fineLayerIndices` already contains the exact
  subdivision formula. The two inequalities use the existing coarse bounds
  and `Nat.mul_le_mul_left`; no further helper is needed at present.
- **Notes:** Both occurrences lie in one file, below the promotion threshold.
  The proof-session scan reports no exact repeated block in the three new
  fine-belt modules at its default thresholds.


### Normalizing the three nonvertical allowed slopes — candidate (2026-10-07)

- **Pattern:** After specializing an integer line slope to zero, one or minus one,
  unfold the coordinate equality and close the scalar equation with
  `dsimp at hs; norm_num; linarith`.
- **Seen:** Three occurrences in `Geometry/MeshGeometry.lean`, in the horizontal
  and two diagonal cases of `affineMesh_line_dist_ge`.
- **Abstraction:** The shared line-distance argument already uses
  `nonvertical_mesh_line_dist_ge`. Consider consolidating the remaining slope
  normalization if it recurs in another file; the current occurrences are in
  one file and do not meet the two-file promotion condition.
- **Notes:** The October 7 Geometry scan detected these three short blocks.

### Rectangle corners and elementary midpoints — candidate (2026-10-07)

- **Pattern:** Express the four corners of a rectangle and the two coordinates
  of the midpoint of an elementary side to compare open and closed rectangles.
- **Seen:** The private `rectangleCorner` and `midpoint_coordinates` helpers in
  `ElementarySideOpponents.lean` and `ElementarySideOpponentUniqueness.lean`.
- **Abstraction:** Two occurrences across two files, below the promotion
  threshold. Reuse a shared geometric statement if a third proof needs these
  calculations; do not copy the coordinate table again.
- **Notes:** The existence proof extends midpoint containment to an entire
  side, while uniqueness compares three rectangles. Their common elementary
  boundary geometry has already been promoted separately.

### Cell-side parametrization — promoted (2026-10-08)

- **Pattern:** Parametrize the four sides of an axis-parallel square by the
  match `(1, w)`, `(-w, 1)`, `(-1, -w)`, `(w, -1)` scaled about its center.
- **Seen:** A private `sideVector` in `Geometry/CellFans.lean`, a second private
  copy in `Geometry/ActualSideMatching.lean`, and the same match written out
  three times in the statement of `side_interpolation` in
  `Geometry/SideSubdivisionMask.lean`.
- **Abstraction:** `cellFanSideVector` in `Geometry/CellFans.lean` is now public.
  The side-matching module uses it in place of its private copy, and
  `side_interpolation` states the whole-side interpolation in terms of it.
- **Notes:** The tangent and normal coordinates in `ActualSideMatching.lean`
  remain private to that module; no second consumer needs them.

### Marked-endpoint segment containment — candidate (2026-10-07)

- **Pattern:** Put two marked endpoints in a closed dyadic square and use
  `Convex.segment_subset` to contain their segment in that square.
- **Seen:** The private whole-side containment in `SideSubdivision.lean` and
  `segment_contact_of_marks` in `ElementarySideReciprocity.lean`.
- **Abstraction:** Two computations across two files, below the promotion
  threshold. The reciprocal module shares its one private helper across
  three uses, adding nontrivial contact when the endpoints are distinct.
- **Notes:** Mathlib supplies the interval and product convexity statements.
  Future fan-base containment can instead follow directly from the actual
  triangle's convex hull and the existing fan-cover theorem. Do not copy the
  marked-endpoint calculation into a third file.

### First and last elementary endpoints — promoted (2026-10-08)

- **Pattern:** Identify the first and last half-slot endpoints by specializing
  the indexed affine parameters of a whole side.
- **Seen:** `first_half_endpoints` and `last_half_endpoints` in
  `Geometry/FanRunContacts.lean`, and the two successor endpoint cases in
  `Geometry/CellFanCycle.lean`.
- **Abstraction:** `cellFan_elementary_endpoints_lineMap` in
  `Geometry/SideSubdivisionMask.lean` exposes the existing full parameter
  statement and proof unchanged. Both old private endpoint proofs and the
  new successor proof specialize this pair. Their signatures and existing
  callers are unchanged; no second scalar calculation is copied.
- **Notes:** The related midpoint reachability step in `FanRuns.lean` has
  a different conclusion and remains unchanged. The successor proof also
  uses the existing whole-side coordinates at consecutive corners.

### Infinitude of a nondegenerate real segment — candidate (2026-10-08)

- **Pattern:** Express a real segment as the affine image of $[0,1]$;
  distinct endpoints make the affine map injective and preserve infinitude.
- **Seen:** The private `segment_infinite` in `BeltRunInterfaces.lean` and
  the local infinitude argument in `DummyRunInterfaces.lean`.
- **Abstraction:** Two instances in two files are below the promotion
  threshold. A third consumer should first search Mathlib for a direct
  infinitude lemma, then share the minimal geometric consequence if needed.
- **Notes:** The interface proofs require an actual nondegenerate segment;
  two isolated points of a disconnected intersection are insufficient.


### Excluding integer-translated scalar equalities — candidate (2026-10-08)

- **Pattern:** Subtract the integer translation from a coordinate equality,
  convert the resulting integer expression to a real expression, and apply
  the established nonintegrality assertion.
- **Seen:** Four branches of
  `dyadicOrigin_supporting_lines_avoid_lattice` in `Geometry/DyadicOrigin.lean`.
- **Abstraction:** These branches occur in one file and do not meet the
  two-file promotion condition. They share the existing four-part
  nonintegrality theorem; no additional exported theorem is needed here.
- **Notes:** The four equations concern the two coordinates, their sum and
  their difference. They establish line avoidance; classifying actual edges
  remains a separate geometric argument.

### Single-cell specializations of the quarter mesh — promoted (2026-10-08)

- **Pattern:** Pass from marks in one cell to the quarter mesh, either pointwise
  or as a set inclusion, including the unit-spacing specialization.
- **Seen:** The private helpers `cellMark_mem_quarter_mesh` in
  `FineMarkSeparation.lean`, `mark_mem_unitMesh` in
  `InitialRegionBoundaries.lean`, and `cellMarks_subset_quarter_mesh` in
  `NearMarkGeometry.lean`.
- **Abstraction:** All three already use the public
  `beltMarks_subset_affineMesh` in `MeshGeometry.lean`. The new set-level
  application uses Mathlib's `Finset.singleton_biUnion` to specialize the
  finite-family theorem. The coordinate argument remains in its existing
  shared owner.
- **Notes:** These are short pointwise or set-level applications of the same
  theorem. No coordinate table is copied, and no further export or tactic is
  needed. The existing pointwise applications remain unchanged.

### Square-frontier whole-side extraction — promoted (2026-10-08)

- **Pattern:** Pass from a boundary point of a half-open dyadic square to
  one of its four closed whole sides.
- **Seen:** The dummy-contact proof in `DummyRunInterfaces.lean` and the
  actual nearby-frontier proof in `InitialStarFrontiers.lean`.
- **Abstraction:** `exists_dyadicCellSide_of_mem_frontier` in `CellSides.lean`
  shares the original product-frontier proof unchanged. The consumers use
  the actual side endpoints and the slopes already carried by the triangles.
- **Notes:** The proposed third marked-endpoint containment calculation was
  removed from the nearby-frontier proof. Its radial point belongs to the
  closed defining cell by the actual fan cover and closure monotonicity;
  the existing segment-containment candidates remain at two old instances.

- **Promoted: actual fan interiors and base distance.**
  `cellFanPolygon_interior_nonempty_and_closure_eq` in
  `PEPS/AreaLaw/Geometry/FanRegularity.lean` shares the existing determinant
  proof of nonempty triangle interior and its closure equality. Both old
  initial-regularity callers use it. The existing base-distance proof in
  CellFans is public as `norm_sub_cellFanCenter_of_mem_base`, so concentric
  restriction uses the same actual base without another coordinate argument.
  The three existing callers are renamed; both complete proofs are unchanged.

### Radial membership from triangle contact — candidate (2026-10-08)

- **Pattern:** Transport membership in two intersecting fan triangles through
  their contact equality, with an explicit radial-segment type, before
  identifying the fan center with the marked point.
- **Seen:** The two contact orientations in
  `initialRegion_frontier_near_mark_iff_active_radial` in
  `PEPS/AreaLaw/Geometry/InitialActiveRays.lean`.
- **Abstraction:** Two branches in one file are below the promotion threshold.
  The explicit intermediate statements keep the geometric argument readable.
  A further consumer should first seek a shared contact-membership lemma.
- **Notes:** The two branches use the existing intersection classification;
  neither repeats a coordinate calculation.

### Ordered regularized regional filters — candidate (2026-10-07)

- **Pattern:** Use a coordinate isometry to transport a regional matrix action to
  a Kronecker product with the identity, then apply the existing Euclidean bound.
  Obtain the lower bound by cancelling the filter with its positive power.
- **Seen:** The lifted regional bound and local inverse-cancellation argument in
  `PEPS/AreaLaw/RegularizedPatchMinimum`; scalar shifted-density power bounds are
  supplied by `QICLean.Analysis.ShiftedDensityPowers`.
- **Abstraction:** The native lift estimate is factored once. Product bounds use
  a private list induction; there is no new optimizer or contraction-chain type.
- **Notes:** These are distinct uses of existing isometry and CFC results, below
  the threshold for any additional tactic or general framework.

### Coordinate exponential and canonical partial trace — candidate (2026-10-07)

- **Pattern:** replace one indexed factor in a reverse product by a linear
  insertion, use exact unitary covariance before differentiation, and apply
  Fermat's theorem to the squared norm of the actual output. Separately,
  transport the actual regional lift through the existing configuration
  equivalence and pair its pure state by the existing partial trace.
- **Seen:** `PEPS/AreaLaw/RegularizedPatchCoordinate`,
  `RegularizedPatchStationarity`, and `RegularizedPatchMarginal`.
- **Abstraction:** the coordinate module factors the insertion linear map once;
  the marginal module exposes one full-region/global configuration isometry and
  one arbitrary-complex expectation theorem. Existing real-power covariance,
  exponential derivative, and finite-product reduced-state results are reused.
- **Notes:** these are distinct proofs, not three copies of one tactic block.
  No custom tactic or new optimizer/state structure is justified. Keep the
  actual product order and complex inner-product orientation explicit; neither
  trace-duality nor descending commutation is inferred by this pattern.
  The scoped AreaLaw scan found no exact repeated tactic blocks at the default
  thresholds.


### Monotonicity of a regional-entropy supremum — candidate (2026-10-09)

- **Pattern:** apply `Real.sSup_le` with the nonnegativity of the target supremum,
  unpack a regional-entropy witness, and include its region in the target collection.
- **Seen:** two occurrences in `TNLean/PEPS/AreaLaw/InitialBoxEstimate.lean`,
  `boxEntropy_mono` and `boxEntropy_antitone`.
- **Abstraction:** both proofs already use `Real.sSup_le`. A further helper is deferred
  until the same inclusion argument occurs in another module.
- **Notes:** the nonnegativity argument also covers an empty collection; an additional
  nonemptiness hypothesis would unnecessarily restrict these statements.

### Owners of fixed pair-source registers — candidate (2026-10-09)

- **Pattern:** From membership in a fixed source-register layout, use
  `List.mem_flatMap` to identify the pair, `List.mem_ofFn` to identify its
  slot index, and `PairSource.layout` to choose its left or right owner.
- **Seen:** `SourceInventory.restrict_endpointWord_eq_nil_and_eval_eq_id` in
  `PEPS/Approximation/EndpointWordRestriction.lean` and
  `SourceCircuit.restrict_allResidualSourceLayout_isNone` in
  `PEPS/Approximation/ActualSourceEmptyOwner.lean` (the latter is proposed
  separately in #8999). These are two mathematical uses across two files,
  rather than copies of one source proposal.
- **Abstraction:** At a third occurrence, prefer an ordinary lemma stating
  that every owner in `SourceInventory.slotLayout R U V` is the left or
  right owner of some slot `R.get i`. The assigned register spaces are
  irrelevant to that conclusion. A selector-exclusion corollary can then
  reuse that owner description.
- **Notes:** The rule of three is not yet met, so no new helper or tactic is
  added. The endpoint word's separate participating-party support proof
  remains necessary: a general local operation on empty registers may still
  name a participating party. The corpus scanner was run; unrelated reported
  patterns are outside this change.
