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

Entries that were retired, rejected or completed as one-off refactors are removed from
this file; git history keeps them. Only the promoted abstractions and the open
candidates are listed.

---

## Promoted

### Sitewise tensor powers of a one-site matrix — promoted (2026-11-16)

- **Seen:** five local definitions of the configuration-indexed product
  `∏ n, V (s n) (t n)`: `MPOTensor.sitewisePhysicalMatrix` (MPDO, MPU, Symmetry and
  RFP, 36 files), `MPOTensor.sitewiseMatrixFamily` (site-dependent factors), and the
  MPU copies `chainPower`, `siteProduct` and `rectangularProduct`, each with its own
  multiplication, identity, adjoint and isometry lemmas.
  The earlier candidate entry "sitewise Kronecker power in configuration
  coordinates" (2026-10-06) recorded the first two MPU copies, `siteProduct` in
  `MPU/FundamentalTheoremGates.lean` and `chainPower` in
  `MPU/Examples/ShiftStrictEquivalence.lean`; this entry supersedes it.
- **Abstraction:** `Matrix.piKronecker` (`QICLean/Algebra/Kronecker/PiKronecker.lean`,
  QICLean dependency), the Kronecker product of a finite family of matrices: a constant
  family `fun _ : Fin N ↦ V` for one factor at every site, a general family for
  site-dependent factors, with `Matrix.piKronecker_apply`, `Matrix.piKronecker_mul`,
  `Matrix.IsIsometry.piKronecker`, `Matrix.IsUnitaryBetween.piKronecker` and
  `Matrix.piKronecker_mem_unitaryGroup`. The local definitions and their duplicated
  lemmas are deleted; the lemmas that remain are named after `piKronecker`.
- **Remaining case:** `MPOTensor.sitewise_prod_conjTranspose_mul_self`
  (`MPS/MPDO/CyclicActiveSector/LemmaC5CaseI.lean`) still restates the isometry of a sitewise product in
  entrywise form; it is a candidate for `Matrix.IsIsometry.piKronecker`.

### Disjoint summands of `Fin (m + n)` — promoted (2026-11-16)

- **Seen:** `MPS/Symmetry/MPOSymmetry/MixedPath/Joint/JointMixedEndpointEdgeFactors.lean`,
  `MixedEndpointEmbedding.lean`, `MixedEndpointSwap.lean`,
  `MPS/MPU/Circuit/Merging/SingleSiteCircuit.lean` and the former `Circuit/ZeroRegisterConjunction.lean`,
  now QICLean's `Circuit/Protocol/ZeroRegister/Conjunction.lean` (five copies, found by `scripts/audit/tactic_pattern_scan.py` over the MPO-symmetry modules).
- **Pattern:**
  ```lean
  intro h
  have hval := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hval
  omega
  ```
  proving `Fin.castAdd n a ≠ Fin.natAdd m b`.
- **Abstraction:** `Fin.castAdd_ne_natAdd` and `Fin.natAdd_ne_castAdd` in
  QICLean's `Algebra/FinCastAddNatAdd.lean` (moved from TNLean); all five call sites use them.
- **Decision:** A lemma removes the duplication; no tactic is needed.

### Even-family adjoint equality from time-reversal invariance — promoted (2026-11-16)

- **Seen:** four five-line `have hEq` blocks deriving `mpo U N = mpo (physicalAdjointTensor U) N`
  on even lengths from `hTR : ∀ N, 1 < N → Even N → mpo U N = (mpo U N)ᴴ`, in
  `MPS/MPU/Symmetry/TimeReversal/CanonicalTwistedTransfer.lean`, `SuppliedFourSpinSourceComparison.lean`,
  `TimeReversalLocalNecessity.lean` and `TwoSiteStandardFormSourceCuts.lean`.
- **Abstraction:** none needed; the existing `mpo_physicalAdjointTensor_eq_conjTranspose` gives
  the term `fun N hN heven ↦ (hTR N hN heven).trans (mpo_physicalAdjointTensor_eq_conjTranspose
  U N).symm`, now used at all four sites.
- **Decision:** a term-mode composition of an existing lemma is the weakest mechanism; no new
  lemma or tactic.
- **Net line delta:** −8 Lean lines (four 5-line blocks → 3-line terms; #10700).

### Polynomial AKLV threshold above the logarithmic one — promoted (2026-11-15)

- **Pattern:** From `0 < g ≤ 1`, `0 ≤ E0` and `(1024/g)*(E0/g+1) ≤ t`, derive
  `aklvLogarithmicThreshold g ≤ t` by `aklvLogarithmicThreshold_le_div` and
  `nlinarith` with the positivity of `E0/g` and `1024/g`.
- **Helper:** `aklvLogarithmicThreshold_le_of_polynomial` in
  `MPS/AreaLaw/ChebyshevAGSP/PhysicalRobustness.lean`.
- **Occurrences:** Three polynomial-threshold corollaries, two in
  `AKLV/PhysicalRobustness.lean` and one in `AKLV/ClippedFilter.lean`, now use
  the helper.
- **Decision:** The common content is a scalar inequality, so a lemma replaces
  the repeated four-line argument.

### Reduced coordinate heights from a common denominator — promoted (2026-11-04)

- **Pattern:** Convert a common Gaussian-integer denominator and a norm bound
  into a decoded height bound, then use `decode_height_iff` to obtain heights
  of the two rational fractions actually stored in the code.
- **Helper:** `RationalComplexCode.coordinate_heights_of_common_denominator`
  in `MPS/AreaLaw/GroundStateAlgorithm/RationalTensor/RationalCodeHeights.lean`.
- **Occurrences:** Eight conversions in
  `BoundarySDP/WeightedTransferAccumulationBounds.lean`,
  `ContractionIntermediateBounds.lean`, `WeightedTransferBounds.lean`,
  `RationalAccumulationBounds.lean`, `WeightedOverlapBounds.lean`, and
  `RationalLocalEnergyBounds.lean` now use the helper.
- **Decision:** The conversion is a mathematical consequence of denominator
  and norm control, so a lemma replaces the repeated two-step argument.

### Left compressed Hamiltonian norm bound — promoted (2026-11-04)

- **Pattern:** From `h.hamiltonian = HL + B`, `‖h.hamiltonian‖ ≤ 2L`, and `‖B‖ ≤ 2L`,
  derive `‖HL‖ ≤ 4L` and pass the bound through restriction to the left cut,
  tensoring with the bond identity, and isometric compression.
- **Helper:** `ManyBody.ChainInteraction.leftObjective_norm_bounds` in
  `MPS/AreaLaw/GroundStateAlgorithm/ViableVector/CompressedSolutions.lean` returns the
  full-chain and cut-and-bond objective bounds. Existing
  `l2_opNorm_isometricCompression_le` gives the compressed bound.
- **Occurrences:** Seven repeated arguments in the split modules
  `SizeTrimming/CompressedSolutions.lean`, `ApproximateCertificates.lean`,
  `RationalSearch.lean`, and `LeadingVectorPrecision.lean` now use the helper.
- **Decision:** The common content is a norm estimate, so a mathematical lemma
  removes the duplication without introducing a tactic.

### Spectral tolerances from cone-order bounds — promoted (2026-11-04)

- **Pattern:** Convert tolerances of size
  `Δ / (129792 * L * nMax)` into the realized inequalities
  `2 * n * ε ≤ Δ / (64896 * L)`, using `n ≤ nMax`, and similarly for the
  auxiliary cone order.
- **Helper:** `fullyApproxSDP_scaled_errors_of_order_bounds` in
  `MPS/AreaLaw/GroundStateAlgorithm/BoundarySDP/ErrorBudgets.lean`.
- **Occurrences:** The general LVV margin theorem and the physical uniform-certificate
  theorem in `SizeTrimming.lean`; the helper treats both cone orders simultaneously.
- **Decision:** The scaling is a mathematical lemma.  It replaces repeated denominator
  positivity and nonlinear-arithmetic arguments; no tactic is introduced.

### Regional lift and inclusion of sites — promoted (2026-11-03)

- **Seen:** `Circuit/EntropySupport.lean` (deleted), `MPS/AreaLaw/LowEnergyAlgorithm/RegionalFactors/SelectedMiddleData.lean`,
  and the native middle approximation in `MPS/AreaLaw/LowEnergyAlgorithm/MPO/SoftGeneratedMiddleApproximation.lean`.
- **Pattern:** Compare the entries of a regional local lift with placement
  along the inclusion of the same sites, then identify the exterior matching
  condition with agreement away from the inclusion.
- **Helper:** `ManyBody.placeAlong_subtype` in QICLean `ManyBody/Sites/PlaceAlong.lean`.
- **Decision:** The existing coordinate identity is stated once and reused;
  the support characterization and selected singleton calculation retain their
  mathematical statements.

### Full short-interval size bounds — promoted (2026-11-03)

- **Pattern:** Bound the full interval dimension by `q ^ width`, then use
  its orthonormal basis to obtain the recorded weighted-rank bound. The
  physical leaf count also compares `q ^ (4 * ell)` with `D ^ 6 * s ^ 3`.
- **Helpers:** `interval_top_dimension_and_rank_bounds` in
  `MPS/AreaLaw/LowEnergyAlgorithm/IntervalTrimming/IntervalGenerators.lean` and the Mathlib-only
  `Nat.viable_tree_leaf_count_le` in QICLean's `Analysis/ViableNodeLeafCount.lean`.
- **Decision:** Physical-coordinate dimension and recorded-rank reasoning
  stays in TNLean; pure natural-number arithmetic belongs to QICLean.
  Neither helper assumes viability, and no new tactic is needed.

### Retaining the same calibrated physical parameters — existing construction (2026-11-03)

- **Seen:** `PhysicalDGInterleavedFamily.lean`, `PhysicalDGInterleavedIteration.lean`,
  `PhysicalDGInterleavedNode.lean` and `PhysicalDGInterleavedTree.lean`.
- **Pattern:** Unpack the shared scalar and reference data, retain their bounds,
  and introduce the local names for the reference estimate. The scanner matches
  the type exposure and tuple introduction in the earlier three consumers.
- **Reuse:** `exists_physical_dg_interleaved_filter_family` constructs the analytic
  parameters once. The iteration, sampled node and tree retain those same data;
  none repeats the tail, suppression or reference proof.
- **Decision:** This is forwarding through different mathematical conclusions,
  not repeated analytic reasoning. No tactic is introduced. The tree omits
  unnecessary type-exposure steps for the count and sampling size. The stronger
  constructions also retain the ordered-word bounds of their same family;
  the former public conclusions are projections of those shared proofs.

### Lower bound for the interleaved logarithmic scale — promoted (2026-11-03)

- **Pattern:** Derive `1 ≤ 1 + log m + log (1/g) + log (1+w)` from
  `m ≥ 2`, `0 < g ≤ 1`, and `w ≥ 1` by logarithm monotonicity.
- **Helper:** `Real.one_le_interleaved_log_scale` in
  `MPS/AreaLaw/LowEnergyAlgorithm/DegenerateGround/InterleavedFilterParameters.lean`, previously private.
- **Occurrences:** the count and width estimates in that module and the
  actual cutoff estimate in `InterleavedFilterSuppression.lean`.
- **Decision:** Expose the existing mathematical lemma with its unchanged
  statement and proof; the new consumer reuses it directly.

### Nonempty bond from a trace-one matrix — promoted (2026-10-31)

- **Pattern:** `have ha : a ≠ 0 := by intro ha; subst a; simp at htr` followed by
  `let : NeZero a := ⟨ha⟩`, where `htr : Matrix.trace ρ = 1`.
- **Helper:** `Matrix.neZero_of_trace_eq_one` in
  `TNLean/MPS/CanonicalForm/FixedPointApproximation/SecondOrderOverlap.lean`.
- **Occurrences:** about ten Preparation modules, and seven sites in
  `UncleGroundGram.lean`, `UncleNormGrowth.lean` and `UncleFiniteGaplessness.lean`,
  all now one `have : NeZero a := Matrix.neZero_of_trace_eq_one htr`.
- **Decision:** The lemma stays in `SecondOrderOverlap.lean` because that module is
  near the changed-module compile-time limit; the parent-Hamiltonian modules import it.
  A move to a leaf algebra module is a later cleanup.

### Positive dimensions of canonical blocks — promoted (2026-10-30)

- **Pattern:** `let : NeZero (h.dim k) := ⟨(h.dim_pos k).ne'⟩` before using a
  canonical block as a tensor of positive bond dimension.
- **Helper:** the instance `MPSTensor.PGVWC07CanonicalFormData.neZero_dim` in
  `TNLean/MPS/CanonicalForm/TranslationInvariant.lean`.
- **Occurrences:** two in `WeightedCanonicalSectors.lean` and one in
  `WeightedCanonicalPhysicalLimit.lean`, all removed; the two local `have`s in
  `TNLean/MPS/Examples/PVBS/WStateCanonicalBound.lean` are now redundant.
- **Decision:** An instance lets typeclass search supply positivity for every
  block, instead of a local assumption at each use.

### Boundary operator norm from its positive cap — promoted (2026-10-30)

- **Seen:** QICLean `Spectral/Filter/ExteriorClippingGap.lean` (moved from
  `MPS/AreaLaw/ChebyshevAGSP/HighEnergyMass.lean` and `ProjectionEnergy.lean`) and
  `MPS/AreaLaw/ChebyshevAGSP/InverseGapRobustness.lean`; the targeted pattern scan reports three uses.
- **Pattern:** Convert `0 ≤ A ≤ 2I` to `‖A‖ ≤ 2` with
  `CStarAlgebra.norm_le_iff_le_algebraMap` and the scalar-matrix identity.
- **Abstraction:** `Matrix.PosSemidef.norm_le_of_le_smul_one`
  (`0 ≤ A ≤ c • 1 → ‖A‖ ≤ c`) in `HighEnergyMass.lean`; the three call
  sites now apply it. No tactic or alternate operator norm is introduced.

### Matrix positivity on the Euclidean operator space — promoted (2026-10-29)

- **Seen:** QICLean `Spectral/Filter/ExteriorClippingGap.lean` (moved from
  `MPS/AreaLaw/ChebyshevAGSP/HighEnergyMass.lean`, `ProjectionEnergy.lean` and
  `LowSpectrumGap.lean`) and `MPS/AreaLaw/ChebyshevAGSP/Robustness.lean`.
- **Pattern:** Combine `Matrix.isPositive_toEuclideanLin_iff` and
  `ContinuousLinearMap.isPositive_toLinearMap_iff` to transport a matrix order bound.
- **Abstraction:** `Matrix.PosSemidef.isPositive_toEuclideanCLM` in
  `QICLean/Spectral/Filter/EnergyTruncation.lean` (QICLean dependency); all four repeated
  positivity proofs use it.
- **Decision:** A mathematical transport lemma removes the repeated coercion proof.

### One-site MPO blocking as physical relabeling — promoted (2026-10-29)

- **Pattern:** Expand one-site blocking into singleton words and identify
  its decoded physical letter with the original alphabet.
- **Defined in:** `MPS/Operator/Product/PhysicalBlocking.lean`,
  `MPOTensor.blockTensor_one_eq_reindexPhysical`.

### Conjugating a rectangular unitary identity — promoted (2026-10-29)

- **Pattern:** Commute entrywise complex conjugation with the adjoint and
  matrix multiplication, then transport the two identities `Aᴴ * A = 1`
  and `A * Aᴴ = 1` through conjugation.
- **Seen:** The two gates in `TwoSiteStandardFormData.mapStar` in
  `MPS/MPU/StandardForm/ConjugationSymmetry.lean`, and the supplied source gate in
  `IsMPUCanonicalFormII.exists_local_conjugation_gauges` in
  `MPS/MPU/StandardForm/ConjugationSourceFactors.lean`.
- **Abstraction:** `Matrix.IsUnitaryBetween.map_star` in
  `MPS/MPU/StandardForm/ConjugationSymmetry.lean` transports both identities at once.

### Adjoint simplicity from the canonical rank product — promoted (2026-10-29)

- **Pattern:** Convert simplicity to `r*ℓ=d*d`, exchange the ranks under
  physical adjunction and convert back using canonical form II.
- **Defined in:** `MPS/MPU/Simple/SourceFactorsPhysicalAdjoint.lean`,
  `IsMPUCanonicalFormII.isMPUSimple_physicalAdjointTensor`.

### Faithful bipartite matrix embeddings — promoted (2026-10-29)

- **Pattern:** Convert a left or right Kronecker embedding through ordered
  bipartite finite-region coordinates and then into the quasi-local algebra.
  Previously the local-inclusion identity and inverse-equivalence cancellation
  were written separately for both factors at each use.
- **Defined in:** `QCA/QuasiLocal/BipartiteQuasiLocalEmbedding.lean`, the canonical
  `bipartiteMatrixToQuasiLocalObservable`, its injectivity and left/right
  evaluation and full-factor range theorems.

### Eventual equality of scalar cocycle classes — promoted (2026-10-29)

- **Pattern:** transport eventual equality of `H2π` classes to eventual coboundary
  ratios using the same pointwise equivalence.
- **Defined in:** `QICLean/Algebra/Cohomology/CocycleCohomology.lean` (QICLean dependency),
  `eventually_H2π_eq_iff_isMulCoboundary₂_div`, a direct application of Mathlib's
  `Filter.eventually_congr` to the existing scalar-cocycle equivalence.

### Eliminating a geometric prefactor from a spectral rate — reused Mathlib (2026-10-29)

- **Seen:** `norm_transfer_spectrum_le_of_limitCorrelator_bound` in
  `MPS/CanonicalForm/Correlation/DecayingCorrelations.lean`.
- **Pattern:** An exact eigenvalue correlator `λ^n` and an eventual bound
  `C r^n` imply `|λ| ≤ r`, even when `C` and the starting separation depend
  on the observables.
- **Reuse:** `pow_unbounded_of_one_lt` for the ratio `|λ|/r`, then
  `pow_le_pow_right₀` to shift past the starting separation.
- **Decision:** Reuse the existing Archimedean power lemmas and physical
  eigenvalue-observer construction; no new asymptotic tactic is introduced.

### Identity site translation — promoted (2026-10-28)

- **Pattern:** Unfold the matrix of a site permutation and rewrite the identity
  laws of its two group homomorphisms.
- **Helper:** `ManyBody.sitePermOp_one` in `QICLean/ManyBody/Sites/Relabel.lean`
  (QICLean dependency).
- **Occurrences:** the arbitrary-observable ground-space power formula in
  `TranslationGroundSpace.lean`, and the two translation-orbit arguments in
  `TranslationFiniteOrbitCommutator.lean`.
- **Decision:** The third occurrence across two files was replaced by the same
  identity lemma. The statement records the mathematical unit law directly.

### From a support budget to an anchor budget — promoted (2026-10-28)

- **Pattern:** An index whose chosen anchor is a site has support containing that
  site. Monotonicity of finite sums of nonnegative weights therefore bounds the
  anchor sum by the support sum.
- **Helper:** `ManyBody.sum_weight_anchor_le_of_support_budget` in
  `QICLean/ManyBody/Dynamics/GraphGrowth.lean` (QICLean dependency).
- **Decision:** The 2026-10-28 scan found the third occurrence. The common
  inequality is stated for arbitrary nonnegative real weights; the applications
  specialize it to the original interaction norms.

### Norm of a ground-space compression — promoted (2026-10-28)

- **Seen:** the former TNLean modules `LowEnergyBasisConstruction`,
  `LowEnergyBasisUniform` (now `QICLean/ManyBody/Hamiltonian/LowEnergyBasisUniform.lean`),
  and the normalization of the general recursive basis theorem in
  `LowEnergyBasisUniformGeneral`, all since moved to QICLean.
- **Pattern:** Restrict a ground compression to its invariant ground eigenspace,
  compare its operator norm with the ambient compression, and then with the
  original term norm.
- **Helper:** formerly `norm_groundSpaceCompression_le`; in QICLean the
  ground compression is a `subspaceCompression` and the bound is the
  `subspaceCompression` norm lemma.
- **Decision:** The normalized basis arguments use this mathematical norm bound
  rather than repeat the subspace coercion and operator-norm calculation.

### Retained vectors in nested operator ranges — promoted (2026-10-28)

- **Pattern:** from `P * Q = Q` and `Q φ = φ`, deduce `P φ = φ`, previously
  proved by substituting the second equality into the first matrix action.
- **Abstraction:** `Matrix.toEuclideanLin_eq_of_mul_eq`
  in `QICLean/Spectral/LowEnergy/HierarchicalProjection.lean` (QICLean dependency).
- **Call sites:** the compressed-window and child-projection arguments in
  `FinalStateEnergy.lean`, and the child and closing-window arguments in
  `HierarchyNesting.lean`. The matrix identities still state the particular
  nesting relation; the common argument on retained vectors is shared.

### Diameter of a chain support in graph distance — promoted (2026-10-28)

- **Pattern:** Convert the range condition of `ChainSupport L R` to an upper
  bound on the path-graph distance between two sites of the support.
- **Defined in:** `QICLean/ManyBody/Sites/Lattice/Chain.lean` (QICLean dependency),
  `ManyBody.ChainSupport.edist_le`.

### Matrices of submodule orthogonal projections — promoted (2026-10-26)

- **Pattern:** Form `Matrix.toEuclideanLin.symm W.starProjection.toLinearMap`
  and prove that it is Hermitian and idempotent, either separately or by
  transporting `isStarProjection_starProjection` through `Matrix.toEuclideanCLM`.
- **Defined in:** `QICLean/Analysis/Projection/MatrixStarProjection.lean` (QICLean dependency),
  `Submodule.starProjectionMatrix`, `Submodule.isStarProjection_starProjectionMatrix`,
  and the evaluation lemma `Submodule.toEuclideanLin_starProjectionMatrix`.

### Raising a time bound inside a light-cone exponential — promoted (2026-10-25)

- **Pattern:**
  ```lean
  Real.exp_le_exp.mpr (sub_le_sub_right (mul_le_mul_of_nonneg_left hs hv) _)
  ```
  turning `hs : |s| ≤ T` and `hv : 0 ≤ v` into
  `Real.exp (v * |s| - c) ≤ Real.exp (v * T - c)`.
- **Defined in:** `QICLean/Analysis/Real/ExplicitThresholds.lean` (QICLean dependency),
  `Real.exp_mul_sub_le_exp_mul_sub (hv : 0 ≤ v) (hx : x ≤ T) :
  exp (v * x - c) ≤ exp (v * T - c)`.
- **Use when:** A Lieb–Robinson factor `exp (v |t| - c)` must be bounded
  uniformly on `[-T, T]`; pass `x = |t|`.

### Hermitian partial sums of terms Hermitian on a set — promoted (2026-10-25)

- **Pattern:** `Matrix.isHermitian_sum T fun i hi ↦ hh i (hT hi)` for `hT : T ⊆ S`.
- **Seen:** Five occurrences across three files: three in
  `QICLean/Analysis/ClusterExpansion/ClusterPart.lean` and one each in the
  former TNLean modules `ClusterExpansion/ThermalProduct` and
  `ClusterExpansion/TruncatedPositivity`, all three since moved to QICLean's
  `Analysis/ClusterExpansion`.
- **Abstraction:** `Matrix.isHermitian_sum_of_subset` in
  `QICLean/Algebra/Hermitian/HermitianPartSum.lean` (QICLean dependency); all five occurrences use the theorem.

### Hermitian sum of pointwise-Hermitian terms — promoted (2026-10-23)
- **Pattern:**
  ```lean
  isSelfAdjoint_sum Finset.univ fun j _ => (hHerm j).isSelfAdjoint
  ```
- **Seen:** 5 occurrences across 3 files: three in
  the former TNLean module `GaussianFilteredTermLocalization` (since moved to
  QICLean), one each in
  `QICLean/ManyBody/Dynamics/GraphLocalization.lean` and
  `QICLean/ManyBody/Dynamics/CommutatorRecursion.lean`.
- **Abstraction:** `Matrix.isHermitian_sum` in
  `QICLean/Algebra/Hermitian/HermitianPartSum.lean` (QICLean dependency); all five call sites refactored.

### Gaussian absolute first moment — promoted (2026-10-23)

- **Pattern:** Bound the integral of `|t|` against a centred Gaussian, either
  by `√(2h/π)` or by the simpler `√h`.
- **Seen:** The tail specialization in the former TNLean module `GaussianFilteredIncrement`
  and the independent variance argument in `MPS/AreaLaw/ProjectorFactorization/GaussianTimeAverage.lean`.
  The additional proof reported in #9945 is already absent from main.
- **Abstraction:** `GaussianFilter.integral_abs_gaussianReal_le_sqrt_two_mul_div_pi`
  specializes the existing tail bound to zero; `integral_abs_gaussianReal_le`
  follows by `2 ≤ π`. Both live in `QICLean/Analysis/Calculus/Kernel.lean` (QICLean dependency).

### A configuration from a unit vector — promoted (2026-10-23)

- **Pattern:** Prove the configuration type nonempty by contradiction: an empty index
  type makes the vector space a subsingleton, so a unit vector would have norm zero.
- **Seen:** Three occurrences in `MPS/AreaLaw/ProjectorFactorization/IntervalMutualInformation.lean`,
  `RelentAssembly.lean`, and `SchmidtDiagonalChain.lean`.
- **Abstraction:** Use the existing Mathlib results `Function.ne_iff`,
  `WithLp.ofLp_eq_zero`, and `norm_ne_zero_iff` directly:

  ```lean
  obtain ⟨σ₀, _⟩ := Function.ne_iff.mp
    ((WithLp.ofLp_eq_zero (x := Ω)).not.mpr (norm_ne_zero_iff.mp (by simp [hΩ])))
  ```

### Replica-swap entropy comparison — promoted (2026-10-21)

- **Pattern:** Two identical normalized replicas, a regional swap, and a unitary supported away from two cores imply a mutual-information bound from the vector approximation error.
- **Defined in:** QICLean (dependency), `ManyBody.regionMutualInformation_cores_le_of_reset_unitary`.

### Supported Gaussian averaging — promoted (2026-10-21)

- **Pattern:** Factor the two-Hamiltonian integrand into an evolved observable and relative evolution, localize the two factors on possibly different regions, and integrate against the restricted Gaussian measure.
- **Defined in:** `QICLean/ManyBody/Dynamics/SupportedGaussianIntegral.lean`, `ManyBody.exists_supported_gaussian_integral_of_projection_bounds`.
- **Use when:** Actual observable and generator projection estimates give scalar errors on a symmetric time interval. The theorem constructs one supported path before the observable and averaging data, retains the two projection regions and a common containing output region, and supplies support, norm and error bounds for the average.

### Counting supports in short windows — promoted (2026-10-21)

- **Pattern:** Bound the number of supports contained in a window of at most `n`
  sites by `2^n`.
- **Seen:** `ManyBody.card_crossingTerms_interval_le`,
  `ManyBody.ChainInteraction.sum_norm_terms_containing_le`, and
  `ManyBody.card_crossingTerms_le_mul_card_boundaryEdges`, now in QICLean.
- **Abstraction:** `ManyBody.ChainSupport.card_filter_subset_le_pow_of_card_le` in
  QICLean's `ManyBody/Sites/Lattice/ChainCut.lean`, combining the powerset count with
  monotonicity of powers.

### Squared logarithms of bounded support dimensions — promoted (2026-10-21)

- **Pattern:** Compare `log (exp 1 * d_X)^2` with
  `log (exp 1 * q^(R+1))^2` for a support of range `R`.
- **Seen:** `ManyBody.cutLogBudget_interval_le` and
  `ManyBody.ChainInteraction.cutLogBudget_interval_le_of_consecutive_terms`.
- **Abstraction:** `ManyBody.ChainSupport.log_sq_supportDim_le` in QICLean's
  `ManyBody/Sites/Lattice/ChainCut.lean`.

### Monotone range-R patch radii — promoted (2026-10-21)

- **Pattern:** cast `i ≤ j` to `ℝ`, note `0 ≤ s_R`, unfold the radius
  `u + s_R j` and close with `nlinarith`.
- **Seen:** 3 occurrences across 2 files (`rangeNestedPatch_mono` in
  `QICLean/ManyBody/Sites/Lattice/RangeNestedPatches.lean`, and
  `uniform_rangeNestedPatch_cylinders` and `rangeAdaptivePatchSupply` in
  `TNLean/PEPS/Approximation/NestedPatches/RangeNestedPatchApproximation.lean`).
- **Abstraction:** `ManyBody.rangeNestedPatchRadius_mono`.

### Exact commutation across an infinite graph distance — promoted (2026-10-21)

- **Pattern:** Finite interaction-support diameter makes the sites not reachable
  from the final site interaction-closed. This set contains the entire initial
  support and is disjoint from the final site. Exact locality then gives zero
  commutator for every time.
- **Abstraction:**
  `ManyBody.heisenberg_commutator_eq_zero_of_forall_edist_eq_top` in
  `QICLean/ManyBody/Dynamics/GraphPropagation.lean` states the arbitrary-support result.
  It needs neither anchors nor Hermiticity, a norm budget, a support-cardinality
  bound, positive local dimension, or nonempty initial support.
- **Seen:** The anchored theorem
  `heisenberg_commutator_eq_zero_of_edist_eq_top`, the infinite-distance branch of
  `norm_heisenberg_commutator_le_graph_kernel_sum` in `GraphLocalization.lean`,
  and `norm_heisenberg_commutator_le_graphDistance_inf`, formerly in
  a TNLean chain module and now in QICLean's `GraphPropagation.lean`.

### Margin and cell-side bounds of angular information — promoted (2026-10-21)

- **Pattern:** From `0 < a`, derive `0 < angularMargin a`,
  `angularMargin a < a / 100`, `0 < angularCellSide a` and
  `angularCellSide a < angularMargin a / 4` (and sometimes
  `angularCellSide a ≤ 1`) by unfolding `min a 1 / 200` and `/ 8`.
- **Seen:** `angularInformationBound_of_sublinearCollarBoundAt_le` in
  `PEPS/Approximation/Information/AngularInformationFromCollar.lean`, and
  `isAngularScale_of_bounds` and `isAngularScale_range_closed_le` in
  `PEPS/Approximation/Information/RangeAngularInformation.lean` (2026-10-21).
- **Promoted:** `angularMargin_cellSide_bounds` in
  `PEPS/Approximation/Information/AngularInformationFromCollar.lean` returns the five
  bounds from `0 < a`; the three proofs destructure it with `obtain`.

### Nonnegative interaction bound at a site — promoted (2026-10-18)

- **Pattern:** At an actual site, use its admissible singleton support and
  `norm_nonneg` followed by the interaction norm bound to derive `0 ≤ J`.
- **Seen:** `ManyBody.ChainInteraction.sum_norm_terms_containing_le` in
  QICLean's `ManyBody/Hamiltonian/Models.lean`, the nonempty-chain branch of
  `ManyBody.ChainInteraction.partialSwap_boundary_spec` in
  QICLean's `ManyBody/Hamiltonian/Chain/Doubled.lean`, and the logarithmic-separation proof in
  `MPS/AreaLaw/Entropy/AreaLaw.lean`.
- **Abstraction:** `ManyBody.ChainInteraction.norm_bound_nonneg` in
  QICLean's `ManyBody/Hamiltonian/Models.lean`; all three arguments use this lemma.
  For finite induced domains, `ManyBody.DomainInteraction.norm_bound_nonneg` in
  QICLean's `ManyBody/Hamiltonian/Models.lean` uses the admissible singleton
  and is reused by the domain per-site budget. The domain swapped and
  per-replica perturbation proofs also use it at a member of each original
  nonempty support.

### Collar and amplification constants from the existential collar bound — promoted (2026-10-18)

- **Pattern:**

  ```lean
  obtain ⟨C, N, hcol⟩ := hcol
  obtain ⟨Ca, Na, hamp⟩ := amplificationBound (q := q) (R := 1) (J := J) hΔ (max C 1)
    (lt_of_lt_of_le one_pos (le_max_right _ _)) 1 le_rfl
  ```

- **Seen:** Six occurrences across six files: `TNLean/PEPS/Approximation/Information/CoarseInformation.lean`,
  `CellConditionalInformation.lean`, `SquareCellConditionalInformation.lean`,
  `AngularWholeCellInformationFromCollar.lean`, `AngularSingleScaleReset.lean` and
  `AngularInformationFromCollar.lean`.
- **Abstraction:** `TNLean.PEPS.Approximation.exists_sublinearCollarBoundAt_amplificationBoundAt
  (hΔ : 0 < Δ) (hcol : SublinearCollarBound q R J Δ D₀ Ctpl) : ∃ C N Ca Na,
  SublinearCollarBoundAt q R J Δ D₀ Ctpl C N ∧ AmplificationBoundAt q R J Δ (max C 1) 1 Ca Na`
  in `CoarseInformation.lean`, built on `amplificationBoundAt_collarAmplification` in the same
  file.

### Real initial-box scale exceeds one — promoted (2026-10-18)

- **Pattern:** cast `1 < initialBoxScale q R J Δ` from the natural bound
  `sixteen_le_initialBoxScale` to obtain positivity of its real logarithm.
- **Seen:** Three occurrences across `InitialBoxEstimate.lean`
  (`initialBoxExponent_pos_and_lt_one`) and `InitialExponentGain.lean`
  (`one_sub_initialBoxExponent_eq`, `initialBoxExponent_gain_bounds`).
- **Abstraction:** `TNLean.PEPS.AreaLaw.one_lt_initialBoxScale` in
  `TNLean/PEPS/AreaLaw/Polygons/SafeRectangles/InitialBoxEstimate.lean`, beside `sixteen_le_initialBoxScale`.

### Independent gate arity and party lifetime — promoted (2026-10-18)

- **Pattern:** Count the tagged links meeting a party by summing the two link
  kinds over its actual gate occurrences, keeping arity and lifetime separate.
- **Seen:** The general incidence estimate and the former common-bound proof
  in `PEPS/Approximation/DistributedLinks.lean`; its transports occur in
  `PEPS/Approximation/SeparateArityCompression.lean`.
- **Abstraction:** `card_incidentDistributedLinks_le_of_arity_lifetime` gives
  `2 * lifetime * (arity - 1)`. The old common-bound theorem is its specialization,
  and the source-circuit and replacement estimates call it.

### Unit logarithm from a threshold at least three — promoted (2026-10-18)

- **Pattern:**

  ```lean
  have hlogn : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    exact Real.exp_one_lt_three.le.trans (by exact_mod_cast hn3)
  ```

- **Seen:** Four occurrences across four files: `Scan/RadiusAsymptotics.lean`,
  `Scan/FixedWeightTransportSmallness.lean`, `Scan/SourceSelectedSharpEnergy.lean`
  and `Scan/GenericChargeEnergy.lean`.
- **Abstraction:** `Real.one_le_log_natCast_of_three_le {n : ℕ} (hn : 3 ≤ n) :
  1 ≤ Real.log n` in `QICLean/Analysis/Real/ExplicitThresholds.lean` (QICLean dependency), next to
  `Real.one_le_log_of_ceil_logRpowThreshold_le`, which covers only thresholds of
  the form `⌈logRpowThreshold C η u v L⌉₊`.

### Nonnegative interaction bound at a site — promoted (2026-10-18)

- **Pattern:** At an actual site, use its admissible singleton support and
  `norm_nonneg` followed by the interaction norm bound to derive `0 ≤ J`.
- **Seen:** `ManyBody.ChainInteraction.sum_norm_terms_containing_le` in
  QICLean's `ManyBody/Hamiltonian/Models.lean`, the nonempty-chain branch of
  `ManyBody.ChainInteraction.partialSwap_boundary_spec` in
  QICLean's `ManyBody/Hamiltonian/Chain/Doubled.lean`, and the logarithmic-separation proof in
  `MPS/AreaLaw/Entropy/AreaLaw.lean`.
- **Abstraction:** `ManyBody.ChainInteraction.norm_bound_nonneg` in
  QICLean's `ManyBody/Hamiltonian/Models.lean`; all three arguments use this lemma.

### Labels introduced by the edge operations — promoted (2026-10-16)

- **Pattern:** the case analysis showing that one of the seven births and deaths of an
  edge construction introduces a single label.
- **Seen:** the aggregate `edgeOperations_insertsOne` and the per-operation chains of
  `DyadicEdgeOperationChains.lean`.
- **Abstraction:** the seven lemmas `auxBirthB_insertsOne`, …, `mainDeathB_insertsOne` in
  `Approximation/DyadicTrueVertices.lean`; the aggregate is derived from them.

### Sites separated from guide holes — promoted (2026-10-16)

- **Pattern:** recover the patch of a guide hole, turn membership in its outer sample
  into a weak distance bound, and contradict strict separation of the changed sites.
- **Seen:** three copies in `centralBirth_hasFrameChange_of`,
  `bandBirth_hasFrameChange`, and `bandDeath_hasFrameChange`.
- **Abstraction:** `TNLean.PEPS.Approximation.disjoint_outerHoles_guideFrame` in
  `DyadicGuideFrames.lean`, reusing `disjoint_footprint_of_forall`; all three callers
  now supply their separation estimate to this lemma.

### Non-root dyadic side bound — promoted (2026-10-16)

- **Pattern:** for `R : RepaintedSquare k` and `hk2 : 2 ^ k < 2 * L`, derive
  `(2 : ℝ) ^ (R.1.1 : ℕ) ≤ (L : ℝ)` from the non-root level bound.
- **Promoted helper:** `RepaintedSquare.side_le` in
  `TNLean/PEPS/Approximation/Guides/DyadicProtocolParties.lean`.
- **Consumers:** `centralBirth_hasFrameChange`, `edgeExchange_hasPairChange`,
  `bandBirth_hasFrameChange`, and `bandDeath_hasFrameChange`.

### The two labels near a treated central birth — promoted (2026-10-16)

- **Pattern:** use the central separation floor to show that the surrounding
  guide is the old label near the changed region, then split according to
  whether the point is changed to bound the central guide by two labels.
- **Seen:** two proof copies, in `RepaintingBaseline.isTrueVertex_central_treated`
  (`DyadicTrueVertices.lean`) and `RepaintingBaseline.central_treated_mem`
  (`DyadicCentralBirthChange.lean`).
- **Abstraction:** the existing `RepaintingBaseline.central_treated_mem` is
  placed in `DyadicTrueVertices.lean`; the true-vertex theorem uses its two
  conclusions, and the central-birth frame proof keeps the same call.

### Owner change of a sampled guide frame — promoted (2026-10-16)

- **Pattern:** the frame of a reading equals the frame of another reading with
  the owners of the differing sites handed to one label, from equal true
  vertices, equal incident labels and the label at the differing sites
  (`06-geometry.tex`, lines 375–387).
- **Seen:** the band birth and death of `DyadicBandStepChanges.lean` and the
  central birth of `DyadicCentralBirthChange.lean`.
- **Abstraction:** `TNLean.PEPS.Approximation.guideFrame_eq_changeOwner_of_ne`
  (`Approximation/DyadicBulkFrames.lean`); the three call sites use it.

### Fixed-circuit bounded-change lifts beside spectator sheets — promoted (2026-10-16)

- **Pattern:** Assemble the five `OriginalCircuit.IsBoundedChange` fields for
  `liftOne` or `liftTwo`: transport the nonprivate count, participants, expansion
  bound, monomial bound and error estimate through untouched spectator sheets.
- **Seen:** `hasBoundedChange_liftOne`, `hasBoundedChange_liftTwo` and their
  source-bounded forms, now in `QICLean/Circuit/Party/Sheet/StackChange.lean`.
- **Abstraction:** `QuantumCircuit.Party.isBoundedChange_liftOne` and
  `isBoundedChange_liftTwo` in `QICLean/Circuit/Party/Sheet/StackChange.lean`
  (QICLean dependency), stated for the fixed
  lifted circuit over any type of sheets; all four results now use them, and the
  encoded-frame forms in `PEPS/Approximation/Frames/SheetStackChange.lean` read them at the
  frames.

### Positive part of a polynomial constant — promoted (2026-10-16)

- **Pattern:** Replace a constant `C` of a polynomial bound `x ≤ C * L ^ k` by `max C 0`, so that
  a theorem needs no sign hypothesis on `C`, and transport the given bound along
  `C * L ^ k ≤ max C 0 * L ^ k` for `0 ≤ L`.
- **Seen:** the compression theorems and the dyadic protocol, in
  `TNLean/Network/SampledApproximation/UniformApproximateSampledNetwork.lean`,
  `TNLean/PEPS/Approximation/PartyCircuit/UniformMessageGateCompression.lean` and
  `TNLean/PEPS/Approximation/Protocol/DyadicProtocolCompression.lean`.
- **Abstraction:** `TNLean.Network.mul_pow_le_max_zero_mul_pow` in
  `UniformApproximateSampledNetwork.lean`.

### Euclidean norm and nonvanishing in augmented replica coordinates — promoted (2026-10-16)

- **Pattern:** Reindex a replica prevector from the physical and two auxiliary
  site coordinates to the scanner coordinates, preserve its Euclidean norm,
  and transfer nonvanishing or a norm upper bound.
- **Seen:** Three nonvanishing arguments and three norm arguments across
  `AugmentedReplicaPrevectorProperties.lean`, `ActualRoughLowerPrevector.lean`,
  `ActualSharpLowerPrevector.lean`, and `ActualEndpointRoughBudget.lean`, under
  `PEPS/AreaLaw/Scan/`.
- **Abstraction:** `norm_augmentedReplicaPrevector_eq_global` and
  `augmentedReplicaPrevector_ne_zero_iff_global` in
  `AugmentedReplicaPrevectorProperties.lean`, using Mathlib's
  `LinearIsometryEquiv.piLpCongrLeft` and the characterization of zero by its
  norm. The existing larger coordinate theorem and all three comparison
  consumers use these declarations.

### Scanner prevector coordinates and selected density — promoted (2026-10-15)

- **Pattern:** Transfer nonvanishing, copy symmetry and a mean-energy
  eigen-equation from global replica coordinates to augmented site coordinates;
  then bound the selected normalized density using the rough endpoint estimate.
- **Seen:** Two identical private copies of each proof in
  `SourceRoughSelection.lean` and `SourceSelectedSharpComparison.lean`, under
  `PEPS/AreaLaw/Scan/`, plus the new consumer `SourceChargeSelection.lean`.
  The two copies were extracted; the new consumer uses the shared declarations.
- **Abstraction:** `augmented_prevector_properties_of_global` in
  `AugmentedReplicaPrevectorProperties.lean` and
  `selected_density_of_rough_endpoint` in `RoughSelectionBudget.lean`.
  All three comparisons use these shared declarations.

### Rough lower comparisons at a prescribed metric weight — promoted (2026-10-15)

- **Pattern:** Prove the actual rough lower comparison and its vanishing
  remainder for an arbitrary per-band weight, then specialize to total weight
  four by substituting `a = 4 / K`.
- **Seen:** The finite-copy comparison, remainder limit and supplied-prevector
  comparison in `ActualRoughLower.lean` and `ActualRoughLowerPrevector.lean`,
  under `PEPS/AreaLaw/CollarEntropy/NormComparisons/`, and the remainder limit in
  `QICLean/Representation/Bell/LabelDimensionRemainder.lean`.
- **Abstraction:** `exists_actualScan_rough_lower_norm_of_weight`,
  `tendsto_roughLowerRemainderAtWeight_of_label_dimension` and
  `exists_actualScan_suppliedPrevector_rough_lower_of_weight` retain the weight
  as a parameter. Each general proof occurs once, and the original
  weight-four statements invoke these results.

### Patch net covers in the plane conditions — promoted (2026-10-15)

- **Pattern:** From `exists_netCover`, turn the cover of a set `K` by the net `u ℤ²` into a cover
  by the inner squares of the patches at the net points, and bound the outer square of a patch at
  a net point within `3 u` of `K`.
- **Seen:** the direct repainting, the resize and the local rewrite, in
  `DyadicDirectRepaintingRewrite.lean`, `DyadicResizeRewrite.lean` and `LocalGuideRewrite.lean`
  under `TNLean/PEPS/Approximation/`.
- **Abstraction:** `exists_mem_image_dist_le_scale` and `exists_dist_lt_of_mem_image` in
  `GuideFrameRewrite.lean`.

### Ambient dilation in coordinate inequalities — promoted (2026-10-14)

- **Pattern:** Expand the finite union of integer squares, their Cartesian
  products and interval membership to obtain coordinate inequalities.
- **Seen:** The original membership lemma in `Geometry/TemplateRows.lean`,
  `ManyBody.ambientDepth_le_iff_mem_ambientDilation` (now in QICLean's
  `ManyBody/Sites/Lattice/SupDistance.lean`), and
  `exterior_union_subset_graphNeighborhood_compl_of_clearance` in
  `GraphNeighborhoodCutClearance.lean`, under `TNLean/PEPS/AreaLaw/`.
- **Abstraction:** QICLean's `ManyBody.mem_ambientDilation_iff` follows
  `ManyBody.ambientDilation` in `QICLean/ManyBody/Sites/Lattice/Plane.lean`. The ambient-depth
  equivalence and the whole-remote exclusion proof simplify with this lemma.
  No alias, new tactic, global attribute or geometric hypothesis is added.
- **Remaining occurrences:** Direct expansions remain in `BufferedRectangles.lean`
  and `Geometry/DistanceLayers.lean`, `Geometry/DummyContacts.lean`,
  `Geometry/DyadicExhaustion.lean` and `Geometry/DyadicLayers.lean`. They are
  retained for a focused follow-up. The private dyadic-layer lemma has a
  different absolute-value formulation and is not a duplicate declaration.

### Finite virtual coordinates — promoted through Mathlib (2026-10-14)

- **Pattern:** Enumerate each finite virtual alphabet independently, then
  transport the finite contraction sum through the product bijection.
- **Seen:** `Routing.toTensor_stateCoeff` in `RoutedContraction.lean` and
  `DistributedOperatorContraction.operatorCoeff_toPartyNetwork` in
  `DistributedPartyNetwork.lean`, both under `PEPS/Approximation/`.
- **Abstraction:** Mathlib's `Equiv.piCongrRight` forms the product bijection;
  `Equiv.sum_comp` transports the whole sum. Local factors reduce by
  `Equiv.symm_apply_apply`. Both proofs use these existing declarations.

### Named comparison of arbitrary word evaluations — promoted (2026-10-14)

- **Pattern:** Retain two constructed words and their own layouts in a named
  proposition defined literally by heterogeneous equality of their evaluations.
- **Seen:** `preparedWordEvalComparison` in `IncidentSourceWordComparison.lean`,
  `wordEvalComparison` in `IncidentSampledEndpointComparison.lean`, the generic
  coordinate and original-word comparisons in `IncidentSampledPhysicalFactor.lean`,
  and the sampled-to-incident comparison in
  `SampledEndpointIncidentComparison.lean`, under `PEPS/Approximation/`.
- **Abstraction:** `Word.IsEvalComparison` in `WordEvalComparison.lean` states this
  common comparison. The two existing private predicates delegate to it with
  unchanged signatures; their theorem statements and proofs are unchanged.
  `Word.IsEvalComparison.eval_eq` reuses Core `eq_of_heq` on fixed layouts.
  `Word.isEvalComparison_of_eval_eq` reuses Core `heq_of_eq` with both word
  arguments explicit; the three physical component comparisons use it before
  the actual operator-equality proof is supplied.
- **Purpose:** Match propositions on arbitrary words before evaluating concrete
  original-circuit or sampled-operator expressions. The physical-coordinate
  argument derives all three component comparisons from the existing word
  results and converts them to ordinary equality only for abstract words.

### Final comparison after restricted simplification — promoted (2026-10-14)

- **Pattern:** simplify a supplied equality with a fixed list of lemmas, then
  compare its result with the goal when ordinary definition unfolding is
  needed to identify coordinate aliases or an equivalence's forward function.
- **Seen:** four final comparisons in
  `PEPS/Approximation/IncidentSampledPhysicalFactor.lean`,
  `PEPS/Approximation/IncidentPureSampledPhysicalSum.lean`,
  `PEPS/Approximation/SourceNetworkDimensions.lean`, and
  `PEPS/Approximation/OriginalGateSamplePhysicalSum.lean`.
- **Abstraction:** reuse Lean's existing `simpa only [...] using! h`. Its
  simplification is identical to `simpa only [...] using h`; only the final
  comparison uses default transparency. The pinned implementation is
  `Lean/Elab/Tactic/Simpa.lean`, lines 50–54 and 168–177.

### Restriction of equal words with dependent source proofs — promoted (2026-10-13)

- **Pattern:** Transport the word together with its source-free proof before
  comparing restrictions. Ordinary rewriting may keep a generated proof fixed
  while changing the word on which it depends.
- **Seen:** The unequal-owner source case of `WordSelectedOwnerLocalPart`,
  the two actual gate words in `AllPartySingletonComparison`, and the fixed-layout
  sampled-word comparison in `SampledEndpointIncidentComparison`.
- **Abstraction:** The existing `congrArg` and `congrArg₂` transport the complete
  comparison proposition. For source-free words on a fixed layout, `Subtype.ext`
  transports the word together with its proof before `congrArg` is applied.
  Changes of layouts use the existing `Word.restrict_castLayouts`.

- **Shared selected-word comparison:** `Word.IsSelectedLocalPartComparison` in
  `AllPartySingletonComparison` records the exact selected remaining evaluation.
  Its single-gate theorem supplies the circuit comparison directly from the
  existing incident and nonincident arguments. The circuit's superseded private
  lifting lemma is removed. Two named axiom checks and two unmarked blueprint
  entries accompany the new declarations; Lean verification remains pending.

### Parent ground-space equivalences and ordered transports — promoted (2026-10-13)

- **Pattern:** (a) a parent ground-space equivalence built as
  `LinearEquiv.ofBijective` of a `codRestrict`ed transport, with injectivity
  proved by cancelling a left inverse by hand; (b) an ordered-edge parent
  transport statement proved in parallel with its oriented counterpart
  (SCP10, arXiv:1001.3807, Theorem 5.7 and Section 7, lines 2938–3019).
- **Seen:** (a) five equivalences, in `CopyCanonicalParentTransport.lean`,
  `OrientedCopyParentTransport.lean`,
  `GraphCoordinateCanonicalParentTransport.lean`,
  `OrientedCoordinateParentTransport.lean` and
  `RangePhysicalParentTransport.lean` under `PEPS/ParentHamiltonian/`;
  (b) the ordered statements of `CopyCanonicalParentTransport.lean` and
  `GraphCoordinateCanonicalParentTransport.lean`.
- **Abstraction:** (a) `LinearMap.submoduleEquivOfInjOn`
  (`PEPS/ParentHamiltonian/Region/RegionPhysicalGroundSpaceTransport.lean`), with
  injectivity from Mathlib's `Set.LeftInvOn.injOn`; (b) state the ordered
  result as the oriented one at `o = fun _ => false`, through
  `numberedGraphOrientedAveragingTensor_false` and
  `graphNumberedBondFamilyMatrix_orientedBondCoordinateMatrix_false`.

### Homogeneous ceiling bound — promoted (2026-10-13)

- **Pattern:** for `0 ≤ x ≤ A * s` and `1 ≤ s`, absorb rounding into the
  coefficient by `(Nat.ceil x : ℝ) ≤ (A + 1) * s`, before taking any
  nonnegative real powers of the scale.
- **Seen:** three elementary ceiling estimates in
  `PEPS/AreaLaw/CollarEntropy/BoxExponent/BootstrapRoundedClearance.lean`,
  `PEPS/AreaLaw/Collar/Scales/RoundedScalePower.lean`, and
  `PEPS/Approximation/PartyCircuit/UniformMessageGateCompression.lean`.
- **Abstraction:** `Nat.ceil_le_add_one_mul_of_le_mul` in
  `QICLean/Analysis/Real/ExplicitThresholds.lean` (QICLean dependency), proved from Mathlib's
  `Nat.ceil_lt_add_one`, monotonicity of addition, and distributivity.

### Actual sampled local physical matrices — promoted (2026-10-12)

- **Pattern:** The same mixed physical trace, with independent chronological
  choices and one original sample assignment, appeared in
  `ActualSampledPhysicalFactors`, `ActualSampledPhysicalScalar` and
  `ActualPureSampledPhysicalSum`.
- **Promotion:** `SourceCircuit.sampledPhysicalFactor` records this matrix once
  in `ActualSampledPhysicalFactors`. All three statements use that definition;
  its physical indices are the original indices and its private basis is the
  actual selected private basis. No scalar or norm is cancelled.
- **Verification:** The existing physical-trace fixture checks the definition
  by name, and its blueprint definition is marked complete.

### Reflected marked-chain scalar and gauge cancellation — promoted (2026-10-12)

- **Pattern:** conjugate a double sum `∑ i j, star (x i) * K i j * y j`
  through `star_sum`/`star_mul'`/`Finset.sum_comm`, cancel a positive
  self-conjugate scalar from a conjugate identity by `mul_left_cancel₀`, and
  cancel a vertical gauge by conjugating a reflected identity with the
  adjoint gauge (`hCov`/`hLeft`/`hRight`).
- **Seen:** each of the three blocks twice, in
  `TNLean/MPS/MPDO/Vertical/ReflectedMarkedChain.lean` and
  `TNLean/MPS/MPDO/Vertical/FigureEightPairwise.lean` (the gauge block
  also in `FigureEightPairwise.lean`); 150 lines in total.
- **Abstraction:** `Finset.sum_sum_star_mul_mul_eq_star` and
  `MPOTensor.markedChainCoefficient_eq_reflectedAdjoint_of_mul_eq_star` in
  `ReflectedMarkedChain.lean`;
  `MPOTensor.markedChainCoefficient_gramDressing_eq_of_bondMul_reflected` in
  `FigureEightPairwise.lean`. The self-conjugacy of a positive scalar is
  Mathlib's `IsSelfAdjoint.of_nonneg`.

### Incident edges that are not internal — promoted (2026-10-12)

- **Pattern:** an edge with an endpoint in a region `R` but not both endpoints
  in `R` crosses the boundary of `R`, proved by a case split on which endpoint
  lies in `R`, either as a private lemma or inline when splitting incident
  configurations into internal and boundary edges.
- **Seen:** nine call sites in nine files: three private copies
  (`boundary_of_incident_not_internal` in `RegularRegionProjectorCoordinates.lean`,
  `ParentHamiltonian/RegionGroundSpaceNesting.lean` and
  `ParentHamiltonian/RegularRegionOrbitCoordinates.lean`) and six inline case
  splits (`GraphOpenRegionContraction.lean`,
  `ParentHamiltonian/GraphDependentRegionSupport.lean`,
  `GraphInsertedRegionSupport.lean`, `RegularRegionCoordinates.lean`,
  `ParentHamiltonian/RegularLiftedRegionRange.lean`,
  `RegularEdgeChargeContraction.lean`).
- **Abstraction:** `ManyBody.IsRegionIncidentEdge.isRegionBoundaryEdge` in
  `QICLean/ManyBody/Sites/Lattice/Edge.lean` (QICLean dependency), combined with
  `isRegionIncidentEdge_of_regionVertex` for an edge at a region vertex.

### Fan endpoints, capped-partition moments and closed-cell convexity — promoted (2026-10-12)

- **Pattern:** (a) `change` blocks spelling out the coordinates of the
  endpoints of an elementary fan segment of a dyadic cell, one per side
  (Section 11, lines 299–310); (b) grouping a capped dyadic partition by scale,
  summing the geometric series and comparing powers to bound its moment of
  order `1 + e` (Lemma 9.4, `08-scanner.tex`, lines 656–664); (c) an inline
  proof that the closed rectangle of a dyadic cell is convex.
- **Seen:** (a) six files under `PEPS/AreaLaw/Geometry`: `SideEndpoints.lean`,
  `CellContacts.lean`, `SideSubdivision.lean`, `SideSubdivisionMask.lean`,
  `ActualSideMatching.lean` and `FanRuns.lean`; (b) three weighted cover
  estimates, in `TemplateCoreCover.lean`, `TemplateShellCover.lean` and
  `RectangleShellWeightedCover.lean`; (c) four files: `DummyCorners.lean`,
  `ElementarySideOpponents.lean`, `ElementarySideReciprocity.lean` and
  `SideSubdivision.lean`.
- **Abstraction:** in `TNLean.PEPS.AreaLaw.Geometry`: (a) `cellFanStart_eq`,
  `cellFanEnd_eq` (`Geometry/CellFans.lean`), used as
  `simp [cellFanStart_eq, cellFanEnd_eq, cellFanCenter, cellFanSideVector]`
  after `fin_cases`; (b) `sum_rpow_cappedDyadicPartition_le`
  (`Geometry/CappedDyadicPartitionByScale.lean`); (c)
  `convex_closure_dyadicCell` (`Geometry/DyadicClosure.lean`).

### Endpoint-membership splits closed by `grind` — promoted (2026-10-12)

- **Pattern:** a propositional classification of an edge relative to two
  disjoint vertex sets, closed by a sixteen-way `by_cases` split on the
  membership of both endpoints in both sets followed by `simp_all`.
- **Seen:** six classifications in
  `PEPS/Approximation/WholeGroupContraction.lean` (proof of Lemma 6.2,
  `05-frames.tex`, lines 143–157); under `PEPS/RegionBlock/`,
  `CoarseThreeSiteCoherentFrame.lean`, `CoarseThreeSite4.lean`,
  `UnionInjectivityGeneral.lean`, `UnionInjectivityGeneral2.lean`,
  `UnionInjectivityOverlapSetup.lean`, `UnionInjectivityOverlap3.lean`,
  `UnionInjectivityOverlapBridge.lean`, `InsertResidual.lean` and
  `ScalarExtraction.lean`; and `PEPS/FundamentalTheorem/Torus/Window/EndPairBoundary.lean`.
- **Abstraction:** `grind` (no annotations added), after the same unfolding;
  for region-block edge classifications, the endpoint lemmas
  `TNLean.PEPS.IsCrossingEdge.of_incident`, `IsCrossingEdge.not_incident`
  (`PEPS/FundamentalTheorem/Normal/CoarseThreeSite/CoherentFrame.lean`) and
  `boundary_right_mem`, `boundary_right_not_mem`
  (`PEPS/FundamentalTheorem/Normal/RegionInsertion/InsertedCoefficientExpansion.lean`).

### Separation of pair-conjugacy classes by extracting functionals — promoted (2026-10-11)

- **Pattern:** prove linear independence of a family indexed by
  simultaneous-conjugacy classes by rescaling, for each pair, a functional that
  vanishes on the other classes and not on its own, then applying
  `LinearIndependent.of_pairwise_dual_eq_zero_one` (SCP10, arXiv:1001.3807,
  Theorem 5.9, lines 1595–1610).
- **Seen:** three identical 25-line proofs: `linearIndependent_pairConjugacyClassOperator`
  (`PairConjugacyOperators.lean`),
  `DependentTorus.linearIndependent_closureClass_canonical`
  (`DependentTorusClosureIndependence.lean`) and
  `NativeTorus.linearIndependent_closureClass_canonical`
  (`NativeTorusClosureIndependence.lean`).
- **Abstraction:** `TNLean.PEPS.PairConjugacyClass.linearIndependent_of_extraction`
  in `TNLean/PEPS/Injectivity/Closure/PairConjugacy.lean`.

### Coherent-sum expansion after a mixed physical product map — promoted (2026-10-11)

- **Pattern:** after a mixed product map expands each boundary factor of a
  coherent sum as `∑ z, c b z * x b a z`, exchange sums and products to write
  the result as a combination of fixed-label coherent sums with weights
  `∏ b, c b (ζ b)`.
- **Seen:** four copies of the same 12-line sum manipulation, in
  `graphRegionCoordinateMatrix_open`, `graphOrientedRegionCoordinateMatrix_open`
  and the two copy-transport counterparts
  (`GraphOpenBondCoordinateTransport.lean`, `GraphOrientedCoordinateTransport.lean`,
  `GraphOpenCopyTransport.lean`, `GraphOrientedCopyTransport.lean`).
- **Abstraction:** `TNLean.PEPS.sum_prod_sum_mul_eq_sum_prod_smul` in
  `TNLean/PEPS/ParentHamiltonian/GInjective/MixedPhysicalProductMap.lean`.

### Complementary block of a three-block cover — promoted (2026-10-11)

- **Pattern:** a six-line case split on the three-block cover showing that a
  vertex outside the red and blue blocks lies in the complementary block.
- **Seen:** five copies in `RegionBlock/UnionInjectivityGeneral.lean` and
  `RegionBlock/UnionInjectivityGeneral2.lean`.
- **Abstraction:** `TNLean.PEPS.ThreeBlockGeometry.mem_complement_of_notMem` in
  `TNLean/PEPS/Injectivity/Region/DisjointUnionSetup.lean`.

### Shared rectangle, midpoint and partial-row entropy steps — promoted (2026-10-11)

- **Pattern:** (a) intersect the two halves of a segment at its midpoint;
  (b) write the interior or closure of a dyadic cell through its extreme
  corners; (c) bound the change of regional entropy by `|Y| log q` when the
  actual sites of a disjoint `Y` are added (Lemma 9.4, partial-row step,
  `08-scanner.tex` lines 666–667).
- **Seen:** (a) two private copies, in `Geometry/FanRunContacts.lean` (equality
  under `a ≠ b`) and `Geometry/ActualSideMatching.lean` (subsingleton only);
  (b) private copies of `rectangleCorner` and the midpoint formula plus four
  local `have`s in `Geometry/ElementarySideOpponentUniqueness.lean`; (c) the
  same proof in `template_partial_row_entropy_le` and
  `IntRect.partial_row_entropy_le`.
- **Abstraction:** in `TNLean.PEPS.AreaLaw.Geometry`:
  `segment_midpoint_inter_segment` (`Geometry/SideSubdivisionMask.lean`, no
  hypothesis `a ≠ b`); `interior_dyadicCell_eq_corners`,
  `closure_dyadicCell_eq_corners`, `dyadicCellCorner_lt`,
  `rectangleCorner`, `midpoint_prod_eq` and
  `rectangleCorner_eq_dyadicCellCorner`, now public in
  `Geometry/ElementarySideOpponents.lean`. In `TNLean.PEPS.AreaLaw`:
  `abs_regionEntropy_filter_union_sub_le` (`Geometry/TemplateEntropy.lean`).

### Designated support at a truncated middle — promoted (2026-10-11)

- **Pattern:** show that a designated support meeting a receiving side and a
  partition middle in the truncation set is the base-radius ball
  (`08-scanner.tex`, lines 225–233).
- **Seen:** re-proved independently in `designatedSupport_eq_ball_of_split` and
  `designatedSupport_eq_ball_of_state_split` (`Scan/DesignatedDilution.lean`).
- **Abstraction:** `TNLean.PEPS.AreaLaw.Scan.CollarScan.designatedSupport_eq_ball_of_incidence`
  in `TNLean/PEPS/AreaLaw/Scanner/Histories/DesignatedSampling.lean`.

### Integer row as an interval — promoted (2026-10-11)

- **Pattern:** an `ext`/`min'`/`max'` argument showing that a nonempty finite
  set of integers containing every integer between two of its members is the
  interval between its least and greatest members.
- **Seen:** `Template.latticeRow_eq_Icc` and
  `Template.latticeRow_dilation_eq_Icc` (`Geometry/TemplateLayers.lean`).
- **Abstraction:** `ManyBody.finset_eq_Icc_min'_max'_of_between`
  in `QICLean/ManyBody/Sites/Template/Rows.lean`.

### Dyadic footprint scaling, templates and band rim — promoted (2026-10-11)

- **Pattern:** (a) hand-written norm computations identifying
  `‖t⁻¹ • (q - v)‖ < ρ` (or `≤ ρ`) with membership in the open (or closed)
  square of radius `t ρ` about `v`; (b) a twelve-line identification of a
  block guide near a block corner with the unit block template read through
  the similarity; (c) the case split placing both hole radii `h_n`, `h_{2n}`
  in `[ε₀ n, 2 ε₀ n]`; (d) slot lifting and injectivity of a relabelled
  footprint template near a corner; (e) a 35-line argument that the guide and
  its band update are locally constant at a rim point of the closed band
  (`06-geometry.tex`, lines 227–241, 321–326, 464–541).
- **Seen:** (a) five computations in `image_similarity_closedBall`,
  `HasTwoOwnerFootprints.of_template` and `exists_template_eq`; (b) two
  identical blocks in `exists_blockGuide_footprintRatio` and
  `exists_blockGuide_footprintRatio_reading`; (c) the resizing ratio and its
  reading version; (d) three copies, in `exists_pointTreatment_footprintRatio`
  and twice in `DyadicReadingFootprints.lean`; (e) `hasTwoLabelsNear_bandUpdate`
  and `eventually_bandUpdate_eq` (`DyadicRimPatterns.lean`).
- **Abstraction:** in `TNLean.PEPS.Approximation`: (a)
  `norm_smul_inv_sub_lt_iff`, `norm_smul_inv_sub_le_iff` and (b)
  `blockGuide_eq_classRep` (`DyadicFootprintScaling.lean`); (c)
  `mem_Icc_of_mem_holeRadius_pair` (`DyadicBlockFootprints.lean`); (d)
  `exists_template_injOn` (`DyadicFootprintTemplates.lean`); (e)
  `exists_eventuallyEq_bandUpdate_of_mem_closedEdgeBand`
  (`DyadicUnmodifiedVertices.lean`).

### Homogeneous birth ownership and inner-square membership — promoted (2026-10-11)

- **Pattern:** (a) the four ownership facts of handing a region `T` owned by
  `P∘` to `Q∘` (Lemma 6.5, `05-frames.tex`, lines 396–446); (b) the membership
  of a site outside the untouched outer footprints in an inner square of a
  hole of the rewritten patch (Lemma 6.3, `05-frames.tex`, lines 282–300).
- **Seen:** (a) derived by hand in both `birth_bounded` and `death_bounded`;
  (b) the old-frame and new-frame membership lemmas.
- **Abstraction:** in `TNLean.PEPS.EncodedFrame`:
  `Frame.changeOwner_birth_owners` (`Approximation/HomogeneousOwnership.lean`) and
  `SmallPatchRewrite.exists_mem_inner_of_notMem_untouched`
  (`Approximation/PatchRewriteExpansion.lean`).

### Copy-map block as a scalar multiple — promoted (2026-10-11)

- **Pattern:** a nine-line `have` showing that each block of the global
  copy-restoring map is the block scalar times the regional copy map (SCP10,
  arXiv:1001.3807, Section 7, lines 2977–3019).
- **Seen:** four verbatim copies in the unoriented and oriented copy parent
  transports (`CopyCanonicalParentTransport.lean`,
  `OrientedCopyParentTransport.lean`).
- **Abstraction:** `TNLean.PEPS.regionOperatorBlock_fullMultiplicityBondMap_eq_smul`
  in `TNLean/PEPS/ParentHamiltonian/SemiRegular/CopyCanonicalLocalTransport.lean`.

### Twisted sites, cyclic coordinates, centralizers, virtual equivalences and unitary inversion — promoted (2026-10-11)

- **Pattern:** (a) inserting the identity on every regular bond leaves the
  twisted site coefficient unchanged (SCP10, `eq:2d:peps-with-ug-uh`);
  (b) inequalities such as `(3 : ZMod height) ≠ 2` from a small integer
  difference; (c) an element fixes a pair under simultaneous conjugation
  exactly when it lies in the common centralizer (SCP10, proof of Theorem 5.9,
  lines 1595–1610); (d) transporting G-injectivity along a linear equivalence
  of virtual spaces that intertwines the representations (local consequence of
  SCP10, Definition 5.1); (e) for a unitary `U`, `U x = y` gives `Uᴴ y = x`.
- **Seen:** (a) a private copy in `ParentHamiltonian/RegularRegionFlatness.lean`
  and three local proofs in `RegularRegionGaugeContraction.lean` and
  `RegularClosedChargePairPreparation.lean`; (b) fifty-seven inequalities in the
  string-movement files (`TorusTwoStepStringRouteHolonomy.lean`,
  `TorusSecondStringPhysicalCrossing.lean`,
  `TorusInitialStringRightPhysicalStep.lean`,
  `TorusInitialStringPhysicalCrossing.lean`, `TorusSweptHorizontalStep.lean`);
  (c) three local proofs in the pair-operator and closure-extraction diagonals;
  (d) the two numbered-graph G-injectivity proofs
  (`GraphAveragingGInjective.lean`, `GraphOrientedGInjective.lean`); (e) eight
  three-line Gram rewrites in the flux-move and bidirectional-permutation
  files.
- **Abstraction:** (a) `TNLean.PEPS.regularTwistedSite_one`
  (`TNLean/PEPS/Tensor/GraphState/RegularTwistedRegion.lean`); (b)
  `ZMod.intCast_ne_intCast_of_natAbs_sub_lt`
  (`QICLean/Algebra/Combinatorics/ZModIntCast.lean`, QICLean dependency), with the bound discharged by
  `omega`; (c) `TNLean.PEPS.conj_fixed_iff_mem_centralizer`
  (`TNLean/PEPS/Injectivity/Closure/PairConjugacy.lean`); (d)
  `TNLean.PEPS.IsGInjective.comp_virtualEquiv`
  (`TNLean/PEPS/Injectivity/Regular/GInjectivePhysicalMap.lean`); (e)
  `Matrix.conjTranspose_mulVec_eq_of_mulVec_eq`
  (`QICLean/Analysis/Isometry/UnitaryMulVecInner.lean`, QICLean dependency).

### Nonfar sites remain in the compact truncation set — promoted (2026-10-10)

- **Pattern:** persistence of the initial far assignment forces a nonfar site
  into the color and below the initial upper cutoff, which is at most `8Km`.
- **Seen:** The previous private near-containment proof in `SideSeparation.lean`,
  the non-contained-support proof in `SplitSupportSize.lean`, and the common
  five-region budget in `StatusMarginalBudget.lean`.
- **Abstraction:** `CollarScan.mem_truncationSet_of_not_far` in
  `TNLean/PEPS/AreaLaw/Scanner/Statuses/StatusContainment.lean`, with completed and
  pre-charge far-complement inclusions. Both previous proof copies are removed.

### Uniform norm lower bound on a tail over a compact parameter set — promoted (2026-10-10)

- **Pattern:** `apply hS.exists_uniform_pos_nat_bounds` with the predicate
  `fun δ N₀ x => ∀ N, N₀ ≤ N → ∀ v ∈ V x N, δ * ‖v‖ ≤ ‖H x N v‖`, then the two monotonicity
  bullets (shrinking `δ` by `mul_le_mul_of_nonneg_right`, enlarging `N₀` by `le_trans`)
  before the local bound.
- **Seen:** `IsCompact.exists_uniform_norm_lower_bound_on_tail` itself and three
  parent-Hamiltonian gap theorems that inlined it:
  `exists_uniform_parentHamiltonianES_gap_of_strict_openWindows`
  (`CompactParentGap.lean`),
  `exists_uniform_parentHamiltonianES_gap_of_compact_isNBlkInjective`
  (`CompactNormalParentGap.lean`) and
  `exists_uniform_parentHamiltonianES_toTensorFromBlocks_gap_of_compact`
  (`CompactBlockParentGap.lean`), all under `TNLean/MPS/ParentHamiltonian/`.
- **Abstraction:** `IsCompact.exists_uniform_norm_lower_bound_on_tail` in
  `QICLean/Spectral/Gap/EigenvalueGap.lean` (QICLean dependency); pass `H := fun x N => …` and
  `V := fun x N => (LinearMap.ker …)ᗮ` and prove only the local bound.

### Remainder-absorbing block lengths — promoted (2026-10-10)

- **Pattern:** write `N / q = m + 1`, take `m` blocks of length `q` and one
  of length `q + N % q`, and prove the sum is `N` by separating the last
  summand with `Fin.sum_univ_castSucc`, summing the constants, and applying
  `Nat.div_add_mod`; then prove `q ≤ ℓ k ≤ 2 q` by `split_ifs <;> omega`.
- **Seen:** nine occurrences, one each in `LogDepthPreparation`,
  `LogLogDepthEveryLength`, `SupportedLogLogPreparation`, `UnequalTreeMERA`,
  `OverlappingMeasurementPreparation`, `RectangularPreparation`,
  `VaryingReferencePreparation`, `CoherentGroundspaceConversion` and
  `ZeroSubleadingPreparation` under `TNLean/MPS/Preparation/`.
- **Abstraction:** `MPSPreparation.exists_remainderBlocks` in
  `TNLean/MPS/Preparation/Circuit/RemainderBlocks.lean`: for `0 < q ≤ N` it supplies
  `m`, `ℓ : Fin (m + 1) → ℕ`, `N / q = m + 1`, `∑ k, ℓ k = N` and both
  bounds. Each call site is one `obtain`. Use `remainderBlockLengths` instead
  when the block family must be indexed by `Fin (N / q)` with a definitional
  formula.

### Order-two family with a bond-two generator — promoted (2026-10-10)

- **Pattern:** a `ℤ₂`-indexed family `1 ↦ E`, `g ↦ A` (bond dimensions one and two) written
  out with `Fin 2` label matches for tensors and fusion tensors, together with the cast and
  associator lemmas that reduce the two fusion trees of three generators to `V ⊗ 1` and
  `1 ⊗ V` and make `ω(g,1,g) = 1`.
- **Seen:** `Examples/CZX/CZXAnomalyClass.lean` (`czxFamily`),
  `Examples/AnomalousCondensation/Z2Z2AnomalyClass.lean` (`pairFamily`, two uses), and
  `Examples/KleinSymmetryAnomaly.lean` (the restriction to `{e, a}`).
- **Abstraction:** `MPOTensor.GroupFamily.orderTwoFamily`,
  `MPOTensor.GroupFamily.FusionData.orderTwo`, and
  `MPOTensor.GroupFamily.FusionData.cyclicInvariant_orderTwo_of_isAssociator` in
  `TNLean/MPS/FundamentalTheorem/OperatorGroup/AssociatorOrderTwo.lean`. State the generator as
  `orderTwoGen`: a bare `Multiplicative.ofAdd 1` may elaborate through a different instance
  path for `ZMod 2` and then fail to match in `rw`.

### Boundary on one Kronecker factor of a letter sum — promoted (2026-10-10)

- **Pattern:** unfold `kronId`/`idKron`, collapse the boundary into the index space of the
  `finProdFinEquiv` submatrix with `Matrix.submatrix_mul_equiv`, distribute with
  `Matrix.mul_sum`/`Matrix.sum_mul`, then `congr 1`, `Finset.sum_congr rfl`, and push the
  boundary onto one factor with `← Matrix.mul_kronecker_mul` and
  `Matrix.one_mul`/`Matrix.mul_one`.
- **Seen:** fifteen occurrences across four files: `MPTensor.IsReduction.mulTensor_kronId`,
  `mulTensor_idKron`, `kronId_mul_evalWord_toMPSTensor_mulTensor_ofFn`,
  `idKron_mul_evalWord_toMPSTensor_mulTensor_ofFn` and
  `MPOTensor.mulTensor_mul_kronId_of_intertwine`
  (`TNLean/MPS/Operator/ReductionComposition.lean`); `MPTensor.IsReduction.actTensor_idKron`,
  `actTensor_kronId`, `MPOTensor.actTensor_mul_kronId_of_intertwine`,
  `MPTensor.IsDressedProportional.actTensor_idKron` and `actTensor_kronId`
  (`TNLean/MPS/Operator/ActionTensorReduction.lean`); and the four `hres` steps of
  `MPOTensor.isReductionResidualNilpotencyBound_mulTensor_kronId`, `_mulTensor_idKron`,
  `_actTensor_kronId` and `_actTensor_idKron`
  (`TNLean/MPS/FundamentalTheorem/Reduction/ReductionResidualComposition.lean`), the last four added by #8244.
- **Abstraction:** `MPOTensor.kronId_mul_submatrix_sum`, `submatrix_sum_mul_kronId`,
  `idKron_mul_submatrix_sum` and `submatrix_sum_mul_idKron` in
  `TNLean/MPS/Operator/ReductionComposition.lean`: a boundary `X ⊗ 1` or `1 ⊗ X` on either side
  of `(∑ j, A j ⊗ B j)` in the `finProdFinEquiv` bond order acts on one factor of every
  summand. Each call site rewrites with one or two of them and closes by
  `simp only [h.evalWord]` (or the intertwining or proportionality hypothesis).

### Chosen nonzero dressed-proportionality scalar — promoted (2026-10-10)

- **Pattern:**
  ```lean
  open Classical in
  ... if hz : ∃ z : ℂ, z ≠ 0 ∧ MPTensor.IsDressedProportional B X Y z
  then Units.mk0 hz.choose hz.choose_spec.1 else 1
  ```
  with the spec lemma closing by
  `simp only [_, hex, ↓reduceDIte, Units.val_mk0]; exact hex.choose_spec.2`.
- **Seen:** four occurrences across three files: `FusionData.omega` (through
  `IsAssociator`) and `FusionData.relativeScalar`
  (`TNLean/MPS/FundamentalTheorem/OperatorGroup/Associator.lean`), `ActionData.lSymbol`
  (`TNLean/MPS/FundamentalTheorem/OperatorGroup/AnomalyObstruction.lean`), and
  `BlockActionData.lSymbol` (`TNLean/MPS/FundamentalTheorem/OperatorGroup/PermutedBlocks.lean`).
- **Abstraction:** `MPSTensor.dressedScalar B X Y : Units ℂ` and
  `MPSTensor.isDressedProportional_dressedScalar` in
  `TNLean/MPS/Operator/ReductionComposition.lean`. The four definitions are
  `dressedScalar` of their boundaries, and each spec lemma ends with
  `exact MPSTensor.isDressedProportional_dressedScalar hex`. The one external proof that
  unfolded the `dite` of `omega`, `MPOTensor.GroupCocycle.fusionData_omega`
  (`TNLean/MPS/MPU/Representation/GroupCocycleMPO/FusionTensors.lean`), uses the same lemma.

### Canonical initial sector assignment — promoted (2026-10-09)

- **Pattern:** name the same unique assignment of the eight working sectors
  to actual initial identifiers in a theorem statement and its proof.
- **Seen:** twenty-one bindings in theorem statements and proofs:
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialSectorAssignment.lean`: two bindings.
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialSectorAssignment.lean`: four bindings.
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialSectorComponents.lean`: six bindings.
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialActiveRays.lean`: three bindings.
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialSectorAssignment.lean`: two bindings.
  - `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialActiveRays.lean`: four bindings.
- **Abstraction:** `initialSectorAssignment` in
  `TNLean/PEPS/AreaLaw/BirthRegions/InitialRegions/InitialSectorAssignment.lean` is exactly the
  choice from `exists_unique_initialRegion_sector_assignment`, with the
  original parameters and cell/mark hypotheses.

### Ambient depth variation in an actual charge ball — promoted (2026-10-09)

- **Pattern:** unfold charge-ball membership, identify the induced domain graph,
  apply the ambient-depth variation bound, and reverse the absolute difference.
- **Seen:** Four copies in `Scan/GoodSampling.lean`, `Scan/SplitIntervals.lean`,
  `Scan/PhysicalChargeAncestry.lean`, and `Scan/BadHistoryProbability.lean`.
- **Abstraction:** `CollarScan.abs_depth_sub_anchor_le_planeDomainGraph_of_mem_ball`
  in `TNLean/PEPS/AreaLaw/Scanner/Histories/GoodSampling.lean`.

### Empty final tensor memory — promoted (2026-10-09)

- **Pattern:** identify the tensor product with an empty final memory with
  scalar multiplication on the preceding memory.
- **Seen:** `WordAppendTail.lean` and `UnitMemoryCoordinates.lean` contained
  the same induction on the register list and its tensor vectors.
- **Abstraction:** `Layout.memCongr_append_nil_appendIso_symm_tmul` in
  `UnitMemoryCoordinates.lean`.

### Tensor memory identifications under equality — promoted (2026-10-09)

- **Pattern:** identify equal tail register lists before adjoining a fixed head,
  or identify equal selected and complementary lists before applying the head
  associativity/exchange maps; addition respects the same identification.
- **Seen:** the head congruence proof occurred in `LayoutOwnerMap.lean`,
  `WordAppendTail.lean`, and `UnitMemoryCoordinates.lean`; the partition
  congruences occurred in `PartyPartition.lean` and `PartyPartitionAppend.lean`.
- **Abstraction:** `Layout.memCongr_cons_tmul`, `Layout.selectedHead_heq`,
  `Layout.complementaryHead_heq`, and `Layout.add_heq` in `PartyPartition.lean`.

### Local contractions on the first prepared pair — promoted (2026-10-09)

- **Pattern:** use `Word.mapPair_spec` to obtain an allowed source-free word,
  use `Word.eval_mapPair_source` to transform the first pair vector, and compose
  the identity on the right with the unchanged tail preparation.
- **Seen:** former private proofs `pair_cons_mapIsometry_expands` and
  `common_pair_cons_expands` in the former TNLean party-circuit modules
  `FiniteSourcePreparation` and `CommonSourcePreparation`.
- **Abstraction:** the theorem
  `QuantumCircuit.Party.SourceInventory.Expands.cons_mapL` in
  `QICLean/Circuit/Party/Source/Preparation.lean` (QICLean dependency) takes the two
  local maps and their norm bounds. Issue #8973 requests
  the common lemma; the two private copies are removed, rather than retained
  as aliases. Both existing family theorem statements remain unchanged.

### Integer quotient-interval cardinality — promoted (2026-10-09)

- **Pattern:** bound the cardinality of an integer quotient interval by
  monotonicity of division and the two endpoint remainder inequalities.
- **Seen:** two coordinate estimates in each of
  `Geometry/TemplateDyadicRows.lean` and `Geometry/RectangleMixedSquares.lean`.
- **Abstraction:** `ManyBody.quotient_interval_card` in
  `QICLean/ManyBody/Sites/Template/RectangleShellCounts.lean`.

### Crossing edge on a walk that leaves a region — promoted (2026-10-09)

- **Pattern:** a walk in the induced domain starts in a region and ends outside it; take
  its boundary dart, cut the walk at the first endpoint of the dart, and show that the
  dart is an edge of the edge boundary no farther from the start than the walk is long.
- **Seen:** `subset_of_isSafe` (now QICLean's `ManyBody.subset_of_isSafe`),
  `card_crossingTerms_le_edgeBoundary` in `TNLean/PEPS/AreaLaw/Polygons/SafeRectangles/TailParameter.lean`, and
  `TNLean/PEPS/AreaLaw/Scanner/Histories/GoodSampling.lean`.
- **Abstraction:** the lemma `ManyBody.exists_edgeBoundary_of_walk` in
  `QICLean/ManyBody/Sites/GraphBoundary.lean` (QICLean dependency) returns the boundary
  edge, its endpoint in the region and the shortened walk, for any graph; the three call
  sites use it.

### Retained pieces of the all-midpoint fan — promoted (2026-10-09)

- **Pattern:** repeat the region of a fan triangle after deleting the actual
  successor color-change radials and intersecting with the open ball of
  radius equal to the cell's half-side.
- **Seen:** three descriptions across `FanInactiveSeams.lean` (the statement
  and its local proof expression) and `FanRunConnectedness.lean`.
- **Abstraction:** `cellFanCutPiece` in
  `TNLean/PEPS/AreaLaw/BirthRegions/Fans/FanInactiveSeams.lean` names this common set.

### Telescoping two contraction compositions — promoted (2026-10-08)

- **Pattern:** Expand `B ∘ A - D ∘ C` as `B ∘ (A - C) + (B - D) ∘ C`,
  then apply the triangle inequality and operator-norm submultiplicativity.
- **Seen:** The identical 17-line proof in `EffectCircuitError` and the
  approximate-gate error development; both chronological induction proofs use it.
- **Abstraction:** The matrix form is QICLean's `Matrix.norm_mul_sub_mul_le` in
  `QICLean/Analysis/Norm/ContractionChain.lean` (QICLean dependency), used by the
  effect-circuit and approximate-gate error estimates of `QICLean/Circuit/Party`.

### Single-qubit plus-state positivity — promoted (2026-10-08)

- **Pattern:** Identify the all-halves two-by-two density matrix with one half
  of the outer product of the vector `![1, 1]`, then apply
  `Matrix.posSemidef_vecMulVec_self_star` and nonnegative scalar multiplication.
- **Seen:** Three copies in `TNLeanTest/RegularizedPatchStationarity.lean`,
  `RegularizedPatchNoncommuting.lean`, and `RegularizedPatchZeroWeight.lean`.
- **Abstraction:** `TNLeanTest.SingleQubitConfig.plusDensity` and
  `plusDensity_posSemidef` in `TNLeanTest/Support/SingleQubitConfig.lean`.
  The three regressions use the shared density and positivity result directly.
- **Removed (2026-10-28):** the abstraction and its three call sites were
  deleted with the rest of `TNLeanTest/`.

### Rectangular sandwich of a matrix product operator word — promoted (2026-10-08)

- **Pattern:** replace every letter `U i j` of a nonempty word by `A * U i j * B` with
  `B * A = 1` and telescope, so that the word evaluation is `A * evalWord U is js * B`.
- **Seen:** `evalWord_padBond` (an isometry and its adjoint) and `evalWord_virtualSandwich`
  (a bond similarity) in `TNLean/MPS/MPU/`, beside the Kraus form
  `Kraus.evalWord_compress_of_left_absorb`.
- **Abstraction:** `MPOTensor.evalWord_sandwich` in `TNLean/MPS/MPU/CanonicalForm/VirtualSandwich.lean`, for
  rectangular `A` and `B`.

### Rank from a factorization and an identity minor — promoted (2026-10-08)

- **Pattern:** prove `rank M = k` from `M = P * Q` through `k` (upper bound) and a `k × k`
  submatrix equal to the identity (lower bound).
- **Seen:** four cut-rank proofs in `TNLean/MPS/Examples/ControlledZ/ControlledZ.lean` and
  `leftRank_oddRingTensor` in `TNLean/MPS/Examples/OddRing.lean`.
- **Abstraction:** `Matrix.rank_eq_card_of_eq_mul_of_submatrix_eq_one` in
  `QICLean/Algebra/Matrix/MatrixRankOfFactor.lean` (QICLean dependency).

### Functional calculus under a unitary conjugation — promoted (2026-10-08)

- **Pattern:** `f (x * A * xᴴ) = x * f A * xᴴ` for a unitary `x` and Hermitian `A`, and the same
  for `PosSemidef.supportInvSqrt`.
- **Seen:** general `Matrix` lemmas that had been placed in `TNLean/MPS/MPU/Simple/SourceFactorChoice.lean`.
- **Abstraction:** `Matrix.IsHermitian.cfc_eq_of_eq_unitary_conj`,
  `Matrix.PosSemidef.supportInvSqrt_eq_of_eq_unitary_conj` and
  `Matrix.conjTranspose_mul_unitary` in `QICLean/Analysis/FunctionalCalculus/CfcUnitaryConjugation.lean` (QICLean dependency).

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

### Boundary geometry of an elementary side — promoted (2026-10-07)

- **Pattern:** Derive nondegeneracy and the constant square-boundary coordinate
  of an elementary side, allowing arbitrary midpoint subdivisions.
- **Seen:** The two opposing-region existence cases in
  `ElementarySideOpponents.lean` and the opposing-region uniqueness proof in
  `ElementarySideOpponentUniqueness.lean`.
- **Abstraction:** `cellFan_elementary_geometry` promotes the existing private
  statement and proof unchanged in `ElementarySideOpponents.lean`. The two
  existing callers and the new uniqueness proof use this common theorem.

### Four orientations of fine-cell endpoints — promoted (2026-10-07)

- **Pattern:** Identify the ordered whole-side endpoints from the cell center
  and side vectors, then recognize the two endpoints as binary cell corners.
- **Seen:** The coordinate calculation in `CellContacts`, the full-mesh
  witnesses in `DummyCorners`, and the corner witnesses in `ActualSideMatching`.
- **Abstraction:** `cellFan_unsplit_endpoints_coordinates` and
  `cellFan_unsplit_endpoints_are_corners` in `SideEndpoints.lean`. The existing
  coordinate statement and proof move unchanged to their shared owner; the
  corner witnesses follow from that formula.

### Actual fine-cell containment in a layer — promoted (2026-10-07)

- **Pattern:** Rewrite the exact union over actual fine-layer indices and insert
  the indexed cell as one summand.
- **Seen:** Three copies in `NonbeltPrimaries.lean`,
  `FineMarkSeparation.lean` and `SideSubdivision.lean`.
- **Abstraction:**
  `ManyBody.dyadicCell_subset_dyadicLayer_of_mem_fineLayerIndices`
  in `LayerPartition.lean`. It requires only the aligned exponents and actual
  index membership, including empty layers and arbitrary origins and radii.

### Quasi-local MPS expectation on an interval — promoted (2026-10-07)

- **Pattern:** Rewrite the quasi-local MPS expectation of an interval
  observable by unfolding the interval inclusion, applying the interval
  formula, and cancelling the coordinate equivalence.
- **Seen:** Six parent-Hamiltonian modules repeated the same three-step
  rewrite.
- **Abstraction:** `MPSTensor.quasiLocalExpectation_quasiLocalIntervalObservable`
  in `LocalObservableQuasiLocalState`, next to the interval formula it uses.

### Column selection identified with a fixed-input contraction — promoted (2026-10-07)

- **Pattern:** Select a nonzero column with
  `exists_column_ne_zero_of_traceNorm_sub_pure_le`, rewrite it as the
  contraction of the network with the input fixed, and repackage.
- **Seen:** Two sites in `TNLean/PEPS/Approximation/Routing/VectorColumn.lean` and two
  in `TNLean/PEPS/Approximation/Routing/SquareGridColumn.lean`.
- **Abstraction:** `exists_eq_column_ne_zero_of_traceNorm_sub_pure_le` in
  `ColumnSelection`, taking a family `ψ z` identified with the columns `σ|z⟩`.

### Periodic norm as transfer trace — promoted (2026-10-06)

- **Pattern:** Apply the physical expectation trace identity to the identity
  observable and simplify its action to obtain the periodic squared norm.
- **Seen:** The canonical norm limit and two finite full-ring proofs repeated
  the same calculation, in addition to the existing `WindowClustering` lemma.
- **Abstraction:** The existing public
  `MPSTensor.inner_mpvState_self_eq_trace` is moved unchanged to its lower owner
  `WindowCorrelator`; no alias or second declaration is added.

### Canonical purity consequences — promoted (2026-10-05)

- **Pattern:** From a faithful canonical stationary density and the simple
  peripheral eigenspace property, derive irreducibility and peripheral
  primitivity before applying a twisted-transfer theorem.
- **Seen:** The source spectral theorem and physical selection rule repeated
  this reduction; finite physical endpoints need the same consequences.
- **Abstraction:** `MPSTensor.pureCanonical_isIrreducibleMap_and_isPrimitive`
  in `PureTwistedSpectrum`; the existing two consumers and the new canonical
  endpoint theorem use it without altering their mathematical hypotheses.

### Logarithmic normalization cutoff — promoted (2026-10-05)

- **Pattern:** Turn `(log K - log ε) / r ≤ x` into `K exp(-rx) ≤ ε`.
- **Seen:** The three eventual-nonvanishing proofs in
  `InhomogeneousMixingPreparation`, `VaryingReferencePreparation`, and
  `RectangularPreparation`.
- **Abstraction:** `mul_exp_neg_mul_le_of_div_log_le` in
  `InjectivityCutoff`, using the existing exponential threshold theorem.

### Sites in a one-block partition — promoted (2026-10-05)

- **Pattern:** Proving that the site map of a singleton partition is the identity
  by finite-index extensionality and unfolding the block offset.
- **Seen:** Five uses in `RectangularPreparation`, `VaryingReferencePreparation`,
  `InhomogeneousMixingPreparation`, and `OrderedMixingPairRate`.
- **Abstraction:** `MPSPreparation.blockSite_singleton` in `BlockSites`.

### Uniform Gram/transfer reshuffling — promoted (2026-10-05)

- **Pattern:** Reshuffle the transfer-matrix error into the physical Gram
  error, bound the reshuffling by its operator norm, and reverse the same
  involution when starting from a Gram estimate.
- **Seen:** `InhomogeneousOverlap`, `VaryingReferenceOverlap`, and
  `InhomogeneousChoiResidual` repeated this fixed-dimensional argument.
- **Abstraction:** `MPSTensor.exists_norm_gram_transferMatrix_sub_le` in
  `PositivePartRate` proves both directions with one constant chosen before
  the physical dimension, tensor, and positive semidefinite reference.

### Transported-reference Choi residual estimate — promoted (2026-10-05)

- **Pattern:** Subtract trace-preparation terms from actual block channels,
  compose the completely positive residuals, and bound their normalized Choi
  traces before reshuffling to the physical Gram matrix.
- **Seen:** `InhomogeneousPositivePartRate` and `WindowMixing` previously needed
  the same residual/trace bookkeeping with different reference hypotheses.
- **Abstraction:**
  `MPSPreparation.norm_gram_blockTensor_sub_transport_le_of_choi_domination`
  in `InhomogeneousChoiResidual` handles varying strengths and minorizers.

### A positive binary measurement from an orthogonal projector — promoted (2026-10-03)

- **Pattern:** Derive Hermiticity, positivity, idempotence, orthogonality and
  completeness for a projector and its complement.
- **Occurrences:** The return measurement in `PEPS/Injectivity/Charge/RegularChargePair.lean`,
  the physical charge measurement in `PEPS/Injectivity/Charge/RegularTwoSitePhysicalChargeMeasurement.lean`,
  and the physical transport in `QICLean/Algebra/Hermitian/BinaryProjectionFamily.lean`.
- **Abstraction:** `Matrix.binaryProjectionFamily_complete` in
  `QICLean/Algebra/Hermitian/BinaryProjectionFamily.lean` (QICLean dependency); all three calculations use this lemma.
- **Related reuse:** `Matrix.scaledProjectionTransport_properties` replaces the
  private transported-projection calculation in the two-site charge measurements.
  It proves positivity and the coefficient-map intertwiner from the explicit
  scaled Gram identity, support identity and commuting virtual projector.

### Absorption of the regional regular projector — promoted (2026-10-03)

- **Pattern:** Expand the product physical map, apply local absorption of the
  regular averaging projector, and reassemble the product to obtain AP=A.
- **Abstraction:** `regionPhysicalProductMatrix_mul_regularLocalProjector` in
  `PEPS/Injectivity/Regular/RegularPhysicalUnitaryTransport.lean` states this regional identity once.
- **Reuse:** The physical charge-pair image proof and original-spin return
  measurement use it directly. The two-site local data calculation already uses
  `regularSiteMap_projector_coefficients`, the same underlying local identity.
  The return measurement also uses `Matrix.exists_binaryProjectionFamily_transport`
  for the complete positive measurement on the full physical space.

### Simultaneous permutation invariance of matrix entries — promoted (2026-10-03)

- **Pattern:** Convert simultaneous invariance of matrix entries into commutation
  with the associated permutation matrix.
- **Seen:** Regular cycle flux creation, two-site charge-projector commutation,
  and regional charge-reference preparation.
- **Abstraction:** `Matrix.commute_permMatrix_of_entry_invariant` in
  `QICLean/Algebra/Matrix/PermutationMatrixCommute.lean` (QICLean dependency), over an arbitrary semiring.

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
- **Validation:** the shared table and all three consumers pass the
  package Lean options at the default heartbeat limit. Their theorem
  audits use only the ordinary logical axioms.

### Physical coordinate permutations from translation equivariance — promoted (2026-10-03)

- **Pattern:** Conjugate a coordinate permutation by the actual spanning-tree
  equivalence, transport its vertex-translation commutation, and apply the
  permutation-matrix homomorphism. Average the translations to obtain
  commutation with the product local invariant projector.
- **Seen:** The controlled-boundary argument in
  `PEPS/Injectivity/Regular/RegularCycleControlledSupport.lean`, the cycle argument in
  `PEPS/Injectivity/Flux/RegularCyclePermutation.lean`, and the charge-reference operation in
  `PEPS/Injectivity/Charge/RegularChargeFluxCoordinateTransport.lean`.
- **Abstraction:** `regularRegionCoordinatePhysicalPermutation` and its
  `_commute_vertexTranslation` and `_commute_localProjector` theorems in
  `PEPS/Injectivity/Regular/RegularCycleControlledSupport.lean`. All three consumers supply only
  their derived coordinate equivariance.

### Local projector commutation from independent vertex translations — promoted (2026-10-02)

- **Pattern:** Express the product of local regular averaging projectors as the
  scalar average of independent vertex translations, then move commutation
  through the finite sum and scalar action.
- **Seen:** `RegularCycleControlledSupport.lean`,
  `RegularTwoCyclePhysicalFluxMove.lean`, and
  `RegularCyclePhysicalFluxCreation.lean`.
- **Abstraction:** `commute_regionLocalProjector_of_vertexTranslation` in
  `TNLean/PEPS/Injectivity/Regular/RegularCycleControlledSupport.lean` gives the mathematical
  commutation criterion for the actual regional projector.

### Product maps on coherent finite sums — promoted (2026-10-02)

- **Helper:** `TNLean.PEPS.physicalProductMap_sum_prod` in
  `TNLean/PEPS/Injectivity/Multiplicity/TorusPhysicalCoherentMap.lean`.
- **Use:** apply one rectangular coefficient matrix independently to the
  factors of a finite coherent sum. Interchange the configuration sum and
  coherent-label sum, then use Mathlib `Fintype.prod_sum` once.
- **Consumers:** actual multiplicity restoration of the weighted torus state
  and transport of coherent bond coefficients between orthonormal coordinates.

### Transport of coherent bond products — promoted (2026-10-02)

- **Pattern:** Rewrite the coherent contraction, transform every one-bond
  vector, and reconstruct the finite sum of bond products.
- **Seen:** Six coefficient calculations across
  `PEPS/Injectivity/Multiplicity/TorusMultiplicityBondState.lean`,
  `PEPS/Injectivity/Multiplicity/TorusBlockMultiplicityState.lean`,
  `PEPS/Injectivity/Multiplicity/TorusBondCoordinateTransport.lean`, and
  `PEPS/Injectivity/Multiplicity/GraphAveragingBondState.lean`.
- **Abstraction:** `physicalProductMap_sum_prod_eq` in
  `PEPS/Injectivity/Multiplicity/CoherentMultiplicityTransport.lean` reduces each consumer directly to its
  mathematical single-bond vector identity. It reuses
  `physicalProductMap_sum_prod` and replaces the repeated product congruence.
- **Related helper:** `physicalProductMap_eq_on_inclusion_range` in the same
  module extends equality after one inclusion to the product inclusion range.
  The torus and general-graph full-domain isometry proofs use this shared lemma.

### Weighted blocks and actual torus multiplicity restoration — promoted (2026-10-02)

- **Pattern:** rewrite the coherent dressed-state expansion, reconstruct weighted
  diagonal blocks with matching-sector inclusion, and apply the multiplicity map
  to each factor of every vertex-label summand.
- **Sites:** the orthonormal-sector and explicit fourth-root block constructions
  in `PEPS/Injectivity/Multiplicity/TorusMultiplicityBondState.lean` and
  `PEPS/Injectivity/Multiplicity/TorusBlockMultiplicityState.lean` contained four repeated congruence blocks.
- **Promotion:** `torusBondRegrouping_dressedAveragingSite_of_weightedBlocks`
  proves support and the actual state equality from the single-bond matrix identity.
  Both constructions derive that identity and commutation before using the helper;
  their duplicated coherent-state arguments have been removed.

### Common bond operators outside a region — promoted (2026-10-02)

- **Pattern:** show an incident edge at an exterior vertex is not internal,
  derive equality of exterior twisted site tensors, and apply the identity
  vertex gauge to obtain one common crossing-boundary transport.
- **Seen:** the global movement and coherent global creation arguments in
  `PEPS/Injectivity/Flux/RegularTwoCycleGlobalFluxMove.lean` and
  `PEPS/Injectivity/Flux/RegularCycleGlobalFluxCreation.lean`; four incident-edge exclusions
  and three twisted-site expansions in the 130-file PEPS scan.
- **Abstraction:**
  `regularTwistedSite_regularRegionBondExtension_eq_outside` and
  `openRegionWeight_regularTreeCycleBondExtension` in the global movement
  module. Both movement and creation consumers apply these shared identities;
  their public statements are unchanged.

### Uniform open-column action on an actual cut — promoted (2026-10-02)

- **Pattern:** obtain the same scalar action on every boundary column, assemble
  the open-region matrix identity, and multiply by the complementary matrix.
- **Seen:** the private plaquette measurement argument in
  `PEPS/Injectivity/Flux/TorusPlaquetteFluxMeasurement.lean` and the joint-flux measurement in
  `PEPS/Injectivity/Flux/TorusJointFluxMeasurement.lean`; the cycle-permutation global consumer
  requires the same actual cut implication.
- **Abstraction:**
  `mul_regularPhysicalCutMatrix_eq_smul_of_openRegion_eigen` in
  `PEPS/Tensor/GraphState/RegularOpenRegion.lean` proves the implication from the
  actual cut factorization. Both measurement consumers now use it.

### Combining commuting representation weights — promoted (2026-10-02)

- **Pattern:** move a power of a commuting weight past a representation factor,
  then combine the two representation factors.
- **Seen:** `PEPS/Injectivity/Multiplicity/TorusThetaBondState.lean`, `PEPS/Injectivity/Multiplicity/GraphAveragingBondState.lean`,
  and `PEPS/Injectivity/Multiplicity/GraphOpenAveragingBondState.lean`.
- **Abstraction:** `MonoidHom.mul_commuting_pow_mul` and its adjacent-weight
  specialization `MonoidHom.mul_weight_mul_weight_mul` in
  `QICLean/Algebra/MonoidAux.lean` (QICLean dependency); all three callers use these results.

### Conjugation leaves the conjugacy-class quotient unchanged — promoted (2026-10-02)

- **Pattern:** exhibit the conjugating element, use symmetry of conjugacy,
  and conclude equality in the conjugacy-class quotient.
- **Seen:** the former private class calculation in
  `PEPS/Injectivity/Flux/RegularCycleFluxMeasurement.lean` and the two component class
  calculations in `PEPS/Injectivity/Flux/RegularThreePlaquetteDoubleExchange.lean`.
- **Abstraction:** `ConjClasses.mk_conjugate` in
  `QICLean/Algebra/MonoidAux.lean` (QICLean dependency) proves the group identity once.
  The measurement module uses it at both former call sites; the exchange
  module uses it on the two derived conjugate component formulas.

### Ordered non-tree bonds under graph isomorphisms — promoted (2026-10-02)

- **Pattern:** split the two possible sorted endpoint orders, cancel the
  graph isomorphism, and contradict adjacency in the original tree.
- **Seen:** the native chord constructions in
  `PEPS/Graph/Plaquette/TwoPlaquetteGeometry.lean`,
  `PEPS/Graph/Plaquette/TranslatedTwoPlaquetteGeometry.lean`, and
  `PEPS/Graph/Plaquette/ThreePlaquetteGeometry.lean`.
- **Abstraction:** `Edge.comap_adj_map_iff` in
  `PEPS/Graph/Region/EdgeMapSubgraph.lean` proves the adjacency equivalence for any
  transported graph. All three certificate proofs now use its negation.

### Conditional group-column action on the actual cut — promoted (2026-10-02)

- **Pattern:** encode group-valued boundary configurations, introduce the common
  indicator scalar, and transport a conditional column identity to the cut.
- **Seen:** `PEPS/Injectivity/Flux/TorusPlaquetteFluxMeasurement.lean`,
  `PEPS/Injectivity/Flux/TorusJointFluxMeasurement.lean`, and
  `PEPS/Injectivity/Flux/TorusThreePlaquetteOutputMeasurement.lean`.
- **Abstraction:** `mul_regularPhysicalCutMatrix_eq_ite_of_openRegion_eigen` in
  `PEPS/Tensor/GraphState/RegularOpenRegion.lean` derives the numbering and scalar
  internally from the existing uniform scalar action theorem. All three
  consumers now apply the conditional implication directly.

### Native plaquette transport — promoted (2026-10-02)

- **Pattern:** unfold the four actual plaquette steps, reverse the top and left
  transports, and evaluate the resulting ordered group product.
- **Seen:** `PEPS/Injectivity/Flux/TorusPlaquetteFluxMeasurement.lean`,
  `PEPS/Injectivity/Flux/TorusTwoPlaquetteFluxHolonomy.lean`,
  `PEPS/Graph/Plaquette/TorusJointFluxGeometry.lean`, and
  `PEPS/Graph/Plaquette/TorusThreePlaquetteFluxGeometry.lean`; both orientations are also
  required by the four-endpoint string calculation.
- **Abstraction:** `regularWalkHolonomy_torusPlaquetteWalk` and
  `regularWalkHolonomy_torusPlaquetteWalk_reverse` beside the defining walk
  in the measurement module. The native consumers use the common formulas.

### Sorted-edge endpoint comparison — promoted (2026-10-02)

- **Pattern:** compare the two endpoint orders of native sorted edges, or
  distinguish them by a coordinate constant on one pair of endpoints.
- **Seen:** repeated plaquette and translated-movement edge inequalities in
  `PEPS/Injectivity/Flux/TorusPlaquetteFluxMeasurement.lean` and
  `PEPS/Injectivity/Flux/TorusTranslatedFluxMove.lean`; the vertical movement needs the same
  endpoint comparison.
- **Abstraction:** `Edge.ofAdj_eq_iff_endpoints` and
  `Edge.ofAdj_ne_of_endpoint_coordinates` in `PEPS/Graph/Region/EdgeMapSubgraph.lean`.
  Both former private coordinate helpers are removed and their callers use
  the common result.

### Sparse cycle assignments — promoted (2026-10-02)

- **Pattern:** reconstruct an internal assignment from identity on a spanning
  tree and a small explicit list of non-tree bonds.
- **Seen:** the two private horizontal support proofs in
  `PEPS/Injectivity/Flux/TorusTranslatedFluxMove.lean` and
  `PEPS/Injectivity/Flux/TorusTwoPlaquetteFluxHolonomy.lean`, and the vertical movement proof.
- **Abstraction:** `regularTreeCycleAssignment_eq_of_support` and its
  two-bond specialization `regularTreeCycleAssignment_twoSupport`, beside
  the defining assignment in `PEPS/Injectivity/Flux/RegularTwoCycleFluxMove.lean`.

### Regional PEPS subspace inclusion by open contraction columns — promoted (2026-10-02)

- **Pattern:** Rewrite the regional ground space as the span of its actual
  open contraction columns, apply `Submodule.span_le`, and extract each
  crossing configuration from the generator range.
- **Seen:** Twice in `PEPS/ParentHamiltonian/Regular/RegularRegionFlatness.lean`
  (exposure into canonical coordinates and recovery through the inverse),
  and once in `RegularRegionBondRightInvariance.lean`
  (exposed shared-bond right invariance).
- **Abstraction:** `TNLean.PEPS.regionGroundSpace_le_iff` in
  `TNLean/PEPS/Tensor/Region/RegionGroundSpace.lean` gives the universal
  subspace property of the actual regional contraction.

### Finite linear combinations in a supported subspace — promoted (2026-10-02)

- **Pattern:** prove membership of a sum by `Submodule.sum_mem`, then prove
  each scalar multiple belongs by `Submodule.smul_mem`.
- **Seen:** regional support transport in
  `PEPS/ParentHamiltonian/Region/RegionPhysicalGroundSpaceTransport.lean`,
  `VertexInverseRegionSlice.lean`, and `VertexVirtualParentTransport.lean`.
- **Abstraction:** existing Mathlib `Submodule.sum_smul_mem`; all three
  consumers now apply it directly. No new lemma or tactic is needed.

### continuous argument along slit-plane paths — promoted (2026-10-02)

- **Pattern:** Reduce continuity of a principal-argument path to continuity at
  each point, use `Complex.continuousAt_arg`, and compose with the path.
- **Seen:** three angular-branch constructions in `PEPS/Graph/Cell/IntegerCellNoHoles.lean`.
- **Abstraction:** Mathlib's `Complex.continuousOn_arg.comp_continuous`.

### finite compact cell quotients — promoted (2026-10-02)

- **Pattern:** Map a finite disjoint union of compact locally path connected
  cells continuously onto its realized union, use compactness and the Hausdorff
  property to obtain a closed quotient map, and pass local path connectedness
  to the quotient.
- **Seen:** the original torus-cell proof in
  `PEPS/Graph/Cell/TorusRegionRealization.lean` and the planar integer-cell construction in
  `PEPS/Graph/Cell/IntegerCellNoHoles.lean`.
- **Abstraction:** `locallyPathConnectedSpace_iUnion_range` in
  `PEPS/Graph/Cell/TorusRegionRealization.lean`. Both geometric instances now use the shared
  theorem; the torus instance no longer repeats the quotient argument.

### Finite contour winding gradients — promoted (2026-10-02)

- **Pattern:** Sum a finite signed vertical edge flow along a horizontal ray,
  then compute its east and north increments by finite telescoping.
- **Occurrences:** `PEPS/Graph/Cell/IntegerContourRayPotential.lean` and the actual exposed
  orbit flow in `PEPS/Graph/Cell/IntegerCellBoundaryContour.lean`. The contour proof's
  former specialized horizontal and vertical contribution calculations have
  been removed.
- **Promotion:** `integerContourRayPotential_east` and
  `integerContourRayPotential_north`; the actual contour constructs its finite
  horizontal and vertical flows, proves conservation from successor endpoint
  continuity, and applies these shared mathematical identities.

### Functions constant on graph edges — promoted (2026-10-02)

- **Pattern:** Induct on a graph walk to propagate equality of a function at
  adjacent vertices. Two such inductions occurred for occupied and missing
  cells in the exposed-contour proof.
- **Promotion:** Mathlib's
  `Relation.reflTransGen_le_of_equivalence_of_le`, applied to the kernel
  equivalence of the function, together with
  `SimpleGraph.reachable_iff_reflTransGen`. The contour module has one private
  application of these existing results, reused for both cell graphs.

### Positional factors in reversed finite lists — promoted through Mathlib

- **Pattern:** Recover an index of a factor in a reversed finite list, transfer
  its indexed assumptions, and express descending nesting by the original
  increasing index order.
- **Seen:** `isPatchMinimizer_regularizedPatchFactorList` in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchListCoordinates.lean` and
  `normalizedRegularizedPatchMarginal_stationarity_of_isMinOn` in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchMinimizerStationarity.lean`.
- **Abstraction:** Existing `List.mem_reverse`, `List.mem_ofFn`,
  `List.pairwise_reverse` and `List.pairwise_ofFn` give the positional
  membership and order statements. The stationarity proof shares its local
  index witness when transferring exponent and density assumptions.

### Pointwise comparison of finite-chain symmetries — promoted
- **Pattern:** compare invariance at every applicable chain length by proving
  equivalent operator equations pointwise, for symmetries with the same
  applicable lengths.
- **Seen:** six uses across
  `TNLean/MPS/Examples/Shift/SwapSymmetryTransport.lean` and
  `TNLean/MPS/Examples/Shift/SwapBlockedSymmetryTransport.lean`, in the adjunction,
  transposition and conjugation comparisons (2026-10-03).
- **Abstraction:** `MPOTensor.isInvariantUnderSymmetry_iff_of_pointwise` in
  `TNLean/MPS/MPU/Equivalence/Equivalence.lean` performs the common quantifier reduction once.

### Induced walks after extension by exterior operators (promoted, 2026-10-03)

`regularRegionInternalOperators_bondExtension` restricts an extended assignment
back to its original internal operators. `regularWalkHolonomy_induced_bondExtension`
then evaluates an induced-region walk directly with the original assignment.
They are defined in `TNLean/PEPS/Injectivity/Flux/RegularTwoCycleGlobalFluxMove.lean` and replace
repeated restriction proofs in the two-plaquette joint measurement, the
three-plaquette output measurement, and the routed reunion measurement.

### Adjoint of dependent block diagonals (promoted, 2026-10-02)

- **Pattern:** Expand dependent block-diagonal entries to move conjugate
  transpose through the block construction.
- **Occurrences:** `QICLean/Representation/Permutation/FiniteGroupCommutant.lean`,
  `QICLean/Algebra/MatrixAlgebra/ScalarCommutant.lean`, and
  `QICLean/Algebra/Matrix/DependentBlockDiagonal.lean`.
- **Promotion:** Reuse Mathlib's `Matrix.blockDiagonal'_conjTranspose`.
  The finite-group commutant proof removes its private entrywise copy and
  rewrites directly with this theorem; the companion-library consumers
  already use it.

### Weighted isotypic scalar action (promoted, 2026-10-02)

- **Pattern:** Expand a weighted character-projector sum on an irreducible
  summand, replace each projector by its character-equality indicator,
  and retain the weight of that summand.
- **Occurrences:** `RepresentationDelta.deltaOperator_apply_of_mem`,
  `CharacterProjectorTwirl.averageMap_linHom_rep`, and the reciprocal
  coefficient in `RepresentationDeltaInverse.deltaOperatorInverse_apply_of_mem`.
- **Promotion:** `Representation.sum_smul_charProjector_apply_of_mem` in
  `QICLean/Representation/Character/Projector.lean` (QICLean dependency). All three calculations
  use this mathematical helper. The same module proves that every such
  isotypic scalar operator commutes with the group action.

### Positivity of weighted character projectors (promoted, 2026-10-02)

- **Pattern:** Express a weighted sum through occurring irreducible characters,
  obtain the corresponding subrepresentation, inherit unitarity there, and
  sum its positive character projectors with nonnegative coefficients.
- **Occurrences:** `RepresentationDeltaPositive.isPositive_deltaOperator_of_unitary`
  and `RepresentationThetaPositive.isPositive_thetaOperator_of_unitary`.
  Positive representation weights require the same argument in subsequent
  bond constructions.
- **Promotion:** `Representation.isPositive_sum_smul_charProjector_of_nonneg`
  in `QICLean/Representation/Character/DeltaPositive.lean` (QICLean dependency). Both calculations use
  this lemma and retain only their scalar nonnegativity arguments.

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
  `QICLean/Representation/Character/Projector.lean` (QICLean dependency); the listed calculations use this
  finite-dimensional mathematical extensionality lemma.

### Coherent weighted-block multiplicity restoration (promoted, 2026-10-02)

- Pattern: derive matching-sector support and multiplicity restoration from a
  coherent product of square-root weighted diagonal matrix blocks.
- Promotion: `coherentWeightedBlocks_support_restore` and
  `exists_isometric_coherentWeightedBlocks` in
  `TNLean/PEPS/Injectivity/Multiplicity/CoherentMultiplicityTransport.lean`.
- Consumers: the actual graph and torus weighted-state support theorems, and
  the actual group-inserted closed-graph isometry theorem. The ordinary matrix
  hypothesis remains distinct from an assumed contraction identity; every
  actual-state consumer derives its coherent expansion.

### Averaged left inverse of a G-injective MPS tensor (promoted, 2026-10-02)

- **Pattern:** Extract the invariant tensor and its averaged left inverse from
  general G-injectivity, then rewrite map invariance as conjugation invariance
  of every physical tensor coefficient.
- **Seen:** The concatenation proof in `PEPS/Injectivity/GInjective/GInjectiveMPS.lean`, both original
  intersection and closure proofs in `PEPS/Injectivity/GInjective/GInjectiveMPSIntersection.lean`,
  and the inhomogeneous intersection proof in
  `PEPS/Injectivity/GInjective/GInjectiveStripIntersection.lean`.
- **Abstraction:** `IsGInjective.exists_mpsLeftInverse` in
  `TNLean/PEPS/Injectivity/GInjective/GInjectiveMPS.lean` combines the existing general left-inverse
  theorem with the conjugation-invariance characterization.

### injectivity under translations of a torus region — promoted
- **Pattern:** transport blocked-region injectivity along a torus translation,
  then replace the transported tensor by the original translation-invariant tensor.
- **Seen:** four uses in `TorusWitnessTranslate.lean`,
  `TorusTranslatedScalarComparison.lean`, and `TorusWindowGaugeUniqueness.lean`.
- **Abstraction:** the existing `regionBlockedTensorInjective_translate` now lives in
  `TorusTranslationInvariant.lean`, so the witness, scalar and uniqueness arguments
  can use it without importing the later torus Fundamental Theorem.

### propagation of two PEPS reference witnesses — promoted
- **Pattern:** translate horizontal and vertical coefficient witnesses to every edge,
  absorb their boundary gauges, and prove covariance by composition of translations.
- **Seen:** the rectangle construction in `PEPS/FundamentalTheorem/Torus/TorusReferenceAbsorbedFamily.lean`
  and the normal-window construction in `PEPS/FundamentalTheorem/Torus/TorusArcWindowFundamentalTheorem.lean`.
- **Abstraction:** `exists_torusCovariantAbsorbedGaugeFamily_of_edgeReferenceWitnesses`
  in `PEPS/FundamentalTheorem/Torus/TorusReferenceAbsorbedFamily.lean` accepts arbitrary witnessing regions.

### Integer-cell collar offset decomposition (promoted, 2026-10-02)

- **Pattern:** Split the displacement from an occupied integer center into
  two equal offsets; use one in the closed unit cell and one in the
  radius-three-quarters enlargement.
- **Occurrences:** `PEPS/Graph/Cell/IntegerCellExteriorCollar.lean` and
  `PEPS/Graph/Cell/TorusRegionBoundaryLift.lean`, formerly the private
  `unitStep_mem_collar` placement proof. Actual edge and boundary-endpoint
  geometry both need the same numerical placement.
- **Promotion:** `mem_integerClosedCell_add_of_abs_le_one` in
  `TNLean/PEPS/Graph/Cell/IntegerCellExteriorCollar.lean`. The generic theorem already
  serves edge-segment containment and the integer-center collar
  characterization; the torus boundary-lift consumer uses it after reducing
  its unit-step hypothesis to coordinate distance at most one.

### Flat spectral entropy reduction (promoted, 2026-10-02)

- **Pattern:** Apply a quadratic matrix identity to a nonzero eigenvector,
  cancel the vector coefficient, and conclude that each eigenvalue is zero
  or the reciprocal flatness parameter.
- **Occurrences:** The von Neumann calculation in `QICLean/Entropy/Renyi/FlatDensityEntropy.lean`
  and the spectral real-power trace calculation in
  `QICLean/Entropy/Renyi/FlatDensityEntropy.lean`; the same spectral argument would otherwise
  precede each Rényi order and each boundary-density specialization.
- **Promotion:**
  `Matrix.IsHermitian.eigenvalues_eq_zero_or_inv_of_mul_self_eq_inv_smul` in
  `QICLean/Entropy/Renyi/FlatDensityEntropy.lean` (QICLean dependency). Both entropy calculations consume
  this lemma, with no repeated eigenvector cancellation proof.

### Integer unit-step seam arithmetic (promoted, 2026-10-02)

- **Pattern:** Split an integer unit step into its four orientations; apply
  Euclidean division at a seam, and negate the crossing pair for reverse steps.
- **Occurrences:** Exterior walk approximation in
  `PEPS/Graph/Cell/TorusExteriorPathApproximation.lean` and boundary endpoint lifting in
  `PEPS/Graph/Cell/TorusRegionBoundaryLift.lean`; the four-case argument is shared by
  exterior walks and native boundary crossings.
- **Promotion:** `torusIntegerDeckCoordinate` and
  `torusDirectedWinding_eq_of_integerUnitStep` in
  `PEPS/Graph/Walk/TorusIntegerStepWinding.lean`. The exterior approximation now uses
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
  `TNLean/PEPS/Injectivity/Regular/RegularCycleControlledBoundary.lean`. The matrix depends only on
  the fixed trees and actual walks, before any bond assignment or closure label.
  Known consumers use this definition directly; there is no compatibility alias.

### integer fibers and affine lifts of additive circles — promoted
- **Pattern:** extract an integer fiber from `AddCircle.coe_eq_zero_iff`,
  or compare a continuous lift of a projected affine interval path with
  the affine lift by `IsCoveringMap.eq_of_comp_eq`.
- **Seen:** the two coordinate constructions in
  `PEPS/Graph/Cell/TorusRegionRealization.lean` and
  `PEPS/Graph/Cell/TorusRegionLiftRealization.lean` (2026-10-02); the integer-fiber
  proofs were identical, and the affine-lift proofs differed only in
  their final use of function extensionality.
- **Abstraction:** `exists_intCast_eq_of_addCircle_eq_zmod_val` and
  `eq_affine_of_addCircle_eq` in `PEPS/Graph/Cell/TorusRegionRealization.lean`.

### products of finite indicator sums — promoted
- **Pattern:** after separating scalar factors, expand a product of sums by
  `Fintype.prod_sum` and collapse each product of zero-one indicators by
  `Fintype.prod_boole`.
- **Seen:** `regularProjectorOpenRegionMatrix_apply`,
  `regularProjectorTwistedRegionMatrix_apply`, and
  `prod_torusSiteGram_eq_sum_translation` in the corresponding three PEPS
  modules (2026-10-02).
- **Abstraction:** `Fintype.prod_sum_boole` in
  `QICLean/Algebra/Combinatorics/DependentProducts.lean` (QICLean dependency), for dependent finite choice types
  over an arbitrary commutative semiring.

### equality of labels under a boundary numbering — promoted
- **Pattern:** prove equality of two functions on a numbered boundary by
  evaluating an equality of their pullbacks at the inverse numbering, and
  prove the converse by function extensionality.
- **Seen:** three occurrences in
  `PEPS/Tensor/GraphState/RegularRegionGram.lean`, `PEPS/Tensor/GraphState/RegularTwistedRegionGram.lean`, and
  the private projector-numbering lemma in
  `PEPS/Injectivity/Boundary/RegularRegionEntropy.lean` (2026-10-02).
- **Abstraction:** Mathlib's `Function.Surjective.right_cancellable`,
  applied to the surjective boundary equivalence.

### recovering site coefficients from a composed site map — promoted
- **Pattern:** apply `LinearMap.toMatrix'` to a composition identity, expand
  the matrix of the four-leg site map, and read one physical and virtual entry.
- **Seen:** the former forward local inverse and reverse projector action in
  `PEPS/Injectivity/TorusSector/RegularGInjectiveTorus.lean`, and their generalization to arbitrary
  virtual representations in `PEPS/Injectivity/TorusSector/GInjectiveTorusProjector.lean`
  (2026-10-02).
- **Abstraction:** `siteMap_injective` and
  `physicalMapSite_eq_iff_siteMap_comp` in
  `PEPS/Injectivity/TorusSector/GInjectiveTorusProjector.lean` recover coefficient equality from
  equality or physical composition of site maps.

### equality of boundary functions under incident-edge indexing — promoted
- **Pattern:** compare boundary functions after pulling them back to the
  boundary subtype of incident edges, then recover their equality by
  function extensionality at the canonical incident-edge inclusion.
- **Seen:** four occurrences in `PEPS/Graph/Holonomy/RegularRegionCounting.lean` and
  `PEPS/Graph/Holonomy/RegularRegionCounting.lean`, detected by the tactic pattern
  scan on 2026-10-02.
- **Abstraction:** `regionBoundaryLabel_eq_iff` in
  `PEPS/Graph/Holonomy/RegularRegionCounting.lean`.

### finite sums supported on constant functions — promoted
- **Pattern:** when a summand indexed by vertex labels vanishes unless the
  label function is constant, replace the sum by a sum over its common value.
- **Seen:** `sum_regionLabelCompatible_eq_sum_translation` in
  `PEPS/Graph/Holonomy/RegularRegionConnectivity.lean`,
  `sum_torusClosureCompatible_eq_sum_intertwiner` in
  `PEPS/Graph/Holonomy/RegularTorusCompatibility.lean`, and
  `sum_twistedRegionLabelCompatible_eq_sum_translation` in
  `PEPS/Graph/Holonomy/RegularTwistedRegionConnectivity.lean` (2026-10-02).
- **Abstraction:** Mathlib's `Fintype.sum_of_injective`, applied to the
  constant-function injection. All three proofs already use it.

### compact finite-volume kernel gaps — promoted
- **Pattern:** obtain a positive lower norm bound on a finite-dimensional
  kernel complement at each parameter, preserve half of it in a neighborhood
  using continuity of the operator and its kernel projection, and pass to a
  finite subcover of a compact parameter set.
- **Seen:** the finite-volume argument in
  `TNLean/MPS/ParentHamiltonian/Continuity/PeriodicShortGapContinuity.lean` and the
  fixed-injectivity-length extension in
  `TNLean/MPS/ParentHamiltonian/Continuity/CompactNormalParentGap.lean`, the multiblock
  fixed-volume theorem in `BlockPeriodicGroundSpaceContinuity.lean`, and the
  local positive-interaction comparison in `CompactParentInteractionGap.lean`
  (2026-10-02).
- **Abstraction:**
  `ContinuousLinearMap.exists_uniform_norm_gap_of_compact` in
  `QICLean/Spectral/Gap/EigenvalueGap.lean` (QICLean dependency).

### scalar cancellation in the fixed-point physical action — promoted
- **Pattern:** replace an invertible virtual matrix by a nonzero scalar
  multiple in `Wᵀ ⊗ W⁻¹`; the scalar and its reciprocal cancel.
- **Seen:** three uses across two files: the identity and multiplication
  proofs of `sptFixedPointAction` in `SPTFixedPoint.lean`, and
  `sptFixedPointAction_eq_of_forall_eq_smul` in
  `CohomologousFixedPointPath.lean`, under `TNLean/MPS/Symmetry/`.
- **Abstraction:** `MPSTensor.sptKron_eq_of_eq_smul` was already the private
  helper for the first two uses. It is now public and serves the third use.

### Gram left inverses of injective matrix sections — promoted
- **Pattern:** cancel the product of an injective section with its Hermitian
  Gram left inverse.
- **Seen:** quotient algebra recovery, letter-coordinate recovery, and
  continuous range frames.
- **Abstraction:** `Matrix.gramLeftInverse_mul` in
  `QICLean/Analysis/Topology/ContinuousIdempotentFrames.lean` (QICLean dependency).

### Continuity of Gram left inverses — promoted
- **Pattern:** prove continuity of `(Cᴴ * C)⁻¹ * Cᴴ` for a continuous injective
  rectangular matrix family.
- **Seen:** trace-quotient multiplication coordinates, reconstructed letter
  coordinates, and continuous range frames.
- **Abstraction:** `Matrix.continuous_gramLeftInverse` in
  `QICLean/Analysis/Topology/ContinuousIdempotentFrames.lean` (QICLean dependency).

### Bilinear maps in pair-indexed coordinates — promoted
- **Pattern:** expand a bundled bilinear map into the matrix acting on
  coordinates `(a,b) ↦ x a * y b`.
- **Seen:** quotient algebra recovery, continuous quotient units, and
  continuous primitive elements.
- **Abstraction:** `Matrix.toLinearMap₂'_apply_mulVec_prod` in
  `QICLean/Algebra/MatrixAlgebra/MatrixAlgebraCoordinates.lean` (QICLean dependency).

### Restricting continuous data to an open subtype neighborhood — promoted
- **Pattern:** transfer an open neighborhood in an open subtype to its image
  in the ambient space, then restrict the chosen continuous data.
- **Seen:** continuous quotient units, continuous canonical normalization,
  continuous range frames, and minimal tensor reconstruction.
- **Abstraction:** Mathlib's `IsOpen.isOpenMap_subtype_val` and
  `Topology.IsInducing.subtypeVal.continuousOn_image_iff`.

### Associativity and units from an injective multiplicative map — promoted
- **Pattern:** transfer associativity and the two unit identities through a
  bijective coordinate identification with a matrix algebra.
- **Seen:** the associative product in
  `TNLean/MPS/CanonicalForm/TraceQuotient/TraceQuotientAlgebraRecovery.lean` and both unit
  identities in `TNLean/MPS/CanonicalForm/TraceQuotient/TraceQuotientTripleContinuity.lean`.
- **Abstraction:** install the coordinate product as a local `Mul` and the
  recorded unit as a local `One`. Use Mathlib's
  `Function.Injective.semigroup` and `Function.Injective.mulOneClass`, then
  `mul_assoc`, `one_mul`, and `mul_one`. No additional transport lemma is needed.

### bilinear extension from spanning tensor letters — promoted
- **Pattern:** extend an identity on pairs of tensor letters first in one
  matrix argument and then in the other.
- **Seen:** four successive single-argument extensions in the two proofs
  `MPS/Tensor/Words/OneSidedInverse.lean` and
  `MPS/CanonicalForm/TraceQuotient/FiniteRingTraceAlgebra.lean` (2026-10-02).
- **Abstraction:** Mathlib's `LinearMap.mul`, `LinearMap.compr₂`,
  `LinearMap.compl₁₂`, and two nested `LinearMap.ext_on_range` calls express
  the identity as equality of bundled bilinear maps.

### physical-matrix covariance from tensor letters — promoted
- **Pattern:** rewrite the physical rotation as left multiplication of
  the physical matrix, then vectorize the two bond factors; for a unitary
  general linear factor, replace its inverse by its adjoint.
- **Seen:** seven occurrences across
  `MPS/Symmetry/GappedPath/PolarDeformation.lean`,
  `MPS/Symmetry/GappedPath/PolarFrameEmbedding.lean`,
  `MPS/Symmetry/GappedPath/PolarFixedPointEmbedding.lean`,
  `MPS/Symmetry/SPTClassification/CommonPhysicalEndpointPaths.lean`, and
  `MPS/Symmetry/SPTClassification/CommonPhysicalExactPhase.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.physicalMatrix_covariance_of_rotatePhysical`
  in `MPS/Symmetry/GappedPath/PolarDeformation.lean`, with
  `MPSTensor.physicalMatrix_mul_eq_sptKron_of_unitary_covariance` in
  `MPS/Symmetry/SPTClassification/PhysicalMatrixBondCovariance.lean` for unitary virtual actions.

### summing on-site symmetric local interactions — promoted
- **Pattern:** expand the periodic interaction Hamiltonian, prove that each
  embedded two-site term commutes with the full on-site tensor power, and
  sum the commutation identities.
- **Seen:** four occurrences in `MPS/Symmetry/GappedPath/CanonicalInjectiveGappedPath.lean`,
  `MPS/Symmetry/SPTClassification/WeightedMatrixUnitParentPath.lean`, and
  `MPS/Symmetry/SPTClassification/CommonPhysicalFixedPointPath.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.hamiltonian_translationInvariant_commute_onSiteTensorPow`
  in `MPS/ParentHamiltonian/Deformation/ParentHamiltonianSymmetry.lean`.

### orthogonal matrix projections as symmetric linear projections — promoted
- **Pattern:** map a star projection through the orthonormal matrix-coordinate
  equivalence, then apply
  `LinearMap.isStarProjection_iff_isSymmetricProjection`.
- **Seen:** three occurrences in
  `MPS/Symmetry/FixedPoint/BondProductParentHamiltonian.lean`,
  `MPS/Symmetry/GappedPath/PhysicalInteractionGap.lean`, and
  `MPS/Symmetry/GappedPath/PhysicalInteractionGroundSpace.lean` (2026-10-02).
- **Abstraction:** `MPSTensor.bondMatrixEquiv_symm_isSymmetricProjection` in
  `MPS/Symmetry/FixedPoint/BondProductParentHamiltonian.lean`.

### reindexing an orthogonal matrix projection — promoted
- **Pattern:** transport idempotence by the matrix reindexing equivalence
  and self-adjointness by the conjugate-transpose reindexing identity.
- **Seen:** three uses in `MPS/Symmetry/FixedPoint/TwoSiteBondInteraction.lean`,
  `MPS/Symmetry/FixedPoint/FixedPointGappedPath.lean`, and
  `MPS/Symmetry/GappedPath/PhysicalInteractionGap.lean` (2026-10-02).
- **Abstraction:** `Matrix.isStarProjection_reindex` in
  `QICLean/Analysis/Projection/MatrixStarProjection.lean` (QICLean dependency).

### inverse of a unitary general linear matrix — promoted
- **Pattern:** identify the general linear inverse with the matrix inverse,
  then use the unitary adjoint as a left inverse.
- **Seen:** three uses in `MPS/Symmetry/FixedPoint/SPTFixedPoint.lean`,
  `MPS/Symmetry/SPTClassification/CommonPhysicalEndpoints.lean`, and
  `MPS/Symmetry/SPTClassification/CommonPhysicalEndpointPaths.lean` (2026-10-02).
- **Abstraction:** `Matrix.coe_gl_inv_eq_conjTranspose_of_mem_unitaryGroup`
  in `QICLean/Algebra/Unitary/IsometricFrameEmbedding.lean` (QICLean dependency).

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

### positivity of the cyclic step-orbit length — promoted
- **Pattern:** derive `0 < m / m.gcd p` from `0 < m`.
- **Seen:** four uses across `FinStepOrbit.lean`, `SectorPhaseWord.lean`, and
  `StepOrbitSectors.lean` (2026-09-29).
- **Abstraction:** the core Lean theorem `Nat.div_gcd_pos_of_pos_left p hm`
  (`Init/Data/Nat/Gcd.lean`) provides the result directly; the phase
  construction and prescribed-blocking sectors use it.

### fixed-volume C3 from a physical open-chain bound — promoted
- **Pattern:** split a martingale index into `n < l`, `n = l`, and `l < n`;
  the first two products vanish, while the last is bounded by its physical
  open-chain representative after adjoining the right spectator sites.
- **Seen:** the original threshold theorem in
  `TNLean/MPS/ParentHamiltonian/Gap/Filtration/FixedAmbientMartingaleBound.lean`
  and the prescribed-gap theorem in
  `TNLean/MPS/ParentHamiltonian/Gap/PrescribedGap.lean` (2026-09-28).
- **Abstraction:** `fixedAmbient_martingaleDifference_norm_le_of_openChain`
  in `FixedAmbientMartingaleBound.lean` retains the chosen nonnegative bound
  without tying it to the threshold `1 / sqrt (l + 1)`.

### passing a scalar grading through a matrix word — promoted
- **Pattern:** move a grading matrix through each letter and multiply the
  letter-dependent scalars.
- **Seen:** three occurrences across `MPS/Tensor/GroundSpace/ParentHamiltonianBasic.lean`,
  `MPS/Examples/MajumdarGhosh/MajumdarGhoshGroundSpace.lean`, and
  `MPS/Examples/MultiBlock/ParityAmplitudes.lean`.
- **Abstraction:** `MPSTensor.mul_evalWord_of_mul_eq_smul_letter` in
  `MPS/Tensor/Words/Basic.lean`; the constant-scalar theorem is a specialization.

### virtual-leg cancellation in source-gate contractions — promoted
- **Pattern:** cancel the adjacent factors $z^\dagger z=I$ between two
  rectangular matrices, leaving the site-specific Kronecker expansions intact.
- **Seen:** three occurrences across two files: `transported_source_u_contraction`
  in `TNLean/MPS/MPU/StandardForm/VirtualSourceFactorTransport.lean`, and `rawU_virtual_cancel`
  and `rawV_virtual_cancel` in `TNLean/MPS/MPU/StandardForm/SelectedSourceGateVirtualGauge.lean`.
- **Abstraction:** `Matrix.mul_unitary_adjoint_mul_cancel` in
  `QICLean/Analysis/FunctionalCalculus/CfcUnitaryConjugation.lean` (QICLean dependency).

### bilinear identities on operators with disjoint supports — promoted
- **Pattern:** prove an identity `f A B = g A B`, bilinear in operators `A`, `B` acting on
  sets of sites `S`, `S'`, by nested `Submodule.span_induction` on
  `A ∈ supportedOperators d S` and `B ∈ supportedOperators d S'`: a product-generator case
  `Matrix.piKronecker m`, `Matrix.piKronecker m'` settled site by site, and eight zero, addition and
  scalar cases.
- **Seen:** 4 occurrences in 3 files (2026-09-27): `commute_of_mem_supportedOperators`
  `expect_productVector_mul` and `trace_piKronecker_mul_mul_mul_trace` in
  the supported-operator module (now in QICLean, the last as
  `ManyBody.trace_piKronecker_mul_mul_mul_trace` in
  `QICLean.ManyBody.Sites.ProductOperatorTrace`), and `OnsiteChannel.dual_mul` in
  `TNLean/Circuit/Channel/Conversion.lean` (deleted; onsite channels are now QICLean
  layers without cells).
- **Abstraction:** `ManyBody.eq_of_mem_supportedOperators₂` in QICLean
  (formerly `QuantumCircuit.eq_of_mem_supportedOperators₂`): two bilinear maps
  `f g : M →ₗ[ℂ] M →ₗ[ℂ] P` agree on supported pairs once they agree on pairs of product
  generators (`LinearMap.eqOn_span'` applied in each argument). A call site builds the two
  maps from `LinearMap.mul`, `LinearMap.compr₂` and `LinearMap.compl₁₂`, then proves only the
  product-generator case after a `change`.

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
  `QICLean/Analysis/Real/PowerExponential.lean`; the single-length site
  instantiates the index type with `Unit`.

### error from a logarithmic block-length threshold — promoted
- **Pattern:** close `K * (M * Real.exp (-x)) ≤ ε` from a threshold
  `log K + log M - log ε ≤ x` by a hand-written `calc` through
  `Real.exp_log`, `Real.exp_add`/`Real.exp_sub` and `Real.exp_le_exp`.
- **Seen:** three occurrences across three files (2026-09-30):
  `DepthLogBound.lean`, `LogDepthPreparation.lean` and `TreeMERA.lean`, all
  under `TNLean/MPS/Preparation/`.
- **Abstraction:** `mul_mul_exp_neg_le_of_log_le` in
  `QICLean/Analysis/Real/PowerExponential.lean`.

### error from a block-length threshold with a logarithmic offset — promoted
- **Pattern:** from `a log(M q/ε) + b ≤ q` with `b ≥ a max(log K, 0)`, expand
  `log(M q/ε)`, discard `a log q ≥ 0`, and pass `log K + log M - log ε ≤ q/a`
  to `mul_mul_exp_neg_le_of_log_le`.
- **Seen:** two occurrences across two files (2026-10-01):
  `DepthLogBound.lean` and `NonNormalMeasurementPreparation.lean`, under
  `TNLean/MPS/Preparation/`.
- **Abstraction:** `mul_mul_exp_neg_div_le_of_le` in
  `QICLean/Analysis/Real/PowerExponential.lean`.

### depth from the window of block lengths — promoted
- **Pattern:** from `q ≤ 2 (a log(N/ε) + b)`, `N ≥ 2`, `0 < ε ≤ 1`, `b ≥ 1`,
  a `calc` through `log(N/ε) ≥ log 2` giving
  `C q ≤ C (2a + 2b/log 2) log(N/ε)`.
- **Seen:** two verbatim occurrences across two files (2026-10-01):
  `DepthLogBound.lean` and `NonNormalMeasurementPreparation.lean`.
- **Abstraction:** `MPSPreparation.natCast_mul_le_mul_log_of_le_two_mul` in
  `TNLean/MPS/Preparation/Normal/DepthLogBound.lean`.

### gap of the transfer map of a normal tensor — promoted
- **Pattern:** `uniform_eigenvalue_gap_of_finite_lt_one` with
  `Kraus.isChannel_mapLM … |>.eigenvalue_norm_le_one` and
  `primitive_transfer.unique_peripheral`, then `t := max (1 - δ) (1 / 2)`.
- **Seen:** three occurrences across three files (2026-10-01):
  `ApproximationError.lean`, `DepthLogBound.lean` and
  `NonNormalMeasurementPreparation.lean`, under `TNLean/MPS/Preparation/`.
- **Abstraction:** `MPSTensor.exists_eigenvalue_norm_le_of_isNormal` in
  `TNLean/MPS/CanonicalForm/FixedPointApproximation/ApproximationError.lean`; the family version
  `MPSPreparation.exists_forall_eigenvalue_norm_le` takes the maximum over the
  blocks.

### kernel projection under a right-spectator fiberwise conjugacy — promoted
- **Pattern:** from a right-spectator conjugacy `U G U⁻¹ = rightFiberwiseMap H`,
  conclude `U P_{ker G} U⁻¹ = rightFiberwiseMap P_{ker H}` by combining
  `LinearIsometryEquiv.conj_starProjection_ker_of_conj` (QICLean) with
  `ContinuousLinearMap.ker_starProjection_rightFiberwiseMap` and a `change`.
- **Seen:** five occurrences across two files:
  `openPrefixGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`,
  `openPrefixWholeGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`,
  and `openIntervalGroundProjectionES_conj_rightSpectatorConfigLinearIsometryEquiv`
  in `TNLean/MPS/ParentHamiltonian/Gap/Filtration/SpectatorTransport.lean`, and
  both `hP` and `hQ` in
  `norm_suffixGroundProjection_comp_prefixDifference_le_active` in
  `TNLean/MPS/ParentHamiltonian/Gap/Filtration/WholeIncrementSpectatorTransport.lean`.
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
  `TNLean/MPS/CanonicalForm/SimpleMPU/SimpleBlocking.lean`.

### fixed-range block parent gap from an open-chain kernel identity — promoted
- **Pattern:** obtain a gapped range `W ≥ 2 * R` for a primitive block sum, then transfer the
  gap to range `R` through the open-chain kernel identity at `W`; the uniform form then
  converts the eventual gap into a gap for every chain length with
  `Filter.Eventually.exists_forall_of_atTop` and `parentHamiltonianES_gap_of_eventual_gap`.
- **Seen:** the transfer step three times, in
  `TNLean/MPS/ParentHamiltonian/Gap/PrimitiveBlockGapThreshold.lean`,
  `TNLean/MPS/ParentHamiltonian/Gap/PrimitiveBlockGapThreshold.lean`, and
  `TNLean/MPS/ParentHamiltonian/Gap/PrimitiveBlockGapThreshold.lean`; the
  eventual-to-uniform step twice, in
  `TNLean/MPS/ParentHamiltonian/Gap/PrimitiveBlockGapThreshold.lean` and
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
  `TNLean/MPS/Operator/ReductionComposition.lean` (the `kronId`/`idKron` lifts of reductions and
  dressed proportionality) and four in `TNLean/MPS/Operator/ActionTensorReduction.lean` (the
  action-tensor lifts).
- **Abstraction:** `List.exists_eq_ofFn` in `QICLean/Algebra/Word/OrderedProduct.lean` (QICLean dependency); call sites write
  `obtain ⟨L, u, rfl⟩ := List.exists_eq_ofFn w`.

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
  `TNLean/MPS/Operator/Periodic/OperatorFromWordTrace.lean`.

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
  `Examples/MultiBlock/OneSlotGauge.lean`, `TNLean/MPS/Examples/CZX/Gauging/CZXTensor.lean`,
  `TNLean/MPS/Examples/BondTwoSingleton/BondTwoSingletonGramBoundary.lean`,
  `TNLean/MPS/CanonicalForm/DiagonalRestrictionCounterexample.lean`,
  `TNLean/MPS/Examples/MPDOCounterexamples/PositiveMinimalRealizationCounterexample.lean`,
  `TNLean/MPS/RFP/BellPairCIDObstruction.lean` and
  `TNLean/PEPS/FundamentalTheorem/Torus/TorusRowColumnReductionObstruction.lean`.
- **Abstraction:** `Submodule.eq_top_of_forall_single_mem` in
  `QICLean/Algebra/Matrix/MatrixSingleSpan.lean` (QICLean dependency).

### cancelling a nonzero scalar in a submodule membership — rejected (Mathlib)
- **Pattern:**
  ```lean
  have h' := Submodule.smul_mem _ c⁻¹ hmem
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  ```
- **Seen:** eight occurrences across seven files (2026-10-10): `Examples/AKLT.lean` (twice),
  `Examples/MultiBlock/OneSlotGauge.lean`, `FundamentalTheorem/Reduction/RingEmbedding.lean`,
  and the four `TNLean/MPS/MPDO/` injectivity proofs listed in the previous entry.
- **Abstraction:** none needed: Mathlib's `Submodule.smul_mem_iff (p) (hc : c ≠ 0)` states
  `c • x ∈ p ↔ x ∈ p`; write `(Submodule.smul_mem_iff _ hc).mp hmem`.  All eight sites
  were rewritten that way on 2026-10-10.

### simplicity with the recorded canonical fixed pair — promoted
- **Pattern:** specialize supplied-witness `simple2` to the canonical transfer
  power at `max (D * D - 1) 1`, deriving physical nonvanishing from canonical
  form II and using the recorded vectorized right boundary and identity left boundary.
- **Seen:** three occurrences across three files (2026-09-06):
  `IsMPUCanonicalFormII.sourceV_isIsometry` in
  `TNLean/MPS/MPU/Simple/SourceVCompleteNetwork.lean`,
  `IsMPUCanonicalFormII.doubleLayer_boundary_contractions` in
  `TNLean/MPS/MPU/Simple/AdjointSimpleContraction.lean`, and
  `IsMPUCanonicalFormII.oneLetter_physical_contraction` in
  `TNLean/MPS/MPU/Simple/SourceYPhysicalContractions.lean`.
- **Abstraction:** `MPOTensor.IsMPUCanonicalFormII.simple2_recorded_fixed_pair`
  in `TNLean/MPS/MPU/Simple/SuppliedFixedWitnesses.lean`.

### reciprocal scalar cancellation across a matrix product — promoted
- **Pattern:** move scalars out of a matrix product and cancel nested actions
  by a nonzero scalar and its inverse, in either order.

  ```lean
  simp (disch := exact hβ) only [matrix_reciprocal_smul]
  ```
- **Seen:** three declarations across three files (2026-09-04):
  `MPTensor.IsReduction.reciprocal_smul` in `TNLean/MPS/Tensor/Reduction/Reduction.lean`
  (two goals), `MPTensor.reductionResidual_reciprocal_smul` in
  `TNLean/MPS/Tensor/Reduction/ReductionResidual.lean`, and
  `MPSTensor.IsReductionExteriorBufferLength.reciprocal_smul_iff` in
  `TNLean/MPS/Tensor/Reduction/ReductionBlocking.lean`.
- **Abstraction:** the `matrix_reciprocal_smul` simp set, registered in
  [`TNLean/Tactic/Attr.lean`](../TNLean/Tactic/Attr.lean) and populated in
  [`TNLean/Tactic/MatrixReciprocalSmul.lean`](../TNLean/Tactic/MatrixReciprocalSmul.lean)
  with Mathlib's `Matrix.smul_mul`, `Matrix.mul_smul`, `inv_smul_smul₀`, and
  `smul_inv_smul₀`. No new cancellation theorem or tactic is needed.

### source-rank nonvanishing from a trace equation — promoted
- **Pattern:** derive `rank ≠ 0` from `htrace : coefficient * rank = d` and
  `hd : d ≠ 0` by assuming the rank is zero and simplifying the trace equation.
- **Seen:** four occurrences across three files (2026-09-06):
  `IsMPUCanonicalFormII.sourceY₁_mul_conjTranspose` in
  `TNLean/MPS/MPU/Simple/SourceYOneNormalization.lean`,
  `IsMPUCanonicalFormII.sourceY₂_weighted_mul_conjTranspose` in
  `TNLean/MPS/MPU/Simple/SourceYTwoNormalization.lean`, and
  `IsMPUCanonicalFormII.sourceX₁_physical_contraction` and
  `IsMPUCanonicalFormII.sourceX₂_physical_contraction` in
  `TNLean/MPS/MPU/Simple/SourceXPhysicalNormalization.lean`.
- **Abstraction:** existing Mathlib `right_ne_zero_of_mul`, applied as
  `right_ne_zero_of_mul (htrace.trans_ne hd)`.

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
  `QICLean/Algebra/Combinatorics/FinSumPermutation.lean` (QICLean dependency), with
  `{κ : ι → Type*}`, `{t : (i : ι) → Finset (κ i)}`, and an
  `AddCommMonoid` codomain. Both the inner index type and its finite set may
  depend on the outer index. Two applications of Mathlib's `sum_congr`
  prove it; no macro, product API, or additional typeclass is needed.

- **2026-11-04 sweep:** the scanner still found the literal four-line
  descent `apply Finset.sum_congr rfl` / `intro i _` / `apply Finset.sum_congr
  rfl` / `intro j _` at 93 sites in 65 files, counting each adjacent pair of a
  three-binder descent once. Every one is now
  `refine Finset.sum_congr₂ fun i _ j _ ↦ ?_`; a third binder keeps its single
  descent. 62 files gained the import. Net Lean change: 190 lines
  removed. Statements are unchanged.

### three-block configuration extensionality — promoted
- **Pattern:** prove equality of vectors indexed by a concatenated three-block
  configuration by splitting an arbitrary configuration through the canonical
  three-block equivalence.
- **Seen:** five occurrences in
  `TNLean/MPS/ParentHamiltonian/ProjectorDefect/FNWProjectorDefect.lean` before promotion
  (2026-09-02).
- **Abstraction:** the private theorem `euclideanSpace_threeBlock_ext` in
  `TNLean/MPS/ParentHamiltonian/ProjectorDefect/FNWProjectorDefect.lean`.

### torus-translation bond uniformity — promoted
- **Pattern:** use a translation carrying one right (respectively up) edge to
  another to prove constancy of a bond-dimension function, then reduce an
  arbitrary horizontal or vertical edge to the corresponding reference edge.
- **Seen:** six occurrences across two files before promotion (2026-08-31):
  the right-edge, up-edge, and orientation-uniformity proofs in
  `TNLean/PEPS/Tensor/Torus/TorusTranslationInvariant.lean` and
  `TNLean/PEPS/FundamentalTheorem/Torus/TorusStateTranslationInvariant.lean`.
- **Abstraction:** `bondDim_torusRightEdge_const_of_translate`,
  `bondDim_torusUpEdge_const_of_translate`, and
  `torusUniformBondDim_of_translate` in
  `TNLean/PEPS/Tensor/Torus/TorusTranslationInvariant.lean`.

### torus shift of a product over sites — promoted
- **Pattern:** reindex a product over torus sites by `Equiv.addRight (1, 0)`
  (or `(0, 1)`), rewrite `u + (1, 0)` as `(u.1 + 1, u.2)` and cancel with
  `add_sub_cancel_right`, turning factors on the left (or down) leg of each
  site into factors on the right (or up) leg of its neighbour.
- **Seen:** six occurrences across three files before promotion (2026-09-26):
  `TNLean/PEPS/Examples/Cluster/Cluster.lean` (`stateCoeff_clusterPEPS`),
  `TNLean/PEPS/Examples/AKLT.lean` (`stateCoeff_akltPEPS`), and
  `TNLean/PEPS/Examples/RVB.lean` (`stateCoeff_rvbPEPS`), one horizontal and
  one vertical shift each.
- **Abstraction:** `TNLean.PEPS.prod_torus_sub_fst` and
  `TNLean.PEPS.prod_torus_sub_snd` in `TNLean/PEPS/Tensor/Torus/TorusSiteTensor.lean`.

### permutation-matrix unitarity — promoted
- **Pattern:** unfold unitary-group membership, rewrite the conjugate transpose
  of a permutation matrix as the inverse permutation matrix, and reduce their
  product to the identity permutation.
- **Seen:** three occurrences before promotion (2026-08-30):
  `TNLean/MPS/Examples/Shift/Shift.lean` (`rightShiftTensor_isMPU`),
  `TNLean/MPS/FundamentalTheorem/Sectors/FundamentalCoord.lean`
  (`permGL_mem_unitaryGroup`), and
  `TNLean/MPS/Examples/Shift/ShiftTilde.lean`
  (`shiftPhysicalSwap_mem_unitaryGroup`).
- **Abstraction:** `Equiv.Perm.permMatrix_mem_unitaryGroup` in
  `QICLean/Algebra/Unitary/MatrixUnitaryBetween.lean` (QICLean dependency).

### non-injectivity from an annihilating linear functional — promoted
- **Pattern:** exhibit a matrix outside the span of a finite Kraus family by
  running `Submodule.span_induction` over an entrywise linear condition
  (`M 0 1 = 0`, `M 0 0 = M 1 1`), discharging the `zero`, `add`, and `smul`
  cases by `simp`/`linear_combination`, then contradicting the membership of a
  chosen witness supplied by `span_eq_top ▸ Submodule.mem_top`.
- **Seen:** eight occurrences before promotion (2026-08-26):
  `TNLean/MPS/Examples/AKLT/AKLT.lean` (`aklt_not_isInjective`),
  `TNLean/MPS/Examples/GHZ/GHZ.lean` (`ghz_not_isInjective`),
  `TNLean/MPS/Examples/Cluster/Cluster.lean` (`cluster_not_isInjective`),
  `TNLean/MPS/Examples/EvenParity.lean` (`evenParity_span_diag_eq` and
  `evenParity_not_isInjective`),
  `TNLean/MPS/Examples/MajumdarGhosh/MajumdarGhosh.lean` (`majumdarGhosh_not_isInjective`,
  `majumdarGhosh_not_isNBlkInjective_of_odd`,
  `majumdarGhosh_not_isNBlkInjective_of_even`), and
  `TNLean/MPS/CanonicalForm/DiagonalRestrictionCounterexample.lean`
  (`diagBlock_diagonalRestrictionUnits_not_isNormal`).
- **Abstraction:** `Kraus.not_isInjective_of_linearMap` and
  `Kraus.not_isNBlkInjective_of_linearMap` in
  `QICLean/Kraus/Injectivity.lean`.

### Kronecker product of matrix isometries — promoted
- **Pattern:** expand `Matrix.IsIsometry`, commute conjugate transpose and
  multiplication with the Kronecker product, and substitute the two constituent
  isometry identities.
- **Seen:** two source-factor proofs in
  `TNLean/MPS/MPU/Simple/SourceFactorsTensorProduct.lean`, private copies in
  `TNLean/MPS/FundamentalTheorem/PhysicalSupport/PhysicalSupportBondCommutativity.lean` and
  `TNLean/MPS/Examples/CorrelatedFlip/Spectrum.lean`, and reindexed hand proofs in
  `TNLean/MPS/MPDO/Fusion/BNTRightTripleFusion.lean` and
  `TNLean/MPS/MPDO/Fusion/BNTLeftTripleFusion.lean` before promotion (2026-08-24).
- **Abstraction:** `Matrix.IsIsometry.kronecker` in
  `TNLean/Algebra/MatrixIsometryKronecker.lean`.

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
  `QICLean/Algebra/Unitary/MatrixIsometryEntries.lean` (QICLean dependency).

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
  `QICLean/Algebra/Unitary/MatrixIsometryEntries.lean` (QICLean dependency).

### positive-definite trace pairing with a nonzero positive matrix — promoted
- **Pattern:** prove `0 < Matrix.trace (A * B)` or its cyclic orientation from
  `A.PosDef`, `B.PosSemidef`, and `B ≠ 0` by combining nonnegativity with
  faithfulness of the positive-definite weighted trace.
- **Seen:** three occurrences across two TNLean files before promotion
  (2026-08-23): two in
  `TNLean/MPS/Examples/NonCartesianSectors/NonCartesianActiveSectorCounterexample.lean` and one in
  `TNLean/MPS/CanonicalForm/NormalBlocks/NormalTensorGauge.lean`. QICLean also contained
  two private copies before the upstream promotion.
- **Abstraction:** `Matrix.PosDef.trace_mul_pos_of_posSemidef_of_ne_zero` and
  `Matrix.PosSemidef.trace_mul_pos_of_ne_zero_of_posDef` in
  `QICLean/Algebra/Matrix/MatrixAux.lean` (QICLean dependency).

### matrix-reindex entry transport — direct
- **Pattern:** package an entrywise formula as a `Matrix.reindex` equality with
  `ext` and `Matrix.reindex_apply`, or restate an entry in the reindexing
  coordinates by destructuring both index arguments through `Equiv.surjective`
  and discharging the inverse equivalences with `Equiv.symm_apply_apply`.
- **Seen:** four coordinate-restatement proofs in
  `TNLean/MPS/Examples/Shift/ShiftSourceBlockedFormulas.lean` (lines 25, 44, 121,
  and 140). Locations re-derived 2026-09-03 after the source-cut file split and
  recounted 2026-09-04: the eight packaging proofs formerly counted in the
  mixed-kernel example module went with its deletion.
- **Abstraction:** none. The former project wrappers were retired with
  `QICLean.Algebra.Matrix.MatrixReindex`; the direct extensionality and evaluation
  proofs are the canonical pattern.

### multiplication of compatibly reindexed matrices — Mathlib API
- **Pattern:** replace the product of two `Matrix.reindex` operations with one
  reindexing of the matrix product along the common middle equivalence.
- **Seen:** eight occurrences in
  `TNLean/MPS/Examples/Shift/ShiftSourceFactors.lean` and four in
  `TNLean/MPS/MPU/Simple/SourceFactorsTensorProduct.lean`.
- **Abstraction:** Mathlib's `Matrix.reindexLinearEquiv_mul`; instantiate the
  row, middle, and column equivalences explicitly and use
  `Matrix.coe_reindexLinearEquiv` when coercion normalization is needed.

### blocked-coordinate transport of a channel — promoted
- **Pattern:** relabel the source matrix index along one equivalence, conjugate
  by a rectangular isometry, and relabel the target index back along a second
  equivalence; then assemble trace-preserving complete positivity from the two
  reindexings and the single-Kraus conjugation.
- **Seen:** four defining occurrences and four accompanying positivity proofs
  in `TNLean/MPS/MPDO/PhysicalSector/PhysicalSectorPhysicalTransport.lean` before promotion
  (2026-08-27).
- **Abstraction:** the private `blockTransportMap` and
  `blockTransportMap_isKrausCPTP` at the head of that file.

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
  `TNLean/MPS/Examples/CZX/Gauging/CZXTensor.lean`, and `mpo_rightShiftTensor_apply` in
  `TNLean/MPS/Examples/Shift/Shift.lean`.
- **Abstraction:** `MPOTensor.mpo_apply_eq_sum_cyclic` and
  `MPOTensor.mpo_apply_eq_prod_of_forced_bond` in `TNLean/MPS/Operator/Periodic/OperatorCyclicSum.lean`;
  for monomial tensors, `MPOTensor.mpo_apply_of_forced_right_bond` and
  `MPOTensor.mpo_apply_of_forced_left_bond` in the same file.

### SAL nonvanishing of the physical-trace transfer — promoted
- **Pattern:** contradict the positive-length trace clause in `IsSAL` at one
  site by rewriting the periodic trace as the trace of the vertical loop and
  then setting the physical-trace transfer equal to zero.
- **Seen:** two duplicated proofs in `TNLean/MPS/MPDO/BNTSectors/BNTSectorAreaLaw.lean`
  and `TNLean/MPS/MPDO/RFP/RFPViaTSSAL.lean`; the literal-idempotence bridge in
  `TNLean/MPS/MPDO/Entropy/SALTraceTransfer.lean` supplied the third use at promotion
  (2026-08-21).
- **Abstraction:** `MPOTensor.IsSAL.physTraceTransfer_ne_zero` in
  `TNLean/MPS/MPDO/Entropy/SALTraceTransfer.lean`.

### Powers on an eigenspace — promoted
- **Pattern:** prove `(f ^ n) x = μ ^ n • x` from `x ∈ f.eigenspace μ`, either by induction
  using `Module.End.mem_eigenspace_iff` or by splitting on `x = 0` before applying
  `HasEigenvector.pow_apply`.
- **Seen:** 3 occurrences across `TNLean/Channel/Peripheral/WeightedCesaro.lean`,
  `TNLean/Channel/Peripheral/CesaroRecurrence.lean`, and
  `TNLean/Kraus/Wielandt/Primitivity/VectorSpreadToPrimitive.lean`.
- **Abstraction:** `Module.End.pow_apply_of_mem_eigenspace` in
  `QICLean/Spectral/Eigenvalue/EigenspaceMap.lean` (QICLean dependency) handles the zero vector directly and is used by all
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
  `QICLean/Kraus/Transfer.lean` (QICLean dependency).

### contiguous restriction of open-boundary MPS vectors — promoted
- **Pattern:** split a full-chain configuration into the words left of, inside,
  and right of a nonwrapping window; absorb both outside words into the boundary
  matrix; then use trace cyclicity to identify the restricted vector.
- **Seen:** duplicate private proofs in
  `TNLean/MPS/ParentHamiltonian/ParentInteraction/OpenHamiltonian.lean` and
  `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/BoundaryMatrix/BNTBlockDiagonalChain.lean` before promotion
  (2026-08-14).
- **Abstraction:** `MPSTensor.contiguousRestrictₗ_groundSpaceMap_mem_groundSpace`
  in `TNLean/MPS/Tensor/GroundSpace/CyclicWindow.lean`.

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
  in `QICLean/Analysis/Projection/TwoProjectionCompressionSpectrum.lean` (QICLean dependency).

### fixed point from idempotent range membership — promoted
- **Pattern:** derive `P x = x` from `x ∈ LinearMap.range P` when `P` is
  idempotent.
- **Seen:** the two range-subtype arguments in
  `TNLean/Analysis/TwoProjectionAngleBlock.lean` and the compression-eigenbasis
  argument in `TNLean/Analysis/TwoProjectionCompressionSpectrum.lean` before
  cleanup (2026-08-14).
- **Abstraction:** `LinearMap.IsIdempotentElem.mem_range_iff` in Mathlib.

### pointwise idempotent endomorphism application — promoted
- **Pattern:** apply an equality `P * P = P` to a vector with `congrArg`, then
  simplify `Module.End.mul_apply` to obtain `P (P x) = P x`.
- **Seen:** nine occurrences across
  `TNLean/Analysis/ProjectionGeometry.lean` and
  `TNLean/Analysis/TwoProjectionAngleBlock.lean` before promotion (2026-08-12).
- **Abstraction:** `LinearMap.IsIdempotentElem.apply_apply` in
  `QICLean/Algebra/Hermitian/IdempotentEndomorphism.lean` (QICLean dependency).

### two-site cyclic local-embedding reindexing — promoted
- **Pattern:** reindex a cyclic two-site embedding by the equivalence between
  two-site configurations and ordered pairs, prove agreement outside the full
  window by finite index cases, and identify the extracted coordinates.
- **Seen:** the sector-specific public proof in
  `TNLean/MPS/Operator/PhysicalSector/PhysicalSectorBondTwoSite.lean` and the private generic proof
  in `TNLean/MPS/FundamentalTheorem/PhysicalSupport/PhysicalSupportBondCommutativity.lean` before promotion
  (2026-08-12).
- **Abstraction:** `MPOTensor.reindex_placeAlong_ringWindow_two_zero` and
  `MPOTensor.reindex_placeAlong_ringWindow_two_one` in
  `TNLean/MPS/Operator/Simple/PlaceAlongRingWindowTwoSite.lean`.

### Hayashi state evaluation in middle-sector coordinates — promoted
- **Pattern:** evaluate `EtaStructure.h_state` at decomposed middle-site coordinates,
  identify both inverse reindexings, apply the lifted-conjugation entry formula, and
  simplify the dependent block-state conditional.
- **Seen:** five occurrences in `HayashiSectorComparison.lean`,
  `BNTMarkovKeyFormula.lean`, `SectorFactorization.lean`,
  `BNTMarkovSectorProjectors.lean`, and `InverseMapActiveSectorRecurrence.lean`
  before promotion (2026-08-11).
- **Abstraction:** `HayashiMarkovDecomposition.h_state_apply_middle_sector` in
  `QICLean/Entropy/StrongSubadditivity/EntropyMarkovReverse.lean` (QICLean dependency).

### retained vertical-copy dependent-cast evaluation — promoted
- **Pattern:** unfold the multiplicity-expanded assembled tensor at two coordinates
  in the same retained copy, identify the round-tripped dependent copy index, and
  transport both matrix coordinates across the resulting bond-dimension equality.
- **Seen:** three 30-line occurrences in
  `TNLean/MPS/MPDO/Fusion/VerticalCopyBlocks.lean`,
  `TNLean/MPS/MPDO/Fusion/VerticalProductRetainedBlocks.lean`, and
  `TNLean/MPS/MPDO/SectorMaps/BNTAlgebraTensorClausePositivity.lean` before promotion
  (2026-08-11).
- **Abstraction:** `MPOTensor.verticalAssembledTensor_apply_copy_same` in
  `TNLean/MPS/MPDO/SectorMaps/VerticalSectorCoordinates.lean`.

### left finite-Gram cancellation in spectator coordinates — promoted
- **Pattern:** cancel the fiberwise finite Gram against its inverse Gram, then use
  the left-boundary common-map identity to recover the adjoint of the full
  ground-space map.
- **Seen:** duplicate 28-line arguments in the tail and full inverse-Gram C3
  correction factorizations before promotion (2026-08-10).
- **Abstraction:** `MPSTensor.leftFiniteGramCancellation_eq_groundSpaceMapES_adjoint`
  in `TNLean/MPS/ParentHamiltonian/BoundaryMap/C3CorrectionBounds.lean`.

### single-Kraus Kronecker and isometric multiplication identities — promoted
- **Pattern:** unfold `singleKrausMap`, reassociate matrix products, and use
  Kronecker multiplication or the identity `Vᴴ * V = 1`.
- **Seen:** duplicate 7-line and 8-line helpers in
  `TNLean/MPS/FundamentalTheorem/PhysicalSupport/PhysicalSupportBondCommutativity.lean` and
  `TNLean/MPS/FundamentalTheorem/PhysicalSupport/PhysicalSupportProductTransport.lean` before promotion
  (2026-08-10).
- **Abstraction:** `Matrix.singleKrausMap_kronecker` and
  `Matrix.singleKrausMap_mul_of_isometry` in
  `QICLean/Channel/KrausMap/SingleKrausPositivity.lean` (QICLean dependency).

### finite-sum submatrix distribution — promoted
- **Pattern:** prove that taking a submatrix commutes with a finite sum by
  extensionality and entrywise simplification.
- **Seen:** duplicate 6-line helpers in `TNLean/MPS/CanonicalForm/RenormalizationFixedPoint/BNTOrthogonality.lean`
  and `TNLean/MPS/RFP/PhysicalObservableRealization.lean` before promotion
  (2026-08-10).
- **Abstraction:** `Matrix.submatrix_sum` in `QICLean/Algebra/Combinatorics/FinSum.lean` (QICLean dependency).

### transfer-map irreducibility in Kraus-map notation — promoted
- **Pattern:** use the definitional equality of `Kraus.transferMap` and `Kraus.mapLM` to view
  `IsIrreducibleMap (MPSTensor.transferMap F)` as
  `IsIrreducibleMap (Kraus.mapLM F)` before applying generic peripheral
  theorems.
- **Seen:** the five transfer-map compatibility declarations in
  `TNLean/Channel/Peripheral/{ClosureFixedPoint,CyclicGroup}.lean` (2026-08-09).
- **Abstraction:** no conversion theorem is needed: `Kraus.transferMap` and
  `Kraus.mapLM` are definitionally equal.

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
  `TNLean/MPS/FundamentalTheorem/Compression/MultiBlockTrace.lean`: a compression onto weighted
  blocks `μ_s • A_s` gives `tr(B^w) = ∑_s μ_s^{|w|} tr(A_s^w)`.

### CFC square-root Hermiticity — promoted
- **Pattern:** derive `(CFC.sqrt ρ)ᴴ = CFC.sqrt ρ` from `CFC.sqrt_nonneg`,
  `Matrix.nonneg_iff_posSemidef`, and positive-semidefinite Hermiticity.
- **Seen:** six occurrences across `Channel/FixedPoint/Weighted/WeightedFixedPoints.lean`,
  `MaximalRank.lean`, and `WeightedCornerFixedPoints.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Matrix.conjTranspose_cfc_sqrt` in
  `QICLean/Analysis/FunctionalCalculus/MatrixSqrt.lean` (QICLean dependency).

### positive-definite CFC square-root determinant unit — promoted
- **Pattern:** combine `CFC.isUnit_sqrt_iff`, `Matrix.PosDef.isUnit`, and
  `Matrix.isUnit_iff_isUnit_det` to prove `IsUnit (CFC.sqrt ρ).det`.
- **Seen:** four occurrences across `Channel/FixedPoint/Weighted/WeightedFixedPoints.lean` and
  `WeightedCornerFixedPoints.lean` before promotion (2026-08-09).
- **Abstraction:** `Matrix.PosDef.isUnit_det_cfc_sqrt` in
  `QICLean/Analysis/FunctionalCalculus/MatrixSqrt.lean` (QICLean dependency).

### transfer-map trace-adjoint pairing — promoted
- **Pattern:** rewrite a linear map equality `E = transferMap K`, apply the
  finite-Kraus trace-adjoint identity, and unfold the adjoint transfer family.
- **Seen:** three occurrences across `Channel/Irreducible/FromSpectral.lean`,
  `PerronFrobenius.lean`, and `SpectralRadius.lean` before promotion
  (2026-08-09).
- **Abstraction:** `Kraus.trace_mul_mapLM_adjoint` in
  `QICLean/Channel/KrausMap/KrausMap.lean` (QICLean dependency).

### matrix-family irreducibility in transfer-map notation — promoted
- **Pattern:** convert between irreducibility of a finite matrix family and
  irreducibility of its MPS transfer map by passing through the definitionally equal `Kraus.mapLM`.
- **Seen:** nine forward conversions and three converse conversions across
  `MPS/Transfer/Irreducible/DiagonalFixedPoint.lean`, `Spectral/TransferOperatorGap{NT,Injective}.lean`,
  and `Wielandt/Primitivity/{PrimitiveBridge,ToNormal}.lean` before promotion
  (2026-08-20).
- **Abstraction:**
  `Kraus.isIrreducibleMap_mapLM_of_isIrreducibleFamily` and
  `Kraus.isIrreducibleFamily_of_isIrreducibleMap_mapLM` in
  `QICLean/Channel/Irreducible/InvariantProjection.lean` (QICLean dependency).

### pure gauge to heterogeneous repeated blocks — promoted
- **Pattern:** convert `GaugeEquiv A B` to `HetRepeatedBlocks A B` by passing
  through `EquivalentBlocks`, choosing unit phase, and embedding the
  equal-dimension repeated-block relation.
- **Seen:** four occurrences across
  `TNLean/MPS/FundamentalTheorem/Periodic/RepeatedBlocks.lean` and
  `TNLean/MPS/FundamentalTheorem/Periodic/ProportionalOverlap.lean` in the sectorwise-normalization
  draft (2026-08-02).
- **Abstraction:** `MPTensor.GaugeEquiv.toHetRepeatedBlocks` in
  `TNLean/MPS/FundamentalTheorem/Periodic/RepeatedBlocks.lean`.

### spectral-radius-one matrix dimension — promoted
- **Pattern:** exclude zero matrix dimension by observing that every
  endomorphism of the zero-dimensional square-matrix space has spectral radius
  zero.
- **Seen:** three occurrences across `CanonicalForm/Definitions.lean`,
  `CanonicalForm/NormalTensorGauge.lean`, and `Periodic/Defs.lean` before
  promotion.
- **Abstraction:** `matrix_dim_ne_zero_of_spectralRadius_eq_one` in
  `QICLean/Channel/Peripheral/Spectrum/Spectrum.lean` (QICLean dependency).

### positive-semidefinite support congruence — promoted
- **Pattern:** transport the support projection across an equality of positive
  semidefinite matrices while identifying the two positivity proofs by proof
  irrelevance.
- **Seen:** three occurrences across `MatrixFamilySupport.lean` and
  `WeightedHilbertSchmidt.lean` before promotion.
- **Abstraction:** `Matrix.PosSemidef.supportProj_congr` in
  `QICLean/Analysis/Projection/PosSemidefSupport.lean` (QICLean dependency).

### mpv_ext — promoted
- **Pattern:** `intro N σ` / `intro N hN σ` prelude for `SameMPV₂` /
  `SameMPV₂Pos` goals.
- **Abstraction:** `mpv_ext` (elab tactic, `TNLean/MPS/Tensor/Tactic.lean`).

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
  `QICLean/Analysis/Norm/FrobeniusHilbert.lean`. Each is declared
  twice, once in term position (`weighted_matrix_instances ρ hρ in` prefixing a
  statement) and once in tactic position, because the block is repeated in both
  the statement and the proof of nearly every weighted-norm theorem. The norm
  variant expands to the plain one followed by the norm binding, so the two
  stay in step.

### transfer_simp — promoted
- **Pattern:** unfolding `transferMap A X` to `∑ i, A i * X * (A i)ᴴ`.
- **Abstraction:** `@[mps_transfer]` simp set + `transfer_simp` macro
  (`TNLean/MPS/Tensor/Tactic.lean`).

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
  `TNLean/MPS/Examples/CZX/Gauging/CZXGaussCircuitTuple.lean`, the involution, holonomy, fiber
  coordinate, and label lemmas in
  `TNLean/MPS/Examples/CZX/Gauging/CZXGaussInvariantSubspace.lean`, hypercube connectivity in
  `QICLean/Algebra/Combinatorics/HypercubePhasePotential.lean`, and the characteristic-two
  identity in `QICLean/Algebra/Matrix/MonomialFixedSubspace.lean`.
- **Mathlib replacement:** the characteristic-two identity in
  `MonomialFixedSubspace.lean` now uses `CharTwo.add_self_eq_zero` pointwise;
  finite-case automation is no longer needed at that call site.
- **Abstraction:** `generalize_decide t₁, …, tₙ` macro
  (`QICLean/Algebra/Combinatorics/GeneralizeDecide.lean`, QICLean dependency); the terms are abstracted in order
  and `decide +revert` quantifies over the fresh variables.

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
  `TNLean/MPS/MPDO/Fusion/BNTFusionTensorClauseFromRFP.lean`,
  `TNLean/MPS/MPDO/Fusion/BNTLeftTripleFusion.lean`,
  `TNLean/MPS/CanonicalForm/SimpleMPO/BNTProjectorSelection.lean`,
  `TNLean/MPS/MPDO/Fusion/BNTRightTripleFusion.lean`,
  `TNLean/MPS/MPDO/BNTSectors/BNTSectorAreaLaw.lean`,
  `TNLean/MPS/CanonicalForm/SimpleMPO/BNTThreeSiteReducedClosure.lean`,
  `TNLean/MPS/Operator/Fusion/CompleteZipperFusionPentagon.lean`,
  `TNLean/MPS/MPDO/CyclicActiveSector/CyclicActiveFourthRegionFormula.lean`,
  `TNLean/MPS/Examples/MPDOCounterexamples/KatoDeformedRFPObstruction.lean`,
  `TNLean/MPS/CanonicalForm/BlockSeparation/PerCopyHorizontalCF.lean`,
  `TNLean/MPS/Operator/PhysicalSector/PhysicalSectorCoordinateTransport.lean`,
  `TNLean/MPS/CanonicalForm/BlockSeparation/RepresentativeGroupedLemmaL.lean`,
  `TNLean/MPS/MPDO/TopologicalForm/TopologicalProjectorRecursion.lean`,
  `TNLean/MPS/MPDO/TopologicalForm/TopologicalTerminalSpectral.lean`,
  `TNLean/MPS/MPDO/Fusion/VerticalProductRetainedBlocks.lean`,
  `TNLean/MPS/RFP/AppendixBTwoSiteBasicSupport.lean`,
  `TNLean/MPS/RFP/BellPairCIDObstruction.lean`,
  `TNLean/MPS/RFP/CPSVCIDNotRFPExample.lean`,
  `TNLean/MPS/CanonicalForm/RenormalizationFixedPoint/StructuralFull.lean` and
  `TNLean/PEPS/FundamentalTheorem/Torus/Window/CornerExtensionTransitivity.lean`.
- **Abstraction:** `Fintype.sum_mul_mul_eq_mul_sum_mul` in
  `QICLean/Algebra/Combinatorics/FinSum.lean` (QICLean dependency).
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
  `QICLean/Algebra/Combinatorics/FinSum.lean` (QICLean dependency).

### finite-sum coefficient isolation after complement substitution — promoted
- **Pattern:** split a finite sum into a chosen subfamily and its complement,
  replace each complementary vector by a scalar multiple of a vector in a
  second family, collect coefficients along the resulting finite map, and use
  linear independence of the combined family to isolate a chosen coefficient.
- **Seen:** three proof sites across
  `TNLean/MPS/CanonicalForm/BNTPresentation/Characterization.lean`,
  `TNLean/MPS/FundamentalTheorem/Sectors/ProportionalMatchCore.lean`, and
  `TNLean/MPS/FundamentalTheorem/Periodic/ProportionalOverlap.lean` (2026-08-02).
- **Abstraction:** `LinearIndependent.coefficient_eq_zero_of_sum_eq_of_complement_smul`
  in `QICLean/Algebra/Combinatorics/FinSum.lean` (QICLean dependency).

### suffix marginal sector-block expansion — promoted
- **Pattern:** reindex a normalized reduced state into physical-sector
  coordinates, change the discarded-site sum to dependent sector fibers, and
  identify equal retained-sector words with a dependent block-diagonal entry.
- **Seen:** three suffix lengths in
  `CyclicActiveFourthRegionContraction.lean` and
  `CyclicActiveAdjacentCoefficientExtraction.lean` before promotion.
- **Abstraction:**
  `PhysicalSectorFactorization.reindex_reducedBlockState_add_eq_suffixSectorContraction`
  in `TNLean/MPS/MPDO/CyclicActiveSector/CyclicActiveFourthRegionContraction.lean`.

### partial trace under product reindexing — promoted
- **Pattern:** split a simultaneous relabelling of both tensor factors into
  left- and right-factor submatrices, change the summation index in the traced
  factor, and compose the resulting submatrices.
- **Seen:** three occurrences across `PartialTrace.lean`,
  `RelativeEntropyDataProcessing.lean`, and `StrongSubadditivityPosDef.lean`
  before promotion.
- **Abstraction:** `Matrix.partialTraceRight_submatrix_prod_equiv` in
  `QICLean/Algebra/PartialTrace.lean` (QICLean dependency).

### tripartite right partial trace after reassociation — promoted
- **Pattern:** reassociate a matrix indexed by
  \(A\times(B\times C)\) to \((A\times B)\times C\), expand the right
  partial trace, and identify the result with the direct tripartite trace over
  \(C\).
- **Seen:** three occurrences across `StrongSubadditivityPosDef.lean` and
  `SSAEqualityPetzRecovery.lean` before promotion.
- **Abstraction:** `Matrix.partialTraceRight_submatrix_prodAssoc` in
  `QICLean/Entropy/VonNeumann/Entropy.lean` (QICLean dependency).

### eventual word-tuple span from selectors — promoted
- **Pattern:** propagate block injectivity from a positive length to the prefix remaining after
  a fixed selector suffix, concatenate the prefix and suffix, and simplify their total length.
- **Seen:** four occurrences across `PostBlockedRepresentativeSpan.lean` and
  `SourceBNTBlocking.lean` before promotion.
- **Abstraction:**
  `eventually_wordTupleSpanTop_of_blockSelectorWords_of_isNBlkInjective` in
  `TNLean/MPS/CanonicalForm/BlockSeparation/PostBlockedRepresentativeSpan.lean`.

### invariant MPDO first-site action — promoted
- **Pattern:** extract the two doubled-index matrix entries from
  `P₁ H = P₁ H P₁` and `P₁ H = H P₁`, rewrite them as first-site action identities,
  and compose through the common left action.
- **Seen:** formerly handwritten in the BNT-basis and per-block proofs in
  `InvariantProjection.lean` and the representative proof in `HorizontalBNT.lean`; the
  literal CPSV original-space invariant proof uses the same identity.
- **Abstraction:**
  `MPOTensor.firstSiteActionAgree_braRight_ketLeftBraRight_of_invariant` in
  `TNLean/MPS/CanonicalForm/SimpleMPO/InvariantProjection.lean`.

### peps_prod_entry_congr — promoted
- **Pattern:** product congruence followed by component-function extensionality:
  `refine Finset.prod_congr rfl (fun w _ => ?_); congr 1; funext ie`.
- **Seen:** 12 expanded occurrences across 10 PEPS files before promotion. Nine call sites
  now use the shared lemma; one expanded occurrence is its proof, while the two occurrences
  in `RegionBlock/Recovery.lean` remain for the #4522 owner (2026-07-22).
- **Abstraction:** `regionProd_subtype_congr` in
  `TNLean/PEPS/Tensor/Region/RegionBlock.lean`, supported by
  `ManyBody.isRegionBoundaryEdge_of_disjoint_incident` for the repeated disjoint-region side goal.

### eta_cyclic_local_operator_transport — promoted
- **Pattern:** reindexing a translated two-site bond into cyclic edge coordinates, then
  proving it is block diagonal with a single active edge factor.
- **Seen:** two implementations: 269 declaration/proof lines in
  `PhysicalSectorProductRealization.lean` and 250 in
  `CommutingBondEtaCyclicTransport.lean` before the refactor.
- **Abstraction:** `MPOTensor.reindex_placeAlong_ringWindow_etaPairBond` in
  `TNLean/MPS/Operator/PhysicalSector/CommutingBondEtaCyclicCore.lean`; the physical-sector route supplies
  only its coordinate equivalence and local block-decomposition law.

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
  `TNLean/MPS/MPDO/PhysicalSector/PhysicalSectorVirtualTransport.lean`.

### list_ofFn_products — promoted
- **Pattern:** induction on the length to distribute an ordered `List.ofFn` product over
  finite sums, or to extract scalar coefficients from such a product.
- **Seen:** the sum identity occurred in `SitewisePhysicalMatrix.lean`,
  `PhysicalSectorProductTransport.lean`, `CornerContraction.lean`,
  `MPS/Tensor/Gauge/OnSiteSymmetry.lean`, and `MPS/FundamentalTheorem/Refinement/IsometryTensor.lean`;
  the scalar identity also occurred in `TopologicalDensityDecomposition.lean`.
- **Abstraction:** `List.prod_ofFn_sum` and `List.prod_ofFn_smul` in
  `QICLean/Algebra/Word/OrderedProduct.lean` (QICLean dependency).

### ofCommutingInvolutions_mul_conjTranspose — promoted
- **Pattern:** split a `Z₂ × Z₂` element into four cases, expand the representation,
  and prove unitarity from two unitary commuting involutions.
- **Seen:** the cluster-state and AKLT examples each used a four-case finite-matrix
  proof for their physical action.
- **Abstraction:** `ofCommutingInvolutions_mul_conjTranspose` in
  the QICLean module `QICLean/Representation/ZMod2Representation.lean`.

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

### off-edge delta collapse to the consistent-off-`e` subtype — promoted
- **Pattern:** a sum over all open local configurations of a three-factor
  summand whose first factor is the product of the per-edge consistency deltas
  away from a distinguished edge, collapsed by `prod_off_delta_eq` into an
  `if … then … else 0`, then re-expressed as a sum over the subtype of
  configurations consistent off that edge via `Finset.sum_ite` followed by
  `Finset.sum_subtype_eq_sum_filter`.
- **Seen:** four occurrences across `PEPS/FundamentalTheorem/Injective/GaugeAction.lean`
  (`edgeInsertedCoeff_eq_sum_local`),
  `PEPS/FundamentalTheorem/Injective/EdgeInsertion.lean` (`open_gauge_sum_over_outer`),
  `PEPS/FundamentalTheorem/Injective/OneVertexComparison.lean`
  (`edgeInsertedCoeff_eq_doubled`), and `PEPS/FundamentalTheorem/Normal/RegionInsertion/InsertedCoefficientExpansion.lean`
  (`regionInsertedCoeff_eq_smul_edgeInsertedCoeff`) before promotion — four
  files, clearing the rule of three.
- **Abstraction:** `TNLean.PEPS.sum_off_delta_eq_sum_consistentOff` in
  `TNLean/PEPS/FundamentalTheorem/Injective/GaugeAction.lean`. The trailing factor is
  taken as an arbitrary function of the configuration, which is what lets the
  four callers pass their own per-vertex tensor product, gauge-matrix product,
  or region-assembled component product.

### bit-indexed Kraus support fibre sums — promoted
- **Pattern:** a Kraus operator supported on the indicator of a condition
  prescribing some bits of a bit-encoded physical index; a sum against it is
  rewritten into the indicator of the fibre condition by `ite_eq_left` /
  `ite_eq_right` under `Finset.sum_congr`, and the fibre sum is then collapsed
  to the single index (all bits prescribed) or to a sum over the free bits.
- **Seen:** four occurrences across two files (2026-09-02):
  `MPS/Examples/Dimer/TwistedDimerRefine.lean` (`refineKraus_col_sum`, `refineKraus_row_sum`) and
  `MPS/Examples/Dimer/TwistedDimerViaTS.lean` (`coarseKraus_row_sum`, `coarseKraus_res_term`).
- **Abstraction:** `MPOTensor.TwistedDimer.one_site_fiber_sum`,
  `left_fiber_sum`, `right_fiber_sum`, and `pair_fiber_sum` in
  `TNLean/MPS/Examples/Dimer/TwistedDimerRefine.lean`, all stated for an arbitrary
  summand so that each caller supplies its own Kraus amplitude and contracted
  vector.

---

### twisted-dimer bit-encoding destructuring — promoted
- **Pattern:** rewriting an index of the eight-valued physical or bond
  alphabet of the twisted dimer as its bit encoding before case analysis:
  ```lean
  obtain ⟨p, p', k, rfl⟩ : ∃ p p' k, a = physIdx p p' k := ⟨_, _, _, (physIdx_bits a).symm⟩
  ```
- **Seen:** 4 occurrences across 2 files before promotion
  (`TNLean/MPS/Examples/Dimer/TwistedDimerFlagSectors.lean`,
  `TNLean/MPS/Examples/Dimer/TwistedDimerHorizontalCF.lean`).
- **Abstraction:** `MPOTensor.TwistedDimer.exists_eq_physIdx`
  (`TNLean/MPS/Examples/Dimer/TwistedDimerMPDO.lean`); call sites read
  `obtain ⟨p, p', k, rfl⟩ := exists_eq_physIdx a`.

### ground-space invariance under nonzero tensor rescaling — promoted
- **Pattern:** identify the local MPS spaces of `ζ • A` and `A` for `ζ ≠ 0`
  by rewriting `groundSpaceMap (ζ • A) L X` as
  `groundSpaceMap A L ((ζ ^ L) • X)`, then use multiplication by
  `ζ ^ L` and its inverse for the two range inclusions.
- **Seen:** three occurrences before promotion (2026-09-04): the private
  `groundSpace_smul_eq` in
  `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/CoisometricReconstruction.lean`, the private
  `groundSpace_smul_eq_of_ne_zero` in
  `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/CanonicalBlockGroundSpaceAtInjectivityLength.lean` (both 2026-08-31), and
  the normalized primitive gauge of a normal tensor in
  `TNLean/MPS/ParentHamiltonian/Gap/Comparison/PrimitiveGaugeExistence.lean`.
- **Abstraction:** `MPSTensor.groundSpace_smul_eq` in
  `TNLean/MPS/Tensor/GroundSpace/GroundSpace.lean`, placed beside
  `MPTensor.GaugeEquiv.groundSpace_eq` so that the scalar and the gauge half
  of the normalization are available together.

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
  `TNLean/MPS/FundamentalTheorem/Compression/RingEmbedding.lean`, beside
  the entrywise image `Matrix.complexOfRing` of
  `QICLean/Algebra/Matrix/ComplexOfRing.lean` that they belong to.

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
- **Abstraction:** `Matrix.complexOfRing_sub`, `_transpose`,
  `_blockDiagonal'`, `_injective`, `_ne_zero` and
  `Matrix.complexOfRing_mul_eq_one` in
  `QICLean/Algebra/Matrix/ComplexOfRing.lean`; `MPSTensor.evalWordR` with
  `MPSTensor.evalWord_complexOfRing`, and the certificates
  `MPSTensor.isNBlkInjective_of_complexOfRing_smul_single` and
  `MPSTensor.isNormal_of_complexOfRing_smul_single`, in
  `TNLean/MPS/FundamentalTheorem/Compression/RingEmbedding.lean`.

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
  `TNLean/MPS/Examples/Rings/GoldenRing.lean`, since 2026-09-25 an
  instance of the ring-generic `MPSTensor.MultiBlockCompression.ofRing` of
  `TNLean/MPS/FundamentalTheorem/Compression/ExplicitGauge.lean` (see the entry
  on the ring-generic compression datum), with `MPSTensor.unitOrd` and
  `MPSTensor.unitCoord` for the block ordering and bond coordinates of a datum
  with one target placed before the zero slots.

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
  `TNLean/MPS/FundamentalTheorem/Compression/ExplicitGauge.lean`, together with
  the single-slot set `MPSTensor.oneSlot`.

### normality from a golden matrix-unit table — promoted
- **Pattern:** a tensor over `ℤ[σ]` is shown normal by deciding, for every
  matrix unit, a combination of words of one positive length with coefficients
  in `ℤ[σ]`, transporting the identity along `complexOfGolden`, and closing the
  span argument by `Matrix.matrix_eq_sum_single`.
- **Seen:** four occurrences (2026-09-17): the two blocks of
  `TNLean/MPS/Examples/Fibonacci/Fibonacci.lean` and the two
  normal states of `Examples/Fibonacci/FibonacciAction.lean`.
- **Abstraction:** `MPSTensor.isNormal_of_complexOfRing_single` in
  `TNLean/MPS/FundamentalTheorem/Compression/RingEmbedding.lean`, the unscaled
  instance of `MPSTensor.isNormal_of_complexOfRing_smul_single`, applied along
  `goldenToComplex` (the golden-specific wrapper was removed on 2026-09-25).
  The single-letter certificates `P6Compression.isNormal_of_single_eq_smul`
  and `MPSTensor.isNormal_of_single_eq_smul_zsqrt2` are instances of
  `MPSTensor.isNormal_of_complexOfRing_letter_eq_smul_single`, which keeps the
  complex prefactor.

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
  `TNLean/MPS/Examples/Z2Z2/AnomalousCondensationZ2Z2NonSplit.lean`,
  and `eE_int`, `eY_int`, `eX_int`, `eXy_int`, `yE_int`, `yY_int`, `yX_int`,
  `yXy_int`, `xE_int`, `xyE_int`, `xY_int`, `xyY_int` in
  `TNLean/MPS/Examples/Z2Z2/AnomalousCondensationZ2Z2Split.lean`.
  Each theorem differs only in its statement, never in its proof.
- **Abstraction:** the `revert_decide_kernel x₁, …, xₙ` tactic macro, in
  `QICLean/Algebra/Combinatorics/GeneralizeDecide.lean` (QICLean dependency) beside the sibling `generalize_decide`
  macro it is modeled on.

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
  `TNLean/MPS/FundamentalTheorem/Compression/AssemblyLemmas.lean`, wrapping
  `right_intertwiner_eq_zero_of_certificate` and
  `left_intertwiner_eq_zero_of_certificate`.

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
  `TNLean/MPS/Tensor/Words/NormalityFromTwoWords.lean`.

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
  and two in `TNLean/MPS/Preparation/BlockSum/DiagonalPolar.lean`.
- **Abstraction:** `MPSTensor.sum_star_mul_mul_mul`, `MPSTensor.sum_star_mul_mul`
  (scalars out of `∑_τ conj(a F τ) (b G τ)`), and
  `MPSTensor.sum_star_sum_mul_sum_of_orthogonal` (the whole inner product
  `∑ⱼ conj(aⱼ) bⱼ cⱼ` from `⟨Fⱼ, Gⱼ'⟩ = δⱼⱼ' cⱼ`) in
  `TNLean/MPS/Preparation/BlockSum/DiagonalPolar.lean`.

### Spectator ranges of block sums — factored
- **Pattern:** identify a spectator boundary map as a coordinate map composed
  with the pointwise extension of the local boundary map, then distribute its
  range over a sum of local ground spaces.
- **Seen:** the left and tail boundary ranges in
  `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/BlockSumIntervalSpaces.lean`.
- **Abstraction:** the private `pi_univ_iSup_const` lemma follows from Mathlib's
  `Submodule.iSup_map_single`, `Submodule.map_iSup`, and `iSup_comm`.
  Both range calculations use `LinearMap.range_compLeft`; the Hilbert-space
  statements follow by mapping the same submodule identities.

### Uniform decay of whole-increment block errors — factored
- **Pattern:** combine the geometric FNW estimate with the vanishing rational
  coefficient, then choose a common overlap length independently of the two
  exterior intervals.
- **Occurrences:** the single-block numerical threshold in `C3Threshold.lean`
  and the finite-block decay argument.

### Preserving overlap bounds under finite orthogonal sums — promoted
- **Pattern:** expand the inner product over fixed spectator configurations,
  apply the pointwise overlap bound, and finish with finite Cauchy–Schwarz.
- **Occurrences:** the two nested restrictions to a middle interval in
  `TNLean/MPS/ParentHamiltonian/BoundaryMap/SpectatorOverlap.lean`, and the aggregate
  estimate `norm_inner_overlap_sub_inner_aggregates_le` in
  `TNLean/MPS/ParentHamiltonian/ProjectorDefect/FNWOverlapEstimate.lean`, which ran the same
  chain `norm_sum_le`, `Finset.sum_le_sum`, `Finset.mul_sum`,
  `Real.sum_mul_le_sqrt_mul_sqrt` over the spectator configurations.
- **Abstraction:** `Finset.norm_sum_le_mul_sqrt_mul_sqrt` in
  `QICLean/Algebra/Combinatorics/FiniteCauchySchwarz.lean` (QICLean dependency): termwise bounds
  `‖z i‖ ≤ c * a i * b i` with `0 ≤ c` give
  `‖∑ i ∈ s, z i‖ ≤ c * (√(∑ a i ^ 2) * √(∑ b i ^ 2))`.

### Lower Gram bounds and off-diagonal pairings — locally factored
- **Pattern:** turn a lower Gram bound into an upper bound on the Euclidean
  norm of the component norms, then apply a bilinear matrix estimate.
- **Occurrences:** three uses of `norm_norms_le_of_lower_bound` in
  `QICLean/Analysis/Projection/OverlapMatrix.lean`.

### Decomposing membership in a finite sum of subspaces — promoted
- **Pattern:** obtain vectors in the individual subspaces from membership in
  their finite supremum using `Submodule.mem_iSup_finset_iff_exists_sum`, then
  apply a norm or inner-product estimate to their sum.
- **Occurrences:** three proofs across two files:
  `Submodule.norm_inner_le_iSup_of_overlapMatrix` and
  `Submodule.iSup_overlap_bound_of_uniform`
  (`QICLean/Analysis/Projection/OverlapMatrix.lean`), and the
  private lemma `norm_inner_sum_starProjection_sub_le` in
  `QICLean/Analysis/Projection/ProjectorSumConvergence.lean`.
- **Abstraction:** `Submodule.exists_sum_eq_of_mem_iSup` in
  `QICLean/Analysis/Projection/OverlapMatrix.lean` turns
  `u ∈ ⨆ i, V i` over a finite index type into a family `v : ∀ i, V i` with
  `∑ i, (v i : M) = u`, absorbing the `(s := Finset.univ)` instantiation and
  the `simpa` coercion from the indexed supremum.

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
- **Abstraction:** the entrywise image `Matrix.complexOfRing` along a ring
  homomorphism into the complex numbers, with `Matrix.complexOfRing_mul`,
  `Matrix.complexOfRing_one` and `Matrix.complexOfRing_neg` in
  `QICLean/Algebra/Matrix/ComplexOfRing.lean`, whose instantiation at the integer cast
  is the coercion `MPSTensor.complexOfInt` of
  `TNLean/Algebra/ComplexOfInt.lean` with its one-line `complexOfInt_mul`,
  `complexOfInt_one` and `complexOfInt_neg`, together with
  `MPSTensor.gaugeOfMatrix` and `MPSTensor.conjMatrix_gaugeOfMatrix` in
  `TNLean/MPS/FundamentalTheorem/Compression/ExplicitGauge.lean`.

### nested finite-sum binder permutation — promoted
- **Pattern:** permute the binders of three to five nested finite sums over
  `Finset.univ` by folding them into one sum over an iterated product type,
  transporting along an explicit component permutation with
  `Fintype.sum_equiv`, and unfolding again with `Fintype.sum_prod_type`.
- **Seen:** five used private helpers and one unused helper across
  `TNLean/MPS/MPU/Simple/SourceUCompleteNetwork.lean`,
  `TNLean/MPS/MPU/Simple/SourceVCompleteNetwork.lean`, and the range-transport module
  deleted on 2026-09-04 (recorded 2026-09-03).
- **Abstraction:** the `Fintype.sum_reverse_three`,
  `Fintype.sum_last_two_first_four`, `Fintype.sum_last_first_four`,
  `Fintype.sum_last_two_first_five`, and `Fintype.sum_permute_five` helper
  theorems in `QICLean/Algebra/Combinatorics/FinSumPermutation.lean` (QICLean dependency).

### canonical local space as the representative block sum — factored
- **Pattern:** compose `CPSVCanonicalFormData.groundSpace_eq_iSup_representatives` with the
  symmetric form of `groundSpace_toTensorFromBlocks_eq_iSup (fun _ ↦ 1) B (by simp) L`.
- **Seen:** 2 occurrences, in
  `TNLean/MPS/ParentHamiltonian/BlockGroundSpace/CanonicalBlockGroundSpaceAtInjectivityLength.lean` and
  `TNLean/MPS/ParentHamiltonian/Gap/CanonicalGapAtSimultaneousInjectivity.lean`.
- **Abstraction:** `CPSVCanonicalFormData.groundSpace_eq_toTensorFromBlocks_representatives`
  in `CanonicalBlockGroundSpaceAtInjectivityLength.lean`, the first file that needs it. The
  parent-Hamiltonian identity then follows from `parentHamiltonianES_eq_of_groundSpace_eq`.

## Candidates

### Destructuring large existentials in let-heavy goals — candidate (2026-11-18)

- **Seen:** Seven slow `MPS/AreaLaw` proofs: `PhysicalLDTree`,
  `DyadicRegionalLowDensityFamily`, `CanonicalLowDensityFamily`,
  `PhysicalDGCanonicalApproximation`, `PhysicalLowEnergyFamily`,
  `SharpRegionalScalarBudgets` and `SharpRegionalLowDensityFamily`.
- **Pattern:** `obtain ⟨...⟩ := f args` on a family whose statement has many `let`
  binders type-checks the instantiated statement, and inside a large dependent goal
  each `obtain` also re-checks the goal; profiles showed 1–2 s per step. Binding first,
  `have hf := f args` and then `obtain ⟨...⟩ := hf`, halves that. Inside a large goal,
  `refine h.elim fun x hx ↦ ?_` with projections `hx.1`, `hx.2.1`, … avoids the goal
  check altogether; `PhysicalLDTree` went from 30 s to 17 s.
- **Related:** when an `ActualClippedPolynomialFamily` decomposition is passed to the
  nested Chebyshev filter, the coordinate types `ManyBody.RegionConfig β J` and
  `J → Fin q` agree only after unfolding; `have hconj := hM.2; with_reducible exact hconj`
  stops the unifier from unfolding the continuous-linear composition instead.
- **Abstraction:** none yet; a lint or a short `obtain`-like macro that eliminates and
  projects could follow if new slow modules show the same profile.

### Extending mixed-path identities to the endpoints — candidate (2026-11-17)

- **Seen:** The integral-average formula and local commutation in
  `MPS/Symmetry/MPOSymmetry/MixedPath/MPO/MixedWeakHopfAverage.lean` hold first on `(0,1)`.
- **Pattern:** Both sides are continuous, so `Set.EqOn.closure` and `closure_Ioo`
  extend the identities to `[0,1]`. Use this existing Mathlib theorem instead of
  separately constructing a closed equalizer and applying `closure_minimal` each time.
- **Decision:** No custom tactic or new generic topological lemma is needed.

### Passing from a natural localization radius to a real radius — resolved (2026-11-17)

- **Pattern:** Use the floor inequality to bound
  `exp (a - (⌊ℓ⌋₊ : ℝ) / 2)` by `exp (1 / 2) * exp (a - ℓ / 2)`;
  combine this factor with the coefficient of the natural-radius estimate.
- **Seen:** The chain localization theorem, now in QICLean's
  `ManyBody/Dynamics/GraphLocalization.lean`,
  and the domain localization theorem formerly in
  `MPS/AreaLaw/DomainLiebRobinson.lean`.
- **Existing lemmas:** `Nat.lt_floor_add_one`, `Nat.floor_lt`,
  `Real.exp_le_exp` and `Real.exp_add`.

### Overlap and residual of a vector near a unit target — candidate (2026-11-04)

- **Seen:** `MPS/AreaLaw/ChebyshevAGSP/ChangingTargetStep.lean`,
  `Initialization.lean` and `FrustrationFreeMPSApproximation.lean`.
- **Pattern:** From `‖x‖ = ‖φ‖ = 1` and `‖x - φ‖ ^ 2 ≤ c`, expand `norm_sub_sq`,
  compare the real part with `Complex.re_le_norm`, and conclude
  `1 / 2 ≤ ‖⟪φ, x⟫_ℂ‖`; bound `‖x - ⟪φ, x⟫_ℂ • φ‖` by the norm of the projection
  onto `(span {φ})ᗮ`.
- **Abstraction:** A proposed lemma giving both the overlap lower bound
  `1 - ‖x - φ‖ ^ 2 / 2 ≤ ‖⟪φ, x⟫_ℂ‖` and the residual bound, for use with
  `Matrix.exists_phase_normalized_filter_output`.

### Dimension and gap bounds from an actual excitation — candidate (2026-11-04)

- **Seen:** `MPS/AreaLaw/ChebyshevAGSP/SharpPerCutApproximation.lean`
  (`aklv_chain_dimension_and_gap_bounds`) and
  `FrustrationFreeMPSApproximation.lean`
  (`aklv_frustrationFree_dimension_and_gap_bounds`, ground energy zero).
- **Pattern:** Two spectral values give `2 ≤ q` and a nonempty chain; the
  gapped-ground-state predicate then gives `g ≤ 1`.
- **Abstraction:** Derive the frustration-free statement from the general one at
  `μ = 0`, or move the general one beside
  `ManyBody.BondInteraction.gap_le_one_of_nonneg_of_le_one`.

### Transporting three decoded Gram-factor bounds — candidate (2026-11-04)

- **Pattern:** After identifying decoded rational matrices with the rounded
  density and two auxiliary Gram factors, rewrite the three identities and
  discharge their entrywise approximation bounds componentwise.
- **Seen:** Three occurrences in
  `MPS/AreaLaw/GroundStateAlgorithm/BoundarySDP/ApproximateCertificates.lean` near the explicit,
  uniform, and accepted-certificate constructions (scanner output,
  2026-11-04).
- **Abstraction:** A mathematical helper packaging the three transported
  entrywise bounds is preferable if the pattern appears in a second file.

### Entrywise proof that a matrix is diagonal — candidate (2026-11-04)

- **Pattern:** `ext x y`, `by_cases hxy : x = y`, `· subst y`, then a diagonal
  computation and an off-diagonal vanishing argument.
- **Seen:** 13 sites in 7 files by the 2026-11-04 scan, after the five sites of four
  `Circuit/` modules moved to QICLean, as `x y` with `hxy`
  (`MPS/Examples/IdentityPlusZString/FourCycleEntropy.lean` four times,
  `MPS/FundamentalTheorem/PhysicalSupport/PhysicalSupportProductTransport.lean`,
  `MPS/Examples/Shift/ShiftSourceFactors.lean`) and as `σ τ` with `hστ`
  (`MPS/Examples/IdentityPlusZString/Literal.lean` twice,
  `MPS/Examples/MPDOCounterexamples/CaseIIAbsorptionCounterexample.lean`, `MPS/Operator/Periodic/FirstSite.lean`,
  `MPS/Examples/MPDOCounterexamples/KatoDeformedRFPObstruction.lean`,
  `MPS/Examples/MPDOCounterexamples/ThermodynamicLimitCounterexample.lean`,
  `MPS/MPDO/TopologicalForm/TopologicalGibbsHamiltonian.lean` twice).
- **Abstraction:** most goals have the form `M = Matrix.diagonal f` or compare
  two matrices that are both diagonal. A lemma
  `Matrix.eq_diagonal_of_apply (hd : ∀ x, M x x = f x)
  (ho : ∀ x y, x ≠ y → M x y = 0) : M = diagonal f` would replace the three
  lines and the two bullets by two named obligations. Mathlib has
  `Matrix.diagonal_eq_diagonal_iff` for two diagonal matrices but no
  entrywise characterization of equality with a diagonal matrix.

### Equality of indicator propositions through `propext` — candidate (2026-11-04)

- **Pattern:** `congr 1`, `apply propext`, `constructor`, then two
  implications proved by hand.
- **Seen:** 8 sites in 6 files (`Circuit/Channel/PortMatching.lean`, since deleted,
  `MPS/AreaLaw/ViableSet/Basic.lean`, `PEPS/Approximation/Frames/RankOneBlocks.lean`,
  `PEPS/FundamentalTheorem/Injective/EdgeMiddleKernelDescent.lean` twice, since deleted,
  `PEPS/Injectivity/Region/RegionKernelDescent.lean` twice,
  `PEPS/Injectivity/Regular/RegularBoundaryLocalAlgebra.lean`).
- **Abstraction:** the goals are `(if P then a else b) = (if Q then a else b)`
  or a set-builder equality, where `P` and `Q` differ by a transported
  coordinate. `if_congr`, `Set.ext` or `congr 1; exact propext ⟨_, _⟩` state the
  same thing in one line; no new tactic is proposed.

### Identity bond cast of a trivial fusion datum — rejected (2026-11-04)

- **Pattern:** `rw [GroupFamily.castMat_eq_finCongr]`,
  `exact finCongr_toMatrix_eq_one _`, then
  `rw [GroupFamily.FusionData.rightV, hc]`.
- **Seen:** 8 sites in 2 files (`MPS/Examples/Z3/Z3AnomalyClass.lean`
  twice, `MPS/Examples/CZX/Gauging/CZXPermutedBlocks.lean` six times), each proving
  `family.castMat e = 1` for an equation `e` between group elements whose bond
  dimensions reduce to the same numeral.
- **Reason:** a lemma `castMat e = 1` cannot be stated without the cast, since
  the matrix has type `Matrix (Fin (bondDim b)) (Fin (bondDim a)) ℂ` and `1`
  needs `a` and `b` to have definitionally equal bond dimensions. The two
  rewrites are the minimal spelling of that definitional check.

### Generic closing sequences — rejected (2026-11-04)

- **Pattern:** `congr 1` / `push_cast` / `ring` (14 sites), `cases h` /
  `cases h'` / `rfl` and `cases ha` / `cases hb` / `rfl` for cast lemmas
  (19 sites in the former TNLean party-circuit modules), and `ext x` / `constructor` /
  `· intro hx` for set extensionality (10 sites).
- **Reason:** each is a sequence of standard tactics with no shared
  mathematical content and no shorter spelling (`subst h h'; rfl` saves one
  line per cast lemma and is left to the owners of those files). Recorded so
  the scanner's top entries are not re-proposed; `apply Units.ext` /
  `push_cast` / `field_simp` is already in the rejected section.

### Robustness assembly with a sharper cutoff — resolved (2026-10-30)

- **Seen:** `MPS/AreaLaw/ChebyshevAGSP/Robustness.lean`, `NormalizedChain.lean`,
  and `InverseGapRobustness.lean`.
- **Pattern:** Build the minimizing ground vector from an absolute excited-energy
  lower bound, combine its gap with the projected residual and tail, and reconstruct
  the normalized regional sums from the two removed bonds.
- **Decision:** Extracted as cutoff-independent lemmas shared by both cutoffs:
  `exists_ground_gap_twoSidedEnergyTruncation_of_orthogonal` (ground vector and gap
  from the orthogonal energy bound), `robust_ground_of_clipped_ground_gap` (residual,
  tail and phase assembly, with the now public `phase_budget_le_exp`), and
  `exists_normalizedCutBlock_eq_sum_sub` (regional sums away from the removed bonds).
  A fourth extraction, `posSemidef_gap_twoSidedEnergyTruncation_of_quadratic` in
  `NormalizedChain.lean`, turns the quadratic gap bound of the clipping into the
  operator gap inequality for both normalized-chain theorems.
  Each cutoff proves only its orthogonal energy bound. No new tactic is needed.

### Exponential weights and energy windows — candidate (2026-10-29)

- **Seen:** `MPS/AreaLaw/Spectral/SpectralTail.lean` and `GroundStateTail.lean`.
- **Pattern:** Express a Hermitian exponential and a threshold projection in
  the scalar functional calculus, multiply there, and apply `norm_cfc_le`.
- **Abstraction:** `Matrix.IsHermitian.exp_real_smul_eq_cfc` centralizes the
  exponential identity. The high and low weight bounds are public lemmas in
  `SpectralTail.lean`; a future ownership cleanup can move these general
  matrix results to QICLean together with the adjacent weighted-projection API.
- **Decision:** Mathematical lemmas suffice; no new tactic is needed.

### Supplied standard-form source-cut contraction — candidate (2026-10-29)

- **Pattern:** Preserve the external physical coordinates by Kronecker deltas,
  expand the actual supplied half factors, and reorder the virtual sum once
  to identify the middle gate.
- **Seen:** `MPS/MPU/StandardForm/TwoSiteStandardFormSourceCuts.lean`, both cut
  factorizations and both four-spin gate contractions.
- **Abstraction:** Existing `Finset.sum_congr₂` handles consecutive two-index
  descents. The cut identities are the reusable mathematical statements;
  no new contraction tactic or parallel source-factor predicate is needed.

### Exact small indices from their defining sets — candidate (2026-10-29)

- **Pattern:** supply a small admissible positive length, use `Nat.sInf_mem`
  and `Nat.sInf_le`, exclude any smaller positive length, and finish the
  resulting natural-number bounds with `omega`.
- **Seen:** the two concrete index computations `threePauliTensor_qIndex`
  and `threePauliTensor_iIndex` in `MPS/Examples/Wielandt/PauliWielandt.lean`.
- **Abstraction:** the existing Mathlib infimum lemmas already do the main
  work. Two occurrences in one file are below the promotion threshold;
  no specialized index tactic is introduced.

### Completing an orthonormal family by its cardinality — candidate (2026-10-29)

- **Pattern:** Use
  `hv.linearIndependent.span_eq_top_of_card_eq_finrank' hcard`, then
  `OrthonormalBasis.mk hv hspan.ge`, to turn an orthonormal family with as
  many vectors as the dimension into an orthonormal basis.
- **Seen:** The zero and successor cases of
  `LinearIsometry.exists_paired_orthonormalBasis` in
  `QICLean/Analysis/Isometry/OrthogonalComplexStructure.lean`.
- **Abstraction:** Mathlib already supplies both mathematical steps. Two
  occurrences in one proof do not justify a local wrapper or tactic.

### Identifying the ground energy of two physical conditions — candidate (2026-10-29)

- **Seen:** `ExactMPSGroundPath.exists_uniform_ground_line_spectral_gap` in
  `MPS/Symmetry/GroundPath/ExactGroundPathGaussianFilter.lean`.
- **Pattern:** The path gap and the exact ground-line condition each supply
  a least spectral value. Apply each minimality inequality to the other's
  spectral witness, identify the energies by antisymmetry, and transport the
  spectral dichotomy to the actual MPS ground line.
- **Decision:** One use. Keep the mathematical extraction in its named helper
  and reuse the existing Gaussian spectral and ground-space estimates; no
  new tactic or duplicate eigenbasis calculation is needed.

### Constancy of a continuous trace sign — candidate (2026-10-29)

- **Pattern:** A finite matrix-product/trace expression is continuous by
  `Continuous.matrix_mul`, `Continuous.matrix_kronecker` and
  `Continuous.matrix_trace`. A local identity puts its value in `{1,-1}`.
- **Seen:** `MPS/MPU/Symmetry/TimeReversal/TimeReversalSignIntrinsic.lean`,
  `intrinsicTimeReversalSign_eq_on_path`.
- **Abstraction:** Mathlib's
  `IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq` already supplies the
  topological step; no local connectedness tactic or parallel sign predicate
  is needed.

### Diagonal hard-truncation spectral values — candidate (2026-10-29)

- **Pattern:** Rewrite a diagonal Hamiltonian's functional calculus with
  `Matrix.cfc_diagonal` and finite-range continuity, then evaluate a basis state.
- **Seen:** `MPS/Examples/HardTruncationCutoff.lean`, for the actual clipping
  and its closed low-energy projection.
- **Decision:** Existing diagonal functional calculus suffices; no new tactic.

### Canonical matrix spectral spans after reindexing — candidate (2026-10-29)

- **Pattern:** Unfold the actual matrix eigenbasis/eigenvalue reindexing and
  identify the two spectral spans by image inclusions.
- **Seen:** `MPS/AreaLaw/LowEnergyAlgorithm/Truncation/HardTruncationResidual.lean`, both actual residuals.
- **Decision:** One private span identity suffices. The basis application uses
  `OrthonormalBasis.reindex_apply`, rather than definitional equality.

### Recovering letters by an identity contraction — candidate (2026-10-29)

- **Seen:** `isInjective_uncleTensor_of_isInjective_perturbation` in
  `MPS/ParentHamiltonian/Uncle/UncleInjectivity.lean`.
- **Pattern:** Full one-site span gives coefficients of the identity.
  Contracting one physical leg of a bilinear two-site family with those
  coefficients recovers every one-site letter, so its span is full too.
- **Reuse:** `Submodule.mem_span_range_iff_exists_fun`, block-matrix
  injectivity and finite-sum scalar/matrix distribution.
- **Decision:** Use one full-identity contraction in place of four separate
  block witnesses. One occurrence does not justify a new tactic.

### Counting nearest-neighbour bonds that meet a region — candidate (2026-10-28)

- **Pattern:** Bound the number of nearest-neighbour bonds meeting a finite
  region by a linear function of its size: either inject the meeting bonds
  into a `Fin` of the target size by an affine relabelling such as
  `i ↦ i.val + m + 1 - c`, closing the bounds with `omega`, or cover them by
  the region and its translate and count the union.
- **Seen:** QICLean's `ManyBody/Hamiltonian/Chain/ConsecutiveRegions.lean`
  (`card_bonds_meeting_enlarged_interval_le`, clipped linear intervals, by
  injection). The ring occurrence (`card_bonds_meeting_le` in
  `MPS/Preparation/FiniteRingLiebRobinson.lean`) was deleted when that estimate
  became a corollary of the graph bound; its site budget now counts the two bonds
  `{x, x - 1}` meeting one site. One occurrence remains.
- **Abstraction:** A shared counting lemma in `TNLean/Algebra/`, stated for
  bonds `{i, i + 1}` meeting a finite set of sites, from which both the
  clipped-interval and ring bounds follow.

### Local residuals over a bounded assignment fibre — candidate (2026-10-28)

- **Pattern:** centre a sum of local terms, pass its action through the sum,
  and apply a norm bound using the actual number of assigned centres.
- **Seen:** `residual_periodicCoarseOperator_le` in `PeriodicCoarsening.lean`
  and `residual_roundedPeriodicOperator_le` in `RoundedPeriodicCoarsening.lean`.
- **Abstraction:** both already use `norm_edgePartition_le_of_fibre_card`;
  a residual version of that lemma would remove the remaining three-line
  passage through centring and matrix action if another application appears.

### Simultaneous regional factors for a supported family — candidate (2026-10-26)

- **Pattern:** Classify each ordinary term into one of three regions, choose
  its single-region factor and put zero in the other two positions. Choose
  these factors over the entire finite family at once.
- **Seen:** `MPS/AreaLaw/Chain/TwoCutEdgeSupports.lean` and
  `MPS/AreaLaw/Chain/TwoCutEdgeSupports.lean`.
- **Abstraction:** Both use the existing three regional factor lemmas and
  `choose`; there are two occurrences across two files.

### Uniform bounds for sums of natural powers — candidate (2026-10-26)

- **Pattern:** Bound each term by monotonicity of natural powers, then replace
  a finite sum by its cardinality times that bound.
- **Seen:** The degree sum in `QICLean/Algebra/Combinatorics/TwoWindowCounts.lean` and the iterated
  sum in `QICLean/Algebra/Combinatorics/TwoWindowCounts.lean`.
- **Abstraction:** Existing Mathlib lemmas suffice: `Finset.sum_le_sum`,
  `Finset.sum_le_card_nsmul` and `Finset.sum_const`.

### Splitting a chain Hamiltonian at one cut — candidate (2026-10-26)

- **Pattern:** From `H = HL + HR + K` with `HL` supported on `interval L 0 k`, `HR` on its
  complement, `0 ≤ K ≤ 1` and `H ≥ E₀`, pass to the cut coordinates with
  `cutOperator_eq_kronecker_one` and `cutOperator_eq_one_kronecker`, obtain
  `cutOperator H = A ⊗ₖ 1 + 1 ⊗ₖ A' + cutOperator K`, and derive
  `(1 - cutOperator K).PosSemidef` and `(cutOperator H - E₀ • 1).PosSemidef`.
- **Seen:** 2 occurrences in 2 files: `TNLean/MPS/AreaLaw/GroundStateAlgorithm/BoundaryState/ConstantRankCut.lean`
  (energy of a trimmed low-energy state) and `TNLean/MPS/AreaLaw/GroundStateAlgorithm/BoundaryState/Gluing.lean`
  (`exists_trimmed_witness_chain`).
- **Abstraction:** proposed: one lemma returning `A`, `A'`, the Kronecker split and the two
  positivity facts from the six hypotheses on `H`, `HL`, `HR`, `K` and `E₀`.

### Restricting an operator Schmidt decomposition at a fixed configuration — candidate (2026-10-23)

- **Pattern:** Choose an actual configuration in the region carrying an identity
  factor, restrict each outside matrix to that configuration, and retain the
  same number of summands in the operator Schmidt decomposition.
- **Seen:** The left-factor argument
  `ManyBody.exists_reindex_threeCutEquiv_eq_kronecker_one_operatorSchmidtRank_le` and the
  right-factor argument
  `ManyBody.exists_reindex_threeCutEquiv_eq_reindex_one_kronecker_operatorSchmidtRank_le`,
  both now in `QICLean/ManyBody/Sites/ThreeRegion/Cut.lean` (first written in PR #10029).
- **Abstraction (proposed):** If another use appears, first seek a lemma saying
  that restriction by separate coordinate maps preserves a product
  decomposition with the same number of summands.

### Regional expectation compared with a supported approximant — candidate (2026-10-21)

- **Pattern:** For a contractive regional expectation fixing a supported approximant, rewrite the projection error as the difference between the approximation error and its expectation.
- **Defined in:** QICLean `ManyBody/Sites/RegionExpectation.lean`, `ManyBody.norm_sub_regionExpectation_le_two_mul_norm_sub`.
- **Use when:** An approximant is supported on the output region; the error of projecting the original operator is at most twice its distance to that approximant.

### Infimum over walk lengths under graph maps — candidate (2026-10-21)

- **Pattern:** Rewrite extended graph distance as the infimum of walk lengths,
  bound the target distance for each source walk, and preserve the length by
  mapping or inducing that walk.
- **Seen:** `SimpleGraph.Hom.edist_le` maps walks;
  `SimpleGraph.ConnectedComponent.edist_eq` induces ambient walks after
  proving that their support remains in the component. The isomorphism
  theorem applies the homomorphism result twice.
- **Existing lemmas:** Public Mathlib `Walk.length_map`, `Walk.induce` and
  `Walk.map_induce` supply the transport identities. The component argument
  uses public `Walk.takeUntil`, not the private component-walk construction.

### Symmetric two-index uniqueness reduced to `i < j` — candidate (2026-10-21)

- **Pattern:**

  ```lean
  wlog hij : i < j generalizing i j
  · rcases lt_trichotomy i j with h | h | h
    · exact this hi hj h
    · exact h
    · exact (this hj hi h).symm
  ```

- **Seen:** 2 occurrences
  (`QICLean/ManyBody/Sites/Lattice/NestedPatches.lean:141`,
  `QICLean/ManyBody/Sites/Lattice/RangeNestedPatches.lean:179`).
- **Abstraction:** proposed lemma deriving `i = j` for a symmetric property of
  two indices in a linear order from the case `i < j` leading to a
  contradiction.

### Localization error of the regional reset filter — candidate (2026-10-21)

- **Pattern:** After the supported Gaussian buffer step, bound
  `‖W‖ * C * n * (1 + c * J * n * T) * exp (v * T - ⌈K (1 + b + log L)⌉ / 2)` by
  `C * (1 + c * J) * (1 + T₀) * exp (-10 b) * L ^ (-r)`, with `T = T₀ (1 + b + log L)`
  and `n ≤ L ^ 2` sites. First prove the polynomial bound
  `n * (1 + c * J * n * T) ≤ (1 + c * J) * L ^ 4 * (1 + T)` from `n ≤ L ^ 4 (1 + T)` and
  `c J n² T ≤ c J L ^ 4 (1 + T)`, combined by `add_le_add`. Then rearrange with `gcongr`
  and close with `GaussianFilter.localization_error_bound_of_parameter_constant`.
- **Seen:** 2 occurrences, `ManyBody.SquareInteraction.reset_localized_filter` in
  `PEPS/Approximation/DoubledHamiltonian/ResetUnitary.lean` (lines 167–221) and
  `ManyBody.PlaneInteraction.reset_localized_filter` in `PEPS/Approximation/DoubledHamiltonian/RangeResetUnitary.lean`
  (lines 144–201). The two blocks differ only in the constants: `L ^ 2` versus `Λ.card`, the
  crossing coefficient `8` versus `swapBoundaryCoefficient R`, the prefactor
  `squareLocalizationPrefactor` versus `2 * graphBallLocalizationPrefactor R`, and the
  velocity `squareLocalizationVelocity J` versus `graphBallLocalizationVelocity R (2 * J)`.
- **Abstraction:** a lemma over the site bound `n ≤ L ^ 2`, the prefactor `C > 0`, the
  crossing coefficient `c ≥ 0`, the velocity `v` and the radius `K` with
  `v T₀ + 15 + r ≤ K / 2`, which concludes the displayed inequality for any `‖W‖ ≤ 1`.

### Restricting a cut configuration after adjoining one site — candidate (2026-10-18)

- **Pattern:** The inverse of the one-site extension restricts the configuration
  and evaluates it at the cut site. Its inverse proof separates sites before
  the cut from the cut site and reduces subtype equality to the site value.
- **Seen:** the former `prefixStepEquiv` and `suffixStepEquiv` of
  `MPS/Tensor/OpenMPS/CutMatrixGrowth.lean`, copies of the extension
  equivalences of `MPS/CanonicalForm/OpenBoundary/OBCCanonicalConfigurations.lean`.
- **Abstraction:** Since both files index cut configurations by the blocks of
  `ManyBody.cutMatrix (interval N 0 k)`, the copies were deleted; both files use
  `MPSPreparation.extendCutPrefixEquiv` and `MPSPreparation.extendCutSuffixEquiv`
  (`MPS/Tensor/VaryingBond/MinimalCutRepresentationCuts.lean`). The coefficient
  identity is `MPSPreparation.cutMatrix_adjacent`.

### Interval membership in the chain stage assignments — candidate (2026-10-18)

- **Pattern:** Unfold a half-open target interval, separate its endpoint
  inequalities, and use the stage index bounds to establish membership or
  nonmembership before simplifying an owner change.
- **Seen:** Three occurrences each of remainder-target nonmembership,
  block-target membership and right-band-target nonmembership within
  `MPS/AreaLaw/SweepPreparation/ProtocolSweepFrames.lean`.
- **Abstraction:** The existing `mem_interval` and arithmetic tactics suffice
  for these occurrences in one file. If the same inequalities recur in another
  file, first state the common interval assertion as a lemma.

### Two-sheet lists in a finite family of bounded changes — candidate (2026-10-18)

- **Pattern:** Before selecting a circuit witness, identify the two consecutive
  sheet lists with the explicit lists used by the one-sheet or two-sheet lift.
  Associate list append while the statement is still a bounded-change
  proposition; then extract the circuit and its bounds.
- **Seen:** The eight cases of
  `OneBand.circuits_of_primitive_information` in
  `TNLean/MPS/AreaLaw/SweepPreparation/BandDissolution.lean`. Five cases use the same
  two-element-list and spectator-list identification in the source and target.
- **Existing tools:** The construction uses `hasSourceBoundedChange_liftOne`,
  `isBoundedChange_liftTwo` and their source-count lemmas. The repeated part is
  only the equality of the ordered sheet lists.
- **Next step:** This occurs in one file. If a second file needs the same list
  identification, first seek a list lemma or a bounded-change transport lemma;
  no new tactic is warranted by the present occurrences alone.

### Nonnegativity of a natural remainder in arithmetic bounds — candidate (2026-10-18)

- **Pattern:** Supply `Nat.zero_le (L % (20 * w))` explicitly to `nlinarith`
  after Euclidean division of the chain length.
- **Seen:** Two occurrences in `MPS/AreaLaw/SweepPreparation/ProtocolSweepGeometry.lean`, in
  `stage_right_margin` and `twenty_mul_stageCount_le`.
- **Abstraction:** The existing `Nat.zero_le` supplies the needed fact. The
  two occurrences in one file do not justify another arithmetic lemma or tactic.

### Product-basis vectors under a map of labels — candidate (2026-10-18)

- **Pattern:** Induct on a register list to identify the product basis vector
  of its mapped labels with the vector whose owner and configuration are
  precomposed with the same map.
- **Seen:** Two occurrences across two files: `auxiliaryRaw_siteVec` in
  `MPS/AreaLaw/SweepPreparation/ProtocolTerminalWord.lean` and `mapped_siteVec_heq` in
  `MPS/AreaLaw/SweepPreparation/ProtocolTerminalReference.lean`.
- **Abstraction:** Both use the existing canonical tensor transport lemmas.
  A third occurrence should prompt a shared label-map identity; the present
  two do not require another abstraction.

### Partial trace under a change of discarded basis — candidate (2026-10-18)

- **Pattern:** Apply `OrthonormalBasis.tensorProduct_rankOne_basisChange` with
  the physical basis fixed, then
  `Matrix.partialTraceRight_kronecker_conj_of_right_isometry`; the matrix of
  the physical basis against itself is the identity.
- **Seen:** Two occurrences across two files: the private
  `partialTrace_mixed_private_basis_eq` in
  `TNLean/PEPS/Approximation/SelectedPhysicalPrivateTrace.lean` and
  `physicalDensity_terminalRegrouping` in
  `TNLean/MPS/AreaLaw/SweepPreparation/ProtocolTerminalCoordinates.lean`.
- **Abstraction:** The existing basis-change and partial-trace theorems suffice
  for the present proofs. If a third occurrence needs this exact identity,
  consider moving the mixed-vector statement to QICLean.

### Coordinate distance from an ordered diameter bound — candidate (2026-10-18)

- **Pattern:** Use the two ordered support inequalities, unfold `Nat.dist`,
  and apply `omega` to bound the coordinate distance by the interaction range.
- **Seen:** Two former occurrences: `chainSupport_edist_le` in the chain
  Lieb–Robinson module (now `ManyBody.ChainSupport.edist_le` in QICLean) and the common
  local margin argument of the former chain reset-support lemma (deleted in favour of
  `ManyBody.reset_graphNeighborhood_disjoint_cores`).
- **Abstraction:** Consider a minimal `IsChainSupport` distance lemma if a
  third consumer appears; no additional helper is needed at two occurrences.

### Conjugation by a contraction — candidate (2026-10-18)

- **Pattern:** Bound `‖F * A * Fᴴ‖` by a supplied bound on `‖A‖`, using
  `‖F‖ ≤ 1`, invariance of the norm under adjoints, and two applications
  of `norm_mul_le_of_le`.
- **Seen:** Two chain occurrences: the common local argument in
  `ManyBody.ChainInteraction.partialSwap_term_difference_spec` in
  QICLean's `ManyBody/Hamiltonian/Chain/Doubled.lean`, and the norm field of the former chain
  swapped doubled interaction, now `ManyBody.Interaction.norm_conj_term`.
- **Abstraction:** The standard norm inequalities suffice for these short
  arguments; no new lemma or tactic is introduced at two occurrences.

### Coordinate changes in projector-gap inequalities — candidate (2026-10-18)

- **Pattern:** Transport a positive projector defect along a configuration
  bijection and identify the resulting scalar, identity and rank-one terms.
- **Seen:** The complete gap passages in the companion library's
  `Analysis/GaussianFilter/PhysicalBuffer.lean`, `PEPS/Approximation/DoubledHamiltonian/ResetUnitary.lean`
  and QICLean's `ManyBody/Hamiltonian/Chain/Doubled.lean`. A related rank-one-only
  calculation occurs in the companion `Analysis/ReplicaLowDefectCoordinateCovariance.lean`.
- **Abstraction:** Positivity already uses `Matrix.PosSemidef.submatrix`.
  The new chain proof uses the existing `Matrix.reindexAlgEquiv` with
  `map_sub`, `map_smul` and `map_one` to normalize the whole defect; the
  rank-one equality is then definitional. It adds no entrywise proof.

### Reversal of time in graph commutator bounds — candidate (2026-10-17)

- **Pattern:** Apply the nonnegative-time estimate to the interaction family
  `fun k ↦ -h k` at time `-t`, preserve its Hermiticity, supports and norm
  budget, and rewrite with `heisenbergCommutatorNorm_neg_time`.
- **Seen:** Three occurrences in `QICLean/ManyBody/Dynamics/GraphPropagation.lean`,
  in `heisenbergCommutatorNorm_le_graphDistance`,
  `heisenbergCommutatorNorm_le_graphDistance_finset`,
  and `heisenbergCommutatorNorm_le_graphDistance_finsets_numeric`
  (updated 2026-10-25).
- **Abstraction:** The common identity is already the public lemma
  `heisenbergCommutatorNorm_neg_time`. The applications have different
  support and distance hypotheses. Keep their short arguments explicit until
  the pattern occurs in a second file and meets the promotion threshold.

### Dyadic padding bounds — candidate (2026-10-16)

- **Pattern:** Combine the lower and strict upper bounds for
  `2 ^ Nat.clog 2 L`, then add positivity of the ceiling logarithm.
- **Seen:** The bounds in `DyadicAnchors.lean` and their former rederivation
  in `le_two_pow_clog_lt` in `DyadicProtocolConsequences.lean`.
- **Abstraction:** Reuse the existing `le_paddedSide` and
  `paddedSide_lt_two_mul`; the public wrapper packages them with `Nat.clog_pos`.

### Treated-to-level frame equality — candidate (2026-10-16)

- **Pattern:** Identify true vertices from a guide equality, replace the constant
  treated radius by the equal level radius, transport disjointness, and change
  the reference party map.
- **Seen:** Two occurrences in one file: `levelFrame_eq_treatedFrame_guide`
  and `treatedFrame_completedGuide_eq_levelFrame` in
  `TNLean/PEPS/Approximation/Protocol/DyadicTreatedFrameBoundary.lean`.
- **Abstraction:** The private `treatedFrame_eq_levelFrame_of_guide_eq` takes
  the baseline stage, the output stage, an unmodified guide and its equality
  with the level guide. Both endpoint proofs use it.

### Treated birth and death preamble — candidate (2026-10-16)

- **Pattern:** the common setup of a treated birth or death: the scales `n`, `t`, the block
  corner, two `treatedFrame_spec` extractions, `homogenize_endpointBlocks`, the readings and
  true-vertex sets, and `BandOperation.treated_frame_facts`.
- **Seen:** `bandBirth_hasFrameChange` and `bandDeath_hasFrameChange`
  (`Approximation/DyadicBandStepChanges.lean`). In parent PR #9505 both proofs use
  `guideFrame_eq_changeOwner`, with separate owner case splits; this PR (#9507)
  consolidates those splits through `guideFrame_eq_changeOwner_of_ne`.
- **Abstraction:** a lemma returning the readings, vertex sets and facts for the surrounding
  guide, if a third occurrence appears.

### Supported terms in rectangle coordinates — candidate (2026-10-15)

- **Pattern:** Transport membership in a supported-operator algebra through the
  site bijection, replace the resulting embedding by matrix reindexing, and
  identify the image support.
- **Seen:** 2 occurrences: `ManyBody.SquareInteraction.exists_nearestNeighbor_terms` in
  `PEPS/Approximation/GroundState/SquareInteractionTerms.lean` and
  `ManyBody.SquareInteraction.exists_swapped_doubled_planeInteraction` in
  `PEPS/Approximation/DoubledHamiltonian/SwappedSquareHamiltonian.lean`; the range-one
  interaction itself is QICLean's `ManyBody.RectangleInteraction.toPlaneInteraction`.
- **Abstraction:** QICLean's `ManyBody.reindex_siteConfigurationEquiv_mem_supportedOperators`
  with `ManyBody.mem_rectangleSupport_iff` performs the transport, and
  `ManyBody.siteConfigurationEquiv_rectangleSiteEquiv` rewrites the
  configuration bijection to `rectangleConfigurationEquiv`. At a third
  occurrence, consider a lemma giving the reindexed term's supported-operator
  membership directly.

### Logarithmic norm derivatives from squared norms — candidate (2026-10-15)

- **Pattern:** Differentiate the squared norm, compose with the real logarithm,
  and divide by two. Positivity of the original norm justifies the logarithm
  and the subsequent cancellation.
- **Seen:** `hasDerivAt_log_regularizedPatchObjective_exp_neg_of_outer_commute`
  and `exists_hasDerivAt_log_regularizedPatchObjective_exp_neg_uniform`, both in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchRadiusDerivative.lean`.
- **Abstraction:** Both occurrences reuse `HasDerivAt.norm_sq` and `HasDerivAt.log`.
  A third occurrence in another file would justify a helper for the logarithmic
  norm derivative of a nonzero complex vector-valued function.
- **Caveat:** The real inner-product instance must agree with the complex space;
  positivity concerns the same vector whose derivative is being computed.

### Applying an ordered matrix derivative to a vector — candidate (2026-10-15)

- **Pattern:** Compose `Matrix.toEuclideanLin.toLinearMap` with
  `LinearMap.applyₗ Ω` to apply a varying matrix to a fixed Euclidean vector.
  Restrict scalars to ℝ and use finite-dimensional continuity for real derivatives.
- **Seen:** `regularizedPatchInsertion` in `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchCoordinate.lean`
  and `hasDerivAt_regularizedPatchOutput_exp_neg` in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchRadiusDerivative.lean`.
- **Abstraction:** The proofs use the existing linear maps. A third occurrence
  would justify a public continuous linear evaluation map for matrices.
- **Caveat:** The ordered product remains noncommutative; differentiate the
  continuous multilinear product and retain the original insertion indices.

### Uniform expansion bounds under chronological composition — candidate (2026-10-15)

- **Pattern:** Induct on the number of stages while retaining the bounds on
  every stage below the current index; composition forms the conjunction of
  the preceding bound and the last stage's bound.
- **Seen:** `OriginalCircuit.isExpansionBounded_sequence` and
  `OriginalCircuit.isMonomialBounded_sequence`, now in
  `QICLean/Circuit/Party/Original/Sequence.lean`, and formerly
  `DyadicProtocol.isExpansionBounded_chain` and
  `DyadicProtocol.isMonomialBounded_chain` in
  `TNLean/PEPS/Approximation/Protocol/DyadicProtocolCompression.lean`: four
  occurrences across two files.
- **Abstraction:** Done (2026-10-16). `DyadicProtocol.chain` is now
  `OriginalCircuit.sequence` of the protocol changes, and every `chain` lemma
  (counts, participation, participating sets, expansion and monomial bounds)
  is a one-line instance of the generic `sequence` lemma. Two inductions
  remain, both in QICLean's `Original/Sequence.lean`. Before adding a further
  gate-expansion property, derive it from a common occurrence-wise
  description, as in the existing retained-memory entry.

### Removing subsingleton physical coordinates — candidate (2026-10-14)

- **Pattern:** In an inverse configuration map, prove equality at noncarrying
  coordinates using the subsingleton property of their physical alphabet.
- **Seen:** The exterior coordinate in `SelectedPhysicalConfigurations.lean`
  and the complement of the designated owners in `PartyPhysicalCoordinates.lean`,
  both under `PEPS/Approximation/`.
- **Abstraction:** Both cases already use Mathlib's `Subsingleton.elim`.
  The one-owner-per-site theorem supplies the complete dependent configuration
  bijection; no additional closing tactic is proposed.

### Upper endpoint of a scanner band — candidate (2026-10-12)

- **Pattern:** Use the band index bound, the offset bound and $8Km\le L$
  to place $8gm+5m+r$ below the original collar depth.
- **Seen:** The endpoint estimate in
  `Scan/StatusContainment.mem_truncationSet_of_not_far` and the two front
  estimates in `Scan/FrontThresholds.front_comparison_thresholds_le`.
- **Abstraction:** `CollarScan.upper_le` in `Scan/SideSeparation.lean` states
  the shared endpoint bound, used by the front estimates. The containment proof
  precedes it in the import order and keeps its own copy.

### Unselected source positions keep their vectors — candidate (2026-10-12)

- **Pattern:** A selected position that fails the affected-endpoint condition
  is excluded from the selected set, so the selected source vectors return the
  original vector there.
- **Seen:** `selectedSourceVectors_exterior` in `SourceCorrectedContraction.lean`
  and the inline exterior-source step of `eval_selectedSourceVectors_eq_sum` in
  `SourceCircuitSubstitution.lean`, under `PEPS/Approximation` (two occurrences).
- **Abstraction:** At a third occurrence, export the exterior statement from the
  lower module and use it in both proofs. No tactic is needed.

### Pair swaps in regional coordinates — candidate (2026-10-09)

- **Pattern:** derive regional tensor factors from membership in the supported-operator
  space, rewrite multiplication by the pair-swap permutation matrix, and compare
  entries using the region/complement split.
- **Seen:** QICLean's `ManyBody.pairSwapOp_mul_mul_conjTranspose_of_disjoint` and
  `ManyBody.pairSwapOp_mul_kronecker`, which replaced the two lemmas of TNLean's former
  regional swap module.
- **Abstraction:** the support decompositions, permutation-matrix products, and split
  coordinates are already public lemmas. These are the two distinct cases, for
  operators supported outside and inside the swapped region.

### Connected retained pieces along a fan run — candidate (2026-10-09)

- **Pattern:** use the connected-component paths to join connected retained
  triangles whose intersections survive along each retained edge.
- **Seen:** the open-radius and closed-half-radius run proofs in
  `TNLean/PEPS/AreaLaw/BirthRegions/Fans/FanRunConnectedness.lean`.
- **Abstraction:** both already use Mathlib's
  `IsConnected.iUnion_of_reflTransGen`; a further application would justify
  naming the common passage from component paths to intersection chains.

### Unique radial through a noncentral fan point — candidate (2026-10-09)

- **Pattern:** turn membership in two center-to-endpoint segments into a common
  directed ray, then apply `cellFanEnd_sameRay_iff` to identify their slots.
- **Seen:** two uses across `CellFanRadialIncidence.lean` and
  `FanInactiveSeams.lean`, in `TNLean/PEPS/AreaLaw/Geometry/`.
- **Abstraction:** a common noncentral radial-incidence lemma if a third use
  appears; the shared endpoint-ray theorem already contains the geometry.

### Nonnegative barycentric coordinates — candidate (2026-10-08)

- **Pattern:** Obtain nonnegativity of every barycentric coordinate from
  membership in the convex hull of an affine basis.
- **Seen:** Four local coordinate arguments in
  `PEPS/AreaLaw/BirthRegions/Fans/FanRadialConvexity.lean`.
- **Current reuse:** All four use Mathlib's
  `AffineBasis.convexHull_eq_nonneg_coord` directly. They lie in one file,
  so the two-file promotion threshold has not been reached.
- **Promotion trigger:** If this extraction recurs in another module, prefer
  a lemma giving the coordinate inequalities over a new tactic.

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
- **Seen:** Two occurrences in `PEPS/AreaLaw/RegionalStates/Regions/VertexBoundaryCorollaries.lean`,
  for the inner boundary and the set of both endpoints.
- **Abstraction:** Both proofs already use Mathlib's cast and multiplication
  lemmas. A third occurrence in another module should extract the common
  inequality argument into a lemma, with the comparison factor explicit.

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
  `QICLean/Representation/Character/UnitaryAlgebra.lean`.
- **Pattern:** use `Algebra.adjoin_induction` on the generators together with
  their adjoints; replace an adjoint generator by the inverse group element.
- **Current reuse:** Mathlib supplies the algebra induction, while the common
  inverse-adjoint identity is proved once in the same module. The product step
  uses invariance in different ways for vectors and intertwiners.
- **Promotion trigger:** a third use in another file should first seek a
  common generated-algebra statement. Two distinct inductions in one file do
  not justify a new tactic.

### Orthonormal rows as subrepresentation bases — candidate (2026-10-02)

- **Sites:** `QICLean/Representation/Character/UnitaryAlgebra.lean` and
  `PEPS/Injectivity/SemiRegular/RegularFourier.lean`.
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

### adjoints of left polar identities — candidate (2026-10-02)

- **Pattern:** Apply `congrArg Matrix.conjTranspose` to a matrix product
  identity, then simplify `conjTranspose_mul` and the Hermitian factors.
- **Seen:** four instances in `ParentHamiltonian/LeftPolar.lean`: the
  support factorization used for positivity, the support action on the
  partial isometry, and the two identities identifying the physical range.
- **Abstraction:** The existing `Matrix.conjTranspose_mul` supplies the
  algebraic operation. A more specific reusable lemma would need to remove
  repeated Hermitian-factor arguments in a second module.

### Mass of a cut beyond its leading eigenvalues — candidate
- **Pattern:**
  ```lean
  1 - (Entropy.regionState_isHermitian (n := fun _ : Fin L ↦ q) (interval L 0 k)
    ψ).kyFanNorm n
  ```
- **Seen:** 5 occurrences (2026-10-22), in statements and proofs of
  `TNLean/MPS/Tensor/VaryingBond/SequentialTruncation.lean` and
  `TNLean/MPS/AreaLaw/ProjectorFactorization/SchmidtTail/SchmidtTailMPS.lean`.
- **Abstraction:** proposed definition of the mass of the left marginal at the
  cut `k` beyond its `n` largest eigenvalues, with a lemma rewriting it as the
  sum of the trailing eigenvalues.

### Reflected sum over the internal cuts of a sequential truncation — candidate
- **Pattern:**
  ```lean
  rw [Finset.sum_Ico_eq_sum_range]
  conv_lhs => rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi ↦ ?_   -- or `Finset.sum_le_sum`
  have hi' : i < L - 1 := Finset.mem_range.mp hi
  rw [show L - 1 - (L - 1 - 1 - i) = 1 + i by omega, hmass]
  ```
- **Seen:** 2 occurrences (2026-10-22): `TNLean/MPS/Tensor/VaryingBond/SequentialTruncation.lean`,
  in `sequentialTruncation_prefix_rank_error` and
  `norm_sequentialTruncation_leadingEigenprojection_sub_sq_le`.
- **Abstraction:** proposed lemma rewriting `∑ i ∈ range (L - 1), f (L - 1 - i)` as
  `∑ k ∈ Ico 1 L, f k`, which matches the step order of `sequentialTruncation`.

### A maximal finite support fills its coordinate interval — candidate

The minimum-coordinate image argument occurs twice in `Hamiltonian.lean`, in
`IsChainSupport.card_le` and `IsChainSupport.exists_eq_interval_of_card_eq`. Both map
site labels injectively to natural coordinates and compare with the same closed
interval. The latter additionally uses equality of cardinalities to identify the
whole interval. These are two occurrences in one file, below the promotion threshold;
no additional helper is proposed.

### A marginal tail under an upper bound for its cut budget — candidate

- **Pattern:** apply the finite-family marginal tail theorem to a reduced state,
  then enlarge its denominator using an upper bound for the cut logarithmic budget
  and nonnegativity of the width.
- **Seen:** the general prefix-tail estimate and its consecutive-window version in
  `TNLean/MPS/AreaLaw/Approximation/MPSApproximation.lean`.
- **Abstraction:** the private theorem `surprisalTail_region_le_of_family_budget`
  performs the finite-family estimate and scalar comparison once. The two prefix
  estimates supply their respective interaction families and budget bounds.

### Continuity of an ordered regional filter product — candidate

- **Pattern:** Prove continuity of each identity-extended local matrix power,
  apply finite ordered-product continuity, and compose with evaluation on the
  fixed vector and the norm.
- **Seen:** `continuousOn_regularizedPatchObjective` in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchMinimum.lean` and the joint-continuity step in
  `continuous_regularizedPatchMinimum_exp_neg` in
  `PEPS/AreaLaw/RegionalStates/RegionalFilters/RegularizedPatchMinimum.lean`.
- **Abstraction:** Both proofs already use Mathlib's `continuousOn_list_prod`
  or `continuous_list_prod`. A third occurrence may justify a shared theorem
  for evaluation of a continuously varying ordered product.

### simplicity of a tensor with diagonal rank-one double-layer letters — candidate
- **Pattern:** `isMPUSimple_of_rankOne_diagonal` (`TNLean/MPS/MPU/Simple/SimpleRankOne.lean`,
  2026-10-06) proves simplicity from three scalar pairings; the shift's own simplicity proof
  (`rightShiftTensor_isMPUSimple`) has this form and could be replaced by it.

### boundary-weighted physical twists — candidate
- **Pattern:** expand the trace of an ordered product of linear combinations, then match
  each coefficient with the corresponding Kronecker-power matrix entry.
- **Seen:** the ket and bra twists, with and without a boundary, in
  `TNLean/MPS/CanonicalForm/SimpleMPO/Vectorized.lean` (four occurrences in one file, 2026-10-02).
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
  `TNLean/MPS/Preparation/Correlations/PhysicalObservableGauge.lean` (2026-10-02).
- **Reuse:** `MPSTensor.physicalObservableTransfer_congruence_of_gauge`
  proves the word-sum calculation once. The transfer-power identity follows
  from the existing `MPSTensor.physicalObservableTransfer_one`, and the
  connected contraction uses these equations with trace cyclicity.

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

### Exponential error converted to polynomial accuracy — candidate
- **Pattern:** bound the number of blocks by the chain length, compare the
  exponential rate using the logarithmic block-length threshold, and use
  `Real.exp_add`, `Real.exp_log`, and `Real.rpow_def_of_pos` to obtain
  the factor `N ^ (-η)`.
- **Seen:** private `mul_exp_le_polynomial` in
  `TNLean/MPS/Preparation/Normal/PolynomialAccuracy.lean` and private
  `polynomial_error_factor` in
  `TNLean/MPS/Preparation/Normal/AllLengthPolynomialAccuracy.lean` (2026-10-03).

### Ceiling block lengths and logarithmic circuit depth — candidate
- **Pattern:** apply `Nat.le_ceil` and `Nat.ceil_lt_add_one` to the
  prescribed block length, then absorb the additive one using
  `log N ≥ log 2` to bound circuit depth by a multiple of `log N`.
- **Seen:** the block-length choice in
  `TNLean/MPS/Preparation/Normal/LogDepthPreparation.lean` and private
  `polynomialBlockLength_bounds` in
  `TNLean/MPS/Preparation/Normal/AllLengthPolynomialAccuracy.lean` (2026-10-03).

### Finite group fibers in local tensor isometries — candidate
- **Pattern:** parameterize all preimages of a virtual label by one group
  coordinate, use that coordinate as the inverse in a finite-sum bijection,
  and evaluate the resulting weighted sum or fiber cardinality.
- **Seen:** the dual tensor's `siteMap_quantumDoubleDualTensor_apply_spins`
  argument in `TNLean/PEPS/Examples/QuantumDouble/QuantumDouble.lean` and the private
  `primalLabels_fiber_sum` argument in
  `TNLean/PEPS/Examples/ToricCode/ToricCodePrimal.lean` (2026-10-03).

### linearity of a recovered bond operation — candidate
- **Pattern:** apply injectivity of the boundary-insertion map, rewrite the
  virtual operations by their physical realizations, and use linearity of the
  physical operation and boundary insertion.
- **Seen:** two occurrences in
  `TNLean/PEPS/FundamentalTheorem/Torus/Window/CrossTensorAlgebra.lean`, in
  `staircaseCrossTensorVirtualOperation_add` and
  `staircaseCrossTensorVirtualOperation_smul` (2026-10-02).
- **Abstraction:** a linear recovery map from realized physical operations,
  if a third use in another module needs the same argument.

### One-site doubled-alphabet transport — candidate
- **Pattern:** identify the doubled alphabet of one-site MPO blocking with
  the original ket-bra alphabet, then transport the physical-trace contraction
  along the one-site equivalence.
- **Seen:** two occurrences of each identity across two files:
  `TNLean/MPS/CanonicalForm/SimpleMPO/Simple.lean:IsSimpleCanonicalForm.isSimple` and
  `TNLean/MPS/Examples/Dimer/TwistedDimerBondSimple.lean` (2026-10-02).
- **Abstraction:** the bond-factor proof uses private generic identities
  `blockTensor_one_doubled_eq_reindexPhysical` and
  `doubledPhysTraceTransfer_reindex_singleBlock`. At a third occurrence,
  move the equivalence and identities to the physical-blocking API and
  refactor the existing simplicity proof.

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

### semi-regularity through an injective intertwiner — candidate
- **Pattern:** compose each nonzero irreducible intertwiner with an injective
  intertwining map, then use injectivity to preserve nonvanishing.
- **Seen:** `IsSemiRegular.of_equiv` in
  `QICLean/Representation/Character/SemiRegular.lean` and `IsSemiRegular.tprod_of_mem_invariants`
  in `QICLean/Representation/Character/TensorProduct.lean` (2026-10-02). The latter
  proves injectivity of the fixed-factor tensor inclusion by a dual pairing.
- **Abstraction:** if another occurrence arises, a semi-regularity transport
  theorem for injective intertwining maps would include equivalences and
  invariant tensor inclusions in one statement.

### normalization from the physical boundary density trace — candidate
- **Pattern:** rewrite the squared norm of a physical bipartite boundary
  vector as the trace of its Schmidt coefficient matrix times its adjoint,
  identify the reduced density, and use its unit trace.
- **Seen:** the positive cut normalization in
  `PEPS/Injectivity/Boundary/RegularRegionEntropy.lean` and the superposition normalization in
  `PEPS/Injectivity/Boundary/RegularClosureSuperposition.lean` (2026-10-02).
- **Abstraction:** a physical-boundary norm lemma taking the two invariant
  Gram identities would remove the two identical reductions if another
  direct use appears.

### Gram products of vertically stacked matrices — candidate
- **Pattern:** reduce the Gram product of a matrix formed by `Matrix.fromRows`
  to the sum of the two block Gram products, using
  `Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose` and
  `Matrix.fromCols_mul_fromRows`.
- **Seen:** three proofs in `TNLean/MPS/MPU/Circuit/Gates/ProjectionPhaseIsometries.lean`:
  `projectionPrefixMap_isIsometry`, `projectionInteriorMap_isIsometry`, and
  `projectionSuffixMap_isIsometry` (2026-10-02).
- **Abstraction:** combine the two existing Mathlib identities into a helper
  lemma if a second file uses the same reduction.

### quadratic bounds for commuting periodic projections — candidate
- **Pattern:** convert matrix translates to symmetric linear projections,
  use nonnegative cross terms, and specialize the common quadratic-form
  bound with unit gap and zero overlap.
- **Seen:** `MPS/Symmetry/FixedPoint/BondProductParentHamiltonian.lean` and
  `MPS/Symmetry/GappedPath/PhysicalInteractionGap.lean` (2026-10-02).
- **Abstraction:** both already use
  `ProjectionGeometry.quadraticForm_sum_projections_of_ordered_rowSum`;
  the remaining periodic-translate conversion may be shared if another
  caller needs it.

### coordinate restriction at the two bond endpoints — candidate

- **Pattern:** expand a weighted matrix unit, select the occupied summand,
  and reduce its endpoint weight to the corresponding inverse square root.
- **Seen:** the two physical embedding identities in
  `MPS/Symmetry/FixedPoint/EmbeddedFixedPointTensor.lean`.
- **Abstraction:** a general weighted matrix-unit compression lemma if a
  third use appears in a second module.

### relabeling normalized source factors into a standard form — candidate
- **Pattern:** pull source factors back along intermediate-rank equivalences,
  use the supplied gate entry formulas, and rewrite both finite sums along
  those equivalences to inherit the open source-factor contraction.
- **Seen:** `shiftExampleU₂BlockedStandardForm` and
  `shiftExampleU₃BlockedStandardForm` in `Examples/ShiftStandardForms.lean`.

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
  witnesses in `TNLean/MPS/Examples/Shift/ShiftStandardForms.lean`. The direct
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
  `QICLean/Algebra/Cohomology/KleinCocycleCompleteness.lean` (2026-09-30).
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
  `TNLean/MPS/Examples/PVBS/WStateCanonicalBound.lean`.
- **Abstraction:** if another cut-rank application repeats this conversion,
  state a row-membership lemma taking the weighted W-state identity and the
  two cut lengths.

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
  `TNLean/MPS/CanonicalForm/FixedPointApproximation/ApproximationError.lean` and
  `exists_norm_mpvOverlap_sub_pow_le_of_norm_sub_blockSumPosLimit_le` in
  `TNLean/MPS/Preparation/BlockSum/OverlappingBlockOverlap.lean` (2026-10-01: there `T_∞ = t R` with
  `R` idempotent, through `norm_prod_range_sub_pow_le_of_forall_norm_pow_le`).

### off-diagonal constants chosen with a dummy diagonal value — candidate
- **Pattern:** `have hoff : ∀ j k, ∃ K, 0 ≤ K ∧ (j ≠ k → ∀ n, ‖f j k n‖ ≤ K * x ^ n)`,
  proved by `by_cases j = k` with `⟨0, le_rfl, …⟩` on the diagonal, then `choose`, and
  a split `∑ⱼ ∑ₖ = ∑ⱼ (diagonal + ∑_{k ∈ univ.erase j})` by `Finset.add_sum_erase`.
- **Seen:** two occurrences across two files (2026-09-30):
  `exists_norm_gram_blockTensor_blockSum_sub_le` in
  `TNLean/MPS/Preparation/BlockSum/OverlappingBlockGram.lean` and
  `exists_abs_norm_mpvState_blockSum_weight_sq_sub_le` in
  `TNLean/MPS/Preparation/BlockSum/OverlappingBlockOverlap.lean`.

### second-order trace bound for an element compressed by an idempotent — candidate
- **Pattern:** for `T` with `e T e = α e`, `e` idempotent of trace one, `‖T - e‖ ≤ δ` and
  `1 - α` (or `1 - ‖α‖`) at most a multiple of `δ²`: put `Z = α⁻¹ T - e`, prove `e Z e = 0`,
  `T = α (e + Z)` and `‖Z‖ ≤ c₄ δ`, bound the blocks of `Z` by `z = c₅ (c₄ δ) c₅` with
  `c₅ = ‖e‖ + ‖1 - e‖`, apply `IsIdempotentElem.norm_trace_add_pow_sub_le_of_le`, and absorb
  `α^M` through `one_add_mul_le_pow`, with constants `zc = c₅⁴ c₄²` and
  `E₀ = K (‖e‖ + 3 ‖1 - e‖)`.
- **Seen:** two occurrences across two files (2026-10-02):
  `exists_one_sub_norm_mpvOverlap_polarPosTensor_le_sq` in
  `TNLean/MPS/CanonicalForm/FixedPointApproximation/SecondOrderOverlap.lean` (complex `α`, conclusion on
  `1 - ‖tr T^M‖`) and `IsIdempotentElem.exists_norm_trace_pow_sub_one_le_sq` in
  `QICLean/Analysis/Norm/IdempotentTracePerturbation.lean` (real `α ≤ 1`, conclusion on
  `‖tr T^M - 1‖`).

### Adjoint reversal of an orthogonal-projector error — candidate
- **Pattern:** replace the norm of a projector product minus a self-adjoint
  projector by the norm of its adjoint, reverse the product, and reverse the
  sign of the difference.
- **Occurrences:** `norm_projector_defect_adjoint` in
  `TNLean/MPS/ParentHamiltonian/ProjectorDefect/BlockIntervalDefectDecay.lean` and
  `norm_projection_difference` in
  `TNLean/MPS/ParentHamiltonian/Gap/Filtration/WholeIncrementSpectatorTransport.lean`.
- **Count:** two occurrences across two files. The second also removes a
  nested projection using subspace containment. If another use appears,
  separate the common adjoint identity into a submodule helper theorem.

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

### Wielandt block-injectivity length below the uniform square bound — candidate
- **Pattern:**
  ```lean
  calc (dim k ^ 2 - Kraus.krausRank K + 1) * dim k ^ 2
      ≤ (D ^ 2 + 1) * D ^ 2 := Nat.mul_le_mul (by omega) hd
    _ ≤ (D ^ 2 + 1) ^ 2 := by nlinarith
  ```
- **Seen:** 2 occurrences (`TNLean/MPS/Examples/PVBS/WStateCanonicalBound.lean:376`,
  `TNLean/MPS/Examples/PVBS/WStateCanonicalBound.lean:149`).
- **Abstraction:** proposed lemma bounding the Wielandt length
  `(m ^ 2 - r + 1) * m ^ 2 ≤ (D ^ 2 + 1) ^ 2` for `m ≤ D`, stated over `ℕ`.

### reassociating a triple Kronecker sum by `mulTensorAssocEquiv` — candidate
- **Pattern:** four `finProdFinEquiv.surjective` peels on the row and column indices, the
  three-stage `simp only` with `mulTensorAssocEquiv`, `Equiv.prodAssoc_apply`,
  `Matrix.kroneckerMap_apply`, `Matrix.sum_apply`, `Matrix.kronecker_apply`, then
  `Finset.sum_mul`, `Finset.mul_sum`, `Finset.sum_comm`, and `mul_assoc` under
  `Finset.sum_congr`.
- **Seen:** two occurrences: `MPOTensor.mulTensor_assoc`
  (`TNLean/MPS/Operator/Product/OperatorProduct.lean`) and `MPOTensor.actTensor_mulTensor`
  (`TNLean/MPS/Operator/ActionTensorReduction.lean`).
- **Abstraction:** a lemma stating that
  `(∑ j, (∑ m, X m ⊗ Y m j).submatrix e e ⊗ Z j)` is the `mulTensorAssocEquiv`-reindex of
  `∑ m, X m ⊗ (∑ j, Y m j ⊗ Z j).submatrix e e`, for arbitrary families of matrices.

Seeded from `scripts/audit/tactic_pattern_scan.py` (2026-07-18 scan; re-run for
current counts and full location lists).

### ambient left-canonical normalization from a unique full-support MPU block — candidate
- **Pattern:** from the shifted transfer-trace identity, obtain the sole
  canonical-form-II block and its unit-modulus weight; use full support to make
  the block inclusion unitary, then transport the block's left-canonical sum
  through the intertwining relation to the ambient tensor.
- **Seen:** two occurrences across two files (2026-09-26): the local
  `hweightedLeft`/`hAleft` argument in
  `TNLean/MPS/CanonicalForm/SimpleMPU/TransferStabilization.lean` and
  `IsMPUCanonicalFormII.isLeftCanonical_normalizedFlattening` in
  `TNLean/MPS/MPU/CanonicalForm/VirtualUnitaryGauge.lean`.
- **Abstraction:** the new public theorem
  `IsMPUCanonicalFormII.isLeftCanonical_normalizedFlattening` is reusable for
  full-support canonical-form-II data. A later refactor can replace the local
  argument in `TransferStabilization.lean` once its supplied CFII data are
  presented in that theorem's type.

### cycle-edge virtual-configuration sum reindexing — candidate
- **Pattern:** identify assignments on the edges of a cycle with assignments
  indexed by its sites using `cycleEdgeEquiv`, then, when a cyclic product is
  required, rotate the site-indexed assignment by one step so that the two
  incident virtual indices become `g v` and `g (v + 1)`.
- **Seen:** the site-to-edge reindexing occurs in
  `Tensor.stateCoeff_reindexMPSChain` in
  `TNLean/PEPS/FundamentalTheorem/Cycle/CycleMPSConstantDescription.lean`,
  `stateCoeff_cycleTensorOfMPS` in `TNLean/PEPS/Tensor/Cycle/CycleMPSTensor.lean`, and the
  blocked-region calculation in `TNLean/PEPS/Injectivity/Region/CycleMPSInjectivity.lean`
  (2026-08-31). The subsequent one-step rotation occurs in the first two of
  these proofs.
- **Abstraction (proposed):** if a third proof needs the full two-stage
  reindexing, extract a cycle-graph sum lemma parameterized by the local
  factor. Keep the factor-specific incident-edge and blocked-arc identities
  at their call sites.

### one-site blocking by canonical physical reindexing — candidate
- **Pattern:** identify the doubled physical alphabet after one-site blocking
  with the original doubled alphabet, prove that blocking is the resulting
  physical relabeling, and reindex the diagonal physical-trace sum to preserve
  each representative's transfer matrix.
- **Seen:** 2 occurrences: the general implication
  `MPOTensor.IsSimpleCanonicalForm.isSimple` in
  `TNLean/MPS/CanonicalForm/SimpleMPO/Simple.lean` and the four-letter specialization
  `MPOTensor.RescalingStableLengthDependentRFP.R_isSimple` in
  `TNLean/MPS/Examples/Dimer/RescalingStableSimple.lean` (post-merge review of PR #7533,
  2026-08-31).
- **Abstraction (proposed):** if a third occurrence appears, extract the
  dimension-parametric one-site doubled equivalence together with lemmas for
  the blocked-tensor relabeling and invariance of the doubled physical-trace
  transfer. Specialize the existing proofs to those lemmas.

### supplied paper-gate indicator entries — completed refactor
- **Pattern:** multiply two source-entry indicator functions, combine their
  two pairs of physical-index equalities, and cancel the shift normalization.
- **Seen:** six paper-gate entry proofs in
  `TNLean/MPS/Examples/Shift/ShiftSourceGateFormulas.lean` and the two four-spin
  matrix entry proofs in
  `TNLean/MPS/Examples/Shift/ShiftSourceFactors.lean` (recounted 2026-09-04 after
  deleting the mixed-kernel examples).
- **Abstraction:** Mathlib's `ite_zero_mul_ite_zero` combines the two indicator
  factors into one conjunction.  The source-specific scalar identities
  `shiftSourceScale_square_cancel` and
  `shiftSourceScale_inv_square_cancel` record the two remaining normalization
  calculations.

### factor pairing under a two-index finite sum — candidate
- **Pattern:** before collapsing a two-index finite sum, use `simp_rw` with a
  pointwise identity proved by `ring` to pair corresponding scalar factors from
  two products, then factor the independent index sums.
- **Seen:** three occurrences in the private proofs `VFour_collapse_one`,
  `VThree_collapse_one`, and `VTwo_collapse_one` in
  `TNLean/MPS/Examples/CorrelatedFlip/Spectrum.lean` (2026-08-23).
- **Abstraction:** a possible file-local lemma that combines the pointwise ring
  rearrangement with `sum_two_four_factors` for products of varying lengths.

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

### projector-selected sector closure assembly — candidate
- **Pattern:** expand a closure as a finite sum of sector closures, distribute
  a projector-controlled sum of linear maps over it, use the orthogonal
  selector identity to retain the matching sector, and finish with the
  sectorwise closure equation.
- **Seen:** four call sites in
  `TNLean/MPS/MPDO/BNTSectors/BNTChannelComposition.lean`, one coarse-graining/refinement
  pair in each of `exists_chainCoordinateRFP_of_projectiveSectorDecomposition`
  and `exists_chainCoordinateRFP_of_orthogonalSectorDecomposition`
  (2026-08-20).
- **Abstraction (file-local):** the private theorem
  `sum_comp_singleKrausMap_firstSiteMatrix_properties` (lines 445--513)
  extracts all four copies. It is parametrized by `n` and `m`, corresponding
  to input and output chain lengths `n + 1` and `m + 1`, the sectorwise maps
  `F`, and their closure equation.

### explicit finite-generator word-tuple spanning — candidate
- **Pattern:** unfold `MPSTensor.WordTupleSpanTop`, place one or more explicit
  word tuples in the span by `Submodule.subset_span`, express an arbitrary
  block tuple as their scalar linear combination, and conclude by closure
  under scalar multiplication and addition.
- **Seen:** two direct occurrences: `sectors_wordTupleSpanTop_one` in
  `TNLean/MPS/Examples/MPDOCounterexamples/CaseIIAbsorptionCounterexample.lean` and
  `scalarBNT_wordTupleSpanTop` in
  `TNLean/MPS/Examples/MPDOCounterexamples/Theorem49RepeatedCopyCounterexample.lean`, together with
  the related finite-generator reconstruction in
  `TNLean/MPS/Examples/SpanningSectors/ActiveSectorSpanningCounterexample.lean`
  (`sectorMatrix_span_eq_top`) (2026-08-20).
- **Abstraction (proposed):** first determine whether a small finite-generator
  span criterion can cover both dependent block tuples and ordinary matrix
  families without requiring application-specific coefficient functions.

### rational negMulLog prime-logarithm expansion — candidate
- **Pattern:** rewrite `Real.negMulLog (a / b)` for an explicit rational into a
  linear combination of logarithms of small primes: unfold `negMulLog`, split
  the quotient with `Real.log_div`, express `b` (and composite `a`) as prime
  powers, apply `Real.log_pow`/`Real.log_mul`, then `push_cast` and `ring`.
- **Seen:** eight private lemmas in
  `TNLean/MPS/Examples/CorrelatedFlip/FlipWeights.lean`
  (`negMulLog_quarter` through `negMulLog_nine_128ths`) (2026-08-21).
- **Abstraction (proposed):** one lemma computing
  `negMulLog ((a : ℝ) / 2 ^ k)` from the prime factorization of `a`, or a
  small simp set bundling `negMulLog`, `Real.log_div`, `Real.log_pow`, and
  `Real.log_mul` with the needed positivity side conditions.

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

### quasi-local translation laws in automorphism-group form — candidate
- **Pattern:** convert translation composition, symmetry, and identity laws from
  `StarAlgEquiv.trans`, `StarAlgEquiv.symm`, and `StarAlgEquiv.refl` into group
  multiplication, inverse, and one before applying `Commute` closure lemmas.
- **Seen:** six short `StarAlgEquiv.aut_mul` / `aut_inv` / `aut_one` conversions
  at five call sites, all in `TNLean/QCA/Automorphism/TranslationCovariance.lean`, before the
  call-site simplification (2026-08-16).
- **Abstraction:** the reusable public laws `SpinChain.quasiLocalTranslation_mul`,
  `SpinChain.quasiLocalTranslation_inv`, and `SpinChain.quasiLocalTranslation_one`
  are available in `TNLean/QCA/QuasiLocal/QuasiLocalTranslation.lean`.

### flattened-pair reconstruction from quotient and remainder — candidate
- **Pattern:** rewrite `ij : Fin (d * d)` as
  `finProdFinEquiv (ij.divNat, ij.modNat)` using
  `(finProdFinEquiv.apply_symm_apply ij).symm` before simplifying a flattened
  pair operation.
- **Seen:** 3 occurrences across `TNLean/MPS/Operator/Product/PhysicalAdjoint.lean` and
  `TNLean/MPS/MPU/CanonicalForm/PhysicalAdjointCanonicalForm.lean` after the physical-pair
  equivalence deduplication (2026-08-13); the latter contributes one occurrence.
- **Abstraction (proposed):** add a low-level simp lemma such as
  `finProdFinEquiv_divNat_modNat` near the shared flattened-index definitions,
  then replace all occurrences together.

### concrete numeric gauge with an explicit inverse — candidate
- **Pattern:** a concrete invertible numeric matrix is packaged as an element of
  `GL n ℂ` through `Matrix.GeneralLinearGroup.mkOfDetNeZero`, after which the
  inverse coordinate is recovered by building a second `mkOfDetNeZero` for the
  inverse, proving the product is one through `Units.ext`, and rewriting with
  `inv_eq_of_mul_eq_one_right`.
- **Seen:** 2 occurrences (2026-09-19), in
  `TNLean/MPS/Examples/BondTwoSingleton/BondTwoSingletonGramBoundary.lean` and
  `TNLean/MPS/Examples/MPDOCounterexamples/PositiveMinimalRealizationCounterexample.lean`; both now use
  the structure form below.  Seven further `mkOfDetNeZero` gauges in
  `TNLean/MPS/Examples/` keep their present form, where the saving is at most one
  or two lines.
- **Abstraction (proposed):** no new declaration is needed.  Supply the inverse
  directly, `where val := M; inv := N; val_inv := h; inv_val := mul_eq_one_comm.mp h`,
  after which both coordinate lemmas are `rfl` and no determinant lemma is
  required.

### diagonal normalized-ancilla sum collapse — candidate
- **Pattern:** collapse the doubled sum for `normalizedDiagonalLift` by using
  `Finset.sum_eq_single` to retain the diagonal ancilla letter `(a, a)`, then
  cancel the resulting normalization with
  `(x : ℂ) * (Real.sqrt x : ℂ)⁻¹ * (Real.sqrt x : ℂ)⁻¹ = 1` for `0 < x`,
  closed by `Complex.ofReal_sqrt_inv_mul_self` since 2026-09-23.
- **Seen:** 2 occurrences in `TNLean/MPS/MPU/CanonicalForm/PhysicalAncilla.lean`:
  `MPOTensor.transferMap_normalizedDiagonalLift` (lines 160--182), for
  `A ij * X * (A ij)ᴴ`, and
  `MPOTensor.leftCanonical_normalizedDiagonalLift` (lines 224--245), for
  `(A ij)ᴴ * A ij`.
- **Abstraction (proposed):** if a third occurrence appears, extract the
  lowest-sufficient helper lemma shared by both matrix-product orientations;
  do not introduce a tactic solely for this pattern.

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
  `QICLean/Analysis/TraceNorm/TraceNormContractivity.lean` (QICLean dependency) isolates the shared
  projection-chaining estimate; both source-facing lemmas are now
  one-`calc`-block corollaries.

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

### rectangular complement expansion — candidate
- **Pattern:** expand a rectangular remainder by associativity:
  `Q * (1 - L * Q) * L = Q * L - (Q * L) * (Q * L)`.
- **Seen:** two occurrences: `rectangular_remainder_eq_mul_sub_sq` in
  `TNLean/MPS/Examples/SpanningSectors/ActiveSectorSpanningCounterexample.lean` and
  `caseI_rectangular_remainder_eq_zero_of_literal_ZCL` in
  `TNLean/MPS/MPDO/CyclicActiveSector/LemmaC5CaseI.lean` (review on 2026-08-08).
- **Abstraction:** if a third occurrence appears, promote the expansion to a
  general rectangular-matrix lemma over a nonunital nonassociative ring with
  the finite-index assumptions needed for matrix multiplication.

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

### positive-map resolvent distribution — candidate
- **Pattern:** distribute a positive linear map and a nonnegative real scalar
  through the shifted-resolvent difference, commute the scalar identity shift,
  and normalize the resulting module expression.
- **Seen:** 2 occurrences in
  `QICLean/Channel/Convexity/OperatorJensenAux.lean`:
  `positiveMap_rpowIntegrand₀₁_jensen` and
  `positiveMap_rpowIntegrand₁₂_jensen`.
- **Abstraction:** a shared algebraic lemma parameterized by the exponent
  identities for the concave and convex integrands, if a third occurrence
  appears.

### invariant-subspace two-block fork — candidate
- **Pattern:** the general and strict invariant-subspace decompositions repeated the
  spectral split, block construction, and MPV calculation.
```
spectral split → block extraction → MPV calculation
spectral split → block extraction → MPV calculation → strict bounds
```
- **Seen:** 2 full proof paths in
  `TNLean/MPS/Tensor/DirectSum/InvariantSubspaceDecomp.lean`; no further occurrence is
  currently identified, so this remains below the promotion threshold.
- **Abstraction:** the implemented private semantic construction
  `exists_twoBlock_decomp_of_lowerZero_aux`; the strict public theorem adds only
  positivity and arithmetic for the strict dimension bounds.

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

### clm_norm_instances — candidate
- **Pattern:**
  ```
  letI : NormedAddCommGroup (V →L[ℂ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : SeminormedRing (V →L[ℂ] V) := ContinuousLinearMap.toSeminormedRing
  letI : NormedRing (V →L[ℂ] V) := ContinuousLinearMap.toNormedRing
  letI : NormedSpace ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedSpace
  letI : NormedAlgebra ℂ (V →L[ℂ] V) := ContinuousLinearMap.toNormedAlgebra
  ```
- **Seen:** 4 occurrences (`TNLean/MPS/Transfer/Spectrum/QuantitativeGap.lean:94`,
  `TNLean/MPS/Transfer/Spectrum/MPVOverlapTrace.lean:48`,
  `TNLean/MPS/CanonicalForm/RenormalizationFixedPoint/BNTOrthogonality.lean:453`,
  `TNLean/MPS/Transfer/Correlation/StringOrderDefs.lean:230`, the last with the carrier
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
  `TNLean/MPS/MPDO/Fusion/BNTFusionTensorClauseFromRFP.lean` and
  `TNLean/MPS/MPDO/AmbientSectorMaps/BNTAlgebraTensorClauseSpectrum.lean` (2026-07-22).
- **Abstraction (proposed):** first scout the finite-sum linear-map API for a general lemma
  factoring a doubly indexed scalar sum out of a fixed vector. This remains below the ordinary
  rule-of-three threshold, and no further occurrence is currently identified.

### cpsv_matched_phase_coefficient_identity — candidate
- **Pattern:** rewrite two sector-decomposition state expansions through a matched phase
  bijection, then use eventual linear independence to identify their coefficients.
- **Seen:** 2 occurrences in
  `TNLean/MPS/FundamentalTheorem/Sectors/CoeffIdentity.lean` and
  `TNLean/MPS/MPDO/AmbientSectorMaps/BNTAlgebraTensorClauseSpectrum.lean` (2026-07-22).
- **Abstraction (proposed):** generalize `coeff_identity_via_matched_mpv_phase` to accept
  eventual linear independence of the chosen basis directly, while retaining its current
  `IsLeftCanonicalBNTPresentation` wrapper for existing consumers.

### square_interior_edge_translate — candidate
- **Pattern:** given `NormalSquareInteriorEdgeDatum e`, case-split horizontal/vertical,
  extract interior-margin hypotheses (`IsNormalSquareHorizontalEdgeInteriorMargins` /
  `IsNormalSquareVerticalEdgeInteriorMargins`), rewrite `e` to the translated-edge form
  (`normalSquareHorizontalTranslatedEdge` / `normalSquareVerticalTranslatedEdge`) via
  `normalSquareHorizontalTranslatedEdge_sub_eq_rightEdge` /
  `normalSquareVerticalTranslatedEdge_sub_eq_upEdge`, and dispatch to the
  translated-edge version of the target statement.
- **Seen:** 2 occurrences (2026-07-24):
  `TNLean/PEPS/FundamentalTheorem/Normal/NormalSquareEdgeCoeff.lean:84-104` (absorbing gauge),
  `TNLean/PEPS/FundamentalTheorem/Normal/NormalSquareUnconditionalFundamentalTheorem.lean:118-190` (per-edge bond-dimension equality).
- **Abstraction (proposed):** a lemma of shape
  `NormalSquareInteriorEdgeDatum.translatedDispatch` taking the horizontal and vertical
  continuations, or a helper that rewrites the edge and exposes the translated-coordinate
  hypotheses.  Below the rule-of-three promotion bar.

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
  API (`ManyBody.IsRegionIncidentEdge`, `IsCrossingEdge`) already shared. Recorded rather than
  promoted in the triMerge migration PR: the `IsCrossingEdge`-hypothesis restate
  (sharing the `CoarseThreeSite9` derivation shape) was applied there, but unifying the
  six sites needs a partition-with-regions hypothesis bundle common to
  `CoarseThreeSite5/9` and the `UnionInjectivity*` geometry, which is a design
  decision for the #4522 interface arc.

### continuous nonnegative function with zero integral — candidate
- **Pattern:** on the open positive half-line, turn pointwise nonnegativity into an
  almost-everywhere inequality, use integrability and a zero integral to obtain
  almost-everywhere vanishing, then use continuity and
  `Measure.eqOn_open_of_ae_eq` to obtain pointwise vanishing.
- **Seen:** 2 occurrences across 2 files:
  `QICLean/Entropy/Recovery/WeylRelativeEntropyIntegral.lean` in
  `weyl_sourceB_defect_eq_zero_of_gap_eq_zero`, and
  `QICLean/Entropy/Relative/SupportRelativeEntropyGap.lean` in
  `supportSourceBDefect_eq_zero_of_relativeEntropy_sum_eq` (2026-07-27).
- **Abstraction (proposed):** a measure-theoretic lemma taking `IntegrableOn f (Ioi 0)`,
  `ContinuousOn f (Ioi 0)`, nonnegativity on `Ioi 0`, and zero restricted integral,
  and returning `EqOn f 0 (Ioi 0)`.

### right-support range witness for a left--right operator — candidate
- **Pattern:** factor the left--right operator through the right-support
  projection and the shifted relative-modular resolvent, construct
  `P R⁻¹ D y` for a `P`-fixed vector `y`, and use the witness to show that
  the support projection of the left--right operator fixes `y`.
- **Seen:** 2 occurrences in
  `QICLean/Entropy/Relative/SupportLeftRightRelativeModular.lean`, in
  `supportRightProj_mul_supportLeftRightSupportProj_eq` and
  `supportLeftRightSupportInv_mulVec_sourceB_eq_projected_relativeModular`
  (2026-07-27).
- **Abstraction (proposed):** a range-inclusion lemma stating that the range
  of `1 ⊗ P_Bᵀ` is contained in the range of
  `A ⊗ 1 + t(1 ⊗ Bᵀ)` for `t > 0`, with the projection-absorption identity
  and the one-pair source solution as consumers.

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
  `TNLean/MPS/MPDO/BNTSectors/BNTChannelComposition.lean`, in the proofs of
  `firstSiteMatrix_mul_physCloseN_of_mul_physicalSlice`,
  `firstSiteMatrix_mul_physCloseN_eq_zero_of_mul_physicalSlice_eq_zero`, and
  `physCloseN_mul_firstSiteMatrix_of_physicalSlice_mul`.
- **Abstraction (proposed):** left- and right-multiplication lemmas expressing
  the entries of a physical-slice identity as sums of scalar multiples of the
  tensor matrices. The zero conclusion should be a specialization of the left
  lemma rather than a separate argument.

### star preserves the complex norm — candidate
- **Pattern:** `simpa only [RCLike.star_def, RCLike.norm_conj]` to close a goal of the
  form `‖star μ‖ = 1` or `‖star μ‖ ≤ 1` from `‖μ‖ = 1` or `‖μ‖ ≤ 1`.
- **Seen:** 5 occurrences in `TNLean/Channel/Peripheral/AdjointSpectrum.lean` before
  the 2026-08 adjoint-spectrum cleanup, 3 of them newly written in that PR.
- **Abstraction (proposed):** Mathlib's `norm_star : ‖star a‖ = ‖a‖` (a `simp` lemma on
  any `NormedStarGroup`, and `ℂ` is one) closes each of these directly; no new TNLean
  declaration is needed, only the call-site substitution.

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
  `TNLean/MPS/Examples/Dimer/RescalingStableLengthDependentRFP.lean` and `T_isMPDO` in
  `TNLean/MPS/Examples/Dimer/TwistedDimerDensityOperator.lean` (2026-09-02).
- **Abstraction (proposed):** if a third such tensor appears, extract a
  positivity criterion parameterized by the local bond-matching relation and
  the local factor, and specialize the existing proofs to it.

### matrix-unit tensor word and closed-chain expansions — candidate
- **Pattern:** multiply a matrix-unit tensor letter into a matrix unit, induct
  along two words using the open bond-matching condition, then take the trace
  and split on the wraparound match to obtain a cyclic closed-operator entry
  formula.
- **Seen:** 2 occurrences across `TNLean/MPS/Examples/Dimer/TwistedDimerDensityOperator.lean`
  (`T_mul_single_sum`, `evalWord_T_ofFn`, `mpo_T_entry_formula`) and
  `TNLean/MPS/Examples/Dimer/TwistedDimerFlagSectors.lean` (`unitTensor_mul_single`,
  `evalWord_unitTensor_ofFn`, `mpo_unitTensor_apply`) (2026-09-02).
- **Abstraction (proposed):** if a third occurrence appears, extract a generic
  closed-chain formula for block-disjoint matrix-unit tensors and derive both
  existing calculations from it.

### trace-one ambient block fixed matrix — candidate
- **Pattern:** from canonical-form-II data with one retained block and full
  support, rescale the block's diagonal positive fixed matrix to trace one,
  use the unit weight forced by the shifted transfer traces, and transport the
  rescaled matrix along the ambient block inclusion to a positive trace-one
  right fixed matrix of the ambient transfer map.
- **Seen:** two occurrences,
  `TNLean/MPS/CanonicalForm/SimpleMPU/TransferStabilization.lean` (the stabilized-power theorem)
  and `TNLean/MPS/MPU/CanonicalForm/ReducedCanonicalRepresentative.lean` (the reduced
  representative in the ambient diagonal gauge), recorded 2026-09-04.
- **Abstraction:** proposed lemma on canonical-form-II data producing the
  normalized block matrix together with its weighted-block fixed-point
  equation, leaving each call site to choose the ambient coordinates.

---

### scalar multiple preserves block injectivity — migrated (2026-11-15, 2026-11-26)
- **Pattern:** nonzero scalar multiplication preserves fixed-length block
  injectivity and algebraic normality.
- **Abstraction:** the existing `MPSTensor.isNBlkInjective_smul_iff` and
  `MPSTensor.isNormal_smul_iff` in `MPS/Tensor/Words/ScaledNormality.lean`.

### rectangular reduction from local compression data — candidate
- **Pattern:** prove `MPTensor.IsReduction B A V W` by
  `refine ⟨hVW, fun w ↦ ?_⟩` followed by `induction w` with `nil`, singleton,
  and `cons i (cons j w)` cases, the last one rewriting `B i * W * V * B j`
  to `B i * B j` and then splitting the caps off the two factors.
- **Seen:** one occurrence, in `MPOTensor.CZX.fusion_isReduction`
  (`TNLean/MPS/Examples/CZX/Gauging/CZXFusionTensors.lean`), recorded 2026-09-07.
- **Abstraction:** `MPTensor.IsReduction.of_local_compression` in
  `TNLean/MPS/Tensor/Reduction/Reduction.lean`, taking `V * W = 1`, per-letter
  compression, and the two-letter reinsertion identity.

### periodic vector of a doubled-index view at an arbitrary pair letter — candidate
- **Pattern:** rewrite a periodic vector of `MPOTensor.toMPSTensor` at an arbitrary
  configuration of the pair alphabet into a matrix entry of the periodic operator, by first
  proving `(fun n => finProdFinEquiv ((ρ n).divNat, (ρ n).modNat)) = ρ` and then rewriting with
  `MPSTensor.mpv_toMPSTensor_pairConfig`.
- **Seen:** `MPOTensor.GroupFamily.IsRepresentation.sameMPV₂Pos_mulTensor` in
  `TNLean/MPS/CanonicalForm/SimpleMPU/GroupRepresentation.lean`, `TNLean/MPS/MPU/Representation/DaggerInverseGauge.lean`,
  `TNLean/MPS/MPU/CanonicalForm/ReducedCanonicalRepresentative.lean`,
  `TNLean/MPS/MPDO/Entropy/NormalizedMPOProportionality.lean`,
  `TNLean/MPS/CanonicalForm/SimpleMPO/BNTLayerOrthogonality.lean`,
  `TNLean/MPS/MPDO/CommutingForm/FixedBondProductTensor.lean` (recorded 2026-09-17).
- **Abstraction:** `MPOTensor.mpv_eq_mpo` in `TNLean/MPS/Operator/PairAlphabet.lean`, which
  states the identity on the pair alphabet itself; at a doubled-index site, rewrite first with
  `MPOTensor.mpv_toMPSTensor_eq`. The earlier `MPOTensor.mpv_toMPSTensor` was removed with the
  pair-alphabet restatement.

### canonical form of normalized one-dimensional blocks — candidate
- **Pattern:** certify `IsLeftCanonicalBNTPresentation` for a `SectorDecomposition` whose blocks are
  normalized tensors of bond dimension one with unit weights: linear independence of the block
  states from `mpv_of_dim_one` evaluated on constant words, `basis_distinct` by
  `not_gaugePhaseEquiv_of_dim_one` after a `cast_eq`, then `totalDim_*`, bijectivity of the
  copy coordinates by `sigma_eq_of_copyCoord_eq`, the ordering `(Equiv.ofBijective _ _).symm`,
  and `reindex_toTensor_*` by `toTensor_copyCoord` / `toTensor_copyCoord_of_ne`.
- **Seen:** 2 occurrences, `TNLean/MPS/Preparation/BlockSum/RepeatedBlockCounterexample.lean` and
  `TNLean/MPS/Preparation/BlockSum/OverlappingBlockCounterexample.lean` (recorded 2026-09-27).
- **Abstraction:** proposed lemma giving `IsLeftCanonicalBNTPresentation` for a sector decomposition of
  normalized one-dimensional blocks with unit weights whose letters are pairwise distinguished
  by their zero patterns.

### parent interaction from an explicit symmetric idempotent — candidate
- **Pattern:** identify a spin-chain local term, shifted and rescaled, with
  `parentInteraction A n`: prove a coordinate formula by `fin_cases` over the window,
  deduce from it that the operator is symmetric for the \(\ell^2\) pairing and idempotent
  (both by `ring` on the coordinates), match its kernel with `groundSpace A n` through the
  explicit constraint characterization, and close with
  `Submodule.eq_starProjection_of_mem_orthogonal` and `inner_withLpLinearEquiv_symm`.
- **Seen:** `MPSTensor.majumdarGhoshTerm_shift_eq_parentInteraction`
  (`TNLean/MPS/Examples/MajumdarGhosh/MajumdarGhoshLowerBound.lean`) and
  `MPSTensor.akltBondTerm_shift_eq_parentInteraction`
  (`TNLean/MPS/Examples/AKLT/AKLTPolynomialHamiltonian.lean`) (recorded 2026-09-27).
- **Abstraction (proposed):** a lemma `parentInteraction_eq_of_symm_idem_ker` taking a
  linear endomorphism `Q` of `NSiteSpace d n` that is symmetric for the coefficient
  pairing, idempotent, and has kernel `groundSpace A n`, and concluding
  `Q = parentInteraction A n`.

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
  (`TNLean/MPS/FundamentalTheorem/OperatorGroup/DomainWallString.lean`, lines 163, 186, 207 and 227;
  reported by `scripts/audit/tactic_pattern_scan.py`, recorded 2026-09-27).
- **Abstraction (proposed):** a lemma rewriting
  `∑ c, (∑ α, ∑ β, x α β * Â c α β) * y c` as `∑ α, ∑ β, x α β * ∑ c, Â c α β * y c`, or
  one endpoint lemma parametrized by the value of the pairing, from which the four
  endpoint theorems follow by `simp`.

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
  tree-gauge inverse identities in `TNLean/MPS/Operator/Fusion/CompleteZipperFusionGauge.lean`.
- **Count:** six occurrences in one file; the two-file promotion threshold
  has not been reached.
- **Possible abstraction:** a transposed Kronecker inverse-pair lemma if a
  second module needs the same cancellation pattern.

### root-of-unity powers across a cyclic successor — candidate
- **Pattern:** simplify `Fin.val_add` and `Fin.val_one'`, then use
  `pow_eq_pow_mod`, `pow_succ`, and commutativity to prove
  `z ^ (k + 1).val = z * z ^ k.val` from `z ^ q = 1`.
- **Seen:** two occurrences in two files: `Fin.exists_stepOrbit_phases` in
  `QICLean/Algebra/Combinatorics/FinStepOrbit.lean` and the private `map_cyclic_sum` in
  `TNLean/MPS/CanonicalForm/Periodic/Blocking/Spectrum.lean` (2026-09-30).
- **Abstraction (proposed):** a cyclic-successor power lemma over a commutative
  monoid; below the three-occurrence promotion threshold.

### Unitary transport of left-canonical sums — candidate
- **Pattern:** expand the conjugate transpose of `U * A i * Uᴴ`, cancel the
  middle unitary pair, move the outer matrices through the finite sum, and
  use the original left-canonical identity.
- **Seen:** two occurrences in two files: the normalization proof in
  `exists_isLeftCanonical_blockTensor_eq_of_unitary_conj` in
  `TNLean/MPS/CanonicalForm/Periodic/Blocking/SectorPhaseWord.lean`, and
  `leftCanonical_of_unitary_block_intertwining` in
  `TNLean/MPS/MPU/CanonicalForm/VirtualUnitaryGauge.lean`.
- **Abstraction (proposed):** a left-canonical transport lemma for a unitary
  matrix intertwining two tensor families, if a third occurrence arises.

### Selecting and flattening prescribed orbit blocks — candidate
- **Pattern:** choose the prescribed periodic decomposition separately for each
  original block, flatten `(original block, orbit)` with `finSigmaFinEquiv`,
  and transport the weighted MPV identity through that enumeration.
- **Seen:** two occurrences in `IsIrreducibleForm.block` in
  `TNLean/MPS/CanonicalForm/Periodic/Blocking/IrreducibleFormBlocking.lean` and
  `weight_norm_and_dim_eq_of_blocked_sameMPV₂Pos` in
  `TNLean/MPS/FundamentalTheorem/Refinement/DivisibleOfRefinable.lean` (2026-09-30).
- **Abstraction (proposed):** a family-level decomposition lemma returning
  the chosen blocks and dimension identities if a third consumer appears.
  The shared weighted-sum refinement is already a separate theorem.

### measurement-assisted GHZ protocol on two site layouts — candidate
- **Pattern:** the Example 1 protocol of arXiv:2103.13367 written twice: the
  outcome-consistency lemma, the corrections by outcomes and partial sums, and
  the product-state bookkeeping.
- **Seen:** two occurrences (2026-10-01):
  QICLean's `Circuit/Protocol/GHZ.lean`, formerly TNLean's
  `Circuit/Measurement/GHZ.lean` (interleaved single qudits of
  an open chain, `forall_succ_eq_iff`, `forall_add_ghzCorrection_eq_iff`) and
  `TNLean/MPS/Preparation/Circuit/WindowGHZ.lean` (registers of `r₁` sites inside
  blocks of a ring, `forall_cyclic_eq_zero_iff`).
- **Abstraction:** proposed: one protocol over an injective embedding of the
  system and ancilla sites and a label type `Cfg d r₁`, in an open and a
  cyclic form, with the outcome-consistency lemma over an additive group
  indexed by `Fin M`. The partial sums already share `Fin.partialSum`.

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

### finite block coordinates with zero complements — candidate
- **Pattern:** split active and zero block labels, decide the active label,
  derive the coordinate bounds with `omega`, and simplify the block inclusions
  and projections before proving the scalar entry identity.
- **Seen:** three coordinate cases in
  `TNLean/MPS/Examples/Ising/IsingThreeObjectGauge.lean` (2026-10-02).
- **Abstraction:** a coordinate lemma for regrouping active direct sums with
  one-dimensional zero complements, if a second example requires the same
  construction.
