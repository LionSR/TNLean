/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Analysis.MeanErgodic
import TNLean.Analysis.Dirichlet
import TNLean.Channel.Determinant.Bound
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.Peripheral.SpectralRadius
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.FixedPoint.MeanErgodicProjection
import TNLean.Channel.FixedPoint.MeanErgodicAdjoint
import TNLean.Channel.FixedPoint.FullSupportBlockRetraction
import TNLean.Channel.FixedPoint.TraceAdjointDensityBlocks
import TNLean.Channel.FixedPoint.ConditionalExpectation
import TNLean.Channel.FixedPoint.StationarySupport
import TNLean.Channel.FixedPoint.CornerFixedPoints
import TNLean.Channel.FixedPoint.WedderburnDecomp
import TNLean.Channel.FixedPoint.BlockForm
import TNLean.Channel.FixedPoint.CornerBlockForm
import TNLean.Channel.FixedPoint.Corollaries
import TNLean.Channel.FixedPoint.WeightedCornerFixedPoints
import TNLean.Channel.FixedPoint.MaximalSupport
import TNLean.Channel.FixedPoint.MaximalRank
import TNLean.Channel.Irreducible.Ergodicity
import TNLean.Channel.Irreducible.Basic
import TNLean.Channel.Irreducible.Growth
import TNLean.Channel.Irreducible.PerronFrobenius
import TNLean.Channel.Irreducible.SpectralRadius
import TNLean.Channel.Irreducible.FromSpectral
import TNLean.Channel.Peripheral.Spectrum
import TNLean.Channel.PerronFrobenius.Existence
import TNLean.Channel.Irreducible.Similarity
import TNLean.QPF.Assembly
import TNLean.Wielandt.Primitivity.Equivalence
import TNLean.Channel.WolfChapter6Wrappers

/-!
# Wolf Chapter 6 — Spectral Properties: Public Theorem Index

This module serves as a **navigational index** that maps the formalized theorems
in this project to the numbering in:

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 6.

Each entry lists the Wolf result, its status (fully formalized / partially
formalized / not yet formalized), and the Lean declaration(s) that correspond.

No new proofs are introduced here; this is a documentation-only index module.

---

## Section 6.1 Spectral radius and determinant

### Wolf Proposition 6.1 (Spectral radius of positive maps) — TRACE-PRESERVING CASE FORMALIZED

* `IsPositiveMap.eigenvalue_norm_le_one_of_tracePreserving` — every eigenvalue of a
  positive trace-preserving map lies in the closed unit disk, in
  `TNLean.Channel.Determinant.Bound`.
* `IsPositiveMap.eigenvalue_one_exists_of_tracePreserving` — eigenvalue $1$ exists
  (nonzero PSD fixed point), in `TNLean.Channel.Peripheral.SpectralRadius`.

The general bound `ρ(T) ≤ ‖T(1)‖∞` for arbitrary positive maps relies on the
Russo--Dye theorem, which yields factor $1$; this general bound is not yet
formalized.  A factor-$4$ route via the PSD decomposition is a possible
elimination plan.  Documented in
`docs/paper-gaps/wolf_prop61_russo_dye_factor.tex`.


### Wolf Lemma 6.1 (Dirichlet's simultaneous approximation) — FORMALIZED

* `Dirichlet.exists_int_near_mul_simultaneous` — the $m$-variable simultaneous
  approximation $1\le n\le q^m$ with $|x_k n-p_k|\le 1/q$ for all $k$, in
  `TNLean.Analysis.Dirichlet`.

### Wolf Proposition 6.2 (Trivial Jordan blocks for peripheral spectrum) — NOT FORMALIZED

Documented in `docs/paper-gaps/wolf_prop62_jordan_blocks.tex`.
The bounded-orbit lemma (`IsPositiveMap.hasBoundedOrbits_of_tracePreserving`)
is already formalized; the binomial-expansion growth argument for nontrivial
Jordan blocks remains to be formalized.

## Section 6.2 Irreducible maps and Perron–Frobenius theory

### Wolf Theorem 6.2 (Irreducible positive maps) — ITEMS 1,2,4 FORMALIZED

**Item 1** (definition via invariant projections):
* `IsIrreducibleMap` — `TNLean.Channel.Irreducible.Basic`

**Item 2** (growth condition `(id + T)^{d-1}(A) > 0`):
* `growth_posDef_of_irreducible_cp` — `TNLean.Channel.Irreducible.Growth`
  (for CP maps; proves the (1)→(2) direction)
* `posDef_of_ker_subset_irreducible_cp` — structural lemma:
  `ker(A) ⊆ ker(E(A))` + irreducible CP → `A` is PosDef
* `mulVecLin_ker_idPlusE_lt_of_not_posDef` — strict kernel decrease

**Item 3** (exponential condition `exp[tT](A) > 0`): NOT FORMALIZED.

**Item 4** (orthogonal trace condition):
* `orthogonal_trace_pos_of_irreducible_cp` — `TNLean.Channel.Irreducible.Growth`
  For orthogonal PSD `A, B` (tr(BA)=0), ∃ t ∈ {1,...,D-1}, tr(B·T^t(A)) > 0.

### Wolf Theorem 6.3 (Spectral radius of irreducible maps) — ITEMS 2,3,4 FORMALIZED

**Item 2** (non-degenerate eigenvalue, strictly positive eigenvector):

Channel-level (general irreducible CP maps) — `TNLean.Channel.Irreducible.PerronFrobenius`:
* `posDef_of_posSemidef_eigenvector_irreducible_cp`: PSD eigenvector → PosDef
* `exists_posDef_eigenvector_of_irreducible_cp`: ∃ PosDef eigenvector with `r > 0`
* `posSemidef_eigenvector_unique_of_irreducible_cp`: uniqueness up to scalar

MPS/QPF-level (transfer maps):
* `posSemidef_fixedPoint_isPosDef` — `TNLean.QPF.PosDef`
* `posSemidef_fixedPoint_isPosDef_of_irreducible`
* `posSemidef_fixedPoint_unique` — `TNLean.QPF.Uniqueness`
* `posSemidef_fixedPoint_unique_of_irreducible`

**Item 3** (uniqueness of positive eigenvalue):
* `eigenvalue_unique_of_irreducible_cp` — `TNLean.Channel.Irreducible.PerronFrobenius`
  Any two positive eigenvalues with nonzero PSD eigenvectors must coincide.
* `posSemidef_eigenvector_unique_of_irreducible_cp` shows any two PSD
  eigenvectors for the same eigenvalue are proportional.

**Item 4** (spectral radius identity `r = ρ(T)`):
* `spectralRadius_eq_of_posDef_eigenvector_of_irreducible_cp`
  — `ENNReal`-valued statement `ρ(E) = ofReal r`
* `spectralRadius_toReal_eq_of_posDef_eigenvector_of_irreducible_cp`
  — real-valued corollary `(ρ(E)).toReal = r`

Both in `TNLean.Channel.Irreducible.SpectralRadius`.
Combined with `exists_posDef_eigenvector_of_irreducible_cp` from
`TNLean.Channel.Irreducible.PerronFrobenius`, these give the full Wolf item 4
for the Perron–Frobenius eigenvalue.

### Wolf Corollary 6.3 (Time-average / ergodicity) — FORMALIZED

* `IsChannel.exists_unique_density_fixedPoint_of_irreducible` —
  `TNLean.Channel.Irreducible.Ergodicity`
  Qualitative form: an irreducible channel has a unique density-matrix fixed
  point, and it is positive definite.
* `IsChannel.cesaroMean_tendsto_of_irreducible` — `TNLean.Channel.Irreducible.Ergodicity`
  Full Cesàro convergence: for every density matrix `ρ`,
  `(1/N) ∑_{t=0}^{N-1} E^[t](ρ) → σ`.

Supporting formalization in `TNLean.Channel.Irreducible.Ergodicity`:
* `IsChannel.iter_mem_densityMatrices`: iterates of a channel preserve density matrices.
* `IsChannel.cesaroMean_subseq_limit_fixedPoint`: any subsequential Cesàro limit is
  a density-matrix fixed point (compactness + telescoping argument).

### Wolf Theorem 6.4 (Irreducibility from spectral properties) — FORMALIZED

In `TNLean.Channel.Irreducible.FromSpectral`:
* `HasSpectralProperties` — Kraus-witness bundle of the spectral assumptions
  in Wolf's theorem (PD right/left eigenvectors, PSD uniqueness, spectral radius).
* `hasSpectralProperties_of_irreducible_cp` — the forward implication
  `irreducible → spectral properties`.
* `isIrreducibleMap_of_hasSpectralProperties` — the reverse implication via
  TP gauge reduction + channel fixed-point contradiction.
* `isIrreducibleMap_iff_spectral_properties` — the final iff statement.

### Wolf Theorem 6.5 (Spectral radius and positive eigenvectors) — FORMALIZED

* `exists_posSemidef_eigenvector` — `TNLean.Channel.PerronFrobenius.Existence`

Uses Brouwer's fixed-point theorem on density matrices (proved in
`TNLean.Axioms.BrouwerFixedPoint`).

### Wolf Proposition 6.6 (Similarity preserving irreducibility) — FORMALIZED

* Scalar case: `isIrreducibleMap_smul` — `TNLean.Channel.Irreducible.Scaling`
* Similarity case: `isIrreducibleMap_similarity` — `TNLean.Channel.Irreducible.Similarity`
* Full Wolf form `T' = c C⁻¹ T(C · C†) C⁻†`:
  `isIrreducibleMap_full_similarity` (and the stronger
  `isIrreducibleMap_similarity_smul`) — `TNLean.Channel.Irreducible.Similarity`
* Numbered theorem: `Kraus.wolf_prop_6_6` — `TNLean.Channel.WolfChapter6Wrappers`

### Wolf Theorem 6.6 (Peripheral spectrum of irreducible Schwarz maps)

**Item 1** (roots-of-unity structure): PARTIALLY FORMALIZED
* `peripheral_isRootOfUnity_of_pow_eigenvalue` — `TNLean.Channel.Peripheral.Spectrum`

**Items 2–4** (non-degeneracy, unitary eigenvector, cyclic projections):
PARTIALLY FORMALIZED in `TNLean.Channel.Peripheral.CyclicDecomposition`.

---

## Section 6.3 Primitive maps

### Wolf Theorem 6.7 (Primitive maps, 4 equivalent conditions)

**Item 4** (trivial peripheral spectrum, PD eigenvector):
* `IsPrimitive` — `TNLean.Channel.Peripheral.Spectrum`
* `isPrimitive_of_compl_eigenvalues_lt_one` / `compl_eigenvalue_norm_lt_one_of_primitive`

Other items: PARTIALLY via transfer-operator gap formalization in `TNLean.Spectral.*`.

### Wolf Theorem 6.8 (CP primitive maps, Kraus span characterizations)

* `IsPrimitivePaper` — `TNLean.Wielandt.Primitivity.Definitions`
  (item 3: `Kₘ = M_d(ℂ)` for `m ≥ q`)
* Pairwise equivalences from Proposition 3:
  * `primitivePaper_iff_hasEventuallyFullKrausRank` / `primitivePaper_iff_stronglyIrreducible`
    (in `TNLean.Wielandt.Primitivity.Equivalence`)
  * `hasEventuallyFullKrausRank_iff_isNormal`
    (in `TNLean.Wielandt.Primitivity.Definitions`)
* Formulated Wolf-facing formulations:
  * `wolf_theorem_6_8_kraus_span`
  * `wolf_theorem_6_8_conjunction`
  (in `TNLean.Wielandt.Primitivity.Equivalence`)

### Wolf Theorem 6.9 (Quantum Wielandt inequality)

Current formal statements live in `TNLean.Wielandt.Inequality.Bounds`:
* `qIndex_le_iIndex_of_isPrimitivePaper`
* `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit` /
  `iIndex_le_of_isPrimitivePaper_of_isUnit`
* `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` /
  `iIndex_le_sq_of_noninvertible_eigenvector`

The positive-definite primitive-to-normal theorem is
`MPSTensor.isNormal_of_isPrimitiveMPS_with_posDef` in
`TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank`; it is not the
Wielandt index bound itself.

---

## Section 6.4 Fixed points

### Wolf Section 6 stationary-support state (Propositions 6.9--6.11, Lems. 6.4--6.5)

In `TNLean.Channel.FixedPoint.StationarySupport`:

* `Channel.support_proj_fixed` — support projection of a PSD fixed point is
  invariant under the compressed channel action.
* `Channel.stationarySupport` — support projection of the unique density-matrix
  fixed point of an irreducible channel.
* `Channel.stationarySupport_eq_one` — irreducible channels have full
  stationary support.
* TODO: non-vacuous formalizations of Wolf Proposition 6.9 and Proposition 6.10
  (`irreducible_iff_support_full`, `stationary_support_minimal`) remain to be
  reinstated.

### Wolf Theorem 6.12 (Fixed points form a *-algebra) — PARTIALLY FORMALIZED

In `TNLean.Channel.FixedPoint.AbstractAlgebra`:

* `SchwarzMap.fixedPointsStarSubalgebra` — for a positive unital Schwarz map
  whose trace adjoint has an explicitly chosen positive definite fixed point,
  the fixed points form a `StarSubalgebra`.

This is the algebra step after the faithful invariant weight has been chosen.
The source theorem begins with an arbitrary full-rank fixed point and invokes
its proposition on positive fixed points to obtain that weight.  The
full-rank-to-positive-definite reduction theorem remains open.  The explicit
trace-adjoint block realization from Equation (1.39) also remains open at this
level of generality.  The downstream Schrödinger-picture density-block
classification and its complementary zero summand are completed in
`TNLean.Channel.FixedPoint.WolfTheorem614`.

In `TNLean.Channel.FixedPoint.Algebra`:

* `Kraus.fixedPointsStarSubalgebra` — Kraus specialization in the
  Schrödinger picture:
  if `map K` is unital and `adjointMap K` has a positive definite fixed point,
  the fixed points of `map K` form a `StarSubalgebra`.
* `Kraus.adjointFixedPointsStarSubalgebra` — Kraus specialization in the
  Heisenberg picture:
  if `adjointMap K` is unital (`IsTP K`) and `map K` has a positive definite
  fixed point, the fixed points of `adjointMap K` form a `StarSubalgebra`.
* `Kraus.fixedPoints_in_multiplicativeDomain` — the key intermediate step:
  every fixed point of the adjoint map lies in the multiplicative domain.
* `Kraus.fixedPoints_starSubalgebra` / `Kraus.mem_fixedPoints_starSubalgebra`
  — numbered theorem with Wolf naming convention.

### Wolf Theorem 6.13 (Fixed points and Kraus commutant) — FORMALIZED

In `TNLean.Channel.FixedPoint.Algebra`:

* `Kraus.fixedPoint_commutes_kraus` — if `X` and `Xᴴ * X` are both fixed by
  the Heisenberg-picture map `adjointMap K`, then `X` commutes with every
  Kraus operator `K i`.
* `Kraus.krausCommutantStarSubalgebra` — the commutant of {K_i, K_i†} forms
  a `StarSubalgebra`.
* `Kraus.krausCommutantStarSubalgebra_isGreatest_adjointFixedPointStarSubalgebras`
  — the Kraus commutant is the **largest** `*`-subalgebra contained in the
  fixed-point set of the adjoint map.
* `Kraus.adjointFixedPointsStarSubalgebra_eq_krausCommutantStarSubalgebra`
  — under the hypotheses of Theorem 6.12, the full adjoint fixed-point
  `*`-subalgebra coincides with the Kraus commutant.

### Wolf Theorem 6.10 (Brouwer's fixed point theorem)

* `brouwer_fixedPoint_densityMatrices` — `TNLean.Axioms.BrouwerFixedPoint`
  (density-matrix specialization; kernel-checked).
* `Brouwer (vendored Gametheory library)` — exact import citation: Brouwer for the
  standard simplex (LionSR/Brouwer library).
* `exists_fixedPoint_closedCube` — `TNLean.Topology.BrouwerProduct`;
  extends Brouwer to closed cubes.
* `fixedPoint_of_compact_retract` — `TNLean.Topology.CompactRetractFixedPoint`;
  extends Brouwer to compact retracts of finite-dimensional real normed spaces.
* The general compact-convex statement (Wolf's formulation) is not yet proved;
  see `docs/paper-gaps/brouwer_general_compact_convex.tex`.

### Wolf Theorem 6.11 (Stationary states) — FORMALIZED

The theorem is formalized for continuous (not necessarily linear) maps, exactly
matching Wolf's statement ("continuous, trace-preserving, positive (not
necessarily linear)").  The linear specializations are also provided.

In `TNLean.Channel.FixedPoint.StationaryStates`:

* `IsStationaryMap.IsPositive` — positivity predicate for arbitrary (nonlinear) maps.
* `IsStationaryMap.IsTracePreserving` — trace-preservation predicate for arbitrary maps.
* `IsStationaryMap` — conjunction of continuity, positivity, trace preservation.
* `IsStationaryMap.exists_stationaryState` — Wolf Theorem 6.11: existence of a
  density-matrix fixed point for a stationary map.  The proof uses
  `brouwer_fixedPoint_densityMatrices`.
* `IsStationaryMap.exists_stationaryState_of_linear` — specialization to linear
  positive trace-preserving maps.
* `IsStationaryMap.exists_stationaryState_of_channel` — specialization to
  quantum channels (linear CPTP maps).  This recovers the existence result
  already proved by Cesàro means in `Cesaro.lean`, but now via Brouwer.

Additionally:

* Via Cesàro: `IsChannel.exists_posSemidef_fixedPoint` —
  `TNLean.Channel.FixedPoint.Cesaro`.
* Via Brouwer (linear): `exists_posSemidef_eigenvector` —
  `TNLean.Channel.PerronFrobenius.Existence`.

### Wolf Proposition 6.8 (Positive fixed-points) — FORMALIZED

* `IsPositiveMap.posPart_negPart_fixed_of_fixedPoint` — the source-faithful positive
  trace-preserving statement for the four canonical positive parts in
  `TNLean.Channel.FixedPoint.Cesaro`.
* `IsPositiveMap.exists_posSemidef_fixedPoints_decomposition` — the existential form.
* `IsPositiveMap.posPart_negPart_fixed_of_hermitian_fixedPoint` and
  `IsPositiveMap.posSemidef_parts_of_hermitian_fixedPoint` — Hermitian intermediate
  forms.
* `IsChannel.posSemidef_parts_of_hermitian_fixedPoint` — the channel specialization.
* Numbered theorem: `IsPositiveMap.wolf_prop_6_8` —
  `TNLean.Channel.WolfChapter6Wrappers`.

### Wolf Corollary 6.8 (Linearly independent stationary states) — KEY LEMMA FORMALIZED (basis/dimension statement open)

In `TNLean.Channel.FixedPoint.StationarySpan`:

* `IsStationaryDensity` — predicate for a stationary density matrix (PSD,
  trace 1, fixed by the map).
* `IsPositiveMap.fixedPointsSubmodule` — the fixed-point subspace as a
  `Submodule ℂ M_D(ℂ)`.
* `IsPositiveMap.span_posSemidefFixedPointsSet_eq_fixedPointsSubmodule` — the fixed-point
  subspace is spanned (over ℂ) by its positive semidefinite elements (this is
  the key lemma for the corollary).
* The corollary's full statement with basis and dimension (Wolf's form) remains
  to be proved; the spanning lemma is the load-bearing step.

### Wolf Corollary 6.6 (projected support corner) — FORMALIZED (Kraus case)

Wolf states the corollary for a positive trace-preserving map whose trace
adjoint is unital and satisfies the Schwarz inequality; complete positivity is
an example there, not a hypothesis. The declarations below assume a
trace-preserving Kraus family, so they establish the completely positive case
only.

In `TNLean.Channel.FixedPoint.CornerFixedPoints`:

* `Kraus.cornerFixedPointsStarSubalgebra` — for a trace-preserving Schwarz map
  `T* = adjointMap K` (unitality of `T*` is `IsTP K`) and a PSD fixed point `ρ`
  of `T = map K` with support projection `Q := stationaryProj`, the
  corner-restricted fixed-point set `{Y ∈ Q M_D(ℂ) Q | Q T*(Y) Q = Y}` is a
  `StarSubalgebra` of the corner algebra `Q M_D(ℂ) Q`.
* `Kraus.mem_cornerFixedPointsStarSubalgebra` — membership is exactly the
  corner fixed-point condition `Q (adjointMap K Y) Q = Y`.

The proof compresses the supported family `Q Kᵢ Q` to the support sector via
`exists_compressedTensor_of_supported_projection_with_letter_and_isometry`,
where the compressed map is unital with a positive-definite fixed point, applies
Wolf Theorem 6.12 there (`Kraus.adjointFixedPointsStarSubalgebra`), and transports
the `*`-algebra structure back along the compression isomorphism.

### Wolf Theorem 6.14 (density-block form of fixed points) — FORMALIZED

The general finite-dimensional convergence argument is provided by
`LinearMap.HasBoundedOrbits.tendsto_birkhoffAverage_meanErgodicProjection` in
`TNLean.Analysis.MeanErgodic`. It constructs the Cesàro projection onto the
fixed-point space for an endomorphism with bounded orbits. The matrix
specialization is provided by
`IsPositiveMap.hasBoundedOrbits_of_tracePreserving`,
`IsPositiveMap.meanErgodicProjection_isPositiveMap`, and
`IsTracePreservingMap.meanErgodicProjection_isTracePreservingMap`: a positive
trace-preserving matrix endomorphism has bounded orbits, and its mean-ergodic
projection is a positive trace-preserving retraction onto its fixed-point
space. If the original endomorphism is unital, the projection is unital as
well.

The trace-pairing adjoint step is now complete.  The adjoint of the
mean-ergodic projection is a positive unital idempotent retraction onto the
fixed-point space of the adjoint endomorphism.  Combining this retraction with
the full-support star-algebra description, restricting to maximal stationary
support, and adjoining the complementary zero summand gives the full statement
of Theorem 6.14 and Equation (6.63).

In `TNLean.Channel.FixedPoint.StationarySupportRestriction`:

* `IsPositiveMap.map_posSemidef_supported_on_fixedPoint_support` — the order
  argument of Wolf Proposition 6.10 for a positive matrix supported on the
  support of an arbitrary stationary positive matrix.
* `IsPositiveMap.map_supported_on_fixedPoint_support` — the extension to every
  supported matrix by decomposition into four positive matrices.
* `IsPositiveMap.stationarySupportCompression_isPositiveMap` and
  `IsPositiveMap.stationarySupportCompression_isTracePreservingMap` — the
  supported compression is positive and trace-preserving.
* `IsPositiveMap.exists_posDef_fixedPoint_stationarySupportCompression` — the
  compressed stationary matrix is positive definite.
* `IsPositiveMap.fixedPoint_iff_exists_fixedPoint_stationarySupportCompression`
  — the scope-restricted auxiliary form of Wolf Equation (6.51), conditional
  on a fixed-point space already known to be supported in the chosen corner.
* `IsPositiveMap.exists_maximalSupportCompression` — the source-faithful
  restriction theorem: it chooses $T_\infty(\mathbf 1)$ through
  `IsPositiveMap.exists_maximalSupport_fixedPoint` and packages positivity,
  trace preservation, a positive-definite compressed fixed point,
  Equation (6.52), and the complementary zero summand of Equation (6.51).

In `TNLean.Channel.FixedPoint.FullSupportBlockRetraction`:

* `IsPositiveMap.exists_block_densities_of_adjoint_meanErgodicProjection` —
  when the positive trace-preserving map has a positive definite fixed point
  and its trace adjoint satisfies the Schwarz inequality, the adjoint
  mean-ergodic projection is a positive retraction onto the adjoint
  fixed-point star-algebra and has the weighted partial-trace block form of
  Wolf Equation (1.40).

In `TNLean.Channel.FixedPoint.TraceAdjointDensityBlocks`:

* `IsPositiveMap.exists_block_densities_of_meanErgodicProjection` — under the
  same full-support hypotheses, the mean-ergodic projection has the
  Schrödinger-picture density-block form
  `U (⊕_k σ_k ⊗ tr_{m_k}((U† B U)_{kk})) U†`, and the fixed-point space is
  `U (⊕_k σ_k ⊗ M_{d_k}(ℂ)) U†`.

In `TNLean.Channel.FixedPoint.SupportCompressedDensityBlocks`:

* `IsPositiveMap.exists_block_densities_of_maximalSupportCompression` — the
  maximal-support compression has positive-definite density blocks, and its
  fixed points correspond exactly to the ambient fixed points carried by the
  support isometry.

In `TNLean.Algebra.MatrixGramUnitary`:

* `Matrix.exists_unitary_zero_extension_eq` — an isometric inclusion extends
  to an ambient unitary that identifies every compressed matrix with one
  complementary zero block followed by that matrix.

In `TNLean.Channel.FixedPoint.WolfTheorem614`:

* `IsPositiveMap.exists_fixedPoints_densityBlocks_with_zero` — for every
  positive trace-preserving matrix endomorphism whose trace adjoint satisfies
  the Schwarz inequality, the fixed-point space is the unitary conjugate of
  one complementary zero summand followed by positive-definite trace-one
  density blocks, exactly as in Wolf Equation (6.63).

In `TNLean.Channel.FixedPoint.DirectSumBlockRetraction`:

* `Matrix.IsPositiveDirectSumMap.exists_block_densities_of_fixedPoints` — the
  full-support consequence for a finite direct sum of full matrix algebras.

In `TNLean.Channel.FixedPoint.WedderburnDecomp`:

* `Kraus.starSubalgebra_isSemisimpleRing` — every finite-dimensional
  `*`-subalgebra of `M_D(ℂ)` is semisimple.
* `Kraus.FixedPointAlgebra` — type alias for the carrier of the
  adjoint-fixed-point `StarSubalgebra`.
* `Kraus.fixedPointAlgebra_isSemisimpleRing` — the adjoint-fixed-point
  algebra is semisimple.
* `Kraus.fixedPointAlgebra_wedderburnArtin` — abstract Wedderburn--Artin:
  `Fix(T*) ≃ₐ[ℂ] Π i, M_{d_i}(ℂ)`.
* `Kraus.IsWedderburnBlockDecomp` — bundled decomposition data consisting of
  block sizes, multiplicities, an ambient-dimension bound, and an algebra
  isomorphism to a product of full matrix algebras.
* `Kraus.adjointFixedPoints_wedderburnDecomp` — existence of this
  decomposition data for the adjoint-fixed-point algebra.

In `TNLean.Channel.FixedPoint.BlockForm` (unital case, positive definite fixed
point of the pre-dual, no zero block):

* `Kraus.adjointFixedPoints_blockDiagonal_iff` — the unitary realization
  `Fix(T*) = U (⊕_k 1_{m_k} ⊗ M_{d_k}) U†` with `∑_k d_k m_k = D`.
* `Kraus.fixedPoints_blockDiagonal_iff` — the companion for the fixed points
  of a unital Kraus map.

In `TNLean.Channel.FixedPoint.CornerBlockForm` (corner-restricted case, any
positive semidefinite fixed point):

* `Kraus.cornerFixedPoints_blockDiagonal_iff` — the corner-restricted
  fixed-point set is carried by an isometry `W` (`W† W = 1`, `W W† = Q`) onto
  `⊕_k 1_{m_k} ⊗ M_{d_k}` with `∑_k d_k m_k = r` for the support-sector
  dimension `r ≤ D`; embedded in `M_D(ℂ)` this is the block representation
  in the `∑_k d_k m_k ≤ D` form. The equivalence characterizes the
  corner-restricted set only; extending by zero on the complement does not
  produce ambient fixed points in general.

The full Wolf statement is therefore complete.  Its application to the
transported sector maps of arXiv:1606.00608 is a separate tensor-attached
problem: one must still prove the channel hypotheses for those maps on the
whole direct-sum algebras.  This remaining boundary is recorded in
`docs/paper-gaps/cpsv16_vertical_sector_invertibility.tex`.

### Wolf Corollary 6.7 (faithful fixed-point conjugation) — FORMALIZED (Kraus case)

In `TNLean.Channel.FixedPoint.Corollaries`:

* `Kraus.rightCanonicalGauge` — the gauged family `ρ^{-1/2} K_i ρ^{1/2}`.
* `Kraus.weightedFixedPointsStarSubalgebra` — if `T(ρ) = ρ` with `ρ > 0`,
  then `ρ^{-1/2} Fix(T) ρ^{-1/2}` is a `StarSubalgebra`.
* `Kraus.mem_weightedFixedPointsStarSubalgebra_iff` — membership is
  equivalent to saying that `ρ^{1/2} X ρ^{1/2}` is fixed by the original map.

In `TNLean.Channel.FixedPoint.WeightedCornerFixedPoints` (singular case, any
positive semidefinite fixed point, restricted to corner-supported fixed
points):

* `Kraus.weightedCornerFixedPointsStarSubalgebra` — the corner elements `Y`
  with `√ρ Y √ρ` fixed by the map form a star-subalgebra of the corner
  algebra `Q M_D(ℂ) Q`, realizing `ρ^{-1/2} {X | T(X) = X, Q X Q = X} ρ^{-1/2}`
  with the inverse square root taken on the support of `ρ`.
* `Kraus.exists_weightedCorner_sqrt_eq_of_fixedPoint` — conjugation by `√ρ`
  maps the carrier onto the corner-supported fixed points.

In `TNLean.Channel.FixedPoint.MaximalSupportBasic` (the maximal-support property
for arbitrary positive trace-preserving maps):

* `Kraus.stationaryProj_absorb_of_le` — for positive semidefinite $P \preceq \rho$
  the support projection of $\rho$ absorbs $P$.
* `IsPositiveMap.exists_maximalSupport_fixedPoint` — for an arbitrary positive
  trace-preserving map, the fixed point $T_\infty(\mathbf 1)$ has support carrying every
  fixed point, as in Wolf Proposition 6.9.

In `TNLean.Channel.FixedPoint.MaximalSupport` (the Kraus specialization and
the removal of the corner restriction):

* `Kraus.exists_maximalSupport_fixedPoint` — a positive semidefinite fixed point
  $\rho_0$ whose
  support projection $Q_0$ satisfies $Q_0 X Q_0 = X$ for every fixed point $X$.
* `Kraus.exists_maximalSupport_weightedCorner_sqrt_eq` — at $\rho_0$, conjugation
  by $\sqrt{\rho_0}$ maps the corner carrier onto the full fixed-point set,
  realizing $\rho_0^{-1/2}\,\{X \mid T(X) = X\}\,\rho_0^{-1/2}$ without a support
  restriction.

In `TNLean.Channel.FixedPoint.MaximalRank` (the transfer to every fixed point
of maximum rank):

* `Kraus.rank_stationaryProj`, `Kraus.trace_stationaryProj` — the support
  projection of a positive semidefinite matrix has the rank of the matrix,
  and its trace is that rank.
* `Kraus.maximalSupport_of_maximalRank` — if the rank of a positive
  semidefinite fixed point $\rho$ bounds the rank of every fixed-point
  density matrix, its support projection $Q$ satisfies $Q X Q = X$ for every
  fixed point $X$.
* `Kraus.exists_weightedCorner_sqrt_eq_of_maximalRank` — at every such
  $\rho$, conjugation by $\sqrt{\rho}$ maps the corner carrier onto the full
  fixed-point set, realizing $\rho^{-1/2}\,\{X \mid T(X) = X\}\,\rho^{-1/2}$
  with the inverse square root taken on the support of $\rho$.

The scope is the Kraus (completely positive) case of the source's Schwarz
hypothesis, as recorded for the other results of this section; the source's
maximum-rank fixed-point density matrix satisfies the rank hypothesis, with
unit trace of $\rho$ itself not needed for the conclusion
(see `docs/paper-gaps/wolf_cor67_maximal_support_restriction.tex`).

### Conditional expectation used in Wolf Theorem 6.14 — FORMALIZED

In `TNLean.Channel.FixedPoint.ConditionalExpectation`:

* `Kraus.IsConditionalExpectation` — a positive, idempotent, unital matrix
  map whose range is contained in a star-subalgebra and which fixes that
  subalgebra pointwise, following Wolf Proposition 1.5 and Equation (1.40).
* `Kraus.scalarConditionalExpectation` — the linear map
  `E_σ(X) = (tr(σ X) / tr(σ)) • 1` for the scalar fixed-point algebra case.
* `Kraus.scalarConditionalExpectation_idempotent` — `E_σ² = E_σ`.
* `Kraus.scalarConditionalExpectation_unital` — `E_σ(1) = 1`.
* `Kraus.scalarConditionalExpectation_absorbs_adjointMap` —
  `E_σ(T*(X)) = E_σ(X)` when `T(σ) = σ`.
* `Kraus.adjointMap_absorbs_scalarConditionalExpectation` —
  `T*(E_σ(X)) = E_σ(X)` when `T` is TP.
* `Kraus.scalarConditionalExpectation_isConditionalExpectation` —
  bundles everything into `IsConditionalExpectation` for the scalar case.
* `Kraus.meanErgodicAdjoint_isConditionalExpectation` — the trace adjoint of
  the mean-ergodic projection is a conditional expectation onto the adjoint
  fixed-point star-subalgebra.

The general conditional expectation is the trace adjoint of the mean-ergodic
projection, which is positive, idempotent, unital, and fixes exactly the fixed
points of `T*`; the star-algebra structure follows from Theorem 6.12. This is
the conditional-expectation step in the proof of Theorem 6.14. The theorem's
explicit density-block formula is developed in
`TNLean.Channel.FixedPoint.FullSupportBlockRetraction`.

### Wolf Theorem 6.15 (Unique fixed point from full Kraus-word span) — NOT FORMALIZED

The source assumes that the homogeneous words of some fixed length in the
Kraus operators span the full matrix algebra. It concludes that the channel
has a unique fixed density matrix and that this density matrix is positive
definite. No Lean theorem currently has this hypothesis and conclusion.

---

## Section 6.5 Cycles and recurrences

### Wolf Theorem 6.16 (Structure of cycles) — PARTIALLY FORMALIZED

* Reusable formalization for the permutation-of-blocks direction lives in
  `TNLean.Channel.Peripheral.CyclicDecomposition` and
  `TNLean.Channel.Peripheral.Cycles`:
  - `preserves_corner_pow_orderOf_of_perm_decomp` — permutation-of-blocks
    iterate preserves each corner after `orderOf σ` steps.
  - `CycleStructure T` — bundled block-permutation data: a finite family of
    orthogonal projections `P : ι → M_D(ℂ)`, a permutation `σ : Equiv.Perm ι`,
    the compatibility `T (P (σ k)) = P k`, and the multiplicative-domain
    factorisations `T (P k * X) = T (P k) * T X` and `T (X * P k) = T X * T (P k)`.
  - `CycleStructure.map_proj_pow` — `T^n (P (σ^n k)) = P k`.
  - `CycleStructure.pow_orderOf_apply_proj` — `(T ^ orderOf σ) (P k) = P k`.
  - `CycleStructure.preserves_corner_pow_orderOf` — `T ^ orderOf σ` preserves
    each corner `P k · M_D(ℂ) · P k`, the corner-preservation half of
    Theorem 6.16 in its permutation-of-blocks form.
  - `CycleStructure.ofPermDecomp` — constructor from explicit permutation data.

* Multi-cycle block-permutation data (disjoint union of cycles with possibly
  distinct periods) is formulated in `TNLean.Channel.Peripheral.MultiCycleDecomposition`:
  - `MultiCycleDecomposition T` — bundled data: a finite cycle index `ι`, a
    per-cycle period `period : ι → ℕ` (each nonzero), a projection family
    `P : (c : ι) → Fin (period c) → M_D(ℂ)`, the per-cycle cyclic action
    `T (P c (k + 1)) = P c k`, and the multiplicative-domain factorisations.
  - `MultiCycleDecomposition.preserves_corner_pow_period` — per-cycle corner
    preservation: `T ^ (period c)` preserves each corner `P c k · M_D(ℂ) · P c k`.
  - `MultiCycleDecomposition.preserves_corner_pow_of_dvd` — common-period
    corner preservation: whenever every `period c` divides `N`, `T ^ N`
    preserves every corner.
  - `MultiCycleDecomposition.toCycleStructure` — flattens a multi-cycle
    decomposition to a single `CycleStructure` on the sigma index
    `Σ c : ι, Fin (period c)`, using `Equiv.Perm.sigmaCongrRight` of
    per-cycle cyclic shifts.

* The remaining **existence direction** — that every trace-preserving positive
  Schwarz map admits a `MultiCycleDecomposition` on its asymptotic image, with
  the cycles coming from the now-formalized density-block decomposition of the
  fixed-point space — is left to future work.

---

## The quantum Perron–Frobenius theorem

* `quantum_perron_frobenius` — `TNLean.QPF.Assembly`
  Combines existence + positive definiteness + uniqueness (Wolf Theorem 6.3).

* `injective_transfer_unique_fixed_point'` — same, without `0 < D` hypothesis.
-/
