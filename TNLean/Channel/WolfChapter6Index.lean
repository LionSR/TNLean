/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TNLean.Channel.FixedPoint.Algebra
import TNLean.Channel.FixedPoint.Cesaro
import TNLean.Channel.FixedPoint.StationarySupport
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

/-!
# Wolf Chapter 6 — Spectral Properties: Public Theorem Index

This module serves as a **navigational index** that maps the formalized theorems
in this project to the numbering in:

> M. Wolf, *Quantum Channels & Operations: Guided Tour* (2012), Chapter 6.

Each entry lists the Wolf result, its status (fully formalized / partially
formalized / not yet formalized), and the Lean declaration(s) that correspond.

No new proofs are introduced here; this is a documentation-only index module.

---

## §6.2 Irreducible maps and Perron–Frobenius theory

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

Supporting infrastructure in `TNLean.Channel.Irreducible.Ergodicity`:
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

* Scalar case: `isIrreducibleMap_smul` — `TNLean.Channel.PerronFrobenius.Existence`
* Similarity case: `isIrreducibleMap_similarity` — `TNLean.Channel.Irreducible.Similarity`
* Full Wolf form `T' = c C⁻¹ T(C · C†) C⁻†`:
  `isIrreducibleMap_full_similarity` (and the stronger
  `isIrreducibleMap_similarity_smul`) — `TNLean.Channel.Irreducible.Similarity`

### Wolf Theorem 6.6 (Peripheral spectrum of irreducible Schwarz maps)

**Item 1** (roots-of-unity structure): PARTIALLY FORMALIZED
* `peripheral_isRootOfUnity_of_pow_eigenvalue` — `TNLean.Channel.Peripheral.Spectrum`

**Items 2–4** (non-degeneracy, unitary eigenvector, cyclic projections):
PARTIALLY FORMALIZED in `TNLean.Channel.Peripheral.CyclicDecomposition`.

---

## §6.3 Primitive maps

### Wolf Theorem 6.7 (Primitive maps, 4 equivalent conditions)

**Item 4** (trivial peripheral spectrum, PD eigenvector):
* `IsPrimitive` — `TNLean.Channel.Peripheral.Spectrum`
* `isPrimitive_of_compl_eigenvalues_lt_one` / `compl_eigenvalue_norm_lt_one_of_primitive`

Other items: PARTIALLY via spectral gap infrastructure in `TNLean.Spectral.*`.

### Wolf Theorem 6.8 (CP primitive maps, Kraus span characterizations)

* `IsPrimitivePaper` — `TNLean.Wielandt.Primitivity.PaperDefinitions`
  (item 3: `Kₘ = M_d(ℂ)` for `m ≥ q`)
* Pairwise equivalences from Proposition 3 assembly:
  * `primitivePaper_iff_hasEventuallyFullKrausRank`
  * `primitivePaper_iff_stronglyIrreducible`
  * `hasEventuallyFullKrausRank_iff_isNormal`
  (in `TNLean.Wielandt.Primitivity.Equivalence`)
* Packaged Wolf-facing wrappers:
  * `wolf_theorem_6_8_krausSpan`
  * `wolf_theorem_6_8_conjunction`
  (in `TNLean.Wielandt.Primitivity.Equivalence`)

### Wolf Theorem 6.9 (Quantum Wielandt inequality)

Current paper-facing wrappers live in `TNLean.Wielandt.PaperResults.WielandtInequality`:
* `qIndex_le_iIndex_of_isPrimitivePaper`
* `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit` /
  `iIndex_le_of_isPrimitivePaper_of_isUnit`
* `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` /
  `iIndex_le_sq_of_noninvertible_eigenvector`

The auxiliary aperiodicity-based assembly remains in
`TNLean.Wielandt.QuantumWielandt`; it is not the default paper-facing
endpoint.

---

## §6.4 Fixed points

### Wolf §6 stationary-support package (Props. 6.9--6.11, Lems. 6.4--6.5)

In `TNLean.Channel.FixedPoint.StationarySupport`:

* `Channel.support_proj_fixed` — support projection of a PSD fixed point is
  invariant under the compressed channel action.
* `Channel.stationarySupport` — support projection of the unique density-matrix
  fixed point of an irreducible channel.
* `Channel.stationarySupport_eq_one` — irreducible channels have full
  stationary support.
* TODO: non-vacuous formalizations of Wolf Prop. 6.9 and Prop. 6.10
  (`irreducible_iff_support_full`, `stationary_support_minimal`) remain to be
  reinstated.

### Wolf Theorem 6.12 (Fixed points form a *-algebra) — FORMALIZED

In `TNLean.Channel.FixedPoint.Algebra`:

* `Kraus.fixedPointsStarSubalgebra` — Schrödinger-picture form:
  if `map K` is unital and `adjointMap K` has a positive definite fixed point,
  the fixed points of `map K` form a `StarSubalgebra`.
* `Kraus.adjointFixedPointsStarSubalgebra` — Heisenberg-picture form:
  if `adjointMap K` is unital (`IsTP K`) and `map K` has a positive definite
  fixed point, the fixed points of `adjointMap K` form a `StarSubalgebra`.
* `Kraus.fixedPoints_in_multiplicativeDomain` — the key intermediate step:
  every fixed point of the adjoint map lies in the multiplicative domain.
* `Kraus.fixedPoints_starSubalgebra` / `Kraus.mem_fixedPoints_starSubalgebra`
  — prompt-facing wrapper with Wolf naming convention.

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
  — under the hypotheses of Thm 6.12, the full adjoint fixed-point
  `*`-subalgebra coincides with the Kraus commutant.

### Wolf Theorem 6.10 (Brouwer's fixed point theorem)

* `brouwer_fixedPoint_densityMatrices` — `TNLean.Axioms.BrouwerFixedPoint`

### Wolf Theorem 6.11 (Stationary states)

* Via Brouwer: `exists_posSemidef_eigenvector` (for general positive maps)
* Via Cesàro: `IsChannel.exists_posSemidef_fixedPoint` — `TNLean.Channel.FixedPoint.Cesaro`

### Wolf Proposition 6.8 (Positive fixed-points)

* `IsChannel.posSemidef_parts_of_hermitian_fixedPoint` — `TNLean.Channel.FixedPoint.Cesaro`

---

## §6.5 Cycles and recurrences

### Wolf Theorem 6.16 (Structure of cycles)

* Partially formalized in `TNLean.Channel.Peripheral.CyclicDecomposition`.
* Reusable infrastructure for the multi-cycle direction:
  `preserves_corner_pow_orderOf_of_perm_decomp` (permutation-of-blocks iterate
  preserves each corner after `orderOf` steps).

---

## The quantum Perron–Frobenius theorem

* `quantum_perron_frobenius` — `TNLean.QPF.Assembly`
  Combines existence + positive definiteness + uniqueness (Wolf Thm 6.3).

* `injective_transfer_unique_fixed_point'` — same, without `0 < D` hypothesis.
-/
