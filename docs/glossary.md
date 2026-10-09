# Concept glossary

TNLean keeps several source-faithful formulations of the same broad mathematical
ideas. They are not interchangeable merely because their names are similar. This
glossary identifies the public entry points, records the bridges that may be used,
and states the hypotheses or known gaps that prevent stronger identifications.
Declarations under `QICLean/` paths moved to the companion
[QICLean](https://github.com/LionSR/QICLean) library in the quantum-channel
extraction; TNLean imports them through its Lake dependency, so they remain
usable here under the same names.

For new declarations, prefer namespace overloading (`Kraus.IsInjective`,
`MPSChainTensor.IsInjective`, and so on) rather than putting the carrier name into
the predicate name. Preserve a paper's established terminology when a declaration
is deliberately source-faithful.

## Two-site matrix product unitaries

### `MPOTensor.TwoSiteStandardFormData`

- **Declaration:** `MPOTensor.TwoSiteStandardFormData W u v`, for a tensor
  `W : MPOTensor (d * d) D`, a gate from the physical pair to the ordered
  intermediate pair `(ℓ,r)`, and a gate from `(r,ℓ)` back to the physical pair.
- **Defined in:** `TNLean/MPS/MPU/TwoSiteStandardForm.lean`.
- **Meaning:** the dimensions are positive, both supplied gates are unitary
  between their coordinate spaces, the second gate contracts as
  $v^{(i_1,i_2)}_{s,l}=\sum_\beta (X_1)_{(i_1,\beta),s}(X_2)_{(\beta,i_2),l}$,
  and the open tensor contracts as
  $W^{(i_1,i_2),(j_1,j_2)}_{\alpha,\gamma}
  =\sum_{l,s}(X_2)_{(\alpha,i_1),l}u_{(l,s),(j_1,j_2)}
  (X_1)_{(i_2,\gamma),s}$.
- **Source:** arXiv:1703.09188, equations `uuvv` and `StandardForm`, and
  Definition `SF`, `Papers/1703.09188/paper_v2.tex:532-543,603-622`.
- **Sanctioned bridge:**
  `MPOTensor.IsMPUCanonicalFormII.twoSiteStandardFormData` constructs this
  datum for `blockTwo U` when `U` is simple and carries the full-support
  canonical-form-II presentation.
  `MPOTensor.IsMPUCanonicalFormII.exists_twoSiteStandardFormData_blockTensor`
  chooses a positive simple block of length at most $D^4$ and relates its
  two-site block to direct blocking at length $2k$ by an explicit physical
  relabeling.
- **Caveat:** the generic datum does not assume `W.IsMPU` or identify its
  supplied gates with a selected source-cut factorization. The open equation
  has input pair `(j₁,j₂)` in that order; the alternative reflected periodic
  equation is source-specific. The construction from canonical form II is
  restricted as recorded in `docs/paper-gaps/mpu_canonical_form_full_support.tex`.

### Source factors under virtual conjugation

- **Declarations:**
  `MPOTensor.transported_source_factor_premises_at_selected_ranks` and
  `MPOTensor.IsMPUCanonicalFormII.exists_selected_source_factor_unitary_gauges`.
- **Defined in:** `TNLean/MPS/MPU/VirtualSourceFactorTransport.lean` and
  `TNLean/MPS/MPU/SelectedSourceFactorVirtualGauge.lean`.
- **Meaning:** If two simple canonical-form-II tensors are related by a
  unitary virtual conjugation, their selected source factors obey four exact
  identities after identifying their equal source-cut ranks. The two
  source-rank changes are unitary; no positive scalar remains because both
  second-cut left factors are isometries.
- **Source:** arXiv:1703.09188, Theorem `FundamentalMPU`,
  `Papers/1703.09188/paper_v2.tex:624-648`, for the local gauge diagrams;
  Proposition IV.5, lines 786–812, for raw rank transport. The scalar-free
  comparison is the normalized specialization of arXiv:2502.20257,
  Lemma `lem:deco`, lines 1052–1066.
- **Caveat:** The two canonical-form-II weights may be different. This is a
  forward comparison given a virtual conjugation, not a converse asserting
  equality of the original periodic operators at every length.

## Normality

### `Kraus.IsNormal`

- **Declaration:** `Kraus.IsNormal (A : MPSTensor d D) : Prop`.
- **Defined in:** `QICLean/Kraus/Injectivity.lean`.
- **Meaning:** there is a positive word length `N` for which the length-`N`
  products of the matrices of `A` span the full `D × D` matrix algebra; equivalently,
  `A` becomes injective after blocking `N` sites.
- **Source:** Sanz--Pérez-García--Wolf--Cirac, arXiv:0909.5347, definition after
  equation (1), `Papers/0909.5347/main.tex:387-419`; see also
  Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:1815-1830`.
- **Sanctioned bridges:**
  `MPSTensor.hasEventuallyFullKrausRank_iff_isNormal`,
  `Kraus.IsInjective.isNormal`, and
  `MPSTensor.IsNormalTensor.isNormal`.
- **Caveat:** `MPSTensor.IsNormalTensor.isNormal` derives nonzero bond dimension
  from the spectral-radius-one clause; it requires no external positivity
  assumption. There is no equivalence theorem between `Kraus.IsNormal` and
  `MPSTensor.IsNormalTensor`, and this glossary makes no such claim. In
  particular, the reverse direction would have to recover the CPSV
  spectral-radius normalization, not just eventual block injectivity.

### `MPSTensor.IsNormalTensor`

- **Declaration:**
  `MPSTensor.IsNormalTensor (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/CanonicalForm/Definitions.lean`.
- **Meaning:** the CPSV normal-tensor condition: no nontrivial invariant
  orthogonal projection, transfer-map spectral radius exactly one, and no
  unit-modulus eigenvalue other than one.
- **Source:** Cirac--Pérez-García--Schuch--Verstraete, arXiv:1606.00608,
  Definition NT, `Papers/1606.00608/MPDO-22-12-17-2.tex:231-235`.
- **Sanctioned bridges:** `MPSTensor.IsNormalTensor.exists_tpGauge`,
  `MPSTensor.IsNormalTensor.isNormal`, and
  `MPSTensor.IsNormalTensor.selfOverlap_tendsto_one`, all in
  `TNLean/MPS/CanonicalForm/NormalTensorGauge.lean`.
- **Caveat:** `exists_tpGauge` and `isNormal` derive nonzero bond dimension
  internally from spectral normality. Other asymptotic consequences may still
  expose a positive-dimension instance in their signatures. These bridges run
  only from the normalized spectral predicate to downstream algebraic or
  asymptotic consequences; they do **not** establish an equivalence with
  `Kraus.IsNormal`.

### Basis-level normality

- **Declarations:**
  `MPSTensor.IsCPSVBasisOfNormalTensors A blocks` in
  `TNLean/MPS/CanonicalForm/Definitions.lean`, and
  `MPSTensor.IsBNT A_total g dim A_bnt` in `TNLean/MPS/BNT/Basic.lean`.
- **Meaning:** both say that a finite family of normal blocks spans every
  positive-length matrix-product-vector family and is eventually linearly
  independent. The first uses `IsNormalTensor`; the second uses
  `Kraus.IsNormal`.
- **Sources:** arXiv:1606.00608,
  `Papers/1606.00608/MPDO-22-12-17-2.tex:271-274`, and arXiv:2011.12127,
  Definition 4.2, `Papers/2011.12127/TN-Review-main.tex:1846-1850`.
- **Sanctioned bridges:**
  `MPSTensor.IsCPSVBasisOfNormalTensors.blocks_dim_pos` records block positivity
  explicitly, while `MPSTensor.IsNormalTensor.isNormal` now derives it directly
  from each block's spectral normality.
  `MPSTensor.IsCPSVBasisOfNormalTensors.isBNT` then forgets the spectral
  normality data to produce `MPSTensor.IsBNT`.
- **Caveat:** this is a one-way implication, not an equivalence. Their block
  index packaging also differs: the CPSV predicate uses a sigma type of varying
  dimensions, whereas `IsBNT` takes an explicit dimension family. Algebraic
  eventual block injectivity does not recover spectral-radius-one normalization
  or peripheral-spectrum data. Do not treat the predicates as aliases.

### `MPSTensor.IsBNTSectorPresentation`

- **Declaration:** `MPSTensor.IsBNTSectorPresentation A P : Prop` for a
  sector decomposition `P`.
- **Defined in:** `TNLean/MPS/CanonicalForm/BNTRefinement.lean`.
- **Meaning:** `P` presents `A` by a basis of normal tensors grouped into
  phase classes with copy weights: at least one representative occurs, the
  presentation has the same positive-length matrix-product vectors as `A`,
  every representative is a normal tensor, and the representative families are
  eventually linearly independent. Copy weights are nonzero and multiplicities
  are positive by construction of the sector decomposition, in line with the
  nonzero-coefficient convention of
  `docs/audits/2026-08-23_nonzero_coefficient_convention.md`.
- **Sources:** arXiv:1606.00608, lines 217--246 (canonical-form convention),
  eq. `II_CF1`, lines 265--301, and lines 1135--1148.
- **Sanctioned bridges:**
  `MPSTensor.IsBNTSectorPresentation.isCPSVBasisOfNormalTensors` forgets the
  grouping to the literal Definition 2.4 interface; every canonical-form datum
  with at least one block yields a presentation through
  `MPSTensor.CPSVCanonicalFormData.isBNTSectorPresentation`, and presentations
  of the same tensor agree up to permutation, dimension identification, gauge,
  and phase through `MPSTensor.IsBNTSectorPresentation.equiv_of_sameMPV₂Pos`.
- **Caveat:** this is the grouped presentation used by the sector fundamental
  theorem and the MPDO simplicity predicate, not a second BNT definition; the
  literal interface remains `MPSTensor.IsCPSVBasisOfNormalTensors`.

## Periodic irreducible blocks

### `MPSTensor.IsSpectrallyPeriodic`

- **Declaration:**
  `MPSTensor.IsSpectrallyPeriodic (m : ℕ) (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/Periodic/Defs.lean`.
- **Meaning:** the transfer map is irreducible, has spectral radius one, and has
  unit-circle eigenvalues exactly the `m`-th roots of unity, with `m > 0`.
  No trace-preserving normalization is assumed.
- **Source:** de las Cuevas--Cirac--Schuch--Pérez-García, arXiv:1708.00029,
  lines 248--261.
- **Sanctioned bridge:**
  `MPSTensor.IsSpectrallyPeriodic.exists_isPeriodic_tpGauge` in
  `TNLean/MPS/Periodic/Normalization.lean` gives a pure-similarity
  trace-preserving representative. For a multiplicity-bearing sector
  decomposition, `MPSTensor.SectorDecomposition.exists_isPeriodic_replaceBasis`
  applies these gauges simultaneously and leaves all multiplicities and weights
  unchanged;
  `MPSTensor.PeriodicOverlapHypothesis.ofSpectrallyPeriodicSectorDecompositions`
  is the corresponding overlap-hypothesis bridge.
- **Caveat:** general invertible similarities do not preserve
  left-canonicality. The bridge is therefore one-way into `IsPeriodic`, not an
  equivalence between the two predicates.

### `MPSTensor.IsPeriodic`

- **Declaration:** `MPSTensor.IsPeriodic (m : ℕ) (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/Periodic/Defs.lean`.
- **Meaning:** the tensor is irreducible and left-canonical, `m > 0`, and the
  peripheral eigenvalues are exactly the `m`-th roots of unity.
- **Source:** the trace-preserving form obtained in arXiv:1708.00029,
  lines 313--332.
- **Caveat:** this predicate is the normalized input to the periodic overlap
  theory. It must not be substituted for the unnormalized source assumptions
  without applying the pure Perron normalization theorem.

## Primitivity

The unqualified canonical predicate is the generic transfer-map predicate
`_root_.IsPrimitive`. The MPS predicates below retain distinct source or proof
normalizations.

### `_root_.IsPrimitive`

- **Declaration:**
  `_root_.IsPrimitive (E : V →ₗ[ℂ] V) : Prop`.
- **Defined in:** `QICLean/Channel/Peripheral/Spectrum.lean`.
- **Meaning:** the unit-circle eigenvalue set of `E` is exactly `{1}`.
- **Source:** Wolf, *Quantum Channels & Operations: Guided Tour*, §6.3,
  Theorem 6.7; compare arXiv:2011.12127 §IV.
- **Sanctioned bridges:** `_root_.isPrimitive_iff` and
  `_root_.isPrimitive_iff_period_one`.
- **Caveat:** `_root_.isPrimitive_iff_period_one` requires a specified nonzero
  fixed point and finiteness of `peripheralEigenvalues E`; it is not an
  unconditional period-one characterization of an arbitrary linear map. By
  itself `IsPrimitive` does not assert irreducibility, existence of a
  positive-definite fixed point, trace preservation, or spectral radius one.
  Those facts must be supplied separately where required.

### `MPSTensor.IsPeripherallyPrimitive`

- **Declaration:**
  `MPSTensor.IsPeripherallyPrimitive (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/Wielandt/Primitivity/Definitions.lean`.
- **Meaning:** a reducible MPS terminology alias for
  `_root_.IsPrimitive (Kraus.transferMap A)`.
- **Source:** Wolf §6.3, Theorem 6.7, and arXiv:0909.5347 Proposition 3(c).
- **Sanctioned bridge:**
  `MPSTensor.isPeripherallyPrimitive_of_isPrimitivePaper`.
- **Caveat:** the last bridge requires `[NeZero D]` and the left-canonical
  normalization `∑ i, (A i)ᴴ * A i = 1`.

### `MPSTensor.IsPrimitivePaper`

- **Declaration:**
  `MPSTensor.IsPrimitivePaper (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/Wielandt/Primitivity/Definitions.lean`.
- **Meaning:** the uniform spreading condition from Proposition 3(a): at one
  positive length `q`, all nonzero virtual vectors are spread by length-`q`
  Kraus words to the whole virtual space.
- **Source:** Sanz--Pérez-García--Wolf--Cirac, arXiv:0909.5347,
  Proposition 3(a), `Papers/0909.5347/main.tex:403-409` and `:501-509`;
  Wolf Chapter 6, Theorem 6.8.
- **Sanctioned bridges:**
  `MPSTensor.primitivePaper_iff_hasEventuallyFullKrausRank`,
  `MPSTensor.primitivePaper_iff_stronglyIrreducible`, and
  `MPSTensor.wolf_theorem_6_8_kraus_span`.
- **Caveat:** each stated equivalence requires `[NeZero D]` and the explicit
  left-canonical normalization `∑ i, (A i)ᴴ * A i = 1`. The unconditional
  directions `MPSTensor.isPrimitivePaper_of_hasEventuallyFullKrausRank` and
  `MPSTensor.isPrimitivePaper_of_isNormal` do not remove those hypotheses from
  the converse direction.

### `MPSTensor.HasEventuallyFullKrausRank`

- **Declaration:**
  `MPSTensor.HasEventuallyFullKrausRank (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/Wielandt/Primitivity/Definitions.lean`.
- **Meaning:** some positive-length Kraus-word space is the full matrix algebra.
- **Source:** arXiv:0909.5347, definition after equation (1),
  `Papers/0909.5347/main.tex:413-419`.
- **Sanctioned bridge:**
  `MPSTensor.hasEventuallyFullKrausRank_iff_isNormal` is unconditional.
  Its Proposition 3 equivalences are the normalization-conditional declarations
  listed under `IsPrimitivePaper`.
- **Caveat:** despite appearing in the primitivity development, this is the same
  algebraic eventual-span condition as `Kraus.IsNormal`, not the generic
  peripheral-spectrum predicate `_root_.IsPrimitive`.

### `MPSTensor.IsPrimitiveMPS` and `MPSTensor.HasPrimitiveFixedPoint`

- **Declarations:**
  `MPSTensor.IsPrimitiveMPS A ρ` and
  `MPSTensor.HasPrimitiveFixedPoint A`.
- **Defined in:** `TNLean/MPS/Structure/PrimitiveFixedPoint.lean` as reducible
  abbreviations for `Kraus.HasComplementaryFixedPointGap A ρ` and
  `Kraus.HasPrimitiveFixedPoint A`.
- **Meaning:** `IsPrimitiveMPS A ρ` exposes the QIC finite-Kraus certificate packaging
  left-canonical normalization, a nonzero positive-semidefinite fixed point `ρ`, and
  spectral radius less than one on the complement of the fixed-point projection.
  `HasPrimitiveFixedPoint A` uses the QIC existential certificate directly.
- **Source:** the complementary transfer-map-gap formulation used in the MPS
  convergence route; compare Wolf §6.3, Theorem 6.7, and the convergence
  consequences of arXiv:0909.5347 Proposition 3.
- **Sanctioned bridges:**
  QICLean's `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive`,
  `Kraus.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`,
  `MPSTensor.isPrimitiveMPS_of_isStronglyIrreduciblePaper`, and
  `MPSTensor.isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef`.
- **Caveat:** every listed bridge requires `[NeZero D]`. The two bridges from
  peripheral primitivity additionally require left-canonical normalization and,
  respectively, injectivity or irreducibility.
  `isPrimitiveMPS_of_isStronglyIrreduciblePaper` likewise requires the explicit
  left-canonical equation; strong irreducibility alone is insufficient. The
  bridge in the opposite direction requires `ρ.PosDef`; PSD alone is
  insufficient. Consequently `HasPrimitiveFixedPoint` is not an unconditional
  synonym for any of the preceding predicates.

### `MPSTensor.IsStronglyIrreduciblePaper`

- **Declaration:**
  `MPSTensor.IsStronglyIrreduciblePaper (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/Wielandt/Primitivity/Definitions.lean`.
- **Meaning:** the project's strengthened interpretation of Proposition 3(c):
  a positive-definite fixed point, peripheral primitivity, and an explicit
  `IsIrreducibleMap` conjunct. The last conjunct formalizes the paper's phrase
  “the corresponding eigenvector” as uniqueness of the fixed-point space, as
  documented in the declaration's source comment.
- **Source:** arXiv:0909.5347 Proposition 3(c),
  `Papers/0909.5347/main.tex:420-430` and `:501-509`; Wolf Theorem 6.7(3).
- **Sanctioned bridges:**
  `MPSTensor.primitivePaper_iff_stronglyIrreducible` and
  `MPSTensor.hasEventuallyFullKrausRank_iff_stronglyIrreducible`.
- **Caveat:** both equivalences require `[NeZero D]` and left-canonical
  normalization. The explicit irreducibility conjunct is additional data beyond
  the cited passage's literal positive-eigenvector and peripheral-uniqueness
  wording; it records the interpretation above and makes this predicate
  strictly stronger than peripheral primitivity alone.

## Injectivity

### MPS predicates

#### `Kraus.IsInjective`

- **Declaration:** `Kraus.IsInjective (A : MPSTensor d D) : Prop`.
- **Defined in:** `QICLean/Kraus/Injectivity.lean`.
- **Meaning:** the one-site matrices `{A i}` span the full matrix algebra; this
  is the linear-algebraic injectivity of the tensor as a virtual-to-physical map.
- **Source:** arXiv:1804.04964 §2,
  `Papers/1804.04964/paper_normal.tex:196-222`; see also arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:298-300`.
- **Sanctioned bridges:** `Kraus.isNBlkInjective_one_of_isInjective`,
  `Kraus.IsInjective.isNormal`, and
  `MPSTensor.isNBlkInjective_iff_blockTensor_isInjective`.
- **Caveat:** this is one-site injectivity. A tensor can fail this predicate and
  satisfy `Kraus.IsNBlkInjective A N` for a larger `N`.

#### `Kraus.IsNBlkInjective`

- **Declaration:**
  `Kraus.IsNBlkInjective (A : MPSTensor d D) (N : ℕ) : Prop`.
- **Defined in:** `QICLean/Kraus/Injectivity.lean`.
- **Meaning:** products indexed by all words of exactly length `N` span the full
  matrix algebra.
- **Source:** arXiv:0909.5347, equation (1) and the following definition of
  eventual full Kraus rank; arXiv:2011.12127 §IV.A, normal tensors becoming
  injective after blocking.
- **Sanctioned bridge:**
  `MPSTensor.isNBlkInjective_iff_blockTensor_isInjective` in
  `TNLean/MPS/Core/Blocking.lean`.
- **Caveat:** no positivity condition on `N` is built into this predicate;
  `Kraus.IsNormal` explicitly requires a positive witness.

#### `MPSChainTensor.IsInjective` and `MPSChainTensor.IsWindowInjective`

- **Declarations:** `MPSChainTensor.IsInjective A` in
  `TNLean/MPS/Chain/Defs.lean`, and `MPSChainTensor.IsWindowInjective A L` in
  `TNLean/PEPS/CycleMPSChainArc.lean`.
- **Meaning:** the first requires one-site `Kraus.IsInjective` at every site
  of a non-translation-invariant chain. The second requires every cyclic window
  of length `L` to have full arc-product span.
- **Source:** arXiv:1804.04964 §2, lines 145--222, and the normal-window
  formulation in §3 `normal_alt`,
  `Papers/1804.04964/paper_normal.tex:1928-1940`.
- **Sanctioned bridges:**
  `MPSChainTensor.isWindowInjective_one_of_isInjective` and
  `MPSChainTensor.isWindowInjective_const`.
- **Caveat:** window injectivity requires `[NeZero n]`.

#### `MPOTensor.IsInjective`

- **Declaration:** `MPOTensor.IsInjective (K : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/SimpleLocalStructure.lean`.
- **Meaning:** an abbreviation for
  `Kraus.IsInjective K.toMPSTensor` on the doubled physical index.
- **Source:** arXiv:1606.00608 Appendix C.2, where an inverse tensor is used for
  the blocked simple MPDO tensor; see
  `Papers/1606.00608/MPDO-22-12-17-2.tex:1628-1658`.
- **Sanctioned bridge:** this is a definitional abbreviation; unfold it to use
  the `Kraus.IsInjective` API.
- **Caveat:** it does not mean injectivity of the MPO as an operator on every
  chain length.

### PEPS predicates

#### `TNLean.PEPS.PairEffect.SourceInventory.IsNormalized`

- **Defined in:** `TNLean/PEPS/Approximation/SourcePreparation.lean`.
- **Meaning:** every recorded pair-source vector has norm one. The list records
  source occurrences separately, including repeated pairs of parties.
- **Source:** polynomial-PEPS manuscript, September 24, 2026, Lemma 5.1,
  `04-compression.tex`, lines 53–70 and 125–127.
- **Sanctioned bridges:** `SourceInventory.isAllowed_prepare_iff` and
  `Word.isNormalized_sources` identify normalization with allowed preparation
  and derive it from an allowed composition.

#### `TNLean.PEPS.PairEffect.SourceInventory.Expands`

- **Defined in:** `TNLean/PEPS/Approximation/PairSourceGrouping.lean`.
- **Meaning:** `G.Expands S` means that, beside any spectator registers,
  allowed local operations and register exchanges containing no pair-source
  preparations take the preparation of `G` exactly to the preparation of `S`.
- **Source:** the same Lemma 5.1, lines 125–127; the fresh-register argument
  in Theorem 5.2, `eq:compression-source-gate`, lines 233–251.
- **Sanctioned bridges:** `SourceInventory.exists_grouped` constructs a
  normalized `G` with one source for each unordered pair occurring in `S`.
  `Word.exists_grouped_source_preparation` gives the resulting exact
  factorization of an arbitrary allowed composition.
- **Further consequence:** `Word.exists_tensorPartyMaps_parties` collects the
  remaining operations into one contraction per party under canonical register
  identifications. `Word.exists_prepared_tensorPartyMaps` combines this with
  grouped preparation for a prescribed finite gate party type.
- **All pair slots:** `Word.exists_complete_prepared_tensorPartyMaps` also
  supplies a source on every unordered pair of distinct gate parties. Sources
  on pairs absent from the original monomial have one-dimensional halves.
  `SourceInventory.exists_complete_extension` retains the original inventory
  verbatim and supplies an allowed recovery of its preparation.
- **Caveat:** the finite type is the party set of the gate, not necessarily all
  parties in a larger construction. A bound on its cardinality and common
  source spaces across different monomials remain separate data or constructions.

#### `TNLean.PEPS.IsVertexInjective`

- **Declaration:** `TNLean.PEPS.IsVertexInjective (A : Tensor G d) : Prop`.
- **Defined in:** `TNLean/PEPS/Defs.lean`.
- **Meaning:** at every vertex, the physical vectors indexed by incident virtual
  configurations are linearly independent; equivalently, the linearly extended
  virtual-to-physical tensor map has trivial kernel.
- **Source:** arXiv:1804.04964 §3,
  `Papers/1804.04964/paper_normal.tex:979-981`.
- **Sanctioned bridges:**
  `TNLean.PEPS.IsVertexInjective.localTensorMap_injective`,
  `TNLean.PEPS.IsVertexInjective.singletonRegionTensorInjective`, and
  `TNLean.PEPS.regionBlockedTensorInjective_of_isVertexInjective`.
- **Caveat:** the last bridge requires
  `∀ e, 0 < A.bondDim e`. Function injectivity of the raw indexing function is
  strictly weaker and is not the sanctioned notion.

#### `TNLean.PEPS.RegionBlockedTensorInjective`

- **Declaration:**
  `TNLean.PEPS.RegionBlockedTensorInjective (A : Tensor G d) (R : Finset V) : Prop`.
- **Defined in:** `TNLean/PEPS/RegionBlock/Basic.lean`.
- **Meaning:** the blocked tensor family indexed by virtual configurations on
  the boundary of `R` is linearly independent.
- **Source:** arXiv:1804.04964 §3, contraction and union of injective regions,
  `Papers/1804.04964/paper_normal.tex:1205-1210` and Lemma
  `injective_union`, lines 1324--1402.
- **Sanctioned bridges:**
  `TNLean.PEPS.regionBlockedTensorInjective_of_isVertexInjective` and
  `TNLean.PEPS.regionBlockedTensorInjective_union_disjoint`.
- **Caveat / paper gap:** both bridges require all virtual bond dimensions to be
  positive. Without that hypothesis an interior zero-dimensional bond can make
  the blocked tensor vanish. This source assumption and the failure without it
  are recorded in
  `docs/paper-gaps/peps_injective_ft_section3_route.tex`. Never cite either
  bridge as unconditional.

#### `TNLean.PEPS.IsGInjective`

- **Declaration:**
  `TNLean.PEPS.IsGInjective (ρ : Representation ℂ G W) (T : W →ₗ[ℂ] P) : Prop`.
- **Defined in:** `TNLean/PEPS/GInjective.lean`.
- **Meaning:** the virtual-to-physical map `T = 𝒫(A)` is invariant under `ρ`
  and injective on the `ρ`-invariant subspace.
- **Source:** arXiv:1001.3807, Definition `def:2d-Ug-inj`,
  `Papers/1001.3807/paper_v3.tex:1278-1296`.
- **Sanctioned bridges:** `TNLean.PEPS.isGInjective_iff_exists_leftInverse`
  (the source's left inverse with `L 𝒫(A) = Π_U`, for finite `G`),
  `TNLean.PEPS.isGInjective_trivial_iff` (trivial `ρ`: injectivity of `T`), and
  `TNLean.PEPS.siteMap_injective_iff` (injectivity of the map of a four-leg
  site tensor is linear independence of its physical vectors, the vertex-wise
  condition of `IsVertexInjective`).
- **Caveat / paper gap:** the source requires `ρ` semi-regular; here `ρ` is a
  parameter and each instance names its representation. Recorded in
  `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`. No bridge yet
  connects `IsGInjective` of a site map to `IsVertexInjective` of the torus PEPS
  `torusSiteTensor`.

#### `Representation.IsSemiRegular`

- **Declaration:** `Representation.IsSemiRegular (ρ : Representation ℂ G V) : Prop`,
  for `G : Type u`.
- **Defined in:** `TNLean/Algebra/RepresentationDelta.lean`.
- **Meaning:** every finite-dimensional irreducible complex representation of
  `G` on a type in the universe of `G` admits a nonzero intertwining map into
  `ρ`.
- **Source:** arXiv:1001.3807, Definition 4.5,
  `Papers/1001.3807/paper_v3.tex:1010-1013`.
- **Sanctioned bridges:** `Representation.isSemiRegular_leftRegular` (the
  left-regular representation is semi-regular) and
  `Representation.irreducibleCharacters_eq_leftRegular_of_isSemiRegular` (a
  semi-regular representation has the irreducible characters of the regular
  representation), used in
  `Representation.trace_inv_comp_comp_deltaOperator_of_isSemiRegular`
  (Lemma 4.6).
- **Caveat:** irreducible representations of a finite group are
  finite-dimensional, so the restriction to finite-dimensional ones loses
  nothing; the universe restriction suffices because every irreducible
  representation is equivalent to one on a coordinate space. The trace
  identities of Lemmas 4.4 and 4.6 are stated with `ρ(h⁻¹)` in place of the
  source's `U_h†`; the two agree for unitary representations.

#### `TNLean.PEPS.IsGIsometric`

- **Declaration:** `TNLean.PEPS.IsGIsometric (ρ : Representation ℂ G (ι → ℂ))
  (T : (ι → ℂ) →ₗ[ℂ] (κ → ℂ)) : Prop`.
- **Defined in:** `TNLean/PEPS/GInjective.lean`.
- **Meaning:** `IsGInjective ρ T` and `⟪T x, T y⟫ = c ⟪x, y⟫` for invariant
  `x, y` and one constant `c > 0`.
- **Source:** arXiv:1001.3807, Definition `def:iso:isopeps`,
  `Papers/1001.3807/paper_v3.tex:1692-1697`.
- **Caveat / paper gap:** the source asks for the left-regular representation
  and for `𝒫(A)` to be unitary between its domain and range, that is `c = 1`;
  the factor `c` absorbs the missing normalization of the source's
  quantum-double tensor (`c = |G|`), and the rescaling `T / √c` gives the
  printed notion. Recorded in
  `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

#### `TNLean.PEPS.IsGIsometricMPS`

- **Declaration:** `TNLean.PEPS.IsGIsometricMPS (A : ι → Module.End ℂ (MonoidAlgebra ℂ G)) : Prop`.
- **Defined in:** `TNLean/PEPS/GIsometric.lean`.
- **Meaning:** an MPS tensor with bond space `ℂ[G]` carrying the left-regular
  representation `L_g`, invariant (`L_g A^i L_g⁻¹ = A^i`), with
  `𝒫(A†) 𝒫(A) = c σ` for one constant `c > 0`, where `𝒫(A†)|i⟩ = (A^i)†` and
  `σ` is the twirl onto the commutant.
- **Source:** arXiv:1001.3807, Definition `def:iso:isopeps` in the form
  `𝒫(A)⁻¹ = 𝒫(A†)`, `Papers/1001.3807/paper_v3.tex:1668-1700`.
- **Sanctioned bridges:** `IsGIsometricMPS.isGInjective` (G-injectivity for
  the conjugation action of the left-regular representation);
  `IsGIsometricMPS.concatTensor` (Lemma 6.2 in one dimension).
- **Caveat / paper gap:** the constant `c` is the normalization Local fix of
  `IsGIsometric`. No bridge to the coordinate-space `IsGIsometric` is stated:
  the virtual system here is `End ℂ[G]` rather than a coordinate space.
  Recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`.

#### `TNLean.PEPS.IsTorusDimerCovering`

- **Declaration:**
  `TNLean.PEPS.IsTorusDimerCovering (right up : TorusVertex width height → Bool) : Prop`.
- **Defined in:** `TNLean/PEPS/Examples/RVB.lean`.
- **Meaning:** the edges marked by `right` (the edge from `v` to its right
  neighbour) and `up` (the edge from `v` to its upper neighbour) form a
  nearest-neighbour dimer covering of the torus: every site lies on exactly one
  marked edge among its top, right, down and left edges.
- **Source:** arXiv:2011.12127, Appendix A, "The RVB state",
  `Papers/2011.12127/TN-Review-main.tex:2440-2448` ("all ways of covering the
  lattice with nearest neighbor singlets").
- **Sanctioned bridges:** `TNLean.PEPS.stateCoeff_rvbPEPS`, which writes the
  RVB PEPS as the sum over dimer coverings of the product of singlets on the
  covered edges.
- **Caveat:** the bridge is stated for tori of width and height at least three.
  At width or height two the right and left edges of a site coincide in the
  simple torus graph, so the predicate no longer counts the source's
  multigraph coverings; recorded in
  `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

#### `TNLean.PEPS.IsTorusParallelSection` and `TNLean.PEPS.IsTorusFlat`

- **Declarations:**
  `TNLean.PEPS.IsTorusParallelSection (a b f : TorusVertex width height → G) : Prop`
  and `TNLean.PEPS.IsTorusFlat (a b : TorusVertex width height → G) : Prop`.
- **Defined in:** `TNLean/PEPS/TorusParallelSection.lean`.
- **Meaning:** `f` is a parallel section of the horizontal transports `a` and
  the vertical transports `b` if `f (x + 1, y) = a (x, y) * f (x, y)` and
  `f (x, y + 1) = b (x, y) * f (x, y)` at every site; `a, b` are flat if
  `b (x + 1, y) * a (x, y) = a (x, y + 1) * b (x, y)` around every elementary
  square.
- **Source:** project combinatorics for the coloring superposition of
  arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex:2914-2923`; no source
  predicate.
- **Sanctioned bridges:** `TNLean.PEPS.exists_isTorusParallelSection_iff`
  (sections exist exactly for flat transports with trivial holonomy around the
  row and the column through the origin) and
  `TNLean.PEPS.card_isTorusParallelSection` (there are `|G|` sections or none).

#### `TNLean.PEPS.IsQuantumDoubleGaussLaw` and `TNLean.PEPS.IsQuantumDoubleTrivialHolonomy`

- **Declarations:**
  `TNLean.PEPS.IsQuantumDoubleGaussLaw (s : TorusVertex width height → G × G × G × G) : Prop`
  and `TNLean.PEPS.IsQuantumDoubleTrivialHolonomy s : Prop`.
- **Defined in:** `TNLean/PEPS/Examples/QuantumDouble.lean`.
- **Meaning:** for the four physical spins `(s₁, s₂, s₃, s₄)` (top left, top
  right, bottom right, bottom left) of each site of the dual quantum-double
  network, Gauss' law is the vertex rule `s₂ s₁ = s₃ s₄` at every site together
  with the plaquette rule
  `s₁(v + (1, 0)) s₂(v) = s₄(v + (1, 1)) s₃(v + (0, 1))` around every corner;
  trivial holonomy asks that the ordered products of the transports
  `s₂ s₁` along the row `y = 0` and `s₄(v + (0, 1))⁻¹ s₁(v)` along the column
  `x = 0` are the identity.
- **Source:** arXiv:1001.3807, `Papers/1001.3807/paper_v3.tex:2918-2921` (local
  and plaquette terms of the Hamiltonian), and arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:2452` (Gauss' law).
- **Sanctioned bridges:** `TNLean.PEPS.stateCoeff_quantumDoubleDualPEPS` (the
  coefficient of the contracted dual network is `|G|` on configurations obeying
  both predicates and `0` elsewhere).
- **Caveat:** the review identifies the network with the superposition of all
  Gauss-law configurations; on the torus only the trivial-holonomy sector
  occurs, and the bridge is stated for width and height at least three.
  Recorded in `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex` and
  `docs/paper-gaps/rmp_peps_examples_small_torus.tex`.

#### Actual CZX rectangle boundary coordinates

- **Declarations:** `TNLean.PEPS.czxRectangleCoordinatesEquiv`,
  `czxRectangleEffectiveBoundaryConfig`, and `czxRectangleBoundaryMatrix`.
- **Defined in:** `TNLean/PEPS/Examples/CZXRectangleMap.lean`, using the explicit
  clockwise `torusRectanglePerimeterEquiv` in `CZXRectangleBoundary.lean`.
- **Meaning:** clockwise crossing-bond coordinates reverse the native
  bottom/left pairs. Effective bits `c` impose the adjacent-pair constraint
  `(c_i,c_(i+1))`; the matrix column is the actual incident-only open-region
  contraction at that native boundary assignment, without an extra scalar.
- **Source:** Chen, Liu and Wen, arXiv:1106.4752, Section IV, boundary discussion
  lines 330–345 and 377–385; arXiv:2011.12127, Appendix A, printed CZX tensors.
- **Sanctioned bridges:** `range_openRegionMap_czxRectangle` identifies the
  exact span of the effective columns, and
  `regionPhysicalProductMatrix_czxRectangleBoundaryMatrix_review` identifies
  the physical symmetry with the printed boundary operator. The actual
  reduced-density support equals this image by
  `range_regionReducedDensity_czxRectangle`; its rank and the rank after
  trace normalization are `2^(2*w+2*h)`.
- **Caveats:** torus periods are at least three; both rectangle sides are
  positive, strictly shorter than the periods and bounded within the chosen
  coordinates. Seam endpoints and crossing bonds through a seam are allowed;
  a coordinate interval that wraps around the torus is not covered. The
  effective dimension is
  `2^(2*w+2*h)`, not the full unconstrained virtual dimension `4^(2*w+2*h)`.
  No flat nonzero spectrum, entropy, isometric normalization, nonrectangular
  extension or parent-kernel spanning statement follows merely from these
  support theorems. The printed operator's ordering sign disappears because
  the rectangle perimeter is even; normalized bra-ket factors are not silently
  substituted. See `docs/paper-gaps/rmp_peps_czx_boundary_chain.tex`.

#### `TNLean.PEPS.IsToricCodeBondCompatible`

- **Declaration:** `IsToricCodeBondCompatible σ`.
- **Defined in:** `TNLean/PEPS/Examples/ToricCodeTorusAmplitudes.lean`.
- **Meaning:** the virtual labels determined by the physical spins match on
  every oriented horizontal and vertical bond: the left label of the right
  neighbor equals the current right label, and the bottom label of the upper
  neighbor equals the current top label.
- **Source:** the literal primal toric-code tensor in the review,
  `Papers/2011.12127/TN-Review-main.tex`, lines 2451–2465,
  equation `eq:app:tcode-rep-primal`, and the torus closure construction of
  Schuch, Cirac and Pérez-García, arXiv:1001.3807, Theorem 5.9.
- **Sanctioned bridges:** `toricCodeTorusState_apply` gives the exact support
  indicator times the seam phases; `toricCodeTorusState_one_one_apply` is
  the identity-closure indicator; `toricCodeTorusState_ne_zero_iff` identifies
  this predicate with nonvanishing for each of the four closures.
- **Caveats:** this is a physical-configuration support condition for the
  oriented-bond contraction. Its native simple-graph interpretation uses
  both torus periods at least three; smaller positive periods are algebraic
  extensions. It does not assert parent-Hamiltonian kernel membership or
  kernel spanning, and it imposes no additional normalization factor.

#### `TNLean.PEPS.PairConjugacyClass.IsCommuting`

- **Declaration:**
  `TNLean.PEPS.PairConjugacyClass.IsCommuting (C : PairConjugacyClass G) : Prop`.
- **Defined in:** `TNLean/PEPS/PairConjugacy.lean`.
- **Meaning:** the representatives `(g, h)` of a class of pairs under
  simultaneous conjugation commute. Commutation is invariant under
  simultaneous conjugation, so the predicate is well defined on classes.
- **Source:** arXiv:1001.3807, Theorem 5.9 (`thm:2d:gs-struct`),
  `Papers/1001.3807/paper_v3.tex:1582-1621`, where the torus closures are
  indexed by commuting pairs up to simultaneous conjugation.
- **Sanctioned bridges:**
  `TNLean.PEPS.PairConjugacyClass.isCommuting_pairConjugacyClass` (the class of
  `p` is commuting exactly when `Commute p.1 p.2`); the subtype
  `TNLean.PEPS.CommutingPairConjugacyClass` indexes the sector families such as
  `TNLean.PEPS.IsGInjective.linearIndependent_torusGClosureClass_commuting_of_isSemiRegular`.
- **Caveat:** the independence theorem
  `TNLean.PEPS.IsGInjective.linearIndependent_torusGClosureClass_of_isSemiRegular`
  holds for all classes, commuting or not. Commutation is required to move the
  closure seams without changing the vector
  (`TNLean.PEPS.torusBondNetwork_closureAt_eq_torusGClosure` assumes
  `Commute g h`), and hence by every common-density statement built on seam
  deformation; it is also the source's ground-space condition, whose
  identification with the parent-Hamiltonian ground space is not formalized
  (see `docs/paper-gaps/rmp_peps_quantum_double_g_isometry.tex`).

#### `TNLean.PEPS.IsTorusClosureCompatible` and `TNLean.PEPS.IsTorusNonseamCompatible`

- **Declarations:**
  `TNLean.PEPS.IsTorusClosureCompatible (g h g' h' : G) (q : TorusVertex width height → G) : Prop`
  and `TNLean.PEPS.IsTorusNonseamCompatible (q : TorusVertex width height → α) : Prop`.
- **Defined in:** `TNLean/PEPS/RegularTorusCompatibility.lean`.
- **Meaning:** in the overlap of a bra network closed by `(g, h)` with a ket
  network closed by `(g', h')`, `IsTorusClosureCompatible g h g' h' q` says that
  the site translations `q v` carry the ket labels to the bra labels across
  every horizontal and vertical bond, where the closure element is inserted
  only on the bonds crossing the two seams. For a constant `q = x` this is
  `h x = x h'` and `g x = x g'`, that is, `x` conjugates `(g', h')` to `(g, h)`.
  `IsTorusNonseamCompatible q` says that neighbouring labels agree across every
  bond that does not cross a seam.
- **Source:** arXiv:1001.3807, `eq:2d:peps-with-ug-uh`,
  `Papers/1001.3807/paper_v3.tex:1515-1525`, and the local contraction argument
  of Theorem 5.9, lines 1560-1621.
- **Sanctioned bridges:** `TNLean.PEPS.IsTorusNonseamCompatible.eq_origin` and
  `TNLean.PEPS.IsTorusClosureCompatible.eq_origin` (the label is constant);
  `TNLean.PEPS.isTorusClosureCompatible_iff_exists_intertwiner` (closure
  compatibility is a constant `x` with `h x = x h'` and `g x = x g'`); and
  `TNLean.PEPS.sum_torusClosureCompatible_eq_sum_intertwiner`.
- **Caveat:** these are the local equations of the closure overlap calculation,
  not a statement about ground spaces. They hold for every circumference,
  including one.

#### `TNLean.PEPS.IsRegionLabelCompatible` and `TNLean.PEPS.IsTwistedRegionLabelCompatible`

- **Declarations:**
  `TNLean.PEPS.IsRegionLabelCompatible (R : Finset V) (q : {v // v ∈ R} → G) (η θ) : Prop`
  and
  `TNLean.PEPS.IsTwistedRegionLabelCompatible (R : Finset V) (u w : Edge Γ → G) (q) (η θ) : Prop`.
- **Defined in:** `TNLean/PEPS/RegularRegionConnectivity.lean` and
  `TNLean/PEPS/RegularTwistedRegion.lean`.
- **Meaning:** in the regular-basis expansion of the Gram matrix of an open
  region, `η` (bra) and `θ` (ket) are group labels on the bonds incident to `R`. The
  untwisted predicate says that at every vertex `v ∈ R` each incident label of
  `η` is `q v` times the corresponding label of `θ`. The twisted predicate says
  the same after the bond operators `u` (bra) and `w` (ket) are inserted at the
  head of each oriented bond.
- **Source:** arXiv:1001.3807, regular-basis contraction in the proof of
  Theorem 6.9, `Papers/1001.3807/paper_v3.tex:1935-1990`.
- **Sanctioned bridges:** `TNLean.PEPS.IsRegionLabelCompatible.exists_common_label`
  and `TNLean.PEPS.isRegionLabelCompatible_iff_exists_translation` (on a
  connected region the labels are one simultaneous translation);
  `TNLean.PEPS.IsTwistedRegionLabelCompatible.internalEdge_intertwining` and
  `TNLean.PEPS.IsTwistedRegionLabelCompatible.exists_common_label` (a connected
  subgraph of untwisted bonds forces one common translation).
- **Caveat:** both are local equations of a proof calculation and carry no
  connectivity; every bridge to a common translation assumes a connected
  induced region or a connected untwisted subgraph.

#### `TNLean.PEPS.IsTorusRegionIntegerLift`

- **Declaration:**
  `TNLean.PEPS.IsTorusRegionIntegerLift (R : Finset (TorusVertex width height)) (L : {v // v ∈ R} → ℤ × ℤ) : Prop`.
- **Defined in:** `TNLean/PEPS/TorusRegionLiftGauge.lean`.
- **Meaning:** `L` assigns to every site of the torus region `R` a point of the
  square lattice `ℤ × ℤ` projecting to that site, such that every rightward and
  upward native bond inside `R` is a unit step of the lift. It is a supplied
  combinatorial lift, independent of any group or closure operator.
- **Source:** no source predicate. It is a locally introduced device for the
  contiguous-block arguments of arXiv:1001.3807, Theorems 6.7-6.9,
  `Papers/1001.3807/paper_v3.tex:1931-2072`, used to gauge the native closure
  operators away inside the region.
- **Sanctioned bridges:**
  `TNLean.PEPS.exists_isTorusRegionIntegerLift_of_isSimplyConnected` (a lift
  exists when the closed-cell realization of `R` is simply connected),
  `TNLean.PEPS.exists_isTorusRegionIntegerLift_of_continuousLift`,
  `TNLean.PEPS.IsTorusRegionIntegerLift.injective`, and the gauge and
  coordinate theorems `TNLean.PEPS.torusRegionLiftGauge_gradient` and
  `TNLean.PEPS.regularProjectorTwistedRegionMatrix_coordinates_of_torusRegionIntegerLift`.
- **Caveat:** the predicate does not assert that `R` is a disk or simply
  connected; it is weaker, and only the first bridge derives it from simple
  connectedness. The lift statements are stated on tori with both periods at
  least three.

#### `TNLean.PEPS.IsIntegerCellNear`

- **Declaration:** `TNLean.PEPS.IsIntegerCellNear (q a : ℤ × ℤ) : Prop`.
- **Defined in:** `TNLean/PEPS/IntegerCellExteriorCollar.lean`.
- **Meaning:** the two integer centers differ by at most one in each
  coordinate, so their closed unit cells meet, possibly only at a corner.
- **Source:** no source predicate. It is locally introduced plane geometry for
  the exterior collar of a contiguous block in arXiv:1001.3807, proof of
  Theorem 6.9, `Papers/1001.3807/paper_v3.tex:1935-1990`.
- **Sanctioned bridges:**
  `TNLean.PEPS.isIntegerCellNear_of_integerClosedCell_inter_nonempty`
  (intersecting closed cells have near centers); the predicate defines the
  exterior band and collar graph used by
  `TNLean.PEPS.integerExteriorCollarGraph_connected_of_isSimplyConnected`.
- **Caveat:** nearness includes diagonal contact, so it is not the
  four-neighbor adjacency of the square lattice.

#### `TNLean.PEPS.regularizedPatchDomain` and `regularizedPatchMinimum`

- **Defined in:** `TNLean/PEPS/AreaLaw/RegularizedPatchMinimum.lean`.
- **Meaning:** the domain consists of independent positive semidefinite
  trace-one matrices on the physical spaces of a finite family of regions.
  For shift `b > 0`, the objective is the norm of the reverse index-ordered
  product of the identity-extended powers `(xⱼ + bI)^(-aⱼ/2)` applied to a
  unit global Euclidean vector. The minimum is the infimum of this actual
  objective image.
- **Source:** September 24, 2026 polynomial-PEPS manuscript,
  [`03-patches.tex`, lines 68–99](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L68-L99),
  `eq:patch-variational-problem` and `eq:patch-elementary-norm-bounds`.
- **Sanctioned consequences:** compactness, nonemptiness derived from the unit
  vector, continuity, and `exists_isMinOn_regularizedPatchObjective` for
  arbitrary real weights. For nonnegative weights,
  `regularizedPatchObjective_bounds` applies to every feasible tuple;
  `regularizedPatchObjective_eq_minimum` identifies every feasible minimizer
  with the common value, and positivity permits unit normalization.
- **Caveats:** repeated regions retain independent variables; singular
  densities are shifted on the full regional space. No nestedness,
  inter-factor commutation, uniqueness, or smooth optimizer is assumed.
  Stationarity, energy, later regulator-growth and retained-rank estimates,
  and the full adaptive patch constraint are outside this result.
- **Scope:** see
  [the formalization scope](formalization/peps-regularized-patch-minimum.md).

#### `TNLean.PEPS.regularizedPatchCoordinateUpdate` and `regularizedPatchFirstVariation_eq_zero`

- **Defined in:** `TNLean/PEPS/AreaLaw/RegularizedPatchCoordinate.lean` and
  `RegularizedPatchStationarity.lean`.
- **Meaning:** unitary conjugation changes exactly one indexed feasible density.
  The actual output derivative along `exp(tB)`, for skew-Hermitian `B`, is the
  original reverse-product insertion of `BKⱼ − KⱼB`. Every feasible `IsMinOn`
  minimizer has zero real inner product of that insertion with its output.
- **Source:** the September 24, 2026 manuscript,
  [`03-patches.tex`, lines 134–149](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L134-L149).
- **Sanctioned consequences:** feasibility of each coordinate curve, exact
  unitary covariance of the full-space shifted power, and the unstripped
  first variation. Arbitrary real weights and singular densities are allowed.
- **Caveats:** repeated regions retain independent variables. Feasibility alone
  does not imply stationarity. There is no optimizer choice, pairwise filter
  commutation, descending local commutation, or KKT conclusion.
- **Verification boundary:** see the exact-source gates and scope in
  [coordinate first variation](formalization/peps-regularized-patch-stationarity.md).

#### `TNLean.PEPS.normalizedRegularizedPatchMarginal`

- **Defined in:** `TNLean/PEPS/AreaLaw/RegularizedPatchMarginal.lean`.
- **Meaning:** `FiniteProduct.reducedPure` of the same normalized final filtered
  vector for every region, after the explicit univ-subtype/global configuration
  isometry. These are canonical reduced states, not freely supplied densities.
- **Source:** the September 24, 2026 manuscript,
  [`03-patches.tex`, lines 91–99](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L91-L99).
- **Sanctioned consequences:** positivity and the complex-valued identity
  `⟨φ, ι_X(K)φ⟩ = Tr(ρ_X K)` for arbitrary complex `K`; trace one for a unit
  input, nonnegative weights, positive shift, and feasible tuple. Heterogeneous
  local dimensions and the empty region are included.
- **Caveats:** the coordinate variable `xⱼ` need not equal `ρ_Xⱼ`. Zero weight
  does not constrain that density to commute with the final marginal.
  No intermediate filtered vector is substituted for the final state.
- **Scope:** see
  [the source-facing scope](formalization/peps-regularized-patch-stationarity.md).

#### `TNLean.PEPS.IsRegionParentInteraction`

- **Declaration:**
  `TNLean.PEPS.IsRegionParentInteraction (A : Tensor Γ d) (R : Finset V) (h : Matrix _ _ ℂ) : Prop`.
- **Defined in:** `TNLean/PEPS/ParentHamiltonian/RegionParentHamiltonian.lean`.
- **Meaning:** the operator `h` on the physical space of the region `R` is
  positive semidefinite and its kernel is exactly the regional PEPS space
  `TNLean.PEPS.regionGroundSpace A R`, spanned by the contractions of `R` with
  arbitrary boundary conditions. It need not be a projector.
- **Source:** arXiv:2011.12127, Section IV.C.1,
  `Papers/2011.12127/TN-Review-main.tex:2003-2011` (the terms of a parent
  Hamiltonian are positive semidefinite operators with kernel `𝒢_R`).
- **Sanctioned bridges:** `TNLean.PEPS.isRegionParentInteraction_canonical`
  (the orthogonal projector onto the complement of the regional space);
  `TNLean.PEPS.ker_regionParentHamiltonian` (for any such family of terms the
  ground space of their sum is the intersection of the regional conditions);
  `TNLean.PEPS.IsRegionParentInteraction.mul_regionReducedDensity_eq_zero`.
- **Caveat:** the predicate fixes only the kernel of each term. The resulting
  ground space is independent of the chosen terms, but spectral gaps and other
  spectral data are not.

`TNLean.PEPS.SingletonRegionTensorInjective`,
`TNLean.PEPS.VertexComplementTensorInjective`,
`TNLean.PEPS.RegionBlockedTensorInjective`, and the edge-middle predicates are
geometry-specific formulations used by the PEPS proof. They are not aliases for
`IsVertexInjective`. New carrier-specific injectivity predicates should normally
be namespace-overloaded rather than adding another carrier name to the middle of
the identifier.

## Canonical form

There is no single universal canonical-form predicate. The following declarations
model different levels of data and different sources.

### `MPSTensor.CanonicalForm`

- **Declaration:** `MPSTensor.CanonicalForm (d : ℕ)`.
- **Defined in:** `TNLean/MPS/Core/MultiBlock.lean`.
- **Meaning:** lightweight data for a weighted block-diagonal tensor with an
  injective tensor in each block.
- **Source:** the block-diagonal shape of Pérez-García--Verstraete--Wolf--Cirac,
  arXiv:quant-ph/0608197, TI canonical form, and CPSV16 equation `II_CF1`.
- **Sanctioned bridge:** `MPSTensor.CanonicalForm.toTensor_eq_toTensorFromBlocks`.
- **Caveat:** it stores no normalization, irreducibility, peripheral
  primitivity, positivity of block dimensions, ordering of weights, or BNT
  minimality. It is data, not a proposition equivalent to the predicates below.

### Retained-block reconstruction and literal CPSV canonical form

- **Declarations:** `MPSTensor.RetainedBlockReconstructionData A` and
  `MPSTensor.CPSVCanonicalFormData A`.
- **Defined in:** `TNLean/MPS/CanonicalForm/Definitions.lean`; block inclusions
  in `TNLean/MPS/CanonicalForm/RetainedBlockReconstruction.lean`.
- **Meaning:** the common reconstruction is
  $A^i=C^\dagger(\bigoplus_k\mu_k A_k^i)C$ with nonzero weights and
  $CC^\dagger=1$. Literal CPSV data additionally require normal blocks and
  $\sum_k D_k\le D$, permitting an unused ambient zero complement.
- **Source:** arXiv:1606.00608, equation `II_CF1`, lines 214--245.
- **Caveat:** the common reconstruction imposes no normality or full-support
  condition. The nonzero-weight convention is recorded in
  `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex`.

### `MPSTensor.IsMPUCanonicalForm`

- **Declarations:** `MPSTensor.MPUCanonicalFormData A` and
  `MPSTensor.IsMPUCanonicalForm A`.
- **Defined in:** `TNLean/MPS/MPU/MPUCanonicalForm.lean`.
- **Meaning:** the same weighted reconstruction with irreducible blocks of
  transfer spectral radius one, nonzero weights, and full ambient support
  $\sum_k D_k=D$. Periodic blocks are permitted.
- **Source:** arXiv:1703.09188, canonical-form definition, lines 259--267.
- **Sanctioned result:** for an MPU whose original local tensor has this form,
  `MPOTensor.IsMPU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm`
  proves the normality conclusion of Proposition `prop:normal-tensor`.
- **Caveat:** the nonzero-weight and full-support conventions are recorded in
  `docs/paper-gaps/mpu_canonical_form_nonzero_weights.tex` and
  `docs/paper-gaps/mpu_canonical_form_full_support.tex`. Literal CPSV data keep
  their optional ambient complement. The PGVWC07 form has a distinct
  reconstruction using a bond-index equivalence and real weights.

### `MPSTensor.IsCanonicalForm`

- **Declaration:** `MPSTensor.IsCanonicalForm μ A : Prop`.
- **Defined in:** `TNLean/PiAlgebra/CanonicalFormSepAux.lean` despite living in
  the `MPSTensor` namespace.
- **Meaning:** a stronger separated biCF/CFII-after-blocking specialization:
  one-site injective blocks, left-canonical normalization, non-increasing
  nonzero weights, positive block dimensions, and normalized self-overlap.
- **Source:** the direct-sum shape comes from arXiv:1606.00608 equation `II_CF1`
  and `Papers/1606.00608/MPDO-22-12-17-2.tex:237-246`; the additional
  injectivity, normalization, positivity, and overlap hypotheses implement the
  stronger separated form used after blocking. Compare arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:1831-1836`.
- **Sanctioned bridges:** `MPSTensor.IsCanonicalForm.of_peripheral_primitive`
  constructs the form. Its `block_injective` field supplies pointwise
  injectivity directly; its remaining fields feed
  `IsLeftCanonicalBlockFamily.ofForall` and
  `HasNormalizedSelfOverlap.ofForall`.
- **Caveat:** this is not the paper's bare direct-sum CF predicate: it assumes
  one-site injectivity, left-canonical normalization, positive dimensions, and
  normalized self-overlap. The already-separated family also does not retain
  repeated-copy multiplicities of the paper's two-layer BNT decomposition.

### `MPSTensor.IsNormalCanonicalForm`

- **Declaration:** `MPSTensor.IsNormalCanonicalForm μ A : Prop`.
- **Defined in:** `TNLean/PiAlgebra/CanonicalFormSepAux.lean`.
- **Meaning:** a stronger prepared specialization with irreducible,
  left-canonical, peripherally primitive blocks, non-increasing nonzero weights,
  and positive block dimensions.
- **Source:** its direct-sum shape is based on arXiv:1606.00608, lines 233--246
  and equation `II_CF1`, and arXiv:2011.12127, lines 1828--1836. The
  left-canonical, ordered-weight, and positive-dimension fields are additional
  prepared-data hypotheses rather than part of the paper's bare CF definition.
- **Sanctioned bridges:**
  `MPSTensor.IsNormalCanonicalForm.toHasIrreducibleBlocks`,
  `MPSTensor.IsNormalCanonicalForm.toIsLeftCanonicalBlockFamily`,
  `MPSTensor.IsNormalCanonicalForm.ofSeparatedData`, and the direct constructor
  `HasPrimitiveBlocks.ofForall` applied to the `block_primitive` field.
- **Caveat:** this does not encode the source's modulus-bound and unit-witness
  normalization for copy weights. No public theorem identifies this predicate
  with `MPSTensor.IsCanonicalForm`; the block hypotheses differ. The positive
  dimensions are explicit and are used to obtain the needed `NeZero` instances.

### `MPSTensor.IsNormalCanonicalFormBNT`

- **Declaration:** `MPSTensor.IsNormalCanonicalFormBNT μ A : Prop`.
- **Defined in:** `TNLean/MPS/BNT/Construction.lean`.
- **Meaning:** `IsNormalCanonicalForm` plus gauge-phase separation between
  distinct blocks.
- **Source:** the separated-representative reading of arXiv:1606.00608 §II.C,
  especially lines 264--301.
- **Sanctioned bridges:**
  `MPSTensor.IsNormalCanonicalFormBNT.toIsNormalCanonicalForm`,
  `MPSTensor.IsNormalCanonicalFormBNT.ofSeparatedData`, and
  `MPSTensor.IsNormalCanonicalFormBNT.isBNT`.
- **Caveat:** this is a one-representative-per-gauge-phase-class surface. It
  suppresses repeated copies and their power-sum coefficients; see
  `docs/paper-gaps/cpsv16_ft_one_copy_scope_restriction.tex`. It is not equivalent by
  renaming to `MPSTensor.IsBNTCanonicalForm`.

### `MPSTensor.IsBNTCanonicalForm`

- **Declaration:**
  `MPSTensor.IsBNTCanonicalForm (P : MPSTensor.SectorDecomposition d)`.
- **Defined in:** `TNLean/MPS/FundamentalTheorem/SectorBNT/Basic.lean`.
- **Meaning:** the core paper-faithful two-layer sector canonical form: positive
  basis dimensions, irreducible and left-canonical basis tensors, normalized
  self-overlap, eventual BNT independence, separation of basis representatives,
  and normalized raw copy weights while retaining each copy and coefficient
  `∑q (μ[j,q])^N`.
- **Source:** arXiv:1606.00608 §II, lines 271--301, and arXiv:2011.12127
  Definition 4.2 and two-layer display, lines 1846--1884.
- **Sanctioned bridges:**
  `MPSTensor.IsBNTCanonicalForm.basis_isNormal` projects algebraic normality of
  each basis block, and `MPSTensor.IsBNTCanonicalForm.isBNT` forgets the sector
  weights and canonical-form data to produce the algebraic basis predicate.
  Further bridges are
  `MPSTensor.SectorDecomposition.IsBNTCanonicalForm.blockTensor`,
  `MPSTensor.SectorDecomposition.IsBNTCanonicalForm.reindexPhysical`, and the
  supplier declarations
  `MPSTensor.exists_isBNTCanonicalForm_of_tp_primitive_irr_blocks` and
  `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos_normalized`.
- **Caveat:** `IsBNTCanonicalForm.blockTensor` requires a strictly positive
  blocking length `0 < p`; it does not assert preservation at length zero.
  `exists_isBNTCanonicalForm_afterBlocking_pos_normalized` assumes a nonzero
  positive-length MPV family (the standing convention of arXiv:1606.00608,
  line 246) and realizes the weight normalization itself, at the cost of a
  per-site scalar. This is the canonical predicate when
  multiplicities and raw sector weights matter. It is not equivalent to the
  flattened `IsNormalCanonicalFormBNT`; multiplicity recovery is genuine
  mathematical content, not a change of packaging.

### MPDO canonical-form predicates

- `MPOTensor.IsHorizontalCF` in `TNLean/MPS/MPDO/HorizontalBNT.lean` is the
  normalized representative-indexed BNT-refined horizontal decomposition. It
  is stronger than the literal CPSV canonical form from arXiv:1606.00608,
  lines 237--244; see
  `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.
- `MPOTensor.IsVerticalCF` in `TNLean/MPS/MPDO/VerticalCF.lean` is the vertical
  basis decomposition with positive multiplicities, positive diagonal weights,
  and a coisometry `U` satisfying `U * Uᴴ = 1` (equivalently, `Uᴴ` is an
  isometry), sourced to arXiv:1606.00608 lines 1895--1921 and 1952--1956. It
  requires both the compressed block identity and exact reconstruction by `Uᴴ`
  and `U`.
  Reconstruction still permits an omitted all-zero complement because `Uᴴ * U`
  is the retained-support projection; see
  `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.
- `MPOTensor.HasVerticalBNTGroupingInputs` in
  `TNLean/MPS/MPDO/VerticalBNTGrouping.lean` is the pair of
  canonical-form-specific inputs that the grouped vertical construction of
  arXiv:1606.00608, Proposition 4.13, lines 1863--1921 consumes: the
  phase-class grouping of the normal vertical sectors together with their
  physical reducing isometries (`MPOTensor.HasVerticalBNTGroupingWithIsometry`
  in `TNLean/MPS/MPDO/VerticalBNT.lean`), and the pairwise Figure 8 comparison
  of the Gram dressings of two positive vertical corners of a common
  representative (`MPOTensor.HasGroupedCornerGramDressing` in
  `TNLean/MPS/MPDO/GroupedSectorGram.lean`, sourced to the proof of
  Proposition 4.13, Figures 7--8 and lines 1909--1919). Its sanctioned bridge
  forward is `MPOTensor.HasVerticalBNTGroupingInputs.verticalCF`, which gives
  `MPOTensor.IsVerticalCF`; there is no bridge back, and neither input is
  recovered from vertical canonical form.
- The bundle has two independent suppliers, each assuming the matrix product
  density operator condition `MPOTensor.IsMPDO` alongside its own canonical
  form: `MPOTensor.IsHorizontalCF.hasVerticalBNTGroupingInputs` from
  normalized BNT-refined horizontal form, and
  `MPSTensor.IsCPSVCanonicalForm.hasVerticalBNTGroupingInputs` from literal
  CPSV canonical form. Each proves both inputs from its own grouping and
  Figure 8 theorems. No implication between `MPOTensor.IsHorizontalCF` and
  `MPSTensor.IsCPSVCanonicalForm` is proved or used in either direction, and
  none may be assumed: supplying the common grouping properties from one
  canonical form says nothing about the other.
- `MPOTensor.HasVerticalBNTProductInputs` in
  `TNLean/MPS/MPDO/VerticalBNTGrouping.lean` records the grouping properties
  for both the one-site tensor and its two-site block, together with three
  properties of the blocked vertical tensor: every invariant orthogonal
  projection reduces its letters; an irreducible isometric corner with a
  positive definite eigenmatrix at a positive eigenvalue has no other
  peripheral eigenvalue of that modulus; and every
  nonzero corner is detected by a finite-chain sector compression. These are
  the properties used in CPSV16, Proposition 4.13, lines 1873--1921, and
  Appendix C.4, lines 2020--2029. The constructors
  `MPOTensor.IsHorizontalCF.hasVerticalBNTProductInputs` and
  `MPSTensor.IsCPSVCanonicalForm.hasVerticalBNTProductInputs` prove them
  independently under MPDO positivity. They imply the common retained-product
  spectral and positive fusion constructions; together with positivity and
  `IsRFPViaTS`, they give `HasBNTFusionTensorClause`. These are intermediate
  consequences of each canonical form, not additional hypotheses of the
  source-facing fixed-point theorems.
- `MPOTensor.IsSimpleCanonicalForm` in `TNLean/MPS/MPDO/SimpleTensor.lean` is
  the normalized fixed-representative predicate of Appendix C.2: it adds the
  MPDO and nonnilpotent-sector conditions to horizontal canonical form. Its
  sanctioned one-way bridges are
  `MPOTensor.IsSimpleCanonicalForm.isHorizontalCF` and
  `MPOTensor.IsSimpleCanonicalForm.isSimple`; the latter forgets the line-246
  normalization and supplies the one-site BNT presentation required by
  Definition 4.7. It is not a quotient by nonzero scalar rescaling; see
  `docs/paper-gaps/cpsv16_unit_weight_rfp_scale_tension.tex`.
- `MPOTensor.IsSimple` in `TNLean/MPS/MPDO/Simple.lean` is the sole
  simplicity predicate: Definition 4.7 of arXiv:1606.00608 at lines 815--822
  read over the canonical blocks of lines 217--246. It existentially chooses a
  positive physical blocking whose doubled-index tensor has a BNT sector
  presentation (nonzero copy weights, positive multiplicities by definition) by
  a basis of normal tensors with nonnilpotent physical-trace transfers; see
  `docs/paper-gaps/cpsv16_bnt_uniqueness_zero_coefficient.tex` for the
  nonzero-coefficient convention. The theorem
  `MPOTensor.IsSimple.exists_mpo_ne_zero` derives a nonzero closed MPO at some
  positive length from the presentation; this is not an additional defining
  assumption. Nonnilpotency is independent of the chosen presentation by
  `MPOTensor.bnt_basis_not_isNilpotent_iff`. The line-246 unit-weight witness
  is not part of the predicate, and there is no separate all-length
  nonvanishing variant; see
  `docs/audits/2026-08-24_degenerate_readings_wave_2.md`.
- Scalar rescaling of a closed length-$N$ MPO obeys
  $\rho_N(cM)=c^N\rho_N(M)$ by `MPOTensor.mpo_smul`, not a
  $|c|^{2N}$ law. Accordingly, `MPOTensor.isMPDO_smul_ofReal_iff` and
  `MPOTensor.isSimple_smul_ofReal_iff` give invariance only under strictly
  positive real rescaling. They do not give arbitrary complex invariance or
  preservation of the same fixed-scale RFP equations after rescaling.

The `CF` spelling in these established MPDO names is retained for compatibility
and paper-local vocabulary. New public predicates should spell out
`CanonicalForm` unless a source-faithful established name requires otherwise.

## MPDO renormalization fixed points and zero correlation length

The following notions use different transfer objects and are not interchangeable.

### `MPOTensor.IsRFPViaTS`

- **Declaration:** `MPOTensor.IsRFPViaTS (M : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/RFPViaTS.lean`.
- **Meaning:** there exist trace-preserving completely positive maps
  $\mathcal S$ and $\mathcal T$ on the physical indices satisfying the one-site
  and two-site equations $\mathcal S[M_2(X)]=M_1(X)$ and
  $\mathcal T[M_1(X)]=M_2(X)$ for every virtual insertion $X$.
- **Source:** CPSV16 Definition 4.1, label `RFPMixedTS`,
  `Papers/1606.00608/MPDO-22-12-17-2.tex:638-663`.
- **Caveat:** this is the source MPDO renormalization fixed-point predicate. It
  is distinct from pure MPS RFP, doubled-index transfer idempotence, and every
  physical-trace ZCL condition below.

### Twisted-dimer matching and channel-support predicates

- **Declarations:** `MPOTensor.TwistedDimer.IsBondMatchedPair` in
  `TNLean/MPS/MPDO/TwistedDimer.lean`,
  `MPOTensor.TwistedDimer.IsOpenBondMatched` and
  `MPOTensor.TwistedDimer.IsCyclicBondMatched` in
  `TNLean/MPS/MPDO/TwistedDimerMPDO.lean`,
  `MPOTensor.TwistedDimer.IsRefineSupported` and
  `MPOTensor.TwistedDimer.IsCoarseSupported` in
  `TNLean/MPS/MPDO/TwistedDimerRefine.lean` and
  `TNLean/MPS/MPDO/TwistedDimerViaTS.lean`, and
  `MPOTensor.TwistedDimer.IsSameChannel` in
  `TNLean/MPS/MPDO/TwistedDimerCoefficients.lean`.
- **Meaning:** the first predicate requires one ordered pair of physical letters
  to match the right bit of the first against the left bit of the second; the
  next two quantify it over an open segment or around a ring. The two support
  predicates specify the matrix entries carrying the refinement and
  coarse-graining Kraus operators, including their outer bits, site flags, and
  decoded flag. The last one selects the fusion channel $g = f + f'$ of two flag
  labels against its complement.
- **Source:** project-specific coordinate conditions for the twisted-dimer
  example. They support the explicit realization of CPSV16 Definition 4.1 but
  are not predicates stated in arXiv:1606.00608.
- **Sanctioned bridges:** `isOpenBondMatched_succ` peels the first open bond,
  `isCyclicBondMatched_succ` separates the wraparound bond, and
  `isRefineSupported_iff_col` identifies the unique one-site fibre. The Kraus
  definitions use the two support predicates directly; the resulting public
  conclusions are `refineMap_physClose1`, `coarseMap_physClose2`, and
  `isRFPViaTS_T`.
- **Caveat:** these are proof coordinates for this one tensor, not alternative
  definitions of `MPOTensor.IsRFPViaTS`. They imply no simplicity,
  basis-of-normal-tensors fusion law, or coefficient attachment.

### One-letter blocking up to virtual gauge

- **Declarations:** `MPOTensor.IsOneLetterRFPViaTSUpToVirtualGauge M` and
  `MPSTensor.IsPureOneLetterRFPViaTSUpToVirtualGauge A`.
- **Defined in:** `TNLean/MPS/RFP/GaugeBlockingCounterexample.lean`.
- **Meaning:** after restricting to one physical letter, the two-site blocked
  doubled tensor is virtually gauge equivalent to the original doubled tensor.
- **Source:** CPSV16 Appendix D, equation `RFP-gauge`, lines 2091--2110.
- **Caveat:** despite the source-derived name, these predicates do not contain
  the trace-preserving completely positive maps $\mathcal S$ and $\mathcal T$
  in `MPOTensor.IsRFPViaTS`. They encode only the one-letter virtual-gauge
  specialization of the Appendix D diagram.

### `MPOTensor.IsPhysicalTraceIdempotent`

- **Declaration:**
  `MPOTensor.IsPhysicalTraceIdempotent (M : MPOTensor d D) : Prop`.
- **Meaning:**
  `MPOTensor.physTraceTransfer M * MPOTensor.physTraceTransfer M =
  MPOTensor.physTraceTransfer M`, characterized by
  `MPOTensor.isPhysicalTraceIdempotent_iff`.
- **Transfer object:** $\mathcal T_M=\sum_i M^{ii}$, obtained by closing the
  ket and bra physical indices of one MPO tensor.
- **Source:** CPSV16 Definition 4.2, label `DefinitionZCL`,
  `Papers/1606.00608/MPDO-22-12-17-2.tex:735-739`.
- **Sanctioned bridges:** `MPOTensor.isPhysicalTraceIdempotent_of_isRFPViaTS`
  gives the predicate from Definition 4.1. With $\mathcal T_M\ne0$,
  `MPOTensor.IsPhysicalTraceIdempotent.isSourceZCL` gives the separate
  scale-invariant relation.
- **Caveat:** this is neither `MPOTensor.IsSourceZCL` nor `MPOTensor.IsZCL`,
  which use the up-to-scalar relation and doubled-index completely positive
  map, respectively.

### `MPOTensor.periodicTwoPointCorrelation`

- **Declaration:**
  `MPOTensor.periodicTwoPointCorrelation M O₁ O₂ middleGap wrapGap`.
- **Defined in:** `TNLean/MPS/MPDO/Correlations.lean`.
- **Meaning:** the unnormalized periodic contraction
  $\tr(\mathbb E_{O_1}\mathcal T_M^{g_{\mathrm{mid}}}
  \mathbb E_{O_2}\mathcal T_M^{g_{\mathrm{wrap}}})$, where
  $\mathbb E_O=\sum_{i,j}O_{ji}M^{ij}$.
- **Source:** CPSV16 equation `Corr`, lines 490--496, and the mixed-state
  length-independence sentence following Definition 4.2, lines 735--742.
- **Sanctioned results:**
  `MPOTensor.periodicTwoPointCorrelation_positiveWrapGaps_independent`
  compares two positive wrapping gaps at an arbitrary fixed middle gap under
  literal physical-trace idempotence. This gives ring-length independence and
  includes an unchanged zero middle gap. The corollary
  `MPOTensor.periodicTwoPointCorrelation_positiveGaps_independent` compares
  any two pairs positive on both complementary arcs; equal gap sums give
  fixed-ring distance independence for nonadjacent observables.
- **Caveat:** these are scope-restricted results. No theorem compares a zero
  varied gap with a positive one because idempotence does not identify
  $\mathcal T_M^0=1$ with $\mathcal T_M$.
  The contraction is not normalized; the source introduces normalization
  later for entropic quantities. See
  `docs/paper-gaps/cpsv16_mpdo_zcl_correlation_length_boundary.tex`.

### `MPOTensor.IsSourceZCL`

- **Declaration:** `MPOTensor.IsSourceZCL (M : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/ZCL.lean`.
- **Meaning:** $\mathcal T_M\ne0$ and
  $\mathcal T_M^2=\lambda\mathcal T_M$ for some real $\lambda>0$.
- **Source boundary:** this is a scale-invariant version of CPSV16 Definition
  4.2, whose fixed-tensor diagram has $\lambda=1$. The difference is recorded
  in `docs/paper-gaps/cpsv16_zcl_canonical_form_normalization.tex`.
- **Caveat:** it is neither literal physical-trace idempotence nor the
  doubled-index predicate `MPOTensor.IsZCL`.

### `MPOTensor.IsZCL`

- **Declaration:** `MPOTensor.IsZCL (M : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/ZCL.lean`.
- **Meaning:** the doubled-index transfer map is idempotent,
  $E_M\circ E_M=E_M$.
- **Sanctioned bridge:**
  `MPOTensor.isZCL_iff_toMPSTensor_isTransferIdempotent` identifies this with
  transfer idempotence of the doubled-index MPS tensor `M.toMPSTensor`.
- **Caveat:** this is not the physical-trace ZCL diagram of CPSV16 Definition
  4.2 and not the physical-map RFP predicate `MPOTensor.IsRFPViaTS`.

### `MPOTensor.TransferRetractData`

- **Declaration:** `MPOTensor.TransferRetractData M n`.
- **Defined in:** `TNLean/MPS/MPDO/FusionIsometries.lean`.
- **Meaning:** the blocked doubled-index transfer map factors through a
  subspace $\mathcal A_n$ as $S_nT_n=E_n$ and $T_nS_n=\id_{\mathcal A_n}$.
- **Sanctioned bridges:** `MPOTensor.transferRetractData_one_iff_isZCL` is the
  one-site criterion, and `MPOTensor.transferRetractData_of_isZCL` supplies
  such data at every positive blocked size from doubled-index idempotence.
- **Caveat:** these are bond-space linear retracts, not the physical
  trace-preserving completely positive maps in CPSV16 Definition 4.1 and not
  the tensor-attached BNT data in Theorem 4.14(ii)--(iii).

### `MPOTensor.HasBlockedAdjointFixedPointAlgebraTower`

- **Declaration:**
  `MPOTensor.HasBlockedAdjointFixedPointAlgebraTower (M : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/AlgebraStructure.lean`.
- **Meaning:** there is a tower of support $*$-algebras $\mathcal A_n$ whose
  carriers equal $\operatorname{Fix}(E_n^\dagger)$ at every positive blocked
  size, with multiplication and inclusion induced by ambient matrices.
- **Caveat:** this is weaker than CPSV16 Theorem 4.14(ii). It does not include
  the BNT-label product law, the positive diagonal matrices
  $\chi_{\alpha,\beta,\gamma}$, or the length-one idempotent trace identity.
  The theorem
  `MPOTensor.exists_hasBlockedAdjointFixedPointAlgebraTower_not_isZCL` shows
  that this tower does not imply doubled-index transfer idempotence.

## State-level gauging

### `TNLean.Algebra.DefectMaps.IsCompletion`

- **Declaration:** `TNLean.Algebra.DefectMaps.IsCompletion D R : Prop`.
- **Defined in:** `TNLean/Algebra/UnitaryCompletionClass.lean`.
- **Meaning:** the whole family of unitaries $R=(U_{a,b})_{a,b\in G}$ agrees
  with the prescribed defect maps $D_{a,b}$ on every defect subspace
  $\mathcal K_{a,b}$.
- **Source:** arXiv:2502.20257, modified-fusion Lemma `lemma:modif` and the
  nonuniqueness observation at lines 4215--4326.
- **Sanctioned bridges:** `DefectMaps.mem_completionClass_iff` identifies the
  predicate with membership in the full completion class. The transport
  theorems in the same module use exact prescribed-map covariance before
  applying the target completion's adjoint.
- **Caveat:** the predicate characterizes a supplied completion; it neither
  constructs one nor asserts that the completion class has more than one
  member. Nonuniqueness requires a nonspanning defect subspace.

### `MPOTensor.HasDefectSupport` and `MPOTensor.HasPrescribedDefectCovariance`

- **Declarations:** `MPOTensor.HasDefectSupport d G hN D Ψ : Prop` and
  `MPOTensor.HasPrescribedDefectCovariance d G hN D Ψ : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/GaugeInvariantSubspace.lean`.
- **Meaning:** every two-site matter slice of $\Psi_\alpha$ lies in the defect
  subspace selected by the adjacent labels, and the prescribed defect maps
  carry these slices covariantly under $(a,b)\mapsto(ag^{-1},gb)$.
- **Source:** arXiv:2502.20257, lines 4325--4335.
- **Sanctioned bridge:** together with `DefectMaps.IsCompletion`, these
  predicates imply invariance of the gauged vector under every placed Gauss
  operator and averaged projector through
  `MPOTensor.placedGaussOperator_mulVec_gaugedVector` and
  `MPOTensor.placedGaussProjector_mulVec_gaugedVector`.
- **Caveat:** no current theorem derives either predicate from the paper's
  concrete locally orthogonal MPS blocks. That missing specialization and the
  CZX four-domain instance are recorded in
  `docs/paper-gaps/fbc25_state_level_gauging_covariance.tex`.

## States of the quasi-local algebra

### `SpinChain.IsPureQuasiLocalState`

- **Declaration:** `SpinChain.IsPureQuasiLocalState d ω : Prop`, for a continuous
  complex-linear functional `ω` on `SpinChain.QuasiLocalAlgebra d` with `d > 0`.
- **Defined in:** `TNLean/QCA/StateSpace.lean`.
- **Meaning:** `ω` is an extreme point, over the real numbers, of
  `SpinChain.quasiLocalStateSpace d`: the functionals of norm one with
  $\omega(I)=1$ and $\omega(X^*X)\geq0$ for every quasi-local observable $X$.
- **Source:** Nachtergaele, Commun. Math. Phys. 175 (1996),
  arXiv:cond-mat/9410110, lines 854--887 and 1469--1482.
- **Sanctioned bridges:**
  `SpinChain.isPureQuasiLocalState_of_unique_supported_state` proves purity from
  unique determination by expectation-one projections;
  `SpinChain.exists_eq_of_isPureQuasiLocalState_of_finite_decomposition` reads off
  a constituent of a finite convex decomposition; and
  `SpinChain.isPureQuasiLocalState_quasiLocalFunctionalCongr_iff` and
  `SpinChain.isPureQuasiLocalState_quasiLocalBlockingFunctional_iff` transport
  purity along star-algebra isomorphisms and site grouping.
- **Caveat:** purity is extremality among all states, not among
  translation-invariant states; a state that is extremal only among
  translation-invariant states need not satisfy this predicate.

## Gauge relations between blocks

### `MPSTensor.IsGaugeRelated`

- **Declaration:**
  `MPSTensor.IsGaugeRelated (A : MPSTensor d D₁) (A' : MPSTensor d D₂) : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/ZipperUniqueness.lean`.
- **Meaning:** there are rectangular matrices `X : Fin D₁ × Fin D₂` and
  `Y : Fin D₂ × Fin D₁` with `X * Y = 1`, `Y * X = 1`, and
  `A i * X = X * A' i` for every letter, so that $A'^i = X^{-1}A^iX$. The bond
  dimensions may differ in the statement; the two-sided inverse forces
  `D₁ = D₂`.
- **Source:** the blocks $B_c$ of a fusion algebra are pairwise distinct blocks
  of a canonical form, arXiv:1511.08090, `AnyonsPEPS.tex` lines 155--166 and
  191--193; arXiv:2203.12563, lines 415--424. Blocks that are not gauge related
  are the hypothesis under which the zipper fusion and action tensors are unique
  up to the multiplicity gauge.
- **Sanctioned bridges:** `MPSTensor.eq_zero_or_isGaugeRelated_of_intertwines`
  shows that a letter intertwiner between normal tensors is zero or witnesses
  the predicate.
- **Caveat:** for equal bond dimensions this is `MPSTensor.GaugeEquiv A A'`
  with the gauge `X⁻¹`; no bridge to `GaugeEquiv` is stated, because the
  predicate is only used to separate blocks of possibly different bond
  dimensions.

## Sequential preparation

### `MPSPreparation.IsProbabilisticallyGenerated`

- **Declaration:**
  `MPSPreparation.IsProbabilisticallyGenerated (D : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/Sequential.lean`.
- **Meaning:** `ψ` is the state
  $\bra{\varphi_F}A^{[N]}_{i_N}\cdots A^{[1]}_{i_1}\ket{\varphi_I}$ produced
  by arbitrary operations $A^{[k]}$ on a `D`-dimensional ancilla followed by a
  projection on $\ket{\varphi_F}$ (`MPSPreparation.seqAmplitude`). The vector is
  the unnormalized post-measurement vector. Configurations are indexed by ket
  position, so the matrix at position `p` is the source's $A^{[N-p]}$.
- **Source:** Pérez-García--Verstraete--Wolf--Cirac, arXiv:quant-ph/0608197,
  scheme 1 of section "Generation of MPS" and eq. `OBCMPSgen`,
  `Papers/quant-ph_0608197/MPSarchive.tex:1527-1552`.
- **Sanctioned bridges:** `MPSPreparation.isProbabilisticallyGenerated_iff`
  (for `0 < N` and `0 < D`, equivalent to `HasOBCRep D ψ`),
  `MPSPreparation.isProbabilisticallyGenerated_iff_cutRank_le` (for `0 < N`,
  equivalent to all cut ranks being at most `D`),
  `MPSPreparation.isLeast_isProbabilisticallyGenerated` (the least `D` is the
  largest cut rank), and
  `MPSPreparation.isDeterministicallyGenerated_iff_isProbabilisticallyGenerated`
  on normalized vectors.
- **Caveat:** the set equalities are for chains of positive length. At `N = 0`
  every open-boundary coefficient is the empty product `1`, and only the
  component theorems `exists_hasOBCRep_of_isProbabilisticallyGenerated` and
  `isProbabilisticallyGenerated_of_hasOBCRep`, stated up to a nonzero scalar,
  apply. Scheme 3 of Theorem `Thm:seqwith` is
  `MPSPreparation.IsTransitionGenerated`, and the schemes without an ancilla are
  `MPSPreparation.IsProbabilisticallyGeneratedWithoutAncilla` and
  `MPSPreparation.IsDeterministicallyGeneratedWithoutAncilla`.

### `MPSPreparation.IsDeterministicallyGenerated`

- **Declaration:**
  `MPSPreparation.IsDeterministicallyGenerated [NeZero d] (D : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/Sequential.lean`.
- **Meaning:** there are unitaries `U k` on ancilla ⊗ site and unit vectors
  $\varphi_I,\varphi_F\in\mathbb C^D$ such that, starting from
  $\ket{\varphi_I}\otimes\ket{0}^{\otimes N}$, the ancilla component of the
  joint state at every configuration `τ` is `ψ τ • φF`
  (`MPSPreparation.jointState`); that is, the ancilla decouples after the last
  step without measurement. The induced operations are
  $A_{i,\alpha\beta}=\bra{\alpha,i}U\ket{\beta,0}$
  (`MPSPreparation.stepMatrix`).
- **Source:** arXiv:quant-ph/0608197, scheme 2 of section "Generation of MPS",
  `Papers/quant-ph_0608197/MPSarchive.tex:1527-1554`.
- **Sanctioned bridges:** `MPSPreparation.isDeterministicallyGenerated_iff`
  (for `0 < N`, equivalent to normalization together with `HasOBCRep D ψ`),
  `MPSPreparation.isDeterministicallyGenerated_iff_cutRank_le` and
  `MPSPreparation.isLeast_isDeterministicallyGenerated` (the least ancilla
  dimension is the largest cut rank),
  `MPSPreparation.isDeterministicallyGenerated_pow_half` (every normalized state
  of `N ≥ 1` sites, with `D = d^{⌊N/2⌋}`),
  `MPSPreparation.isProbabilisticallyGenerated_of_isDeterministicallyGenerated`,
  and `MPSPreparation.star_dotProduct_self_of_isDeterministicallyGenerated`.
- **Caveat:** `NeZero d` is part of the definition, because each site starts in
  $\ket{0}$.

### `MPSPreparation.IsTransitionInteraction` and `MPSPreparation.IsTransitionGenerated`

- **Declarations:**
  `MPSPreparation.IsTransitionInteraction [NeZero d] (T : Matrix ((Fin D × Fin d) × Fin d) ((Fin D × Fin d) × Fin d) ℂ) : Prop`
  and
  `MPSPreparation.IsTransitionGenerated [NeZero d] (D : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/SequentialTransition.lean`.
- **Meaning:** `IsTransitionInteraction T` says that `T` acts on ancilla
  `ℂ^D`, tag qudit, and site qudit by
  $\ket{\varphi}\ket{t}\ket{0}\mapsto\ket{\varphi}\ket{0}\ket{t}$ for every
  tag `t`; for `d = 2` these are the two printed relations
  $\ket{\varphi}\ket{1}\ket{0}\mapsto\ket{\varphi}\ket{0}\ket{1}$ and
  $\ket{\varphi}\ket{0}\ket{0}\mapsto\ket{\varphi}\ket{0}\ket{0}$
  (`MPSPreparation.isTransitionInteraction_two_iff`).
  `IsTransitionGenerated D ψ` says that there are unitaries `W k` on
  $\mathbb C^D\otimes\mathbb C^d$ and unit vectors $\varphi_I,\varphi_F$ such
  that the steps "ancilla unitary, then the fixed interaction", applied to
  $\ket{\varphi_I}\otimes\ket{0}^{\otimes N}$, leave the joint state
  $\ket{\varphi_F}\otimes\ket{\psi}$ (`MPSPreparation.transitionJointState`).
  A step on a site in $\ket{0}$ is `MPSPreparation.transitionStep`.
- **Source:** arXiv:quant-ph/0608197, scheme 3 (deterministic transition
  schemes) of section "Generation of MPS",
  `Papers/quant-ph_0608197/MPSarchive.tex:1555-1567`; the interaction is the
  `D`-standard map `T` of arXiv:quant-ph/0501096, eq. `IsofromT`, extended to
  qudits as in arXiv:quant-ph/0501096, lines 412--415 of
  `References/quant-ph_0501096/PhotoMPS.tex`.
- **Sanctioned bridges:**
  `MPSPreparation.transitionStep_eq_of_isTransitionInteraction` (a step equals
  the fixed interaction after the ancilla unitary, for any `T` satisfying
  `IsTransitionInteraction`), `MPSPreparation.isTransitionGenerated_iff`
  (for `0 < N`, equivalent to normalization together with `HasOBCRep D ψ`), and
  `MPSPreparation.isTransitionGenerated_iff_isDeterministicallyGenerated`.
- **Caveat:** arXiv:quant-ph/0608197 states the scheme for qubit chains,
  `d = 2`; the predicates are stated for every `d`, as arXiv:quant-ph/0501096
  allows. The sources do not specify the interaction on site inputs other than
  $\ket{0}$, so `IsTransitionInteraction` constrains only site inputs
  $\ket{0}$, which are the only ones that occur.

### `MPSPreparation.IsProbabilisticallyGeneratedWithoutAncilla` and `MPSPreparation.IsDeterministicallyGeneratedWithoutAncilla`

- **Declarations:**
  `MPSPreparation.IsProbabilisticallyGeneratedWithoutAncilla [NeZero d] {n : ℕ} (ψ : (Fin (n + 2) → Fin d) → ℂ) : Prop`
  and
  `MPSPreparation.IsDeterministicallyGeneratedWithoutAncilla [NeZero d] {n : ℕ} (ψ : (Fin (n + 2) → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/SequentialNoAncilla.lean`.
- **Meaning:** `ψ = MPSPreparation.noAncillaState n U` for operations
  `U k` on $\mathbb C^d\otimes\mathbb C^d$, the source's $U^{[k+1]}$ acting on
  sites `k + 1` and `k + 2` of a chain of `n + 2` sites initially in
  $\ket{0}^{\otimes(n+2)}$; the operations are arbitrary in the probabilistic
  scheme (unnormalized output) and unitary in the deterministic one.
  Configurations are indexed by ket position, as for
  `MPSPreparation.IsProbabilisticallyGenerated`.
- **Source:** arXiv:quant-ph/0608197, section "Sequential generation without
  ancilla", `Papers/quant-ph_0608197/MPSarchive.tex:1580-1593`.
- **Sanctioned bridges:**
  `MPSPreparation.isProbabilisticallyGeneratedWithoutAncilla_iff` (equivalent to
  `HasOBCRep d ψ`), `MPSPreparation.isDeterministicallyGeneratedWithoutAncilla_iff`
  (equivalent to normalization together with `HasOBCRep d ψ`), and
  `MPSPreparation.noAncillaState_eq_jointState` (the scheme with a
  `d`-dimensional ancilla for the operations with swapped outputs, read out as
  the site at position `0`; the induced matrices are
  $A_{i,\beta\alpha}=\bra{i,\beta}U\ket{\alpha,0}$).
- **Caveat:** the chain has at least two sites, since the first operation acts
  on sites `1` and `2`; this is a **Local fix** recorded in
  `docs/paper-gaps/pgvwc07_sequential_no_ancilla_two_sites.tex`. The
  identification of the full chain state after `U^{[k]}` with
  $\ket{\chi_k}\otimes\ket{0}^{\otimes(N-k-1)}$ is the motivation for the
  recursive definition, not a proved statement.

### `MPSPreparation.HasOBCRep`

- **Declaration:**
  `MPSPreparation.HasOBCRep (D : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/Sequential.lean`.
- **Meaning:** `ψ = B.coeff` for some varying-bond open chain
  `B : OBCChainTensor d D N`, that is, `ψ` has an open-boundary MPS
  representation whose bond dimensions are all at most `D`.
- **Source:** "OBC MPS representation with maximal bond dimension $D$",
  arXiv:quant-ph/0608197, eq. `eq.vidal`,
  `Papers/quant-ph_0608197/MPSarchive.tex:419-429`, as used in Theorem
  `Thm:seqwith`, lines 1569--1573.
- **Sanctioned bridges:** `MPSPreparation.isProbabilisticallyGenerated_iff`,
  `MPSPreparation.isDeterministicallyGenerated_iff`,
  `MPSPreparation.hasOBCRep_iff_cutRank_le` (for `0 < N` and `0 < D`, equivalent
  to all cut ranks `MPSPreparation.cutRank ψ k` being at most `D`),
  `MPSPreparation.hasOBCRep_pow_half` (every vector on `N ≥ 1` sites, with
  `D = d^{⌊N/2⌋}`), `MPSPreparation.HasOBCRep.smul` and
  `MPSPreparation.hasOBCRep_zero` (on chains of positive length the predicate
  defines a cone), and the left-canonical representations
  `OBCChainTensor.exists_isometric_coeff_eq`,
  `OBCChainTensor.exists_isometric_coeff_eq_of_norm`, and
  `OBCChainTensor.exists_coeff_eq_of_cutRank_le` (bond `k` equal to the cut rank
  at `k`).
- **Caveat:** `D` is a common upper bound, not the least bond dimension; the
  least bond dimension at the cut `k` is `MPSPreparation.cutRank ψ k`
  (`OBCChainTensor.cutRank_coeff_le`). At `N = 0` the predicate holds only for
  the vector `1`, so the sequential-generation component theorems apply it to
  `c • ψ` with `c ≠ 0` to cover that length.

### `MPSPreparation.IsIsometryOn`, `MPSPreparation.IsSupportedBelow`, and `MPSPreparation.IsRowSupportedBelow`

- **Declarations:**
  `MPSPreparation.IsIsometryOn (b : ℕ) (Q : Fin d → Matrix (Fin D) (Fin D) ℂ) : Prop`,
  `MPSPreparation.IsSupportedBelow (b : ℕ) (v : Fin D → ℂ) : Prop`, and
  `MPSPreparation.IsRowSupportedBelow (a : ℕ) (M : Matrix (Fin D) (Fin D) ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/IsometricChain.lean`.
- **Meaning:** `IsIsometryOn b Q` says that the stacked columns
  `(α, i) ↦ Q i α β`, `β < b`, are orthonormal; for `b = D` it is
  $\sum_i Q_i^\dagger Q_i=\mathbb 1$. `IsSupportedBelow b v` says that the
  coordinates `β ≥ b` of `v` vanish, and `IsRowSupportedBelow a M` that the rows
  `α ≥ a` of `M` vanish. Together they encode a varying-bond chain stored in
  square `D × D` matrices whose site `p` lives in the upper-left
  `b p × b (p + 1)` block.
- **Source:** the isometry condition $\sum_i A_i^\dagger A_i=\mathbb 1$ of
  arXiv:quant-ph/0608197, `Papers/quant-ph_0608197/MPSarchive.tex:1535-1537`,
  and of Schön--Solano--Verstraete--Cirac--Wolf, arXiv:quant-ph/0501096, before
  eq. `MPSiso`, restricted to the used bond levels. The support predicates are
  project definitions.
- **Sanctioned bridges:** `MPSPreparation.isIsometryOn_stepMatrix` (operations
  induced by a unitary), `MPSPreparation.exists_unitary_extension` (the
  converse extension), `MPSPreparation.sum_normSq_eval_mulVec` (norm
  preservation), and `OBCChainTensor.sum_conjTranspose_mul_ofSupported`, which
  turns block isometry into $\sum_i A_i^\dagger A_i=\mathbb 1$ for the cut-down
  rectangular chain.
- **Caveat:** these predicates are statements about square padded matrices. No
  bridge to the translation-invariant left-canonical or trace-preservation
  predicates on `MPSTensor` is stated; the rectangular condition is recovered only through
  `OBCChainTensor.ofSupported`.

### `MPSPreparation.HasMixedSequentialFactorization`

- **Declaration:** `MPSPreparation.HasMixedSequentialFactorization hD V : Prop`,
  for a positive bond dimension and a matrix from a finite input space to
  the physical configurations of a left chain, a central site, and a right chain.
- **Defined in:** `TNLean/MPS/Preparation/MixedSequentialFactorization.lean`.
- **Meaning:** $V=(E_L\otimes I_d\otimes E_R)C$, where each side is evaluated
  from its outer boundary inward using isometric site maps, both outer bonds
  have dimension one, every bond has dimension at most $D^2$, and $C$ is an
  isometry from the input to the two inward bonds and the central physical site.
- **Source:** arXiv:2307.01696, page 3, footnotes 3 and 4 to equations (13)--(15).
- **Sanctioned bridges:** `MPSPreparation.exists_mixed_isometric_factorization`
  for an isometric matrix product map;
  `MPSPreparation.exists_mixed_sequential_polarIsoMatrix` for an injective
  blocked chain on its full virtual-pair input; and
  `MPSPreparation.exists_mixed_sequential_polar_support` for every blocked
  chain on its actual polar support, with any chosen central site.
- **Caveat:** no monotonicity of bond dimensions is asserted. For a non-injective
  block, only the support-restricted polar map is an isometry; its extension
  to the full virtual-pair space remains a partial isometry. The original
  map is recovered by the adjoint of the support embedding. This is a local
  correction to the printed full-input pseudoinverse claim, whose nonzero
  rank-deficient witness remains in
  `docs/paper-gaps/mswc24_mixed_polar_injectivity_scope.tex`.

## Quantum circuits

The circuit layer `TNLean/Circuit/` (namespace `QuantumCircuit`) imports nothing
from `TNLean/MPS/`. Its local labels are `Fin d`. The notions that involve no
geometry (operators acting on a set of sites, expectations, product vectors,
placed operators, permutations of configurations and of sites, onsite
channels) are stated for any finite type of sites `ι`. Layers, circuits and
light cones are stated for a bond geometry `bond : β → Set ι` on such a type
(`TNLean/Circuit/Geometry.lean`), with the ring `ringBond k = {k, k + 1}` on
`Fin N` (addition modulo `N`), the open chain `openBond`, and the edges of a
simple graph `edgeBond G` as instances; the ring-facing names (`Layer`,
`IsLocalCircuitOfDepth`, `IsPreparedInDepth`, `IsCircuitOn`, `ChannelLayer`,
`IsChannelPreparedInDepth`) abbreviate the general notions for `ringBond`.
Measurement protocols and teleportation remain stated on the ring. The blueprint chapter is
`ch33_local_quantum_circuits.tex`; the preparation of matrix product states
in `MPS/Preparation/` uses it.

### Local circuits and two-site gates

#### `QuantumCircuit.supportedOperators`

- **Declaration:**
  `QuantumCircuit.supportedOperators {ι : Type*} [Fintype ι] (d : ℕ) (S : Set ι) : Submodule ℂ (Matrix (ι → Fin d) (ι → Fin d) ℂ)`.
- **Defined in:** `TNLean/Circuit/LocalCircuit.lean`.
- **Meaning:** the complex span of the product operators
  `Matrix.rectKronecker m = ⊗ᵢ mᵢ` with `mᵢ = 1` for every `i ∉ S`, that is
  `M_d^{⊗ S} ⊗ 1`: the operators acting on the sites of `S` of a finite type
  of `d`-level sites `ι`. The chain of `N` sites is `ι = Fin N`, where
  `Matrix.rectKronecker m` is `Matrix.finKronecker m`.
- **Source:** arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the
  operators `𝒪₁` and `𝒪'ₛ` acting on sites of the chain).
- **Sanctioned bridges:** `QuantumCircuit.rectKronecker_mem_supportedOperators`
  and its chain form `QuantumCircuit.finKronecker_mem_supportedOperators`,
  `QuantumCircuit.supportedOperators_mono`,
  `QuantumCircuit.one_mem_supportedOperators`,
  `QuantumCircuit.mul_mem_supportedOperators`,
  `QuantumCircuit.star_mem_supportedOperators`,
  `QuantumCircuit.commute_of_mem_supportedOperators` (operators acting on
  disjoint sets commute), and `QuantumCircuit.embedOp_mem_supportedOperators`
  (an operator placed by an injective map acts on its range).
- **Caveat:** membership says nothing about unitarity; for `S = ∅` the
  submodule consists of the scalar multiples of the identity.

#### `QuantumCircuit.bondNeighbourhood` and `QuantumCircuit.lightCone`

- **Declarations:**
  `QuantumCircuit.bondNeighbourhood {ι β : Type*} (bond : β → Set ι) (X : Set ι) : Set ι`
  and `QuantumCircuit.lightCone (bond : β → Set ι) (X : Set ι) : ℕ → Set ι`.
- **Defined in:** `TNLean/Circuit/Geometry.lean`.
- **Meaning:** `X` together with every bond meeting `X`, and its `r`-fold
  iterate.
- **Source:** arXiv:2307.01696, Supplemental Material, proof of Theorem 1 (the
  light cone); arXiv:2103.13367, main text, paragraph "Quantum circuits and
  LOCC" (gates on nearest-neighbour pairs of a lattice) and the graph
  distance before Proposition `propQCA2`.
- **Sanctioned bridges:** `QuantumCircuit.lightCone_ringBond` (on the ring,
  the light cone of radius `r` is `neighbourhood X r`, the sites within ring
  distance `r`, for every `N`), `QuantumCircuit.lightCone_openBond_subset`,
  `QuantumCircuit.lightCone_edgeBond_subset` and
  `QuantumCircuit.lightCone_edgeBond_subset_dist` (graph distance), with the
  disjointness criteria `disjoint_lightCone_ringBond_of_isSeparatedBy`,
  `disjoint_lightCone_openBond`, `disjoint_lightCone_edgeBond` and
  `disjoint_lightCone_edgeBond_of_dist`.
- **Caveat:** for the open chain and graphs only the inclusion in the metric
  ball is proved; on the ring the equality holds.

#### `QuantumCircuit.IsSeparatedBy`

- **Declaration:**
  `QuantumCircuit.IsSeparatedBy {N : ℕ} [NeZero N] (X Y : Set (Fin N)) (s : ℕ) : Prop`.
- **Defined in:** `TNLean/Circuit/Geometry.lean`.
- **Meaning:** the sets `X` and `Y` of ring sites are at ring distance larger
  than `s`: no `y ∈ Y` equals `x + m` with `x ∈ X` and `|m| ≤ s`, the addition
  taken modulo `N`. Equivalently, `Y` misses the neighbourhood
  `neighbourhood X s` of sites within ring distance `s` of `X`.
- **Source:** arXiv:2307.01696, Supplemental Material, proof of Theorem 1
  (operators at a distance larger than `2T` have uncorrelated expectations in a
  state prepared by a local circuit of depth `T`).
- **Sanctioned bridges:** `QuantumCircuit.IsSeparatedBy.symm`,
  `QuantumCircuit.IsSeparatedBy.notMem_neighbourhood`,
  `QuantumCircuit.isSeparatedBy_of_val_bounds` (two windows of consecutive
  sites with gaps of at least `s` on both sides of the ring),
  `QuantumCircuit.disjoint_neighbourhood_of_isSeparatedBy` and
  `QuantumCircuit.disjoint_lightCone_ringBond_of_isSeparatedBy` (separation by
  `2T` makes the light cones of radius `T` disjoint), and, for nonempty sets,
  `MPSPreparation.isSeparatedBy_iff_lt_ringSupportDistance` (separation by `s`
  is `s` strictly below the ring distance of the supports).
- **Caveat:** the inequality is strict, so `IsSeparatedBy X Y (2 * T)`
  excludes sets at ring distance exactly `2T`, whose light cones of radius `T`
  share a site. If `X` or `Y` is empty the predicate holds for every `s`; if
  both are nonempty it fails as soon as `N ≤ 2s + 1`, since the offsets
  `|m| ≤ s` then reach every site of the ring.

#### `QuantumCircuit.BondLayer` and `QuantumCircuit.Layer`

- **Declarations:** `structure QuantumCircuit.BondLayer (d : ℕ) (bond : β → Set ι)`,
  with fields `bonds : Finset β`, `gate : β → Matrix (ι → Fin d) (ι → Fin d) ℂ`,
  and the conditions that every gate of a bond is unitary and lies in
  `supportedOperators d (bond b)`, and that the bonds carrying gates are
  pairwise disjoint; `QuantumCircuit.Layer (d N : ℕ) [NeZero N]` abbreviates
  `BondLayer d ringBond` on `Fin N`.
- **Defined in:** `TNLean/Circuit/LocalCircuit.lean`.
- **Meaning:** one layer of a local circuit: unitaries on pairwise disjoint
  bonds; on the ring, pairs of neighbouring sites. Its operator
  `BondLayer.op` is the product of its gates, which commute.
- **Source:** arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local
  quantum circuits"); arXiv:2103.13367, main text, paragraph "Quantum circuits
  and LOCC".
- **Sanctioned bridges:** `BondLayer.op_mem_unitary`,
  `BondLayer.conj_op_mem_supportedOperators` (the light cone of one layer),
  and `BondLayer.adjoint` with `BondLayer.adjoint_op` (the layer of the adjoint
  gates implements the adjoint).
- **Caveat:** on the ring the pairs are taken modulo `N`, so for `N ≤ 2` they
  degenerate; the open chain is the separate geometry `openBond`.

#### `QuantumCircuit.IsLocalCircuitOfDepth`

- **Declaration:**
  `QuantumCircuit.IsLocalCircuitOfDepth (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (T : ℕ) : Prop`.
- **Defined in:** `TNLean/Circuit/LocalCircuit.lean`.
- **Meaning:** `U = circuitOp Ls` for a list `Ls` of exactly `T` layers, the
  head of the list applied first.
- **Source:** arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local
  quantum circuits").
- **Sanctioned bridges:** it abbreviates `IsBondCircuitOfDepth ringBond U T`;
  `IsBondCircuitOfDepth.mem_unitary`, `IsBondCircuitOfDepth.star`,
  `IsBondCircuitOfDepth.mul` (depths add),
  `IsBondCircuitOfDepth.conj_mem_supportedOperators` (the light cone of radius
  `T` for any bond geometry), `QuantumCircuit.conj_circuitOp_mem_supportedOperators`
  (on the ring, within ring distance `T`),
  `QuantumCircuit.isLocalCircuitOfDepth_finKronecker` (one-site unitaries in
  depth `2`), and `QuantumCircuit.IsBondCircuitOn.isBondCircuitOfDepth`.
- **Caveat:** the depth is exact in the definition; a smaller depth is padded
  with empty layers, as in `IsBondCircuitOn.mono`.

#### `QuantumCircuit.IsPreparedInDepth`

- **Declaration:**
  `QuantumCircuit.IsPreparedInDepth (T : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/LocalCircuit.lean`.
- **Meaning:** `ψ = U *ᵥ productVector v` for a local circuit `U` of depth `T`
  and a product vector `productVector v = ⊗ᵢ vᵢ`.
- **Source:** arXiv:2307.01696, main text before Theorem 1 ("a sequence
  obtained from depth-`T` local quantum circuits applied to product states").
- **Sanctioned bridges:** it abbreviates `IsBondPreparedInDepth ringBond T ψ`;
  `IsBondPreparedInDepth.expect_mul_eq` (vanishing connected correlations of
  operators on sets with disjoint light cones, for any bond geometry),
  `QuantumCircuit.expect_mul_eq_of_isPreparedInDepth`
  and `QuantumCircuit.expect_mul_mul_expect_one_of_isPreparedInDepth`
  (on the ring, operators at ring distance larger than `2T`), `QuantumCircuit.IsPreparedInDepth.exists_eq_smul_mulVec_productVector_single_zero`
  (a nonzero prepared vector is a multiple of a local circuit of depth `T + 2`
  applied to `|0⋯0⟩`), and
  `QuantumCircuit.isPreparedWithMeasurementsInDepth_of_isPreparedInDepth`.
- **Caveat:** no normalization is imposed and `ψ` may be zero. The separation
  `IsSeparatedBy X Y (2 * T)` in the correlation bounds excludes operators at
  ring distance exactly `2T`.

#### `QuantumCircuit.IsNeighbourGate` and `QuantumCircuit.IsPairProduct`

- **Declarations:**
  `QuantumCircuit.IsNeighbourGate (Z : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop`
  and
  `QuantumCircuit.IsPairProduct (d n K : ℕ) (X : Matrix (Fin n → Fin d) (Fin n → Fin d) ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/PairProduct.lean`.
- **Meaning:** `IsNeighbourGate Z` says that `Z` is unitary and acts on two
  neighbouring sites `{p, p + 1}` of the open chain of `n` sites.
  `IsPairProduct d n K X` says that `X` is a product of at most `K` such gates.
- **Source:** Malz--Styliaris--Wei--Cirac, arXiv:2307.01696, main text before
  Theorem 1 (local circuits of two-site gates) and the caption of Fig. 1
  (unitaries with constant support "can be further expressed with a low-depth
  circuit of local gates").
- **Sanctioned bridges:** `QuantumCircuit.exists_isPairProduct` (for `0 < d`
  and `2 ≤ n`, one bound `K` covers every unitary on `n` sites), and
  `QuantumCircuit.IsPairProduct.isCircuitOn`, which places such a product on
  consecutive sites of the ring as a local circuit of depth `K`.
- **Caveat:** the chain is open; the ring structure enters only through the
  placement map of `IsPairProduct.isCircuitOn`.

#### `QuantumCircuit.BondLayer.IsIn`

- **Declaration:**
  `QuantumCircuit.BondLayer.IsIn (L : BondLayer d bond) (R : Set ι) : Prop`.
- **Defined in:** `TNLean/Circuit/Composition.lean`.
- **Meaning:** every gate of the layer `L` acts on a bond contained in the set
  of sites `R`.
- **Source:** arXiv:2307.01696, paragraph "The sequential-RG circuit", where
  the block unitaries act in parallel on disjoint blocks of sites; the source
  has no separate name for this support condition.
- **Sanctioned bridges:** `BondLayer.IsIn.mono` enlarges `R`;
  `BondLayer.op_mem_supportedOperators` places the layer operator among the
  operators supported on `R`; `BondLayer.union` and `BondLayer.union_op`
  merge layers acting in disjoint sets; `BondLayer.empty_isIn` covers the
  empty layer.
- **Caveat:** the condition is on the bonds of the layer, not on its operator;
  it is the per-layer ingredient of `IsBondCircuitOn`. `BondLayer.union_op`
  needs every bond to be nonempty, as the ring bonds are.

#### `QuantumCircuit.IsBondCircuitOn` and `QuantumCircuit.IsCircuitOn`

- **Declarations:**
  `QuantumCircuit.IsBondCircuitOn (bond : β → Set ι) (R : Set ι) (T : ℕ) (U : Matrix (ι → Fin d) (ι → Fin d) ℂ) : Prop`
  and its ring abbreviation
  `QuantumCircuit.IsCircuitOn (R : Set (Fin N)) (T : ℕ) (U : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Composition.lean`.
- **Meaning:** `U` is the operator of a list of exactly `T` layers, each of
  whose gates acts inside the set of sites `R`.
- **Source:** arXiv:2307.01696, main text before Theorem 1 ("depth-`T` local
  quantum circuits"), restricted to gates inside `R` as in the parallel
  application of block unitaries in the paragraph "The sequential-RG circuit".
- **Sanctioned bridges:** `IsBondCircuitOn.isBondCircuitOfDepth` forgets the
  support; `IsBondCircuitOn.mul` composes in series (depths add), and
  `IsBondCircuitOn.par` (for nonempty bonds) and its ring form
  `IsCircuitOn.par` run two circuits of the same depth on disjoint sets of
  sites in parallel.
- **Caveat:** the depth is exact in the definition; `IsBondCircuitOn.mono`
  pads it with empty layers.

#### `QuantumCircuit.IsSpecialTwo`, `QuantumCircuit.IsTwoLevelWord`, and `QuantumCircuit.FixesOutside`

- **Declarations:**
  `QuantumCircuit.IsSpecialTwo (g : Matrix (Fin 2) (Fin 2) ℂ) : Prop`,
  `QuantumCircuit.IsTwoLevelWord (K : ℕ) (X : Matrix ι ι ℂ) : Prop`, and
  `QuantumCircuit.FixesOutside (T : Finset ι) (X : Matrix ι ι ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Gates/ControlledProducts.lean`
  (`IsSpecialTwo`) and `TNLean/Circuit/Gates/Givens.lean`.
- **Meaning:** `IsSpecialTwo g` says that `g` is a real rotation `rotTwo z` or
  a diagonal phase `diagTwo ν` with `‖z‖ = ‖ν‖ = 1`. `IsTwoLevelWord K X` says
  that `X` is a product of at most `K` two-level operators `twoLevel a b g` with
  `a ≠ b` and `IsSpecialTwo g`. `FixesOutside T X` says that every entry of
  `X` in a row or column outside `T` is that of the identity, so `X` fixes the
  basis vectors outside `T` and preserves the span of `T`.
- **Source:** no separate source notion; these are the intermediate steps of
  the Givens elimination behind the caption of Fig. 1 of arXiv:2307.01696.
- **Sanctioned bridges:** `QuantumCircuit.isTwoLevelWord_of_det_eq_one` (every
  unitary of determinant one is a two-level word of bounded length) and
  `QuantumCircuit.isTwoLevelWord_of_fixesOutside`.
- **Caveat:** these predicates are proof-internal vocabulary for
  `exists_isPairProduct`; statements about circuits should use
  `IsPairProduct` or `IsCircuitOn`.

#### `QuantumCircuit.AgreeOff`

- **Declaration:**
  `QuantumCircuit.AgreeOff {ι κ : Type*} (e : κ → ι) (x y : ι → Fin d) : Prop`.
- **Defined in:** `TNLean/Circuit/SiteEmbedding.lean`.
- **Meaning:** the configurations `x` and `y` of the sites `ι` agree at every
  site outside the range of `e`; for chains, `e : Fin m → Fin n`.
- **Source:** no separate source notion; it describes the entries of the
  placement `QuantumCircuit.embedOp e X` of an operator on the sites `κ`.
- **Sanctioned bridges:** `QuantumCircuit.sum_agreeOff` and
  `QuantumCircuit.eq_extend_of_agreeOff` (for injective `e`).
- **Caveat:** proof-internal vocabulary for the site embedding.

### Local circuits assisted by measurements

#### `QuantumCircuit.MeasurementProtocol.IsPreparationOf`

- **Declaration:**
  `QuantumCircuit.MeasurementProtocol.IsPreparationOf [NeZero N] (P : MeasurementProtocol d N) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Protocol.lean`.
- **Meaning:** the protocol `P` (a product vector, a local circuit, a set of
  sites measured in the computational basis, and for every outcome string a
  unitary at every site) starts from a nonzero product vector, and for every
  outcome `m` with `P.postMeasurement m ≠ 0` the corrected vector `P.output m`
  is a scalar multiple of `ψ`.
- **Source:** arXiv:2103.13367, main text, paragraph "State transformations
  with QC and LOCC" (the scheme "apply `U ∈ LU` depending on the outcomes of
  all previous measurements", and deterministic preparation).
- **Sanctioned bridges:** `MeasurementProtocol.IsPreparationOf.ne_zero` (a
  prepared vector is nonzero) and
  `MeasurementProtocol.exists_postMeasurement_ne_zero`.
- **Caveat:** ancillas are sites of the ring; the measurement is fixed in
  advance and in the computational basis; the correction is one product of
  single-site unitaries applied after all the measurements. Each of these
  restricts the source's scheme, so every such protocol is one of the source.

#### `QuantumCircuit.IsPreparedWithMeasurementsInDepth`

- **Declaration:**
  `QuantumCircuit.IsPreparedWithMeasurementsInDepth [NeZero N] (T : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Protocol.lean`.
- **Meaning:** some protocol `P` whose circuit has at most `T` layers
  satisfies `P.IsPreparationOf ψ`.
- **Source:** arXiv:2103.13367, Definition "Transformations under QC and
  LOCC" (the class `QCcc_ℓ`).
- **Sanctioned bridges:**
  `QuantumCircuit.isPreparedWithMeasurementsInDepth_of_isPreparedInDepth` (a
  nonzero vector prepared by a local circuit),
  `QuantumCircuit.exists_isPreparedInDepth_of_isPreparationOf_of_measured_eq_empty`
  (without measurements, preparation by a local circuit up to single-site
  unitaries), and
  `QuantumCircuit.isPreparedWithMeasurementsInDepth_withZeroAncillas_ghzState`
  (GHZ-type states in depth `2`).
- **Caveat:** the free local unitaries of the source between the layers of the
  circuit, acting on a site and its ancillas, are counted here as gates, so the
  depth bounds the source's depth. The light-cone bound of
  `QuantumCircuit.expect_mul_eq_of_isPreparedInDepth` has no analogue here:
  GHZ-type states, whose connected correlations do not decay, are prepared in
  depth `2`.

#### `QuantumCircuit.IsPreparedWithMeasurementsAndCircuitInDepth`

- **Declaration:**
  `QuantumCircuit.IsPreparedWithMeasurementsAndCircuitInDepth [NeZero N] (T : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Protocol.lean`.
- **Meaning:** `ψ = U φ` for a vector `φ` with
  `IsPreparedWithMeasurementsInDepth T₁ φ` and a local circuit `U` of depth
  `T₂`, with `T₁ + T₂ ≤ T`.
- **Source:** arXiv:2307.01696, paragraph "Long-range MPS using measurements"
  ("First create `|χ_{N/q}⟩`, which can be done in constant depth with
  measurements ... Subsequently, apply in parallel the isometries `W`");
  arXiv:2103.13367, paragraph "State transformations with QC and LOCC" ("a
  more general scheme with multiple rounds of LOCC").
- **Sanctioned bridges:**
  `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_sum_blockIsometryState`
  (the states `∑ⱼ αⱼ (⊗ₖ V_{j,k}) ⊗ₖ |ω_j⟩` of blocks with orthogonal blocked
  states, in depth `O(L)`) and
  `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_repeatedBlockSum`
  (error `ε` in depth `O(log(N/ε))` for direct sums of normal blocks with
  orthogonal blocked states and block lengths dividing `N`), and
  `MPSPreparation.exists_isPreparedWithMeasurementsAndCircuitInDepth_le_log_of_mpvState_ne_zero`
  (the same for blocks whose states may overlap, every multiplicity, every
  nonzero complex weight and every `N ≥ 2` with `|φ_N(A)⟩ ≠ 0`).
- **Caveat:** the circuit `U` is applied after the measurement and its
  corrections and does not depend on the outcomes; it is one second round of
  the source's multi-round scheme, with no measurement in it.

#### `QuantumCircuit.IsAsymptoticallyPreparedWithMeasurementsInDepth`

- **Declaration:**
  `QuantumCircuit.IsAsymptoticallyPreparedWithMeasurementsInDepth (f : ℕ → ℝ) (φ : (N : ℕ) → EuclideanSpace ℂ (Fin N → Fin d)) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Asymptotic.lean`.
- **Meaning:** there are unit vectors `ψ_N`, each prepared for all large `N`
  with `IsPreparedWithMeasurementsAndCircuitInDepth T (ψ_N)` for some
  `T ≤ f N`, with `‖|ψ_N⟩⟨ψ_N| - |φ_N⟩⟨φ_N|‖₁ → 0`.
- **Source:** arXiv:2103.13367, paragraph "Phases of matter": `Ψ ↦ Φ` when
  compositions of `k` channels of `QCcc` of depth `f(M)` map `|ψ_M⟩` to states
  `σ_M` with `‖σ_M - |φ_M⟩⟨φ_M|‖₁ → 0`.
- **Sanctioned bridges:**
  `QuantumCircuit.isAsymptoticallyPreparedWithMeasurementsInDepth_of_one_sub_norm_inner_le`
  (overlap errors `1 - |⟨ψ_N|φ_N⟩|` tending to zero give trace-norm
  convergence, via `Matrix.traceNormPureSub_le`) and
  `MPSPreparation.isAsymptoticallyPreparedWithMeasurementsInDepth_normalizedMPVState`
  (the normalized periodic states of a translation-invariant MPS in depth
  `C log N`).
- **Caveat:** the predicate is the relation `Ψ ↦ Φ` of the source only for
  `Ψ` the trivial sequence of product states, `k = 2` (a preparation with
  measurements, then a circuit), and `σ_M = |ψ_M⟩⟨ψ_M|` pure and prepared
  deterministically. The depth `f` is arbitrary; agreement with the source's
  relation requires `f` polylogarithmic. It is one direction only: the
  source's equivalence of phases asks for `Ψ ↦ Φ` and `Φ ↦ Ψ`, and the
  converse direction, with channels acting on arbitrary input states, is not
  covered (`docs/paper-gaps/psc21_mps_classification_scope.tex`).

#### `QuantumCircuit.IsLocalPerm`

- **Declaration:**
  `QuantumCircuit.IsLocalPerm {ι : Type*} (S : Set ι) (σ : Equiv.Perm (ι → Fin d)) : Prop`.
- **Defined in:** `TNLean/Circuit/Gates/Permutation.lean`.
- **Meaning:** the permutation `σ` of the configurations changes only the
  sites of `S`, and its new values on `S` depend only on the old values on
  `S`.
- **Source:** arXiv:2103.13367, Example 1 (the CNOT gates and Pauli
  corrections of the GHZ preparation, generalized to shifts of qudits).
- **Sanctioned bridges:** `IsLocalPerm.permMatrix_mem_supportedOperators` (the
  permutation matrix is a unitary acting on `S`),
  `QuantumCircuit.isLocalPerm_shiftPerm`, and
  `QuantumCircuit.exists_permLayer_op_mulVec` (a layer of such gates on
  disjoint pairs acts as one permutation of the configurations).
- **Caveat:** only permutations of the computational basis are covered; a
  general gate is a `QuantumCircuit.Layer` gate.

#### `QuantumCircuit.IsPreparedWithMeasurementRoundsInDepth`

- **Declaration:**
  `QuantumCircuit.IsPreparedWithMeasurementRoundsInDepth [NeZero N] (T : ℕ) (ψ : (Fin N → Fin d) → ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Rounds.lean`.
- **Meaning:** some sequence of measurement rounds (`QuantumCircuit.MeasurementRound`:
  a local circuit, a computational-basis measurement of a set of sites, and
  outcome-dependent single-site unitaries), whose circuits have at most `T`
  layers in total, takes a nonzero product vector to a scalar multiple of `ψ`
  after every sequence of outcomes of nonzero probability.
- **Source:** arXiv:2103.13367, paragraphs "State transformations with QC and
  LOCC" (one round, and "a more general scheme with multiple rounds of
  LOCC"); arXiv:2307.01696, paragraph "Tree-RG circuit with measurements".
- **Sanctioned bridges:**
  `QuantumCircuit.isPreparedWithMeasurementRoundsInDepth_of_isPreparedWithMeasurementsInDepth`
  (one round is a protocol of `QuantumCircuit.IsPreparedWithMeasurementsInDepth`),
  `QuantumCircuit.MeasurementRound.IsRoundsImplementationOn.isPreparedWithMeasurementRoundsInDepth`,
  and `MPSPreparation.isPreparedWithMeasurementRoundsInDepth_treeOp` (binary
  trees of two-site gates with `k` levels in depth `5k`).
- **Caveat:** the depth counts the layers of all the rounds; measurements,
  classical processing and single-site corrections are free, as in one round.
  The circuit of a later round does not depend on earlier outcomes.
  Every round is a protocol of `QCcc_ℓ` of no larger depth, but the number of
  rounds is not bounded (the tree of `k` levels uses `2k` rounds), whereas in
  the class `QCcc^{(k)}_ℓ` of the paragraph "Phases of matter" of
  arXiv:2103.13367 the number `k` of composed transformations does not depend
  on the system size.

#### `QuantumCircuit.MeasurementRound.IsRoundsImplementationOn`

- **Declaration:**
  `QuantumCircuit.MeasurementRound.IsRoundsImplementationOn [NeZero N] (Rs : List (MeasurementRound d N)) (E : Set ((Fin N → Fin d) → ℂ)) (W : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Measurement/Rounds.lean`.
- **Meaning:** for every `v ∈ E`, every output of the rounds `Rs` from `v` is a
  scalar multiple of `W v`; the single-round form is
  `QuantumCircuit.MeasurementRound.IsImplementationOn`, which asks for one
  scalar per outcome.
- **Source:** arXiv:2307.01696, paragraph "Tree-RG circuit with measurements"
  ("correcting (without postselection) based on the measurement outcomes").
- **Sanctioned bridges:**
  `QuantumCircuit.MeasurementRound.IsRoundsImplementationOn.append`
  (implementations compose), `QuantumCircuit.TeleportHop.isImplementationOn_round`
  (teleportation along chains of hops in one round of depth `2`),
  `QuantumCircuit.LongRangeGate.isRoundsImplementationOn_rounds` (a layer of
  two-site gates between distant sites in depth `5`), and
  `MPSPreparation.isRoundsImplementationOn_treeRounds`.
- **Caveat:** the scalar may depend on the outcomes and is not normalized; zero
  outputs, of probability zero, are allowed.

### Local channel conversions

#### `QuantumCircuit.IsLocalChannelProtocol`

- **Declaration:**
  `QuantumCircuit.IsLocalChannelProtocol [NeZero N] : ℕ → (Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ →ₗ[ℂ] Matrix (Fin N → Fin e) (Fin N → Fin e) ℂ) → Prop`
  (an inductive predicate, with the local dimensions `d`, `e` implicit).
- **Defined in:** `TNLean/Circuit/Channel/Conversion.lean`.
- **Meaning:** `IsLocalChannelProtocol T Ψ` says that
  $\Psi=\Phi_T\circ L_T\circ\Phi_{T-1}\circ\cdots\circ L_1\circ\Phi_0$
  alternates `T` layers `L_t` of local channels on pairs of neighbouring sites
  of the ring (`QuantumCircuit.ChannelLayer`) with onsite channels $\Phi_t$
  (`QuantumCircuit.OnsiteChannel d e (Fin N)`), each a tensor product of
  one-site channels that may change the local dimension; onsite channels
  `QuantumCircuit.OnsiteChannel d e ι` are defined for any type of sites `ι`. Attaching an ancilla in a fixed state
  (`OnsiteChannel.attach`) and discarding it (`OnsiteChannel.discard`) are
  onsite channels.
- **Source:** Piroli--Styliaris--Cirac, arXiv:2103.13367, main text, paragraph
  "Quantum circuits and LOCC" (the circuits
  $V'=U_\ell V_\ell\cdots U_1V_1U_0$ with local operations $U_n$ on each site
  and its ancillas between the layers $V_n$), with channels in place of
  unitaries.
- **Sanctioned bridges:** `IsLocalChannelProtocol.isKrausCPTP` (the map is a
  channel), `IsLocalChannelProtocol.comp` (protocols compose and depths add),
  `IsLocalChannelProtocol.channelCircuitMap_comp` (appending a local channel
  circuit of `n` layers adds `n` to the depth), and
  `IsLocalChannelProtocol.exists_dual` (light cone of radius `T` of the
  Heisenberg dual).
- **Caveat:** the depth `T` counts the two-site layers exactly; onsite channels
  are free. Onsite channels may enlarge the dimension, and a layer on the
  enlarged sites still costs one depth unit. No uniform intermediate-dimension
  bound is imposed. There is no classical feedforward. The source's intersite
  gates act only on fixed-dimensional physical qudits; no uniform-depth
  simulation or inclusion in its LOCC relation is proved. See
  `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

#### `QuantumCircuit.IsAdaptiveChannelProtocol`

- **Declaration:** `QuantumCircuit.IsAdaptiveChannelProtocol T Ψ : Prop`,
  for `[NeZero N]`, a depth bound `T : ℕ`, and a linear map between chain
  operators with possibly different local dimensions.
- **Defined in:** `TNLean/Circuit/Measurement/AdaptiveConversion.lean`.
- **Meaning:** a finite tree of onsite channels, nearest-neighbor channel
  layers, and onsite instruments with outcome-dependent continuations.
  Each branch has at most `T` nearest-neighbor layers; onsite operations
  and communication of the complete outcome tuple cost zero depth.
  `OnsiteChannel.feedforwardMap` sums unnormalized outcome operations,
  including zero-probability outcomes, and never divides by probabilities.
- **Source:** arXiv:2103.13367, paragraph "State transformations with QC and
  LOCC", motivates finite adaptive operations. The formal predicate uses
  enlarged-site gate costs rather than the source's fixed physical-qudit costs.
- **Sanctioned bridges:** `IsAdaptiveChannelProtocol.isKrausCPTP`,
  `IsAdaptiveChannelProtocol.comp` (additive depth bounds),
  `IsAdaptiveChannelProtocol.onsite_comp`, and
  `IsLocalChannelProtocol.adaptive` (deterministic local protocols are included),
  and `MeasurementRound.adaptive` (the existing measurement round's average
  channel has the same quantum-depth bound).
- **Caveat:** intermediate onsite dimensions are unrestricted; a two-site
  gate on the enlarged spaces still costs one layer. No uniform-depth
  simulation into the source physical-qudit model is established. Also,
  this is an upper bound on quantum depth. The source fixes the number of
  composed `QCcc` blocks independently of system size; a block can already
  contain sequential measurements/corrections at many sites. The tree does
  not record a fixed-number source-block decomposition with the required
  internal measurement/control order and one-measurement-per-site rule. See
  `docs/paper-gaps/psc21_adaptive_channel_round_scope.tex`.

#### `QuantumCircuit.IsAdaptiveChannelConversion`

- **Declaration:** `QuantumCircuit.IsAdaptiveChannelConversion T ρ σ : Prop`,
  for `[NeZero N]` and operators on `N`-site chains.
- **Defined in:** `TNLean/Circuit/Measurement/AdaptiveConversion.lean`.
- **Meaning:** there is a map `Ψ` with `IsAdaptiveChannelProtocol T Ψ`
  and `Ψ ρ = σ`.
- **Source:** arXiv:2103.13367, paragraph "State transformations with QC and
  LOCC", with the enlarged-site and finite-round scope of
  `IsAdaptiveChannelProtocol`.
- **Sanctioned bridges:** `IsAdaptiveChannelConversion.refl`,
  `IsAdaptiveChannelConversion.mono`, `IsAdaptiveChannelConversion.trans`,
  `IsAdaptiveChannelConversion.density`, and
  `IsLocalChannelConversion.adaptive`.
- **Caveat:** exact, directed conversion on arbitrary input operators;
  positivity and unit trace of the output follow from those of the input.
  No symmetry or asymptotic phase classification is asserted.

#### `QuantumCircuit.IsLocalChannelConversion`

- **Declaration:**
  `QuantumCircuit.IsLocalChannelConversion [NeZero N] (T : ℕ) (ρ : Matrix (Fin N → Fin d) (Fin N → Fin d) ℂ) (σ : Matrix (Fin N → Fin d') (Fin N → Fin d') ℂ) : Prop`.
- **Defined in:** `TNLean/Circuit/Channel/Conversion.lean`.
- **Meaning:** `σ = Ψ ρ` for a map `Ψ` with `IsLocalChannelProtocol T' Ψ` for
  some `T' ≤ T`.
- **Source:** arXiv:2103.13367, main text, paragraph "Quantum circuits and
  LOCC" (circuits with ancillas attached to each site) and paragraph "Phases
  of matter" (a protocol "where ancillas are traced out at the end, defines a
  quantum channel"), without measurements or classical communication.
- **Sanctioned bridges:** `IsLocalChannelConversion.refl` (depth `0`),
  `IsLocalChannelConversion.mono`, `IsLocalChannelConversion.trans` (depths
  add), `IsLocalChannelConversion.exists_isKrausCPTP`,
  `IsLocalChannelConversion.density` (a conversion of a density matrix is a
  density matrix), `QuantumCircuit.isLocalChannelConversion_circuit` (attach,
  run a local channel circuit, discard),
  `QuantumCircuit.IsChannelPreparedInDepth.exists_isLocalChannelConversion`,
  and `QuantumCircuit.trace_mul_mul_eq_of_isLocalChannelConversion` (vanishing
  connected correlations beyond ring distance `2T` from a product density).
- **Caveat:** the relation is directed and not symmetric: a channel need not be
  undone by another channel. Neither `ρ` nor `σ` is required to be a density
  matrix; positivity and unit trace of `σ` follow from those of `ρ` by
  `IsLocalChannelConversion.density`. Conversions are exact; the approximate
  and asymptotic local-channel relations below extend this relation without
  classical feedforward. The full phase equivalence in arXiv:2103.13367 and
  blocking of sites are not formalized here.

#### `QuantumCircuit.IsApproxLocalChannelConversion`

- **Declaration:** `QuantumCircuit.IsApproxLocalChannelConversion T ε ρ σ : Prop`,
  for `T : ℕ`, `ε : ℝ`, `[NeZero N]`, and operators on `N`-site chains whose
  fixed local dimensions may differ.
- **Defined in:** `TNLean/Circuit/Channel/ApproximateConversion.lean`.
- **Meaning:** there are `S ≤ T` and a map `Ψ` with
  `IsLocalChannelProtocol S Ψ` such that $\lVert\Psi(\rho)-\sigma\rVert_1\le\varepsilon$.
  The trace norm is `QuantumCircuit.chainTraceNorm`, the sum of singular
  values after enumerating the chain configurations.
- **Source:** Piroli--Styliaris--Cirac, arXiv:2103.13367, p. 3, paragraph
  "Phases of matter", for the trace-norm criterion. The protocol class here
  uses enlarged-site channels without classical feedforward.
- **Sanctioned bridges:** `IsApproxLocalChannelConversion.refl`,
  `IsApproxLocalChannelConversion.mono` (both bounds may increase),
  `IsApproxLocalChannelConversion.trans` (depths and errors add for Hermitian
  source and intermediate operators), and
  `QuantumCircuit.isApproxLocalChannelConversion_zero_iff` (zero error is exact
  local channel conversion).
- **Caveat:** the definition does not require density matrices or Hermiticity;
  the composition theorem requires the stated Hermiticity hypotheses.
  Intermediate dimensions are unrestricted and two-site layers on enlarged
  sites have unit depth. Classical feedforward is excluded, but no uniform
  simulation or inclusion in the source relation is established; see
  `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

#### `QuantumCircuit.IsAsymptoticLocalChannelConversion`

- **Declaration:** `QuantumCircuit.IsAsymptoticLocalChannelConversion ρ σ : Prop`,
  for operator families on `N`-site chains with fixed, possibly different,
  local dimensions.
- **Defined in:** `TNLean/Circuit/Channel/AsymptoticConversion.lean`.
- **Meaning:** there are $k\in\mathbb N$, $C\ge0$, and errors
  $\varepsilon_N\to0$ such that, for all sufficiently large positive `N`, an
  approximate local channel conversion from $\rho_N$ to $\sigma_N$ has depth
  $T_N\le C(1+\log(N+1))^k$ and trace-norm error at most $\varepsilon_N$.
- **Source:** Piroli--Styliaris--Cirac, arXiv:2103.13367, p. 3, paragraph
  "Phases of matter", for the trace-norm criterion. The protocol class here
  uses enlarged-site channels without classical feedforward.
- **Sanctioned bridges:** `IsAsymptoticLocalChannelConversion.refl` and
  `IsAsymptoticLocalChannelConversion.trans`, the latter for eventually
  Hermitian source and intermediate families.
- **Caveat:** only the tails of the families matter; the logarithmic shift
  fixes small sizes. The relation is directed, and its definition does not
  assume density matrices. Intermediate local dimensions may grow with `N`
  without changing the unit cost per two-site layer. No uniform-depth
  inclusion in the source `QCcc` relation is established; see
  `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

#### `QuantumCircuit.IsLocalChannelPhaseEquivalent`

- **Declaration:** `QuantumCircuit.IsLocalChannelPhaseEquivalent ρ σ : Prop`,
  for operator families on `N`-site chains with fixed, possibly different,
  local dimensions.
- **Defined in:** `TNLean/Circuit/Channel/AsymptoticConversion.lean`.
- **Meaning:** asymptotic local channel conversion holds in both directions.
- **Source:** Piroli--Styliaris--Cirac, arXiv:2103.13367, p. 3, paragraph
  "Phases of matter", for the trace-norm criterion. The protocol class here
  uses enlarged-site channels without classical feedforward.
- **Sanctioned bridges:** `IsLocalChannelPhaseEquivalent.refl`,
  `IsLocalChannelPhaseEquivalent.symm`, and
  `IsLocalChannelPhaseEquivalent.trans` (for three eventually Hermitian
  families). `IsLocalChannelPhaseEquivalent.equivalence` gives an equivalence
  relation on eventually Hermitian families of one fixed local dimension.
- **Caveat:** density-matrix families satisfy the Hermiticity condition, but
  arbitrary operator families are not asserted to form an equivalence
  relation. The enlarged-site gate convention and absence of classical
  feedforward differ from the source model; no inclusion in its phase
  relation or source `QCcc` classification is asserted. See
  `docs/paper-gaps/psc21_local_channel_phase_scope.tex`.

### Lieb–Robinson propagation on finite graphs

#### `QuantumCircuit.heisenbergCommutatorNorm`

- **Declaration:**
  `QuantumCircuit.heisenbergCommutatorNorm (H B : Matrix (ι → Fin q) (ι → Fin q) ℂ) (X : Set ι) (t : ℝ) : ℝ`,
  with `QuantumCircuit.heisenbergEvolution H t A = e^{itH} A e^{-itH}`.
- **Defined in:** `TNLean/Circuit/LiebRobinson/CommutatorRecursion.lean`.
- **Meaning:** the operator norm of `A ↦ [τ_t(A), B]` restricted to
  `supportedOperators q X`, for any finite type of sites `ι`.
- **Source:** Hastings–Koma, arXiv:math-ph/0507008, Appendix A, (A.13); the
  function `F(X, t)` of OpenAI, *A two-dimensional area law from a global
  spectral gap*, Lemma 4.1 (`03-quasilocal.tex`, lines 70–74).
- **Sanctioned bridges:**
  `QuantumCircuit.heisenbergCommutatorNorm_le_integral` (the local commutator
  recursion for an arbitrary finite interaction family),
  `QuantumCircuit.norm_heisenberg_commutator_le_graphDistance` and
  `QuantumCircuit.exists_graph_lieb_robinson` (graph-distance propagation with
  constants depending only on the support diameter, support size and per-site
  interaction budget), and
  `QuantumCircuit.heisenberg_commutator_eq_zero_of_edist_eq_top` (exact
  vanishing between connected components). The finite-ring estimate
  `MPSPreparation.norm_heisenberg_commutator_le_exp_abs_of_disjoint` is a
  nearest-neighbor ring consumer of the same recursion.
- **Caveat:** the graph theorems take the per-support size bound and the
  per-site norm budget as hypotheses. On a finite induced square-lattice domain
  they are discharged in `TNLean/PEPS/AreaLaw/GraphPropagation.lean`:
  `TNLean.PEPS.AreaLaw.IsAdmissibleSupport.card_le` gives the size bound
  `v_R = 1 + 2R(R + 1)`,
  `TNLean.PEPS.AreaLaw.LocalHamiltonian.sum_norm_term_containing_le` gives the
  budget `μ_R J`, and `TNLean.PEPS.AreaLaw.exists_quasilocal_lieb_robinson` is
  the resulting Lemma 4.1 of the area-law manuscript.

#### `QuantumCircuit.siteExpectation`

- **Declaration:**
  `QuantumCircuit.siteExpectation (q : ℕ) (K : Finset ι) (B : Matrix (ι → Fin q) (ι → Fin q) ℂ)`,
  with the linear map `QuantumCircuit.siteExpectationLM`.
- **Defined in:** `TNLean/Circuit/SiteExpectation.lean`.
- **Meaning:** the normalized partial trace
  `E_K(B) = q^{-|ι \ K|} Tr_{ι \ K}(B) ⊗ 1`, with the factors at their
  original sites.
- **Source:** OpenAI, *A two-dimensional area law from a global spectral gap*,
  `eq:quasilocal-ce` (`03-quasilocal.tex`, lines 17–29).
- **Sanctioned bridges:** `QuantumCircuit.siteExpectation_eq_average` (uniform
  average over products of on-site Weyl operators outside `K`),
  `siteExpectation_mem_supportedOperators`,
  `siteExpectation_of_mem_supportedOperators`, `siteExpectation_one`,
  `norm_siteExpectation_le`, `siteExpectationLM_isKrausCPTP`,
  `norm_sub_siteExpectation_le` (error through on-site commutators), and
  `norm_heisenberg_sub_siteExpectation_graphBall_le` (localization of the
  dynamics onto graph balls under a sphere-growth hypothesis).
- **Caveat:** the averaging formula and its consequences assume `q ≠ 0`.

#### Positive quasi-local constraints (`exists_positiveQuasilocalConstraints`)

- **Declaration:** `TNLean.PEPS.AreaLaw.exists_positiveQuasilocalConstraints`, with the
  constraints `SpectralFilter.positiveConstraint c_* (SpectralFilter.centeredFilter p (Δ / 2) H Ω hᵢ)`
  from QICLean and their ball expectations
  `QuantumCircuit.siteExpectation q (QuantumCircuit.graphBall G aᵢ l) kᵢ`.
- **Defined in:** `TNLean/PEPS/AreaLaw/PositiveConstraints.lean`; the root channels of
  Lemma 4.4 in `TNLean/PEPS/AreaLaw/QuasilocalRoots.lean`.
- **Meaning:** `kᵢ = |Mᵢ| / c_*`, where `Mᵢ` is the term `hᵢ` filtered below the gap and
  centered at the ground vector; the positive contractions annihilate `Ω`, their sum
  dominates `c_*⁻¹ (H - E₀ I) ≥ (Δ / c_*) (I - |Ω⟩⟨Ω|)`, and the ball tails decay like
  `e^{-c l^{p/(p+1)}}`.
- **Source:** OpenAI, *A two-dimensional area law from a global spectral gap*,
  Proposition 4.3 (`prop:positive`) and Lemma 4.4 (`lem:quasilocal-roots`),
  `03-quasilocal.tex`, lines 220–389.
- **Sanctioned bridges:** `SpectralFilter.positive_replacement`,
  `SpectralFilter.exists_norm_positiveConstraint_sub_map_le` (QICLean),
  `positiveConstraint_mem_supportedOperators_component`, `quasilocalRoots`.
- **Caveat:** stated for a general finite graph with the support, multiplicity and
  sphere-growth hypotheses of the propagation estimate. On finite induced square-lattice
  domains these hypotheses are discharged in `TNLean/PEPS/AreaLaw/LatticeConstraints.lean`:
  `TNLean.PEPS.AreaLaw.exists_latticePositiveConstraints` and
  `TNLean.PEPS.AreaLaw.exists_latticeQuasilocalRoots` are Proposition 4.3 and Lemma 4.4
  there, with constants depending only on `p`, `R`, `J` and `Δ`.

## Inhomogeneous short-range correlated chains

### `MPSTensor.IsInjectiveOn`

- **Declaration:**
  `MPSTensor.IsInjectiveOn (B : MPSTensor n D) (S : Set (Fin D × Fin D)) : Prop`.
- **Defined in:** `TNLean/MPS/Preparation/SupportedPolar.lean`.
- **Meaning:** every matrix `B^i` vanishes at the entries outside `S`, and the
  matrices `B^i` span every matrix unit `|α⟩⟨β|` with `(α, β) ∈ S`.
- **Source:** arXiv:2307.01696, footnote to the paragraph "Approximation
  through the fixed-point state" (the blocked tensors are assumed injective),
  applied to zero-padded blocked tensors of chains with bond dimensions at
  most `D`.
- **Sanctioned bridges:** `MPSTensor.isInjectiveOn_univ_iff` (for `S` the set
  of all pairs it is `Kraus.IsInjective`), `MPSTensor.polarSupportMatrix_eq_diagonal`
  (the support projector of `B = V P` is the coordinate projector onto `S`),
  `MPSTensor.sum_star_polarIsoMatrix_mul`, `MPSTensor.polarPosTensor_eq_zero`.
- **Caveat:** for a rectangle `S = [0, a) × [0, b)` the predicate may be read as
  injectivity of a zero-padded tensor with bond dimensions `a` and `b`; no
  rectangular tensor is defined and that reading is not proved.

### `VaryingBondChain.IsBlockInjective`

- **Declaration:**
  `VaryingBondChain.IsBlockInjective (A : VaryingBondChain d D N) (hN : ∑ k, ℓ k = N) : Prop`,
  for a ring of `N ≥ 1` sites with bond dimensions at most `D`, cut into `M`
  blocks of lengths `ℓ`.
- **Defined in:** `TNLean/MPS/Preparation/VaryingBondBlocks.lean`.
- **Meaning:** for every block `k`, the blocked tensor of block `k` of the
  zero-padded chain (`VaryingBondChain.zeroPad`) spans every matrix unit
  `|α⟩⟨β|` with `α < D_{o_k}` and `β < D_{o_{k+1}}`, the dimensions of the bonds
  at the ends of the block.
- **Source:** arXiv:2307.01696, footnote to the paragraph "Approximation
  through the fixed-point state" (the blocked tensors are assumed injective),
  for the chains of the paragraph "Inhomogeneous short-range correlated MPS".
- **Sanctioned bridges:** `VaryingBondChain.IsBlockInjective.isInjectiveOn`
  (for blocks of at least one site, each padded blocked tensor is
  `MPSTensor.IsInjectiveOn` its rectangle).
- **Caveat:** the source's condition concerns the rectangular blocked tensor;
  the identification of the corner of the padded blocked tensor with the
  rectangular product is not proved. For a block of length zero the padded
  blocked tensor is the identity `1_D`, and the predicate differs from the
  rectangular reading; every theorem using it assumes blocks of at least one
  site. See `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

### `VaryingBondChain.IsPairApproximable`

- **Declaration:**
  `VaryingBondChain.IsPairApproximable (A : VaryingBondChain d D N) (hN : ∑ k, ℓ k = N) (δ : ℝ) : Prop`,
  for a ring of `N ≥ 1` sites with bond dimensions at most `D`, cut into `M`
  blocks of lengths `ℓ`.
- **Defined in:** `TNLean/MPS/Preparation/InhomogeneousPreparation.lean`.
- **Meaning:** the state `|φ_pos⟩` of the positive parts is nonzero, and there
  are unit vectors `ω^k` on `ℂ^{D_j} ⊗ ℂ^{D_j}`, `j` the bond joining block `k`
  to block `k + 1`, whose product `|Ω⟩ = ⊗ₖ |ω^k⟩_{R_k L_{k+1}}` has error
  `1 - |⟨Ω|φ_pos⟩| ≤ δ` against the normalized state `|φ_pos⟩` of the positive
  parts of the polar decompositions of the blocked tensors. The blocked
  tensors, positive parts and pairs are those of the chain padded with zeros
  to bond dimension `D` (`VaryingBondChain.zeroPad`,
  `VaryingBondChain.padPairs`).
- **Source:** arXiv:2307.01696, paragraph "Inhomogeneous short-range correlated
  MPS" (finite correlation length of a sequence of states "with bond dimension
  at most `D`"), for one member of the sequence.
- **Sanctioned bridges:**
  `MPSPreparation.exists_isPreparedInDepth_of_isPairApproximable` (preparation
  in depth at most `C L` with error at most `δ` against the normalized state of
  the chain, when the block lengths lie between `3D` and `L`; the blocked
  tensors need not be injective).
- **Caveat:** the source's condition is asymptotic, an error tending to `0` as
  `N → ∞` after blocking `q = O(log N)` sites; the predicate fixes one ring and
  one cutting into blocks; see
  `docs/paper-gaps/mswc24_inhomogeneous_scope.tex`.

## Worked examples

### `MPSTensor.IsPeriodicWState`

- **Declaration:** `MPSTensor.IsPeriodicWState (A : MPSTensor 2 D) (N : ℕ) : Prop`.
- **Defined in:** `TNLean/MPS/Examples/WStatePeriodic.lean`.
- **Meaning:** the trace contraction
  $\operatorname{tr}(A^{\sigma_1}\cdots A^{\sigma_N})$ equals the unnormalized
  W-state amplitude on every configuration of $N$ sites, that is, $A$ is a
  translationally invariant periodic representation of $\ket{W_N}$.
- **Source:** the notion of a translationally invariant representation of the
  W state in arXiv:2011.12127, Appendix A, "The W state", line 2362. The
  predicate itself is a project definition.
- **Sanctioned bridges:** none; the printed open-boundary tensor is related to
  the W state through `MPSTensor.wTensor_openState_eq_wIndicator`, not through
  this predicate.
- **Caveat:** the formalized obstructions constrain one tensor across several
  lengths (`MPSTensor.not_isPeriodicWState_of_lt`,
  `MPSTensor.exists_not_isPeriodicWState_le`). The source's single-length bound
  $D^3\log D=\Omega(N)$ is not formalized; see
  `docs/paper-gaps/rmp_w_state_ti_bound.tex`.

## Scalar L-symbols of group matrix product operators

### `TNLean.Algebra.LSymbol.ActionGaugeEquiv`

- **Declaration:** `LSymbol.ActionGaugeEquiv L₁ L₂`, for scalar L-symbols of a
  group `G` acting on a set `X`.
- **Defined in:** `TNLean/Algebra/StabilizerCocycleReconstruction.lean`.
- **Meaning:** `L₁ = LSymbol.gauge 1 γ L₂` for some action-tensor gauge
  `γ : G → X → ℂˣ`, that is,
  $L_1{}^x_{g,h}=\gamma^x_{gh}(\gamma^{hx}_g\gamma^x_h)^{-1}L_2{}^x_{g,h}$
  with the fusion-tensor gauge held equal to one.
- **Source:** arXiv:2203.12563, `gdgroup` with the fusion gauge fixed as at
  line 761, `Papers/2203.12563/REsubmission.tex:716-721,761`.
- **Sanctioned bridges:**
  `StabilizerRepresentatives.cohomologousTo_iff_exists_actionGauge_inducedLSymbol_eq`
  and `StabilizerRepresentatives.actionGaugeEquiv_mul_inducedLSymbol_iff`
  identify the relation on induced L-symbols with cohomology of stabilizer
  cocycles; on the classes of `StabilizerRepresentatives.solutionSetoid`,
  `StabilizerRepresentatives.solutionAddAction`,
  `StabilizerRepresentatives.h2EquivSolutionClasses`, and
  `StabilizerRepresentatives.existsUnique_vadd_eq` give the torsor under
  Mathlib's `groupCohomology.H2`.
- **Caveat:** `LSymbol.gauge` is the reciprocal of the source's `gdgroup`;
  with trivial fusion gauge this replaces `γ` by `γ⁻¹` and defines the same
  relation. Allowing fusion gauges that preserve `ω` gives a coarser relation,
  under which the classes collapse to the quotient of `H²(H, ℂˣ)` by the
  restriction of `H²(G, ℂˣ)`; that coarser relation is not formalized. See
  `docs/paper-gaps/glm23_eq20_fusion_gauge.tex`.

## Fusion symmetries of matrix product operators

The periodic-boundary layer of non-invertible matrix product operator symmetry.
The operator-level predicates `IsMPOFusionAlgebra`, `IsMPOSymmetricFamily`,
`IsMPOSymmetric` and `GroupFamily.IsNormalRepresentation` impose their
identities only with identity boundaries; for the symmetric-state predicates that
restriction is recorded in `docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`.
The remaining entries are conditions on structure constants or on words and
involve no boundary.

### `MPOTensor.IsMPOFusionAlgebra`

- **Declaration:** `MPOTensor.IsMPOFusionAlgebra O N : Prop`, for a family
  `O : ∀ a, MPOTensor d (χ a)` and structure constants `N : ι → ι → ι → ℕ`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** the periodic operators obey the fusion rules
  $O_aO_b=\sum_cN_{ab}^cO_c$ at every positive chain length.
- **Source:** arXiv:2203.12563, `Papers/2203.12563/REsubmission.tex`,
  lines 321–361 (matrix product operator algebras and their fusion rules).
- **Sanctioned bridges:** `MPOTensor.GroupFamily.IsNormalRepresentation.isMPOFusionAlgebra`
  (a normal group representation satisfies the group fusion rules) and
  `MPOTensor.IsMPOFusionAlgebra.exists_fusionTensors` (fusion tensors with
  multiplicity, for normal tensors of positive bond dimension).
- **Caveat:** nothing is asserted at length zero, and neither normality of the
  tensors nor associativity of `N` is part of the definition; results add them
  where they use them.

### `MPOTensor.IsFusionUnit` and `MPOTensor.IsInvertibleLabel`

- **Declarations:** `MPOTensor.IsFusionUnit N e : Prop` and
  `MPOTensor.IsInvertibleLabel N e a : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** conditions on the structure constants alone:
  $N_{eb}^c=N_{be}^c=\delta_{bc}$ for the unit, and some $b$ with
  $N_{ab}^c=N_{ba}^c=\delta_{ce}$ for an invertible label $a$.
- **Source:** arXiv:2203.12563, line 660 (the trivial block $e$ and inverses
  $g^{-1}$ with $O_{g^{-1}}O_g=O_gO_{g^{-1}}=O_e$).
- **Sanctioned bridges:** `MPOTensor.IsInvertibleLabel.exists_isInvertibleLabel`
  (the inverse is invertible), `MPOTensor.IsFusionCharacter.eq_one_of_isInvertibleLabel`,
  and `MPOTensor.IsNIMRep.exists_equiv_of_isInvertibleLabel` (an invertible
  label acts on the blocks by a permutation).
- **Caveat:** these are statements about `N`, not about the operators; the
  unit operator $O_e$ need not be the identity and in the source is in general
  a projector (line 660).

### `MPOTensor.IsMPOSymmetricFamily`

- **Declaration:** `MPOTensor.IsMPOSymmetricFamily O A M : Prop`, for block
  tensors `A : ∀ x, MPSTensor d (D x)` and complex coefficients
  `M : ι → κ → κ → ℂ`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** $O_a\ket{\psi_{A_x}}=\sum_yM_{a,x}^y\ket{\psi_{A_y}}$ at every
  positive chain length, with coefficients independent of the length.
- **Source:** arXiv:2203.12563, lines 567–568, restated at line 1801; the
  multiplicities are introduced at lines 429–460.
- **Sanctioned bridges:** `MPOTensor.exists_nat_eq_of_isMPOSymmetricFamily`
  (the coefficients are nonnegative integers) and
  `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily` (they form a
  nonnegative integer representation), both for normal blocks with linearly
  independent periodic vectors at one positive length.
- **Caveat:** **Scope restriction (periodic boundary)**: the source defines
  symmetry by invariance of the arbitrary-boundary subspace under the
  arbitrary-boundary algebra (lines 431–434); only the identity-boundary
  consequence is formalized
  (`docs/paper-gaps/glm23_mpo_symmetric_mps_scope.tex`). The coefficients are
  complex in the definition; integrality is a theorem.

### `MPOTensor.IsMPOSymmetric`

- **Declaration:** `MPOTensor.IsMPOSymmetric O A c : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** the periodic vector of a single tensor is a common eigenvector,
  $O_a\ket{\psi_A}=c_a\ket{\psi_A}$ at every positive length, with
  length-independent eigenvalues.
- **Source:** arXiv:2203.12563, lines 567–568 with one block (the setting of
  line 610; compare line 1797).
- **Sanctioned bridges:** `MPOTensor.exists_isFusionCharacter_of_isMPOSymmetric`
  (for a normal block on which the unit acts trivially, the eigenvalues are a
  fusion character in `ℕ`),
  `MPOTensor.not_isMPOSymmetric_of_forall_not_isFusionCharacter`, and
  `MPOTensor.mpo_mulVec_eq_of_isInvertibleLabel`. `MPOTensor.GroupFamily.FixesMPV`
  is the single-operator case $c_a=1$, by unfolding.
- **Caveat:** the source's single-block subsection also assumes
  $M_{a,x}^x=1$ (line 610); that clause is **not** carried by this predicate.
  The periodic-boundary scope restriction of `IsMPOSymmetricFamily` applies.

### `MPOTensor.IsFusionCharacter`

- **Declaration:** `MPOTensor.IsFusionCharacter N e χ : Prop`, for `χ : ι → R`
  in a semiring.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** a one-dimensional representation of the fusion ring:
  $\chi_e=1$ and $\chi_a\chi_b=\sum_cN_{ab}^c\chi_c$.
- **Source:** project-introduced; the source does not use this notion.
- **Sanctioned bridges:** `MPOTensor.exists_isFusionCharacter_of_isMPOSymmetric`,
  `MPOTensor.IsStrongMPOSymmetry.isFusionCharacter`, and
  `MPOTensor.perronFrobeniusDim_eq_of_isFusionCharacter` (a positive real
  character is the Perron–Frobenius dimension).
- **Caveat:** the obstruction it yields
  (`not_isMPOSymmetric_of_forall_not_isFusionCharacter`) differs from the
  source's no-multiplicity obstruction at line 634: it detects only fusion
  rings without a nonnegative integer character, such as the Fibonacci ring,
  and says nothing about group-like algebras.

### `MPOTensor.IsNIMRep`

- **Declaration:** `MPOTensor.IsNIMRep N M : Prop`, for
  `M : ι → κ → κ → ℕ`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Defs.lean`.
- **Meaning:** $\sum_cN_{ab}^cM_{c,x}^y=\sum_zM_{b,x}^zM_{a,z}^y$ for all
  labels and blocks: the matrices $M_a$ represent the fusion ring.
- **Source:** arXiv:2203.12563, lines 564–565, from the associativity of lines
  491–492; for groups, line 683.
- **Sanctioned bridges:** `MPOTensor.exists_isNIMRep_of_isMPOSymmetricFamily`
  and `MPOTensor.IsNIMRep.exists_equiv_of_isInvertibleLabel`.
- **Caveat:** the definition does not require the unit to act as the identity;
  the permutation result adds `M_e = 1` as a hypothesis, matching line 683.

### `MPOTensor.GroupFamily.IsNormalRepresentation`

- **Declaration:** `MPOTensor.GroupFamily.IsNormalRepresentation F : Prop`.
- **Defined in:** `TNLean/MPS/FundamentalTheorem/Reduction/MPOProduct.lean`.
- **Meaning:** every doubled-index tensor $T_g$ is normal and
  $U_gU_h=U_{gh}$ holds exactly on every nonempty periodic chain.
- **Source:** arXiv:2502.20257, `main.tex` lines 1403–1407 (the representation
  law); arXiv:2203.12563, line 1211 (the fusion-tensor lemma for an injective,
  not necessarily unitary, representation).
- **Sanctioned bridges:** `MPOTensor.GroupFamily.IsRepresentation.isNormalRepresentation`
  (from the matrix product unitary representation bundle),
  `MPOTensor.GroupFamily.IsNormalRepresentation.exists_fusionTensors`,
  `MPOTensor.GroupFamily.IsNormalRepresentation.nonempty_fusionData`, and
  `MPOTensor.GroupFamily.IsNormalRepresentation.isMPOFusionAlgebra`.
- **Caveat:** weaker than the source's injectivity, and it carries neither
  unitarity, simplicity, nor the identity law $U_e=\mathbb 1$. The lemma at
  `REsubmission.tex` line 1211 lists $U_e=\mathbb 1$, but the fusion-tensor
  statement it rests on (line 1001) assumes only $U_gU_h=U_{gh}$ and
  injectivity, and line 1216 allows $U_e$ to be a projector. The anomaly
  three-cocycle is defined under this hypothesis alone.

### `MPOTensor.GroupFamily.FusionData`

- **Declaration:** `MPOTensor.GroupFamily.FusionData F : Type`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/Associator.lean`.
- **Meaning:** a choice, for every pair $g,h$, of a reduction
  $(F^<_{g,h},F^>_{g,h})$ of the stacked product of $T_g$ and $T_h$ onto
  $T_{gh}$.
- **Source:** arXiv:2502.20257, `eq:fusion_1` and `eq:fusion_2`, `main.tex`
  lines 1403–1497; arXiv:2203.12563, equation `fusiontensorG2`.
- **Sanctioned bridges:** `MPOTensor.GroupFamily.IsNormalRepresentation.nonempty_fusionData`
  (existence); `MPOTensor.GroupFamily.FusionData.omega` is the anomaly
  three-cochain, and `FusionData.omega_cohomologousTo` shows its class does not
  depend on the choice.
- **Caveat:** data, not a proposition; the nilpotent-remainder clause of the
  existence theorem is not stored.

### `MPSTensor.IsDressedProportional`

- **Declaration:** `MPSTensor.IsDressedProportional B X Y z : Prop`.
- **Defined in:** `TNLean/MPS/Core/ReductionComposition.lean`.
- **Meaning:** $XB^{\mathbf w}=z\,YB^{\mathbf w}$ for every sufficiently long
  word $\mathbf w$.
- **Source:** Molnár–Ge–Schuch–Cirac, arXiv:1706.07329v2, Theorem 22,
  `cornerproblem.tex` lines 3156–3162; the definition of the anomaly
  three-cocycle, arXiv:2502.20257, `main.tex` lines 1506–1535.
- **Sanctioned bridges:** `MPSTensor.exists_isDressedProportional` (two
  reductions onto a normal tensor are dressed proportional with a nonzero
  scalar), `IsDressedProportional.refl` and `.trans`, and
  `MPSTensor.IsDressedProportional.of_forall_mul_mul`.
- **Caveat:** the scalar is not required to be nonzero in the definition, and
  the threshold length is existential.

## Invariant states of matrix product operators

### `MPOTensor.GroupFamily.FixesMPV`

- **Declaration:** `MPOTensor.GroupFamily.FixesMPV T A : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/AnomalyObstruction.lean`.
- **Meaning:** the periodic operator $O_N(T)$ fixes the periodic vector
  $\ket{V^{(N)}(A)}$ for every chain length $N\geq1$; nothing is asserted at
  $N=0$.
- **Source:** arXiv:2203.12563, line 1064, the relation
  $U_g\ket{\psi_{A_x}}=\ket{\psi_{A_y}}$ with $y=x$.
- **Sanctioned bridges:** it is the single-operator, unit-eigenvalue case of
  `MPOTensor.IsMPOSymmetric` (eigenvalue $c_a=1$). `FixesMPV.mulTensor` closes
  it under operator products, and `FixesMPV.sameMPV₂Pos_actTensor` turns it into
  positive-length vector equality of the action tensor with `A`, which is the
  input of `MPOTensor.GroupFamily.nonempty_actionData`.
- **Caveat:** no equivalence with `IsMPOSymmetric` at `c = 1` is stated as a
  theorem; the two definitions agree by unfolding.

### `MPOTensor.GroupFamily.CarriesMPV`

- **Declaration:** `MPOTensor.GroupFamily.CarriesMPV T B B' : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/PermutedBlocks.lean`.
- **Meaning:** the periodic operator $O_N(T)$ carries the periodic vector
  $\ket{V^{(N)}(B)}$ to $\ket{V^{(N)}(B')}$ for every chain length $N\geq1$;
  nothing is asserted at $N=0$. The two tensors may have different bond
  dimensions.
- **Source:** arXiv:2203.12563, line 1064, the relation
  $U_g\ket{\psi_{A_x}}=\ket{\psi_{A_y}}$ for blocks permuted by the group.
- **Sanctioned bridges:** `FixesMPV T A` is the case $B=B'=A$, by unfolding.
  `CarriesMPV.sameMPV₂Pos_actTensor` turns it into positive-length vector
  equality of the action tensor with $B'$, the input of
  `MPOTensor.GroupFamily.nonempty_blockActionData`.
- **Caveat:** no theorem states the equivalence with `FixesMPV` at $B=B'$; the
  definitions agree by unfolding.

### `MPOTensor.GroupFamily.IsOnSite`

- **Declaration:** `MPOTensor.GroupFamily.IsOnSite F : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`.
- **Meaning:** there are one-site matrices $u_g$ with
  $O_N(T_g)=u_g^{\otimes N}$, entrywise
  $\langle\sigma|O_N(T_g)|\tau\rangle=\prod_n (u_g)_{\sigma_n\tau_n}$, for
  every chain length $N\geq1$; nothing is asserted at $N=0$.
- **Source:** arXiv:2203.12563, lines 658 and 842 ($O_g=(u_g)^{\otimes n}$).
- **Sanctioned bridge:** `MPOTensor.GroupFamily.isOnSite_of_closed_fusion`
  derives it from injectivity, $U_e=\Id$ and closed fusion, through
  `MPOTensor.GroupFamily.bondDim_eq_one_of_closed_fusion`.
- **Caveat:** the matrices $u_g$ are not required to form a representation;
  for a representation, $u_gu_h=u_{gh}$ follows from the operator law at
  $N=1$.

### `MPOTensor.GroupFamily.FusionData.IsClosed`

- **Declaration:** `MPOTensor.GroupFamily.FusionData.IsClosed fd : Prop`, for
  a choice of fusion tensors `fd : FusionData F`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/ClosedFusion.lean`.
- **Meaning:** closed fusion: the stacked tensor decomposes exactly, letter by
  letter, $(T_gT_h)^{ij}=F^>_{g,h}\,T_{gh}^{ij}\,F^<_{g,h}$ for all $g,h$ and
  all physical indices, with no remainder. Together with
  $F^<_{g,h}F^>_{g,h}=\mathbf 1$, carried by `FusionData`, this is the zipper
  case of the reduction.
- **Source:** arXiv:2203.12563, equation `fusiontensorG`, lines 641--656, with
  the fusion tensors of `fusiontensorG2`, lines 1002--1026.
- **Sanctioned bridge:** `FusionData.IsClosed.mulTensor_apply` restates it in
  the two physical indices of the operator tensors.
- **Caveat:** for an injective representation with $U_e=\Id$ it forces bond
  dimension one (`MPOTensor.GroupFamily.bondDim_eq_one_of_closed_fusion`), so
  the anomalous examples (CZX, $\mathbb Z_3$, $\mathbb Z_2\times\mathbb Z_2$)
  satisfy only the reduction with a nilpotent remainder, never this predicate.

### `MPOTensor.IsFusionRing`

- **Declaration:** `MPOTensor.IsFusionRing (N : ι → ι → ι → ℕ) (e : ι)
  (dual : ι → ι) : Prop`, a structure with fields `assoc`, `isFusionUnit`,
  `dual_dual`, `apply_unit` and `dual_anti`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/FusionRing.lean`.
- **Meaning:** the structure constants `N_{ab}^c` of a fusion ring: they are
  associative, `e` is a two-sided unit (`MPOTensor.IsFusionUnit`), and the
  duality `a ↦ a*` is an involution with `N_{ab}^e = δ_{b,a*}` and
  `N_{b*a*}^{c*} = N_{ab}^c`.
- **Source:** arXiv:2203.12563, line 1236 (the identity element and dual
  elements of the fusion category of a physical symmetry); the source uses the
  fusion category at lines 1801–1803 to obtain a positive common eigenvector of
  the multiplicity matrices.
- **Sanctioned bridges:** `MPOTensor.IsFusionRing.exists_pos_regular` gives a
  positive regular element with the Perron–Frobenius dimensions
  (`MPOTensor.perronFrobeniusDim`) as eigenvalues;
  `MPOTensor.IsNIMRep.exists_pos_left_eigenvector` transfers it to every
  nonnegative integer representation on which the unit acts as the identity.
- **Caveat:** only the fusion ring of a fusion category is recorded; the
  `F`-symbols, the pivotal structure and the rigidity maps are not. The
  predicate is independent of `MPOTensor.IsMPOFusionAlgebra`, which constrains
  periodic operators rather than structure constants.

## Domain walls of permuted blocks

### `MPOTensor.GroupFamily.BlockActionData.IsDomainWallAction`

- **Declaration:** `ad.IsDomainWallAction g hx hy e e' c : Prop` for action tensors
  `ad : BlockActionData F A`, a group element `g`, a domain wall `e` between the blocks `x` and
  `y`, a domain wall `e'` between `x' = g • x` and `y' = g • y`, and a scalar `c`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/DomainWall.lean`.
- **Meaning:** `e ≠ 0`, `e' ≠ 0`, `c ≠ 0`, and the action tensors of `g`, applied to `O_g`
  acting on `A_x^u e^i A_y^v`, give `c A_{x'}^u e'^i A_{y'}^v` for all words `u`, `v` longer
  than a fixed buffer.
- **Source boundary:** arXiv:2405.00439, `eq:localcdef` and `eq:localcdefG`; the source draws
  the relation with one site on each side of the wall at the renormalization fixed point and
  does not state the nonzero conditions. Both conventions are recorded in
  `docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.
- **Sanctioned bridges:** `IsDomainWallAction.physAct_eq` (configuration-indexed form),
  `IsDomainWallAction.mul` (composition, with L-symbols), `IsDomainWallAction.phase_eq`
  (uniqueness of the phase), `IsDomainWallAction.pair` (a string over a pair of walls),
  `IsDomainWallAction.mpo_mulVec_twoWallMPV` (the periodic state with two walls).

### `MPOTensor.GroupFamily.BlockActionData.IsDomainWallFamily`

- **Declaration:** `ad.IsDomainWallFamily e B : Prop` for domain walls
  `e : (y z : X) → Fin d → Matrix (Fin (D y)) (Fin (D z)) ℂ` and phases `B : G → X → X → ℂ`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallFamily.lean`.
- **Meaning:** every `g` carries `e_{yz}` to `e_{gy,gz}` with phase `B^g_{y,z}`, in the sense of
  `IsDomainWallAction`; in particular all walls and phases are nonzero.
- **Source boundary:** arXiv:2405.00439, line 1894 and `eq:localcdefG`, with the conventions of
  `docs/paper-gaps/gs24_domain_wall_nondegenerate.tex`.
- **Sanctioned bridges:** `IsDomainWallFamily.mul_eq` (`PentLB`),
  `IsDomainWallFamily.prod_eq_inv_cyclicInvariant` (`Intequiv`),
  `IsDomainWallFamily.mul_eq_of_fixed` (projective action of Mathlib's `fixingSubgroup` of the two
  blocks).

### `MPOTensor.GroupFamily.IsSeparatingLeftInverse`

- **Declaration:** `IsSeparatingLeftInverse Âx Ây Ax Ay : Prop` for one-site families
  `Âx`, `Ây` of square matrices on the bond spaces of the tensors `Ax`, `Ay`.
- **Defined in:** `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallString.lean`.
- **Meaning:** `physPairing Âx Ax = 1`, `physPairing Âx Ay = 0`, `physPairing Ây Ay = 1` and
  `physPairing Ây Ax = 0`, where `physPairing P Q = ∑_σ P^σ_{αβ} Q^σ_{γδ}`: each family is a left
  inverse of its tensor, read as a map from the virtual to the physical space, and annihilates
  the other tensor.
- **Source boundary:** arXiv:2405.00439, lines 1422--1425 (the left inverses `Â`, `B̂` in the
  endpoint tensors of `eq:defEndT`, with orthogonal supports at the renormalization fixed point).
- **Sanctioned bridges:** `BlockActionData.wallString_mulVec_mpv_left` and
  `BlockActionData.wallString_mulVec_mpv_right` (`eq:DWophys`),
  `BlockActionData.wallString_mul_wallString_mulVec_mpv` (`signphysop`), and
  `BlockActionData.wallString_mul_wallString_mulVec_mpv_swap_left_far` and
  `BlockActionData.wallString_mul_wallString_mulVec_mpv_swap_left_near` (`eq:z2int`, glued
  half-chains), the last three in `TNLean/MPS/Symmetry/MPOSymmetry/DomainWallStringExchange.lean`.

## Symmetries of matrix product density operators

### `MPOTensor.IsMPDOWithBoundary` and `MPOTensor.commutingBoundaryAlgebra`

- **Declarations:** `MPOTensor.IsMPDOWithBoundary M X : Prop` and
  `MPOTensor.commutingBoundaryAlgebra M`.
- **Defined in:** `TNLean/MPS/MPDO/Boundary.lean`.
- **Meaning:** the operator with entries
  $\operatorname{tr}(X M^{i_1j_1}\cdots M^{i_Lj_L})$ is positive semidefinite
  at every positive length. The commuting boundaries form the complex
  subalgebra centralizing every tensor letter.
- **Source:** arXiv:2504.16985, `References/2504.16985/main.tex:175–182`.
- **Sanctioned bridges:** `MPOTensor.mem_commutingBoundaryAlgebra_iff`,
  `MPOTensor.commute_evalWord_of_mem_commutingBoundaryAlgebra`, and
  `MPOTensor.isMPDOWithBoundary_one_iff`.
- **Caveat:** positivity and membership of the commuting-boundary algebra
  are stated separately. At identity boundary the positivity predicate
  is the ordinary MPDO predicate.

### `Matrix.IsStrongSymmetry` and `Matrix.IsWeakSymmetry`

- **Declarations:** `Matrix.IsStrongSymmetry (O ρ : Matrix n n ℂ) : Prop` and
  `Matrix.IsWeakSymmetry (O ρ : Matrix n n ℂ) : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPDO/Defs.lean`.
- **Meaning:** $O\rho=\lambda\rho$ for some complex $\lambda$ (strong), and
  $[O,\rho]=0$ (weak), at one system size.
- **Source:** arXiv:2504.16985, `References/2504.16985/main.tex:182`.
- **Sanctioned bridges:**
  `Matrix.IsStrongSymmetry.isWeakSymmetry_of_conjTranspose` and
  `Matrix.IsStrongSymmetry.isWeakSymmetry_of_unitary`.
- **Caveat:** the eigenvalue is not required to be a phase and may be zero;
  `Matrix.IsStrongSymmetry.norm_eq_one` gives modulus one only for unitary `O`
  and nonzero `ρ`. Strong implies weak only for Hermitian `ρ` with `O†` also a
  strong symmetry.

### `MPOTensor.IsStrongMPOSymmetry` and `MPOTensor.IsWeakMPOSymmetry`

- **Declarations:** `MPOTensor.IsStrongMPOSymmetry O M X c : Prop` and
  `MPOTensor.IsWeakMPOSymmetry O M X : Prop`.
- **Defined in:** `TNLean/MPS/Symmetry/MPDO/Defs.lean`.
- **Meaning:** the periodic operators $O_a^{(L)}$ of a family of matrix
  product operators satisfy $O_a^{(L)}\rho^{(L)}=\lambda_a^{(L)}\rho^{(L)}$
  (strong) or $[O_a^{(L)},\rho^{(L)}]=0$ (weak) for every label and every
  positive length, where $\rho^{(L)}=\rho^{(L)}(X,M)$ is the
  boundary-weighted periodic operator. Source-admissible `X` belongs to
  `MPOTensor.commutingBoundaryAlgebra M`, the centralizer of the letters.
- **Source:** arXiv:2504.16985, `References/2504.16985/main.tex:182`.
- **Sanctioned bridges:** `MPOTensor.IsStrongMPOSymmetry.isWeakMPOSymmetry`,
  `MPOTensor.IsStrongMPOSymmetry.isFusionCharacter`, and
  `MPOTensor.isStrongMPOSymmetry_iff_purification`.
- **Caveat:** more general than the source, where the $O_a$ are normal matrix
  product operators forming a fusion algebra (lines 125–137) and $\rho$ is
  positive; results add these hypotheses where they use them. Commutation
  of `X` with the letters does not imply positivity; this is the separate
  predicate `MPOTensor.IsMPDOWithBoundary M X`. The arbitrary-boundary
  purification theorem uses an actual global purification, rather than
  assuming that `X` factors on a doubled virtual space.

### `MPOTensor.IsStrongOnSiteSymmetry` and `MPOTensor.IsWeakOnSiteSymmetry`

- **Declarations:** `MPOTensor.IsStrongOnSiteSymmetry M X U c : Prop` and
  `MPOTensor.IsWeakOnSiteSymmetry M X U : Prop`, for a monoid homomorphism
  `U : G →* Matrix (Fin d) (Fin d) ℂ`.
- **Defined in:** `TNLean/MPS/Symmetry/MPDO/Defs.lean`.
- **Meaning:** the MPO-family predicates above for the on-site family
  $U_g^{\otimes L}$ (the periodic operators of `MPOTensor.onSite (U g)`).
- **Source:** arXiv:2504.16985, `References/2504.16985/main.tex:182`; the
  eigenvalue-one strong form $U\rho=\rho$ and the weak form $[U,\rho]=0$ are
  arXiv:2603.28349, line 362.
- **Sanctioned bridges:**
  `MPOTensor.isWeakOnSiteSymmetry_iff_mpvWithBoundary_toMPSTensor` and
  `MPOTensor.isStrongOnSiteSymmetry_iff_mpvWithBoundary_toMPSTensor`
  characterize the boundary-weighted vectorized state. At identity boundary,
  `MPOTensor.isWeakOnSiteSymmetry_iff_isOnSiteSymmetric_toMPSTensor` and
  `MPOTensor.isStrongOnSiteSymmetry_iff_mpv_toMPSTensor` give ordinary periodic
  vector identities; `MPOTensor.exists_isStrongOnSiteSymmetry_iff_of_isNormalTensor`
  characterizes normal periodic local purifications, also at identity boundary.
- **Caveat:** the eigenvalues `c g L` are arbitrary complex numbers in the
  definition; they are phases, multiplicative in `g`, and equal to $1$ at the
  identity only under unitarity and $\rho^{(L)}\neq 0$
  (`IsStrongOnSiteSymmetry.norm_eq_one`, `.map_mul`, `.map_one`).

### `MPSTensor.SymmetricGappedInteractionPath`

- **Declaration:** `SymmetricGappedInteractionPath U h₀ h₁`.
- **Defined in:** `TNLean/MPS/Symmetry/GappedInteractionPath.lean`.
- **Meaning:** a continuous path of Hermitian two-site interactions of
  operator norm at most one, with prescribed endpoints, whose periodic
  Hamiltonians commute with the fixed on-site unitary symmetry and have a
  common positive spectral gap for every parameter and every length at
  least two. The ground energy may vary, and ground-state degeneracy is allowed.
- **Source:** arXiv:1010.3732, Sections II.C.1–2, lines 407–453.
- **Sanctioned constructions:** `SymmetricGappedInteractionPath.reverse`,
  `SymmetricGappedInteractionPath.trans`,
  `normalizedBondFixedPointGappedPath` (the path between the direct-sum
  fixed points built from the normalized interpolating bond),
  `MPSTensor.canonicalInjectiveGappedPath`, and
  `MPSTensor.polarGappedInteractionPath`.
  `exists_symmetricGappedInteractionPath_of_cohomologous_fixedPoint`
  supplies a path on a common physical space after rephasing unitary
  virtual actions with cohomologous factor systems. The first fixed-point
  physical action is preserved. The canonical construction uses a
  continuous one-site injective tensor path with fixed unitary symmetry up to
  virtual gauge. The polar construction starts from an injective tensor whose
  covariance is expressed by unitary bond conjugation; it joins its canonical
  parent to the parent of its isometric form on the original physical space.
  `MPSTensor.exists_prepared_polarGappedInteractionPath_of_isOnSiteSymmetric`
  derives these data from an on-site symmetric injective tensor: nonzero
  rescaling and gauge give a unital representative with identical canonical
  parent interactions, and the unitary virtual covariance is then obtained
  from the symmetry.
- **Caveat:** this describes a path on a common physical space. Endpoint
  blocking and symmetry-preserving embeddings are separate mathematical
  operations. It does not impose an MPS description of intermediate ground
  spaces, which is required for the source's converse classification argument.

- **Virtual class of the prepared path:**
  `MPSTensor.exists_prepared_polarGappedInteractionPath_with_virtual_class`
  retains the original cohomology class and supplies one unitary projective
  representation implementing symmetry throughout the polar deformation.
- **Ordered comparison:** `MPSTensor.orderedGappedInteractionPath` constructs
  affine interpolation of positive interactions of norm at most one when
  the smaller interaction has a uniform gap and the periodic zero modes
  are common. Endpoint commutation with the fixed on-site representation
  suffices for symmetry of the entire path.

- **Weighted canonical endpoints:** `weightedMatrixUnitParentComparisonPath`
  compares each fixed normalized-bond interaction with the canonical parent
  of its weighted matrix-unit tensor. The local operator inequality and the
  shared nonzero periodic ground line hold even when coefficients vanish.
  `weightedCanonicalFixedPointGappedPath` concatenates the two endpoint
  comparisons with the continuous bond path. It concerns unitary virtual
  summands with a common factor system on the common direct-sum physical
  space; arbitrary isometric tensors still require a separate endpoint
  identification. Neither construction assumes continuity of the canonical
  projections as the interpolation parameter varies.

### Independent symmetric phases within exact MPS families

- **Declarations:** `MPSTensor.ExactMPSGroundPath`,
  `MPSTensor.IsSameExactMPSGappedPhase`, and `MPSTensor.SamePositiveMpvRay`.
- **Defined in:** `TNLean/MPS/Symmetry/ExactMPSGappedPhase.lean`.
- **Meaning:** the endpoint tensors are blocked by one common positive length
  and included isometrically, with their whole physical spaces as orthogonal
  summands, into a common unitary representation. Each blocked endpoint
  action may be multiplied by a
  unit-modulus character. An independent symmetric gapped interaction path
  joins their canonical two-site parents. A continuous finite-dimensional
  tensor family represents the unique periodic ground lines for every
  $N\ge2$, and has a positive-dimensional one-site injective representative
  of its positive-length vector rays at every parameter. The representative's
  bond dimension may vary; the ambient tensor dimension stays fixed.
- **Source:** arXiv:1010.3732, Sections II.C.1–2, lines 407–453, and
  Section II.F.2, lines 930–954. This is the continuous exact MPS regime;
  it does not describe every symmetric gapped Hamiltonian path.
- **Sanctioned bridges:** parameter reversal proves symmetry of the phase
  condition. `MPSTensor.isSameExactMPSGappedPhase_of_isInjective_cohomologous`
  constructs the phase condition for one-site injective tensors with exact
  physical symmetries and cohomologous actual invertible virtual factors.
  It derives orthogonal physical inclusions and an exact MPS ground
  realization of the full polar and fixed-point path. Unitary virtual
  actions are obtained by preparation rather than assumed.
  `MPSTensor.IsSameExactMPSGappedPhase.of_smul_gaugeEquiv` preserves the
  condition under nonzero scalar rescaling and invertible bond conjugation.
  `MPSTensor.cohomologousTo_of_continuous_isOnSiteSymmetric_tensorPath`
  derives endpoint cohomology for a continuous one-site injective tensor path
  of fixed positive bond dimension and exact symmetry, without a supplied
  virtual path or a finiteness assumption on the group.
  `TNLean.Algebra.ProjectiveRepresentation.exists_unitary_compression`
  preserves the factor system on a supplied invariant nonzero bond subspace.
  `MPSTensor.ExactMPSGroundPath.exists_rephasing_endpoint_cohomology_of_isInjective`
  proves the physical converse when the continuous ambient tensors are all
  one-site injective: it derives a common scalar character from the ground
  lines, removes it from the physical action, and compares arbitrary endpoint
  projective representatives. Exact tensor symmetry is a conclusion here.
  `MPSTensor.ExactMPSGroundPath.exists_exact_symmetry` derives the common
  physical character and exact rephased symmetry without fixing the minimal
  bond dimension. This removes scalar rephasing from the remaining
  varying-dimension problem.
  `MPSTensor.eventually_cohomologousTo_of_continuous_unital_supported_family`
  proves local cohomology invariance for a supplied continuous unital ambient
  tensor family with one-dimensional adjoint fixed space at the base parameter.
  Its pointwise normalized stationary densities need no continuity assumption:
  `MPSTensor.exists_open_continuousOn_stationaryDensity_of_unital` derives local
  continuity and uniqueness. Actual virtual actions commute with the compressed
  stationary density by uniqueness. Minimal support dimensions may vary;
  support frames and virtual actions need no continuity, and no projective
  action on the complementary bond space is required. Injectivity is required
  only at the base parameter. The more general
  `MPSTensor.eventually_cohomologousTo_of_continuousOn_unique_stationary_density`
  uses supplied continuous locally unique stationary data without unitality.
  `MPSTensor.cohomologousTo_of_continuous_unital_supported_family` gives endpoint
  cohomology equivalence when the fixed-space and injectivity assumptions hold
  at every parameter; preconnectedness extends the local conclusion.
- **Caveat:** the relation contains no virtual representation, factor system,
  or continuous canonical bond data. Its general converse remains open:
  continuous balanced canonical data and the surviving invariant bond subspace
  must be derived from the physical gap when minimal bond dimensions change.
  The obstruction to using raw tensor continuity alone is documented in
  `docs/paper-gaps/spc11_spt_interpolation_upper_range.tex`.

## Exact circuits with initialized auxiliaries

### `QuantumCircuit.IsPhysicalPortUnitary`

- **Declaration:** `QuantumCircuit.IsPhysicalPortUnitary P T U : Prop`,
  for a fixed qudit dimension `d`, a finite `PhysicalPortLayout N W`,
  and a unitary operator on the `W` qudit wires.
- **Defined in:** `TNLean/Circuit/Channel/PhysicalPort.lean`.
- **Meaning:** a circuit generated by free one-site unitaries, free wire
  permutations preserving every spatial site, and counted nearest-neighbor
  layers acting only on the one designated physical port per site.
  Multiplication adds upper bounds, and the bound can be enlarged.
- **Source:** the physical-qudit/onsite-ancilla distinction in
  arXiv:2103.13367, Supplement pp. 7–8. The routing estimates are derived
  comparisons, not claims that the paper states the same formal predicate.
- **Sanctioned bridges:** `.mem_unitary`, `.conjTranspose`, `.selected_layer`,
  `.register_matching`, `.appendEnvironment_comp`,
  `PhysicalPortEmbedding.unitary`, and `IsPhysicalPortProtocol.unitary`.
- **Caveat:** the physical dimension is fixed throughout the circuit. The
  layout may include separate local memory; a counted gate cannot act
  directly on all of an enlarged site's wires. This predicate alone does
  not impose source preparation ancilla initialization or cleanup conditions.

### `QuantumCircuit.PhysicalPortEmbedding`

- **Declaration:** `PhysicalPortEmbedding P Q`, for two wire layouts on the
  same spatial sites.
- **Defined in:** `TNLean/Circuit/Channel/PhysicalPortEmbedding.lean`.
- **Meaning:** an injection of wires preserving each wire's spatial owner
  and carrying every designated physical port to the corresponding port.
  Additional wires are local memories, not new communication ports.
- **Source:** the physical-qudit/onsite-ancilla distinction in
  arXiv:2103.13367, Supplement pp. 7–8; this embedding is the finite spatial
  construction used to retain that distinction when adding environments.
- **Sanctioned bridges:** `.unitary` lifts an actual physical-port unitary
  circuit at unchanged intersite depth. `PhysicalPortLayout.append` assigns
  owners to fresh wires; `.appendEmbedding`, `.appendLeftEmbedding`, and
  `.appendRightEmbedding` preserve the original ports. The maps
  `appendEnvironmentInput` and `discardAppendedEnvironment` prepare literal
  product-zero environment wires and discard precisely those wires.
- **Caveat:** this embedding does not permit a free site-changing permutation.
  A coordinate regrouping used to prove a matrix identity supplies no physical
  gate by itself. The final discard does not assert that the environment resets.

### `QuantumCircuit.IsPhysicalPortProtocol`

- **Declaration:** `QuantumCircuit.IsPhysicalPortProtocol P T Φ : Prop`,
  for a fixed qudit dimension and an endomorphism of the full wire operator
  space of `PhysicalPortLayout N W`.
- **Defined in:** `TNLean/Circuit/Channel/PhysicalPort.lean`.
- **Meaning:** a finite composition of certified physical-port unitaries
  and normalized Kraus channels supported within one spatial site.
  Local channels cost zero; only physical-port intersite layers contribute
  to the depth upper bound. The statement acts on arbitrary input operators.
- **Source:** the reduced-channel resource convention motivated by
  arXiv:2103.13367, Supplement pp. 7–8, with the scope recorded in
  `docs/paper-gaps/psc21_physical_port_simulation_scope.tex`.
- **Sanctioned bridges:** `.isKrausCPTP`, `.of_register_routing`,
  `.of_routed_family`, `.list_prod_uniform`,
  `PortRegisters.matchingChannel_isPhysicalPortProtocol`,
  `exists_bounded_matching_simulation`, `PortRegisters.dataChannelLift_word`,
  `IsDimensionBoundedLocalChannelProtocol.exists_physicalPortSimulation`,
  `.exists_appended_unitary_dilation`, and
  `.exists_appended_unitary_dilation_reference`. The last two construct an
  actual same-depth unitary on a port-preserving extension, with fresh local
  product-zero environments initialized once and discarded only at the end.
- **Caveat:** source pure-state conditions and the fixed number of composed
  `QCcc` blocks with their internal measurement/control rules remain separate.
  The appended environments need not reset, and their total number is only
  asserted finite for each protocol. The uniform `2 * Nat.clog d B` matching
  bound requires a fixed `d ≥ 2` and one dimension bound `B` chosen independently of chain
  length. It does not apply with the same constant to unrestricted
  intermediate dimensions depending on `N`.


### `QuantumCircuit.IsDimensionBoundedLocalChannelProtocol`

- **Declaration:** `IsDimensionBoundedLocalChannelProtocol B T Ψ : Prop`,
  for a native chain channel between possibly different local dimensions.
- **Defined in:** `TNLean/Circuit/Channel/DimensionBoundedConversion.lean`.
- **Meaning:** the native onsite/layer protocol constructors carry explicit
  positivity and upper bounds by the same `B` for every intermediate local
  dimension. Depth counts native pair-channel layers.
- **Source:** a resource-refined abstraction for comparing the enlarged-site
  channel model with the physical-qudit convention in arXiv:2103.13367,
  Supplement pp. 7–8. The paper does not state this predicate.
- **Sanctioned bridges:** `.toIsLocalChannelProtocol`, `.dimension_bounds`,
  `.mono_bound`, `.comp`, `.exists_fixedRegisterWord`,
  `.exists_physicalPortSimulation`, `.exists_physicalPortIO`, and
  `.exists_physicalPortUnitaryIO`. A finite positive-input native protocol
  admits some finite bound via `IsLocalChannelProtocol.exists_dimension_bound`.
- **Caveat:** an existential bound separately for each chain length is not a
  uniform family bound. For fixed physical `d ≥ 2` and `N ≥ 2`, the encoded
  simulation has physical depth at most `2 * Nat.clog d B * T`; a uniform
  constant requires `B` and `d` chosen independently of `N`. The exact channel
  identity retains arbitrary port/scratch-reference correlations. When the
  native input/output dimension is exactly the physical `d`, the port-I/O
  theorem supplies product-zero designated memory, output on the original
  ports, and exact data/scratch reset at the same intersite depth. The unitary
  theorem additionally supplies fresh local product-zero environments and one
  final trace; it does not assert reset of these discarded environments.
  A full source QCcc witness and its pure-output system--ancilla conditions
  remain separate. The bound does not count onsite operations as extra layers.

### `QuantumCircuit.IsCleanImplementation`

- **Declaration:** `IsCleanImplementation J C Z`.
- **Defined in:** `TNLean/Circuit/CleanUnitaryImplementation.lean`.
- **Meaning:** the matrix identity $CJ=JZ$. When $J$ includes a logical
  register with its workspace initialized, this identity says that the
  workspace returns to its initialized state on every logical input.
- **Source:** `docs/audits/2026-10-02_mpu_rank_two_circuits.tex`, Section 5.
- **Sanctioned constructions:** `IsCleanImplementation.mul` composes
  implementations using the same workspace; `IsCleanImplementation.embedOp`
  places one in a larger register; `exists_isPairProduct_isCleanImplementation`
  constructs a neighboring-pair circuit for an included logical unitary.
- **Caveat:** the identity alone does not assert unitarity. It specifies the
  initialized subspace, rather than the action on arbitrary workspace inputs.

### `MPUCircuit.IsIntervalInteriorInitialized`

- **Declaration:** `IsIntervalInteriorInitialized j k x z`.
- **Defined in:** `TNLean/MPS/MPU/IntervalRegisterLayout.lean`.
- **Meaning:** each auxiliary site strictly inside the interval from cut $j$
  to cut $k$ has computational label $z$. Physical and outside sites remain
  unrestricted.
- **Source:** the interval registers in Section 5 of the same circuit note.
- **Sanctioned bridge:** `isIntervalInteriorInitialized_split` separates the
  two child conditions and the initialization of the joining auxiliaries.

### `MPUCircuit.IsIntervalPartition`

- **Declaration:** `IsIntervalPartition start length tree`.
- **Defined in:** `TNLean/MPS/MPU/BalancedIntervalTree.lean`.
- **Meaning:** an ordered binary subdivision of a positive-length interval
  into single-site leaves, with each internal node labelled by its actual
  joining cut.
- **Source:** the balanced interval recursion in Section 5 of the circuit note.
- **Sanctioned construction:** the midpoint tree provides this partition
  without a supplied tree or joining-cut witness.

### `MPUCircuit.IsMinimalIntervalColumnImplementation`

- **Declaration:** `IsMinimalIntervalColumnImplementation ... j k ... Z`.
- **Defined in:** `TNLean/MPS/MPU/MinimalIntervalColumns.lean`.
- **Meaning:** on the prescribed initialized interval input, $Z$ gives the
  weighted minimal interval isometry, with its two outer bond encodings,
  and the identity on every outside logical configuration.
- **Source:** the weighted interval columns in Section 5 of the circuit note.
- **Sanctioned bridges:** exact supported child columns determine the joint
  columns; the actual joining contraction determines the parent columns.
- **Caveat:** this is an initialized-column identity, not a circuit-existence
  or resource assertion by itself.

### `MPUCircuit.IsMinimalIntervalCircuitImplementation`

- **Declaration:** `IsMinimalIntervalCircuitImplementation ... j k ... K Z C`.
- **Defined in:** `TNLean/MPS/MPU/MinimalIntervalCircuit.lean`.
- **Meaning:** $Z$ is a logical unitary supported on the interval and has the
  preceding initialized-column identity. A neighboring-pair circuit $C$ has
  at most $K$ gates and implements $Z$ with the shared workspace returned to
  zero on every logical input.
- **Source:** the full interval circuit conditions in Section 5 of the note.
- **Sanctioned constructions:** the actual leaf construction and
  `exists_minimalInterval_merging_circuit` supply this predicate. The final
  bounded-cut-rank theorem constructs every intermediate datum from $U$.
- **Caveat:** minimal bases, metrics, and child implementations occur only
  in intermediate statements; the final existence theorem does not assume
  them as additional witnesses.

## Arbitrary-boundary MPO algebras and actions

### `MPOTensor.IsBoundaryClosed`

- **Declaration:** `MPOTensor.IsBoundaryClosed T`.
- **Defined in:** `TNLean/MPS/MPDO/BoundaryClosedness.lean`.
- **Meaning:** for every pair of boundary matrices `X,Y`, there is one
  boundary matrix `Z` such that the product of the corresponding closed
  operators equals the operator with boundary `Z` at every positive length.
  The order is `∀ X Y, ∃ Z, ∀ L > 0`; `Z` cannot depend on `L`.
- **Source:** arXiv:2203.12563v3, `algcond`,
  `Papers/2203.12563/REsubmission.tex:321-330`, and Appendix A, lines 2307-2309.
- **Sanctioned bridges:** `isBoundaryClosed_iff_exists_linearMap` derives
  one linear boundary map on the full stacked matrix space, valid at all
  positive lengths; `mpoWithBoundary_eq_physCloseN` identifies the existing
  physical closure; `IsBoundaryClosed.mul_mem_range` gives closure of its
  range at each positive length. Exact biorthogonal data imply the predicate
  through `isBoundaryClosed_of_biorthogonalDecomposition`.
- **Caveat:** closure at each length alone does not supply a common boundary
  choice. No converse from independent lengthwise range closure is asserted.
  `IsBoundaryClosed.exists_blockFusionDecomposition_of_isInjective` now
  constructs exact fusion decompositions from an unweighted block presentation
  with positive-dimensional, individually injective, gauge-scalar-separated
  blocks. The common positive spanning length is derived, not assumed.

### `MPOTensor.IsBoundaryCompatible`

- **Declaration:** `MPOTensor.IsBoundaryCompatible T A`.
- **Defined in:** `TNLean/MPS/MPDO/BoundaryClosedness.lean`.
- **Meaning:** every operator boundary and state boundary admit one output
  state boundary realizing their action at all positive chain lengths.
  Again the existential boundary precedes the universal positive length.
- **Source:** arXiv:2203.12563v3, `eq:compatible`,
  `Papers/2203.12563/REsubmission.tex:431-469`, and Appendix A.
- **Sanctioned bridges:** `isBoundaryCompatible_iff_exists_linearMap`
  supplies a length-independent linear map on the complete product boundary
  matrix space. `MPSTensor.mpvWithBoundary_eq_groundSpaceMap` and
  `IsBoundaryCompatible.mulVec_mem_groundSpace` identify the boundary state
  map and prove ground-space invariance. Exact action data give compatibility
  through `isBoundaryCompatible_of_biorthogonalDecomposition`.
- **Caveat:** separate ground-space invariance at each length does not assert
  a common boundary transport.
  `IsBoundaryCompatible.exists_blockActionDecomposition_of_isInjective`
  constructs exact action tensors from unweighted operator/state block
  presentations and positive-dimensional, individually injective,
  gauge-scalar-separated target state blocks. Operator-block injectivity is
  unnecessary. The predicate itself does not assume those data or their laws.

### `MPSTensor.IsBiorthogonalDecomposition`

- **Declaration:** `MPSTensor.IsBiorthogonalDecomposition B A V W`.
- **Defined in:** `TNLean/MPS/MPDO/BoundaryTransport.lean`.
- **Meaning:** each letter satisfies `B i = ∑ c, W c * A c i * V c`,
  with `V c * W c = 1` and `V c * W e = 0` for distinct labels.
  The rectangular synthesis maps `W` and analysis maps `V` need not be
  adjoints; ambient completeness `∑ c, W c * V c = 1` is not a field.
- **Source:** the exact fusion/action and orthogonality equations
  `fusiontensors`, `eq:orthoW`, `fusiontensors2`, `eq:orthoV` in
  arXiv:2203.12563v3, and its Appendix A.
- **Sanctioned bridges:** the predicate's `evalWord`,
  `trace_mul_evalWord`, and `mpvWithBoundary` theorems transport every
  nonempty word and its arbitrary boundary exactly. `evalWord_of_complete`
  extends this to the empty word under the explicit ambient-completeness
  identity. The MPO product/action constructors in `BoundaryClosedness.lean`
  turn suitable data into arbitrary-boundary closedness/compatibility.
- **Caveat:** this is exact local reconstruction, stronger than a periodic
  trace reduction with a nilpotent remainder. Neither periodic equality nor
  nilpotent-remainder reduction supplies this predicate automatically.
  Empty-word transport without ambient completeness is not claimed, nor is
  reconstruction from closedness/compatibility without further block hypotheses.
  The source-block construction is in `BoundarySourceDecomposition.lean`;
  `BoundaryZipperBlocked.lean` retains its exact unblocked maps and packages
  the same maps into a complete zipper family after a derived common blocking.
  `IsBiorthogonalDecomposition.multiplicity_eq_of_isInjective` proves uniqueness
  of multiplicities under positive dimensions and injective block separation.

## Finite-domain area law and open-grid PEPS approximation

The September 24, 2026 OpenAI manuscripts use two different Hamiltonian
classes. Their precise hypothesis comparison and present proof status are
recorded in [the finite-domain and PEPS statement audit](formalization/openai-area-law-peps.md).

| Declaration | Mathematical meaning | Source and status |
|---|---|---|
| `TNLean.PEPS.AreaLaw.IsAdmissibleSupport` | A nonempty support whose pairs are joined by induced-domain walks of length at most the interaction range | Area-law `eq:hamiltonian`; definition, with the extended-distance equivalence proved. |
| `TNLean.PEPS.AreaLaw.LocalHamiltonian` | One supported, norm-bounded Hermitian term per admissible support | Area-law `eq:hamiltonian`; no unrestricted multiplicity of terms. |
| `TNLean.PEPS.AreaLaw.exists_quasilocal_lieb_robinson` | Positive constants `C, v, c`, chosen before the domain and the Hamiltonian, giving exponential decay in induced-graph distance of commutators of evolved supported operators with on-site operators (exact zero between components), and of their distance from graph-ball partial-trace expectations | Area-law Lemma 4.1 (`lem:quasilocal-lr`); proved with the source's hypotheses, the constants depending only on `R` and `J`. |
| `TNLean.PEPS.AreaLaw.exists_latticePositiveConstraints` | Positive contractions `kᵢ` annihilating the gapped ground vector, whose sum dominates the gap and whose graph-ball expectations converge stretched-exponentially, with constants chosen before the domain and the Hamiltonian | Area-law Proposition 4.3 (`prop:positive`) on induced lattice domains; constants depend only on `p, R, J, Δ`. |
| `TNLean.PEPS.AreaLaw.exists_latticeQuasilocalRoots` | Square roots `(I - kᵢ)^{1/2}`, `kᵢ^{1/2}` and their graph-ball truncations, with stretched-exponential tails and the induced unital local channels | Area-law Lemma 4.4 (`lem:quasilocal-roots`) on induced lattice domains; constants depend only on `p, R, J, Δ`. |
| `TNLean.PEPS.AreaLaw.exists_latticeFiniteSetTruncation` | Constraints truncated near a finite set `S₀` of at most `C₀ n²` sites at radius `⌈C₁ (log n)²⌉`, within `ε_n` of the positive Hamiltonian, with a unit ground vector and gap at least half | Area-law Proposition 4.5 (`prop:truncation`), first part, on induced lattice domains, with `p = 1`; `C₁` depends only on `R, J, Δ, C₀`. |
| `TNLean.PEPS.AreaLaw.exists_latticeCrossingBudget` | Crossing constraints of a cut are balls about their anchors, number at most `C b_X (r₀ + 1)²`, have log-dimension at most `C (r₀ + 1)²`, and the cut budget is at most `C (1 + b_X) (r₀ + 1)⁶` | Area-law `eq:quasilocal-crossing-count` and `eq:quasilocal-cut-budget`; `C` depends only on `q` and `R`. |
| `TNLean.PEPS.AreaLaw.exists_latticeCutBudget_le_log` | The cut budget at radius `⌈C₁ (log n)²⌉` is at most `C n D (log n)¹²` when `b_X ≤ C₂ n D` | Area-law Proposition 4.5, last sentence; `C` depends only on `q, R, C₁, C₂`. |
| `Matrix.IsGappedGroundState`, `Matrix.isGappedGroundState_iff` | Unit eigenvector `HΩ = E₀Ω` of a complex square matrix with the full-system projector-gap inequality; the characterization restates the eigen-equation as `H *ᵥ Ω = E₀ • Ω` on coordinate vectors | Shared by the area-law and polynomial-PEPS models, which specialize it. |
| `TNLean.PEPS.AreaLaw.IsGappedGroundState` | Unit eigenvector with a full-system positive projector-gap inequality | Area-law Theorem 1.1; the checked ground/uniqueness equivalence is tracked in #8739. |
| `TNLean.PEPS.AreaLaw.relabelState` | The same physical vector in configuration coordinates transported by a site bijection | Area-law Section 2; Euclidean norm is preserved, reductions are covariant and regional entropy is invariant when the bijection preserves the cut. |
| `TNLean.PEPS.AreaLaw.UniformAreaLaw` | A uniform boundary entropy bound over every finite induced domain and cut | Area-law Theorem 1.1; a target proposition, not a proved theorem. |
| `TNLean.PEPS.AreaLaw.innerBoundary` | Sites in the cut adjacent to its complement within the induced domain | Area-law Corollary 1.2; every cut has at most four crossing edges per inner-boundary site. |
| `TNLean.PEPS.AreaLaw.endpointBoundary` | Both endpoints of every crossing edge, with repetitions removed | Area-law Corollary 1.2; the number of crossing edges is at most twice the number of boundary endpoints. |
| `TNLean.PEPS.AreaLaw.UniformAreaLaw.vertex_boundary_bounds` | Inner-boundary and endpoint entropy bounds with constants four and two times the edge-boundary constant | Area-law Corollary 1.2; proved conditionally on `UniformAreaLaw`, with the same uniform quantifiers. |
| `TNLean.PEPS.AreaLaw.regionalEntropy_eq_zero_of_edgeBoundary_eq_empty` | A cut with no crossing edge has zero regional entropy in a gapped ground vector | Area-law Lemma 2.2 (`lem:zero-boundary`), `01-preliminaries.tex`, lines 123–134; proved, using only the gapped ground-vector hypothesis with `Δ > 0`. |
| `QuantumCircuit.graphBall` | The closed ball `N_l(a) = {x : d_G(a,x) ≤ l}` of a finite graph in the extended graph distance | Area-law `03-quasilocal.tex`, line 17; sites in other connected components are at infinite distance and never belong to a ball. Defined in `TNLean/Circuit/LiebRobinson/GraphLocalization.lean`. |
| `TNLean.PEPS.AreaLaw.cutLogBudget` | The parameter `ℬ_A = 1 + ∑ log²(e q^{|X|})` of a cut, summed over the admissible supports meeting both `A` and its complement | Area-law Lemma 3.1 (`lem:tail`), `02-initial.tex`, lines 47–55; the lattice instance of QICLean's `Entropy.cutLogBudget`, bounded by the number of crossing supports in `cutLogBudget_le_card`. |
| `TNLean.PEPS.AreaLaw.concentrationWidth` | The width `32 √((1 + J/Δ) ℬ_A) (M log(n+2) + e/2 + log 2)` at which the marginal tail of Lemma 3.1 is at most `(n+2)^{-M}` | Area-law `02-initial.tex`, lines 207–212; an explicit width in terms of `ℬ_A`, used in `LocalHamiltonian.one_sub_rpow_le_typicalMass_reducedState`. |
| `TNLean.PEPS.AreaLaw.tailParameterConstant` | The constant `C = v_R μ_R log²(e q^{v_R})`, with `v_R = 1 + 2R(R+1)` and `μ_R = 2^{v_R - 1}`, in `ℬ_A ≤ C(1 + |∂_Λ A|)` | Area-law `eq:initial-local-tail-parameter`, `02-initial.tex`, lines 202–206; depends only on `q` and `R`, at least one for `q ≥ 1`; the bound is `cutLogBudget_le_edgeBoundary`. |
| `TNLean.PEPS.AreaLaw.typicalWidthConstant` | The constant `C_M = 32 √((1 + J/Δ) C) (M + (e/2 + log 2)/log 2)` with `C = tailParameterConstant q R` | Area-law `02-initial.tex`, lines 207–212; depends only on `q, R, J, Δ, M`; bounds the concentration width by `C_M √(1 + |∂_Λ A|) log(n+2)` in `concentrationWidth_le`. |
| `TNLean.PEPS.AreaLaw.IntRect` | A product `[x₀,x₁] × [y₀,y₁]` of two nonempty finite integer intervals, with `size` the larger number of sites along an axis and `dilate d` the rectangle `Q^{+d}` | Area-law `02-initial.tex`, lines 222–232; an ambient rectangle, not a set of sites of the domain. |
| `TNLean.PEPS.AreaLaw.IsSafe` | The sup-norm distance from the rectangle `Q` to every endpoint of an edge crossing `A` exceeds `D₀ · size Q` | Area-law `02-initial.tex`, lines 220–228; vacuous when no edge crosses `A`, matching the source's infinite distance to the empty set. The source's standing condition `D₀ > 2R + 10` is a hypothesis of the theorems, not of the predicate. |
| `TNLean.PEPS.AreaLaw.rectRegion` | The physical region `A ∩ Q` of an ambient rectangle | Area-law `02-initial.tex`, lines 232–233; sites of `Q` missing from the domain or from `A` are absent. |
| `TNLean.PEPS.AreaLaw.boxEntropy` | The supremum `F_box(r)` of `S_Ω(A ∩ Q)` over all domains, admissible Hamiltonians with gapped ground vectors, cuts, and safe rectangles of size at most `r`, at fixed `q, R, J, Δ, D₀` | Area-law Proposition 3.3 (`prop:initial-box`), `02-initial.tex`, lines 590–594; a real supremum, bounded above by `r² log q` for `q ≥ 1` and estimated in `exists_boxEntropy_le_rpow`. |
| `TNLean.PEPS.AreaLaw.skewSymbol` | The scalar `f(t) = ⟨θ, ρ_P^{[t]} ρ_Y^{[-t]} h ρ_P^{[-t]} ρ_Y^{[t]} θ⟩` for regions `P, Y` of a finite domain, with `ρ^{[s]}` the real power of a regional state taken as zero on its kernel | Area-law Lemma 5.3 (`lem:skew`), `04-conditional.tex`, lines 495–500; equal to QICLean's marked scalar symbol by `skewSymbol_eq_markedScalarSymbol`, with the lemma itself in `skewSymbol_skew_le`. |
| `TNLean.PEPS.AreaLaw.Scan.ScanData` | The finite data of the collar scan at one scale for all replica counts, with the conclusions of Lemma 9.1, Propositions 7.4 and 8.1, and Lemmas 2.1 and 2.3 for that scan as fields | Area-law Proposition 9.2 (`prop:scanner`), `08-scanner.tex`, lines 399–533; the inputs are hypotheses and are not derived from the scan geometry, so results over `ScanData` are Proposition 9.2 restricted to them, as recorded in `docs/paper-gaps/arealaw2d_scanner_inputs.tex`. |
| `TNLean.PEPS.Approximation.SquareHamiltonian` | Bounded supported site and edge terms on the original open square, with Hermitian total sum | Polynomial-PEPS `eq:model`; individual Hermiticity is not assumed. |
| `TNLean.PEPS.Approximation.HasPEPSApproximation` | Nonzero native PEPS, positive polynomially bounded bonds, and normalized global error at most the inverse side length, up to phase | Polynomial-PEPS Theorem 1.1; a predicate defining the desired approximation. |
| `TNLean.PEPS.Approximation.PolynomialPEPSApproximation` | Constants chosen before every square size, Hamiltonian, and ground vector | Polynomial-PEPS Theorem 1.1; a target proposition, not a proved theorem. |
| `TNLean.PEPS.AreaLaw.Geometry.Template` | A nonempty finite ambient lattice union sampled from the permitted rectangles and triangles, with the source size conditions | Area-law Definition 9.3; distinct from induced-graph support geometry. |
| `TNLean.PEPS.AreaLaw.Geometry.OrderedTwoFamilyPartition` | A finite disjoint partition with residual sites and two ordered families | Area-law Lemma 11.1; contains no entropy or separation assumption. |
| `TNLean.PEPS.AreaLaw.Geometry.dyadicNeighborhood`, `dyadicLayer` | Actual translated half-open cell unions and their successive differences at nonnegative dyadic scales | Area-law Section 11; nesting, exact layer-cell unions, closed-cell formulas, uniform cell counts, endpoint-distance bounds, and nonadjacent-layer separation proved. Exhaustion holds for a nonempty endpoint set and radius at least two. |
| `TNLean.PEPS.AreaLaw.Geometry.dyadicLayer_infDist_bounds`, `dyadicLayer_dist_nonadjacent` | The source's lower and upper sup-distance bounds to the endpoints, and separation of closed layers whose scales differ by at least two | Area-law `geometry:layer-distance` and `geometry:nonadjacent`; proved for arbitrary origin and nonnegative integer radius. The nonadjacent lower bound is positive when the radius is at least two; the full two-family partition remains open. |
| `TNLean.PEPS.AreaLaw.Geometry.fineLayerIndices`, `fineScaleIndex`, `pitchScaleIndex`, `exists_sparse_dyadic_belt_shift` | Actual fine-cell layer indices, the fixed rounded fine and pitch scales, and selection of sparse coordinate belts | Area-law `geometry:belt-count`; exact fine-cell unions and counts, scale divisibility, and the bound `64*(2*C₀+1)^2*b*2^(-δ₀*k/2)` proved, including empty layers. The constant is uniform in domain, cut, origin, and scale. The two-family construction remains open. |
| `TNLean.PEPS.AreaLaw.Geometry.exists_dyadicScale_side_ratios` | A threshold for each fixed factor separates the fine-cell side, layer-cell side, and belt pitch at every later scale | Area-law Section 11, lines 200–207; proved uniformly in all physical and geometric data. The later geometric construction remains open. |
| `TNLean.PEPS.AreaLaw.Geometry.exists_polynomial_dyadic_absorption`, `summable_polynomial_dyadic_decay`, `exists_uniform_polynomial_dyadic_sum_bound` | Absorption of every fixed real power into the exponential belt decay, convergence of the resulting series, and one positive bound on arbitrary finite scale sums | Auxiliary numerical estimates for Area-law `geometry:total-repairs`, lines 668–692, uniform in all physical and geometric data. Descendant counts and the actual repair construction and count remain open. |
| `TNLean.PEPS.AreaLaw.Geometry.latticeRow` | Horizontal integer coordinates at a fixed vertical coordinate | Lemma 9.4 proof; this is a horizontal section, not a dilation depth layer. |
| `TNLean.PEPS.AreaLaw.Geometry.template_card_le` | The template area is at most `9*n*s₀` when `Ctpl ≥ 1` | Area part of Lemma 9.4; distinct from the dilation depth-layer bound. |
| `TNLean.PEPS.AreaLaw.Geometry.template_layer_card_le` | Each ambient dilation layer has at most `n` sites for `Ctpl ≥ 24` and `1 ≤ j ≤ s₀` | Geometric depth-layer part of Lemma 9.4, derived from the actual polygon model; no added row regularity. See [validation status](formalization/template-rows.md). |
| `TNLean.PEPS.AreaLaw.ambientBoundary` | Unordered ambient nearest-neighbor crossing edges, using the existing finite-domain boundary on a one-step enclosure | Exact ambient edges, distinct from physical cut intersections; [boundary proof status](formalization/template-boundary.md). |
| `TNLean.PEPS.AreaLaw.Geometry.template_cut_boundary_card_le` | Physical unordered crossing edges of `A ∩ T_j` number at most `4n`; the core and shell have bounds `4n` and `8n` | Lemma 9.4; avoidance is derived from actual separation for `D₀ ≥ 1`, `Ctpl ≥ 24`, and `j ≤ s₀`. [Validation status](formalization/template-cut-boundary.md). |

## Distributed PEPS compression: finite incidence and choice costs

### Corrected source positions and whole-lifetime gate participation

- **Declarations:** `TNLean.PEPS.Approximation.sourceEndpoints`, `correctedParties`,
  `incidentGates` and `gatesTouching` in the same namespace.
- **Defined in:** `TNLean/PEPS/Approximation/DistributedLifetime.lean`.
- **Meaning:** A source position has two party endpoints. For a finite set `S`
  of corrected positions, `correctedParties` is their endpoint union. The gate
  identifiers distinguish occurrences; repeated uses of an identical operation
  remain distinct. `incidentGates` filters the entire finite nonprivate gate
  list by party participation. `gatesTouching` includes every gate meeting the
  corrected party set, including gates with no corrected source of their own.
- **Source:** OpenAI, *Polynomial PEPS approximation of gapped square-grid ground
  states*, September 24, 2026, proof of Theorem 5.2, corrected-position expansion,
  `04-compression.tex:342–381`,
  [immutable manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L342-L381).
- **Sanctioned bridges:** `card_correctedParties_le` gives at most `2 * S.card`
  parties. `card_gatesTouching_correctedParties_le` gives at most
  `2 * b * S.card` affected gates from the actual whole-lifetime bound of `b`
  gates per corrected party. `owner_mem_gatesTouching_correctedParties` uses
  explicit slot-owner incidence; `disjoint_participants_of_not_mem_gatesTouching`
  proves exterior gates contain no corrected party.
- **Caveat:** These are finite incidence statements, not a distributed quantum
  circuit model or a density expansion. Coincident endpoints are permitted by
  the counting lemmas. The eventual source-position model must supply its
  owner/endpoint incidence, and the gate list must use occurrence identifiers.
  No private-memory or source-Schmidt-rank bound is imposed.

### Star and pair-sample virtual links

- **Declarations:** `TNLean.PEPS.Approximation.pairSampleLabels`, `gateLinkLabels`,
  `gateLinkParties`, `linksAtGate`, `distributedLinks`, `distributedLinkParties`,
  `incidentDistributedLinks`, `incidentGateLinkLabels` and `incidentLinksAtGate`.
- **Defined in:** `TNLean/PEPS/Approximation/DistributedLinks.lean`.
- **Meaning:** Each gate has a star rooted at a chosen participant and a sample
  link for every unordered pair of distinct participants. Summand tags keep
  star and sample links distinct, while gate-occurrence tags preserve parallel
  links from different gates. Endpoint sets and incidence lists are derived
  from this actual construction.
- **Source:** The same September 24 manuscript, proof of Theorem 5.2,
  `04-compression.tex:565–588`,
  [immutable manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L565-L588).
- **Sanctioned bridges:** `card_pairSampleLabels` gives `choose n 2` sample
  links at a gate of arity `n`; `card_gateLinkLabels` gives `n - 1 + choose n 2`
  total labels when the star root participates. `card_distributedLinkParties`
  proves two distinct endpoints. `distributedLinkParties_subset` and
  `exists_common_gate_of_mem_distributedLinkParties` derive original-gate
  locality. `card_incidentDistributedLinks_le` gives degree at most
  `2 * b * (b - 1)` from gate arity at most `b` and whole-lifetime participation
  at most `b`.
- **Caveat:** Star-root membership is explicit and must come from a chosen
  participant of a nonprivate gate. This family has no local tensors, virtual
  dimensions or evaluation map. Contraction and parallel-link combination
  remain separate results; these links alone do not represent the compressed
  density operator.

### Weighted cost of affected coefficient and physical-entry choices

- **Declarations:** `TNLean.PEPS.Approximation.ketBraCoefficientCost` and
  `correctedPositionChoiceCost`.
- **Defined in:** `TNLean/PEPS/Approximation/CorrectedPositionCost.lean`.
- **Meaning:** `ketBraCoefficientCost` is the square of the sum of nonnegative
  absolute coefficient weights. `correctedPositionChoiceCost` multiplies these
  quantities over affected gates and the squares of intended physical
  dimensions over corrected parties. Exterior coefficients and dimensions
  do not occur in these products.
- **Source:** The same September 24 manuscript, `eq:compression-polynomial-bounds`
  and `eq:compression-choice-cost`, `04-compression.tex:269–277,356–381`,
  [immutable manuscript](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/04-compression.tex#L356-L381).
- **Sanctioned bridges:** `ketBraCoefficientCost_eq_sum` identifies the square
  with the double ket/bra coefficient sum. For `B,d ≥ 1`, actual coefficient
  sums at affected gates at most `B`, physical dimensions at corrected parties
  at most `d`, and lifetime participation at most `b`,
  `correctedPositionChoiceCost_le` proves the bound `(B^(4*b) * d^4)^S.card`.
  `compressionChoiceBase_le_of_monomial_bounds` gives
  `Q ≤ C^(4*b) * D^4 * L^(4*b*a + 4*c)` when `B ≤ C*L^a` and `d ≤ D*L^c`.
- **Caveat:** Coefficients are supplied as nonnegative weights; the circuit
  expansion must identify them with actual complex coefficient norms. The
  theorem bounds a finite choice cost, not an expected trace error. The full
  circuit expansion, local tensor evaluation, virtual dimension estimates,
  approximate-expansion case and composition with the quantum/sampling results
  remain open in [#8769](https://github.com/LionSR/TNLean/issues/8769).

## Nested regional cylinders

### `TNLean.PEPS.dependentRegionCylinder`

- **Declaration:** `dependentRegionCylinder R S`.
- **Defined in:** `TNLean/PEPS/AreaLaw/Cylinder.lean`.
- **Meaning:** the global vectors all of whose complementary coordinate slices
  lie in the inside subspace `S`; in tensor notation, `S ⊗ H_(V\R)`.
- **Source:** the September 24, 2026 polynomial-PEPS manuscript,
  [`03-patches.tex`, lines 563–603](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Polynomial-PEPS-approximation-of-gapped-square-grid-ground-states-September-24-2026/build/sections/03-patches.tex#L563-L603).
- **Sanctioned identifications:** `range_dependentRegionOperatorLift` identifies
  the range of an identity extension with a cylinder;
  `coordinateRangeProjector_dependentRegionCylinder` identifies the orthogonal
  projector. The `sup`, `iSup`, `subregion`, and `map` theorems give finite-sum,
  containing-region, and image identities in the existing physical coordinates.
- **Caveat:** inside rank means `dim S`, not the global dimension of the
  cylinder. No cancellation of a possibly zero-dimensional outside factor
  is used. The empty region still has inside Hilbert space `ℂ`.

### `TNLean.PEPS.nestedCylinderInnovation`

- **Declaration:** `nestedCylinderInnovation R hR S j`, where `hR` states
  that the finite family of regions is monotone.
- **Defined in:** `TNLean/PEPS/AreaLaw/NestedCylinderOrthogonalization.lean`.
- **Meaning:** the inside image `(I − P_(Wⱼ)) Sⱼ`, where
  `nestedCylinderEarlierInside` constructs `Wⱼ` by lifting the original earlier
  inside projectors into the current region and taking the sum of their ranges.
- **Source:** the variable-radius orthogonalization at the manuscript passage
  linked above.
- **Sanctioned consequences:** `nestedCylinderInnovation_prefix_span` and
  `nestedCylinderInnovation_span` identify all prefix and total spans;
  `nestedCylinderInnovation_pairwise_orthogonal` proves orthogonality in the
  actual global Hilbert space; `nestedCylinderInnovation_projector_sum` gives
  the sum of the lifted inside projectors. The individual and summed
  `finrank` bounds compare inside dimensions directly, in natural and integer
  form. `nestedCylinder_projector_supported` gives support on any containing
  region, and that support result does not require nesting.
- **Caveat:** the image need not equal `Sⱼ ∩ Wⱼ⊥`; the sandwich
  `(I − P_(Wⱼ)) P_(Sⱼ) (I − P_(Wⱼ))` need not be a projector. Neither
  commutation of the original projectors nor a spectral rank estimate is
  assumed. This is the orthogonalization step, not the approximation-error
  or full adaptive-patch theorem. See
  [the construction and scope note](formalization/peps-nested-cylinder-orthogonalization.md).

## Two-family regional entropy

- `FiniteProduct.entropy` (QICLean): canonical von Neumann entropy of the actual
  regional reduced pure-state matrix, for arbitrary finite dependent local bases.
- `FiniteProduct.entropy_le_remainder_add_half_sum` (QICLean): exact normalized
  pure-state two-family cancellation, with coefficient `1/2` and the entire
  exterior-plus-earlier-same-family mutual-information assumptions.
- `TNLean.PEPS.AreaLaw.regionalEntropy_le_residual_add_half_sum`: the finite-domain
  specialization using the existing `OrderedTwoFamilyPartition` and regional
  entropy. It assumes no Hamiltonian, gap, geometry, nonempty family, or separate
  nonnegative error bound. Source: OpenAI (September 24, 2026), area-law Lemma 11.1.
- `FiniteProduct.conditionalMutualInformation` (QICLean): the physical regional
  entropy combination. Generic difference, finite-chain and pure-duality
  identities are available; canonical tripartite identification, exceptional-site
  dimension bounds and the full PEPS conditional-cell theorem remain separate.

## Partial template row entropy

- `TNLean.PEPS.AreaLaw.Geometry.template_partial_row_entropy_le` states the
  absolute entropy cost at most `n * log q` for any subset of one template
  depth row, the partial-row step of area-law Lemma 9.4.

## Weighted template shell coverings

- `TNLean.PEPS.AreaLaw.Geometry.Template.card_shell_le` bounds the actual
  ambient shell by `n*j` for `Ctpl ≥ 24` and `j ≤ s₀`.
- `TNLean.PEPS.AreaLaw.Geometry.Template.card_cappedDyadicPartition_shell_at_cap_le`
  bounds total cap-side length by `2*n` when `j ≤ L ≤ s₀` and `L < 2^(K+1)`.
- `TNLean.PEPS.AreaLaw.Geometry.Template.sum_rpow_cappedDyadicPartition_shell_le`
  states the weighted shell-covering bound with constant `2 + 14/(2^e - 1)`
  for `e > 0` and `2^K ≤ L < 2^(K+1)`. This is the geometric summation step
  of Lemma 9.4, not safe clearance or a regional entropy theorem.
