# Concept glossary

TNLean keeps several source-faithful formulations of the same broad mathematical
ideas. They are not interchangeable merely because their names are similar. This
glossary identifies the public entry points, records the bridges that may be used,
and states the hypotheses or known gaps that prevent stronger identifications.

For new declarations, prefer namespace overloading (`MPSTensor.IsInjective`,
`MPSChainTensor.IsInjective`, and so on) rather than putting the carrier name into
the predicate name. Preserve a paper's established terminology when a declaration
is deliberately source-faithful.

## Normality

### `MPSTensor.IsNormal`

- **Declaration:** `MPSTensor.IsNormal (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/Defs.lean`.
- **Meaning:** there is a positive word length `N` for which the length-`N`
  products of the matrices of `A` span the full `D × D` matrix algebra; equivalently,
  `A` becomes injective after blocking `N` sites.
- **Source:** Sanz--Pérez-García--Wolf--Cirac, arXiv:0909.5347, definition after
  equation (1), `Papers/0909.5347/main.tex:387-419`; see also
  Cirac--Pérez-García--Schuch--Verstraete, arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:1815-1830`.
- **Sanctioned bridges:**
  `MPSTensor.hasEventuallyFullKrausRank_iff_isNormal`,
  `MPSTensor.IsInjective.isNormal`, and
  `MPSTensor.IsNormalTensor.isNormal`.
- **Caveat:** `MPSTensor.IsNormalTensor.isNormal` derives nonzero bond dimension
  from the spectral-radius-one clause; it requires no external positivity
  assumption. There is no equivalence theorem between `MPSTensor.IsNormal` and
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
  `MPSTensor.IsNormal`.

### Basis-level normality

- **Declarations:**
  `MPSTensor.IsCPSVBasisOfNormalTensors A blocks` in
  `TNLean/MPS/CanonicalForm/Definitions.lean`, and
  `MPSTensor.IsBNT A_total g dim A_bnt` in `TNLean/MPS/BNT/Basic.lean`.
- **Meaning:** both say that a finite family of normal blocks spans every
  positive-length matrix-product-vector family and is eventually linearly
  independent. The first uses `IsNormalTensor`; the second uses `IsNormal`.
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
  unchanged; `PeriodicOverlapHypothesis.ofSpectrallyPeriodicSectorDecompositions`
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
interfaces.

### `_root_.IsPrimitive`

- **Declaration:**
  `_root_.IsPrimitive (E : V →ₗ[ℂ] V) : Prop`.
- **Defined in:** `TNLean/Channel/Peripheral/Spectrum.lean`.
- **Meaning:** the unit-circle eigenvalue set of `E` is exactly `{1}`.
- **Source:** Wolf, *Quantum Channels & Operations: Guided Tour*, §6.3,
  Theorem 6.7; compare arXiv:2011.12127 §IV.
- **Sanctioned bridges:** `_root_.isPrimitive_iff`,
  `_root_.isPrimitive_iff_period_one`, and, for transfer maps,
  `MPSTensor.isPeripherallyPrimitive_iff`.
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
- **Meaning:** a thin MPS wrapper around
  `_root_.IsPrimitive (MPSTensor.transferMap A)`.
- **Source:** Wolf §6.3, Theorem 6.7, and arXiv:0909.5347 Proposition 3(c).
- **Sanctioned bridges:** `MPSTensor.isPeripherallyPrimitive_iff`,
  `MPSTensor.IsPrimitiveMPS.isPeripherallyPrimitive`, and
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
  algebraic eventual-span condition as `MPSTensor.IsNormal`, not the generic
  peripheral-spectrum predicate `_root_.IsPrimitive`.

### `MPSTensor.IsPrimitiveMPS` and `MPSTensor.HasPrimitiveFixedPoint`

- **Declarations:**
  `MPSTensor.IsPrimitiveMPS A ρ` and
  `MPSTensor.HasPrimitiveFixedPoint A`.
- **Defined in:** `TNLean/MPS/Structure/PrimitivityBridge.lean`.
- **Meaning:** `IsPrimitiveMPS A ρ` packages left-canonical normalization, a
  nonzero positive-semidefinite fixed point `ρ`, and spectral radius less than
  one on the complement of the fixed-point projection.
  `HasPrimitiveFixedPoint A` existentially quantifies `ρ`.
- **Source:** the complementary transfer-map-gap formulation used in the MPS
  convergence route; compare Wolf §6.3, Theorem 6.7, and the convergence
  consequences of arXiv:0909.5347 Proposition 3.
- **Sanctioned bridges:**
  `MPSTensor.IsPrimitiveMPS.isPeripherallyPrimitive`,
  `MPSTensor.hasPrimitiveFixedPoint_of_peripheralPrimitive`,
  `MPSTensor.hasPrimitiveFixedPoint_of_peripheralPrimitive_of_irreducible`,
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

#### `MPSTensor.IsInjective`

- **Declaration:** `MPSTensor.IsInjective (A : MPSTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/Defs.lean`.
- **Meaning:** the one-site matrices `{A i}` span the full matrix algebra; this
  is the linear-algebraic injectivity of the tensor as a virtual-to-physical map.
- **Source:** arXiv:1804.04964 §2,
  `Papers/1804.04964/paper_normal.tex:196-222`; see also arXiv:2011.12127,
  `Papers/2011.12127/TN-Review-main.tex:298-300`.
- **Sanctioned bridges:** `MPSTensor.isNBlkInjective_one_of_isInjective`,
  `MPSTensor.IsInjective.isNormal`, and
  `MPSTensor.isNBlkInjective_iff_blockTensor_isInjective`.
- **Caveat:** this is one-site injectivity. A tensor can fail this predicate and
  satisfy `IsNBlkInjective A N` for a larger `N`.

#### `MPSTensor.IsNBlkInjective`

- **Declaration:**
  `MPSTensor.IsNBlkInjective (A : MPSTensor d D) (N : ℕ) : Prop`.
- **Defined in:** `TNLean/MPS/Defs.lean`.
- **Meaning:** products indexed by all words of exactly length `N` span the full
  matrix algebra.
- **Source:** arXiv:0909.5347, equation (1) and the following definition of
  eventual full Kraus rank; arXiv:2011.12127 §IV.A, normal tensors becoming
  injective after blocking.
- **Sanctioned bridge:**
  `MPSTensor.isNBlkInjective_iff_blockTensor_isInjective` in
  `TNLean/MPS/Chain/BlockedChainFT.lean`.
- **Caveat:** no positivity condition on `N` is built into this predicate;
  `MPSTensor.IsNormal` explicitly requires a positive witness.

#### `MPSChainTensor.IsInjective` and `MPSChainTensor.IsWindowInjective`

- **Declarations:** `MPSChainTensor.IsInjective A` in
  `TNLean/MPS/Chain/Defs.lean`, and `MPSChainTensor.IsWindowInjective A L` in
  `TNLean/PEPS/CycleMPSChainArc.lean`.
- **Meaning:** the first requires one-site `MPSTensor.IsInjective` at every site
  of a non-translation-invariant chain. The second requires every cyclic window
  of length `L` to have full arc-product span.
- **Source:** arXiv:1804.04964 §2, lines 145--222, and the normal-window
  formulation in §3 `normal_alt`,
  `Papers/1804.04964/paper_normal.tex:1928-1940`.
- **Sanctioned bridges:**
  `MPSChainTensor.isWindowInjective_one_of_isInjective` and
  `MPSChainTensor.isWindowInjective_const`.
- **Caveat:** window injectivity requires `[NeZero n]`. The compatibility alias
  the root compatibility alias `IsInjectiveChain` names
  `MPSChainTensor.IsInjective`; new code should use the namespace-qualified
  predicate.

#### `MPOTensor.IsInjective`

- **Declaration:** `MPOTensor.IsInjective (K : MPOTensor d D) : Prop`.
- **Defined in:** `TNLean/MPS/MPDO/SimpleLocalStructure.lean`.
- **Meaning:** an abbreviation for
  `MPSTensor.IsInjective K.toMPSTensor` on the doubled physical index.
- **Source:** arXiv:1606.00608 Appendix C.2, where an inverse tensor is used for
  the blocked simple MPDO tensor; see
  `Papers/1606.00608/MPDO-22-12-17-2.tex:1628-1658`.
- **Sanctioned bridge:** this is a definitional abbreviation; unfold it to use
  the `MPSTensor.IsInjective` API.
- **Caveat:** it does not mean injectivity of the MPO as an operator on every
  chain length.

### PEPS predicates

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
- **Sanctioned bridges:** `MPSTensor.IsCanonicalForm.of_peripheral_primitive`,
  `MPSTensor.IsCanonicalForm.toHasInjectiveBlocks`,
  `MPSTensor.IsCanonicalForm.toIsLeftCanonicalBlockFamily`, and
  `MPSTensor.IsCanonicalForm.toHasNormalizedSelfOverlap`.
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
  `MPSTensor.IsNormalCanonicalForm.toHasPrimitiveBlocks`, and
  `MPSTensor.IsNormalCanonicalForm.ofSeparatedData`.
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
- **Sanctioned bridges:** the inherited projection
  `MPSTensor.IsNormalCanonicalFormBNT.toIsNormalCanonicalForm` and the public
  projections `toHasIrreducibleBlocks`, `toIsLeftCanonicalBlockFamily`, and
  `toHasPrimitiveBlocks` in its namespace.
- **Caveat:** this is a one-representative-per-gauge-phase-class surface. It
  suppresses repeated copies and their power-sum coefficients; see
  `docs/paper-gaps/ft_one_copy_scope_restriction.tex`. It is not equivalent by
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
  `MPSTensor.exists_isBNTCanonicalForm_afterBlocking_pos`.
- **Caveat:** `IsBNTCanonicalForm.blockTensor` requires a strictly positive
  blocking length `0 < p`; it does not assert preservation at length zero.
  `exists_isBNTCanonicalForm_afterBlocking_pos` is conditional: after
  constructing prepared blocks it requires both `∀ k, ‖μ k‖ ≤ 1` and
  `∃ k, ‖μ k‖ = 1` before it yields the canonical-form witness. It is not an
  unconditional existence theorem. This is the canonical predicate when
  multiplicities and raw sector weights matter. It is not equivalent to the
  flattened `IsNormalCanonicalFormBNT`; multiplicity recovery is genuine
  mathematical content, not a change of packaging.

### MPDO canonical-form predicates

- `MPOTensor.IsHorizontalCF` in `TNLean/MPS/MPDO/HorizontalBNT.lean` is the
  normalized representative-indexed BNT-refined horizontal decomposition. It
  is stronger than the literal CPSV canonical form from arXiv:1606.00608,
  lines 237--244; see
  `docs/paper-gaps/cpgsv17_vertical_cf_grouping.tex`.
- `MPOTensor.IsPerCopyHorizontalCF` in
  `TNLean/MPS/MPDO/PerCopyHorizontalCF.lean` is an older, stronger flattened
  per-copy separation condition. Its gap from the source is recorded in
  `docs/paper-gaps/cpgsv17_bicf_block_separation.tex`; there is no sanctioned
  equivalence with `IsHorizontalCF`.
- `MPOTensor.IsVerticalCF` in `TNLean/MPS/MPDO/VerticalCF.lean` is the vertical
  basis decomposition with positive multiplicities, positive diagonal weights,
  and a coisometry `U` satisfying `U * Uᴴ = 1` (equivalently, `Uᴴ` is an
  isometry), sourced to arXiv:1606.00608 lines 1901 and 1956. It requires both
  the compressed block identity and exact reconstruction by `Uᴴ` and `U`.
  Reconstruction still permits an omitted all-zero complement because `Uᴴ * U`
  is the retained-support projection; see
  `docs/paper-gaps/cpgsv17_vertical_isometry_zero_sector.tex`.
- `MPOTensor.IsSimpleCanonicalForm` in `TNLean/MPS/MPDO/SimpleTensor.lean` is
  horizontal canonical form plus the MPDO and nonnilpotent-sector conditions of
  arXiv:1606.00608, lines 815--822. The sanctioned one-way bridge is
  `MPOTensor.IsSimpleCanonicalForm.isHorizontalCF`.

The `CF` spelling in these established MPDO names is retained for compatibility
and paper-local vocabulary. New public predicates should spell out
`CanonicalForm` unless a source-faithful established name requires otherwise.
