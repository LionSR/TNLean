# Eighteen unused helpers from the zero-reference residue

Scope: proof-debt issue #9881, ledger S2. Base:
`5a13935af88f0349e57dfb2a0edd75e40aae0437`.

The default `python3 scripts/zero_reference_scan.py` at the base reports 41
candidates. Each was read individually. Remove only the eighteen below; none
carries an attribute, a Blueprint anchor or a source citation of its own, and
none is a worked example's headline result or a named object of an example.

Algebra:

- `CoveringMatching.CoveringChain.jump_bijective`, in `CoveringMatching.lean`:
  `(jumpEquiv c c').bijective`. The Blueprint-tagged `jumpEquiv` already states
  the bijection. Replacement: `(jumpEquiv c c').bijective`.
- `mul_rpow_le_mul_rpow_of_ceil_powerRatioThreshold_le`, in
  `ExplicitThresholds.lean`: the natural-number form of the retained
  `mul_rpow_le_mul_rpow_of_powerRatioThreshold_le`, obtained by
  `Nat.ceil_le.mp`. Replacement: that composition.

Area law:

- `TNLean.MPS.AreaLaw.Hastings.lemmaOneBudgetA_nonneg`, in
  `Hastings/FactorizationBudget.lean`: `unfold; positivity` for the constant
  term of the Lemma 1 budget. Consumers bound `lemmaOneBudgetA` directly. The
  used `lemmaOneBudgetB_nonneg` remains. Replacement: none, unused.

Worked examples (no headline result or exposed object is removed):

- `Z2Z2Condensation.xX_dim_eq`, in `AnomalousCondensationZ2Z2NonSplit.lean`:
  the `dim_eq` field of `xXCompression` restated for one of the four blocks
  only. It is not listed among the module's main results. Replacement:
  `xXCompression.dim_eq`.
- `fusionSign_self_eq`, in `AnomalousCondensationZ2Z2Unitary.lean`: a bit
  formula for the diagonal fusion sign, proved by `fin_cases` and used nowhere.
  The inverse and adjoint statements compute with `fusionSign` directly.
  Replacement: none, unused.
- `KWExample.kwTensor_mpo_zero`, in `KramersWannierPhysical.lean`: the value
  `2` of the empty periodic contraction. Every kernel statement of the module
  assumes `NeZero L`. The module docstring still records the length-zero value
  to explain that hypothesis. Replacement: none, unused.
- `MultiBlockExamples.Multiplicity.kronMat_eq_kronecker`, in
  `MultiBlock/Multiplicity.lean`: a reindexed-Kronecker reading of the explicit
  matrix `kronMat`. No statement goes through it. The used
  `tensorB_eq_kronecker` and `commute_tensorB_iff_eq_kronMat` remain.
  Replacement: none, unused.
- `red_z`, in `MultiBlock/Running.lean`: the `rfl` value `z = 0` of the
  reduction `red`. Replacement: `rfl`.
- `gauge_compressionGen`, `coordOfOrd_apply`, `firstOrdGen_inr` and
  `lastOrdGen_inr`, in `MultiBlock/SharpnessOneBlockGeneral.lean`: four `rfl`
  projections of the general one-block sharpness example. The used
  `gauge_firstCompressionGen`, `gauge_lastCompressionGen`, `firstOrdGen_inl` and
  `lastOrdGen_inl` remain. Replacement: `rfl`.

Uniqueness of compressions:

- `MPSTensor.self_mem_gaugeClass`, in `Reduction/SplitUniquenessGauge.lean`:
  reflexivity of the gauge class, via `mem_gaugeClass` and the identity gauge.
  Replacement: none, unused.
- `MPSTensor.MultiBlockCompression.relativeGauge_withGauge`, in the same file:
  an `rfl` identification of the relative gauge with `coordChange`. Nothing
  rewrites with it, and no Blueprint entry tags it. Replacement: `rfl`.
- `subquotEquivOfSupEq_mk`, in `Reduction/UniquenessBlocks.lean`: the `rfl`
  value of `subquotEquivOfSupEq` on a class. Replacement: `rfl`.
- `MPSTensor.MultiBlockCompression.matchedCompl_le`, in
  `Reduction/UniquenessCommonBasis.lean`: `le_sup_right` rewritten by the
  retained `sup_matchedCompl`. Replacement: that rewrite.
- `MPSTensor.MultiBlockCompression.matchedIntertwiner_spec`, in the same file:
  it unpacks `Classical.choose_spec` of the retained
  `exists_intertwiner_of_matching`. That theorem carries the intertwining
  content; the downstream statements go through it and the definition
  `matchedIntertwiner`. Replacement: `Classical.choose_spec` of
  `exists_intertwiner_of_matching`.
- `MPSTensor.MultiBlockCompression.conjTriangular_gauge`, in
  `Reduction/UniquenessSameFlag.lean`: the `rfl` gauge of `conjTriangular`.
  Replacement: `rfl`.

The tracked Lean, Blueprint, documentation, script, note and paper corpus
contains each final name only at its own declaration. Direct searches used
each final name with word boundaries, so they also catch receiver-notation
calls. After the edit, the scan reports 23 candidates. The difference is
exactly these eighteen, and no newly unreferenced declaration appears.

Retained candidates, with reasons:

- `hierarchySum_one`: retained by the issue's standing instruction.
- `xXy_isReduction`, `xyX_isReduction`: explicit compression pairs listed among
  the main results and cited to P5 note Theorem 7.7(iv)–(v).
- `plusLeft0`, `plusRight0`, `plusLeft1`, `plusRight1` and the four
  `..._isIntertwiner` theorems of `KramersWannierAction.lean`: the sitewise
  intertwiners of part (a), cited to the data file §2.1. They are the
  counterpart of the part (b) obstruction.
- `trace_cutProductState_mul_of_isSupportedOn_right`: a listed main result,
  stating the right-hand case of arXiv:0705.2024v4, lines 440–446.
- `IsMPU.index_padBond`: index invariance, stated in the module docstring for
  the CPSV17 Definitions IV.3–IV.4 comparison convention.
- `pulling_through_of_simple_witnesses`, `IsMPUSimple.exists_pulling_through`:
  arXiv:1704.01943, Corollary 1.
- `thm_4_1_p_refinement_forward_witness`: a cited step of arXiv:1708.00029,
  Theorem 4.1.
- `latticeConstraintWord_truncation_explicit`,
  `latticeConstraintWord_omission_of_locality`,
  `latticeConstraintWord_omission_explicit`: Lemma 10.1 at named constants.
- `verticalUnion_insert_eq_of_deformedState_eq`: arXiv:1804.04964, lines
  2133–2179, with the 2D-overlap paper-gap note, Step 1.
- `horizontalStaircasePair_row_span`,
  `horizontalStaircasePair_complement_band_lt_window`,
  `horizontalStaircasePair_window_meets_row`: the recorded impossibility proof
  of the 2D-overlap paper-gap note, Step 3. The ledger keeps this file
  deliberately.

No replacement declarations or compatibility aliases are added. TNLean's
unstable-API policy permits removing unused implementation helpers. The exact
production delta is minus 98 lines in thirteen files: 80 declaration,
docstring and proof lines, and 18 separating blank lines. No imports, `open`
lines, `variable` blocks or section headers change.

Validation: direct reference census, the scan before and after, and whitespace
and line-length checks. These are source checks; no local Lean
elaboration or build was run. Hosted validation and repository integration remain
pending, and #9881 stays open.
