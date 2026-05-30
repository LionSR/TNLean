# Excessive-content scout — next cleanup targets (Lean + blueprint)

Date: 2026-05-30. Read-only scout over `TNLean/` (440 `.lean` files) + `blueprint/src/chapter/*.tex`, looking for the same kinds of bloat already removed (zero-tail / N=0 machinery, PGVWC07 §9.13 ladder, duplicate CPSV predicates, distinct-modulus one-copy scaffolding). Method: a token-level consumer analyzer (external refs, in-file refs, blueprint `\lean{}` tag, attribute membership) cross-checked with raw `grep -rn` across `TNLean/ blueprint/ docs/`. The DEAD list is conservative (short-name collisions only inflate counts).

## Top 5 highest-ROI next cleanups

1. **Delete `IsCPSVBasisOfNormalTensors`** (`MPS/CanonicalForm/Definitions.lean:135`) and retarget the blueprint ch08 statement at `IsBNT` (`MPS/BNT/Basic.lean:75`). Field-for-field the same predicate as the live `IsBNT` (differs only `IsNormalTensor` vs `IsNormal` and `Σ`-packaging); **0 external Lean consumers**; the bridge was never built (`Definitions.lean:68` admits it "would require…"). Also clears blueprint remark `rem:cpgsv_canonical_form_source`. Low risk. ⚠ touches ch08/Definitions.lean — coordinate with active CPSV-single-source work.
2. **Batch-remove ~30 verified-dead leaf theorems** (`ext=0,loc=0`, no blueprint tag), starting with the self-contained, low-collision ones:
   - `Channel/Schwarz/MultiplicativeDomainFull.lean:239-375` — `{zero,add,mul,one,conjTranspose}_mem_multiplicativeDomain`, `krausMap_star_of_mem_multiplicativeDomain` (the *-subalgebra closure, never used).
   - `Channel/Schwarz/OperatorMonotone.lean:68-145` — `IsPositiveMap.cor52_item{1,2,3}_…_subunital`, `matrix_rpow_le_rpow`, `matrix_log_le_log` (unconsumed Cor-5.2 cluster).
   - `MPS/SharedInfra/Scaling.lean:67-120` — `isInjective_smul`, `smul_eq_norm_smul_phase`, `transferMap_norm_smul`, `leftCanonical_phase_smul`, `mpv_toTensorFromBlocks_normalize`.
   - `MPS/FundamentalTheorem/SectorBNT/EqualModulus.lean` — `phase_weight_ne_zero` (:90), `spectral_level_norm_le_one` (:100), `coeff_eq_pow_unit_sum` (:117).
   - `MPS/FundamentalTheorem/SectorBNT/DominantMatch.lean:151` `exists_nondecaying_overlap_pair_of_sameMPV`; `…/Api.lean:266,294` `coeff_tendsto_zero_of_all_weights_subnorm`, `thermodynamic_limit_nonvanishing`.
   - Singletons: `Core/BlockingInfrastructure.lean` `mpv_flattenedIteratedBlockTensor` (:640), `blockIndexOfList_wordOfBlock` (:430), `replicatedWeights_pow_mul_phase_ne_zero` (:337); `FundamentalTheorem/FiniteLength.lean:290` `sameMPVFrom_iff_gaugeEquiv_of_injective`; `RFP/Defs.lean:150` `isRFP_iff_kraus`; `MPS/Chain/…` `physRealize_{linear,one,injective}`, `decompositionMap_rightInverse`; `RFP/Decorrelation.lean` `HasCommutingParentHam.p{AX,XB}_of_ground`, `IsDecorrelated.union_obs{A,B}`, `comp_complement_comm_zero_swap`.
   Group by file, `lake build` after each file. Low risk.
3. **Collapse the SectorBNT `*Pos` duplicate-statement ladder.** `SameMPV₂Pos` (positive-length) differs from `SameMPV₂` only at N=0. Every headline FT-sector theorem exists twice — `ft_sector_bnt_equal_{sector_data,global_gauge,mps_gaugeEquiv,literal,witnesses}` and `…Pos`, plus `coeff_identity_via_global_gauge(Pos)`, `bijective_match_of_sameMPV(Pos)` — where the non-`Pos` member is a 2-line wrapper (e.g. `Fundamental.lean:503`). Keep `SameMPV₂Pos`; delete the ~5 intermediate non-`Pos` full restatements and convert `SameMPV₂ → SameMPV₂Pos` once at the single blueprint-facing headline. ~80–120 lines. Medium risk (proof-internal). Direct continuation of the N=0 cleanup.
4. **Prune dead leaves in `Wielandt/RankOne/` (17) and `Wielandt/RectangularSpan/UniversalityAux/` (11).** The modules are imported, but these are abandoned intermediate steps (e.g. `wordSpan_generates_full_algebra`, `exists_rankOne_in_cumulativeSpan_blockTensor_of_wordEigenvectors`, `wielandt_sharp_parametric_span`, `rectSpan_nilpIndex_range_permanent`). None blueprint-tagged. Largest concrete line savings; build-verify (supporting library).
5. **Blueprint prose compression.** `ch10_bnt.tex`: the comment `% Scope restriction documented in …ft_one_copy_scope_restriction.tex` appears **8×** (lines 1004, 1091, 1201, 1457, 1496, 1529, 1597, 1639) and the "at least one copy weight of modulus 1" prose ≥6×; factor into one named macro/remark + `\cref`. `ch08_canonical.tex`: merge the stacked source-fidelity disclaimers (`rem:cpgsv_canonical_form_source`, `rem:canonical_construction_gaps`, `rem:arbitrary_input_reduction_gap`, "Scope relative to PGVWC07 §III") into one chapter-level scope remark. Prose-only, zero formal risk.

## Other findings

- **PGVWC07 empty-family Lean body** (`NormalReduction/{WeightNormalization,TPGauge}.lean`): the `exists_pgvwc07_*` stack has 0 consumers outside `NormalReduction/`; only `…_allow_empty` is blueprint-tagged (the rest are in the ch08z recordings appendix). Mirror the blueprint quarantine by demoting the intermediates to `private`. Low risk, large surface.
- **`CommonBlockedCyclicSectorFamily.lean` (668 lines)**: a chain of single-use cast/word/reindex transport lemmas (`groupedBlockCastAgrees_iff_iteratedBlockIndex_cast` → … → `blockTensor_eq_commonReindexedBlock_of_word_eq`, each 1 use) — inline into the one consumer. Low-medium risk.
- **Blueprint-only Lean leaf**: `exists_commonBlockedCyclicSectorFamily_of_hasPrimitiveIrreducibleCyclicSectors` (`SectorComparison/CommonBlockedCyclicSectorConstruction.lean:200`) has 0 Lean consumers and exists only for a `\lean` tag; retag the blueprint at the consumed `…_of_commonMultiple` or accept as an exposition leaf.

## Look-excessive but LOAD-BEARING — do NOT remove

- `SameMPV₂Pos` itself (total-dim equality is unknown until late in the FT proof — keep the def, only collapse duplicate statements).
- Genuine boundary cases: `Spectral/TransferOperatorGap{,Rect}.lean` D=0 / `Subsingleton (Matrix (Fin 0) …)`; one-line `Subsingleton.elim` in `RFP/Convergence.lean:85`, `Channel/Semigroup/LindbladForm/Uniqueness.lean:144,188`, `FundamentalTheorem/Basic.lean:48`.
- `MPS/FundamentalTheorem/SectorBNT/Examples.lean` worked-example lemmas (`singletonDecomp/signFlipDecomp/phaseDecomp/halvedDecomp_weight_unit_per_block`) — pedagogical (file is "Executable examples for `IsBNTCanonicalForm`").
- `Archive/*Counterexample.lean` — intentional records.
- `@[mps_block_words]` / `@[simp]` members (e.g. `eq_directToIteratedBlockIndex_iff_iteratedBlockIndex_eq`) — consumed via simp sets.
- `@[deprecated]` aliases `spectral_gap_of_injective`, `uniform_spectral_gap_of_finite_lt_one` — remove only on the planned deprecation cycle.
- Distinct live layers (NOT duplicates): `IsBNT` vs `IsBNTCanonicalForm` (block-family vs sector-decomposition); `SectorBNTCopyWeightMatching` vs `ProportionalMatch`.

## Caveats
- Each removal should be followed by a `lake build` of the touching file — a lemma could be picked up by an unforeseen attribute-driven tactic.
- A few "0-consumer" decls may be intended public API (e.g. `MPS/Chain/Defs.lean` abbrevs `mpsChainCoeff`, `SameChainState`, `IsInjectiveChain`, `ChainGaugeEquiv`) — confirm before deleting.
