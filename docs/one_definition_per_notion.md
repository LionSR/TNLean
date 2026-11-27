# One definition per notion: the remaining families

This document prepares the remaining clean-ups of plan item F4 of
`docs/many_body_circuit_architecture.md` and the rows of its table "Modules named for a bridge"
that are not yet done. It applies the rule "One definition per notion" of the section "No dual
systems":

- a second predicate that is an abbreviation of another, or equivalent to it with no hypothesis,
  is deleted, and the equivalence becomes a characterization theorem;
- one that is equivalent only under a hypothesis becomes a clause of the source's proposition,
  stated as an equivalence under that hypothesis;
- one that is not equivalent is a different notion and keeps a name that says how it differs.

The method is the one of the primitivity change (#10724, #10727, #10743, recorded in
`docs/audits/2026-11-16_primitivity_one_definition.md`): an inventory of the names with their
consumers; one survivor per notion; abbreviations and hypothesis-free equivalents deleted, with
their callers moved to the survivor; translation lemmas deleted and theorems with content
restated on the survivor; a source proposition with several equivalent clauses stated once as a
`List.TFAE` with the source's hypotheses; bridge modules merged or renamed for what they prove;
the glossary section shortened to the surviving notions. Faithfulness (`CLAUDE.md`) bounds every
step: no theorem gains a hypothesis its source does not state, and a survivor is the source's
notion with its intended nondegenerate reading in the definition.

## Basis of the numbers

- Reference commit: `e8f8dd3202` (branch `batch/many-body-2`). Counts were taken on an extraction
  of that commit (`git archive`), never on a working tree. A count of "modules" is the number of
  `.lean` files under `TNLean/` (without `Archive/`) containing the name as a whole word; each
  section says how its other numbers were measured.
- Lean statements were elaborated with `lake env lean` against the complete older build in
  `worktrees/hot-main` (`414a18fb88`, thirty commits behind the reference). Each section says
  which statements elaborated, which carry `sorry`, and which could not be checked because the
  older build lacks an ingredient.
- Each family has a script `rewrite.py` for its mechanical part, with a dry-run mode (the
  default) that prints the files and occurrences per rule, and an apply mode
  (`--apply`) that takes `--root <worktree>`. The scripts, their dry-run outputs on the
  reference commit, and the Lean files with the new statements are in

  `/private/tmp/claude-501/-Users-siruilu-Local-agentFormalization-TNLean/226a396d-1c4a-4cda-ab3e-95f98581e8ff/scratchpad/notions/<family>/`

  with `<family>` one of `fam1_bnt_canonical`, `fam2_commuting_form`, `fam3_mutual_info`,
  `fam4_unique_ground_state`, `fam5_frustration_free`, `fam6_injective_normal`, `fam7_sweep`
  (files `rewrite.py`, `dryrun.txt`, `New.lean`, and the elaboration output). That directory
  is temporary; the scripts should be copied into the worktree of the change that applies them
  and deleted with it.

## A precondition: the QICLean pin

The reference commit pins QICLean `d65bece64d` (`lakefile.toml`, `lake-manifest.json`). That
revision has `ManyBody.Interaction.IsFrustrationFree` but not `Interaction.zeroSpace`,
`mem_zeroSpace_iff` or `zeroSpace_eq_groundSpace`, which the reference commit already uses
(`MPS/ParentHamiltonian/Defs.lean:381`, `PEPS/AreaLaw/Operators/FrustrationFree/Model.lean`); 47 of its
`import QICLean.…` lines name modules absent at the pin and present at QICLean `origin/main`
`551c297e0`. A pin move to `551c297e0` or later precedes any build of the reference commit and
therefore every family below (section 5).

## Summary

| Family | Surviving definition(s) | Removed | Consumers touched | Scriptable |
|---|---|---|---|---|
| 1. Bases of normal tensors, canonical forms | basis: `IsCPSVBasisOfNormalTensors`; presentation: `IsBNTSectorPresentation` on `SectorDecomposition`; canonical form: `CPSVCanonicalFormData`/`IsCPSVCanonicalForm` (both renamed without the source tag after the deletions, decision 1.D1); canonical form II; `IsBNTCanonicalForm` restated as the left-canonical gauge of a presentation | 15 (`IsBNT`, `IsNormalCanonicalForm`, `IsNormalCanonicalFormBNT`, the PiAlgebra `IsCanonicalForm`, `PreparedBNTBlocks` and its `IsWeightNormalized`, `MPSTensor.CanonicalForm`, `HasOrderedNonzeroWeights`, five one-field wrappers, and the two weight fields of `IsBNTCanonicalForm`); `BNT/Bridge` deleted, `CanonicalFormBridge` merged | 166 modules / 1116 occurrences (union of all names touched) | wrappers, the `IsBNT` type rewrite, projections and all renames; restatements and constructors by hand |
| 2. Commuting form of an MPDO | `CommutingForm M extends CommutingBond d` (renames of `EtaLocalStructureData` and `TranslationInvariantBondData`) | 2 (`CommutingFormData`, `HasCommutingForm`) and 17 lemmas; `CommutingFormBridge` deleted | 27 modules, all `MPS/MPDO` | 25 of 27 modules |
| 3. Mutual information on a chain | QICLean's bipartite mutual information; `mutualInfoChain` stays as a named special case defined by it | 0 predicates; the bridge lemma; `MutualInfoBridge` dissolved | 19 modules use `mutualInfoChain` (all `MPS/MPDO`); 16 edited | tactic-list and import rewrites |
| 4. Unique ground states | `ManyBody.groundSpace H E₀ = ℂ ∙ Ω ∧ Ω ≠ 0` | 1 (`HasUniqueGroundState`) and its characterization lemma | step 1: 7 modules; step 2: 10 modules | step 1 entirely |
| 5. Frustration-freeness | QICLean `Interaction.IsFrustrationFree` (of an interaction) and `Interaction.zeroSpace` (frustration-free ground vectors) | 2 (`MPSTensor.IsFrustrationFree`, `IsNNCPHGroundState`) and their projections | at most 24 modules (sum of the per-row counts) | renames only (2 files); the rest by hand |
| 6. Injectivity and normality | `Kraus.IsInjective`, `Kraus.IsNBlkInjective`, `Kraus.IsNormal`, `IsNormalTensor` (a different notion: normal with spectral radius one), the chain, PEPS-vertex, PEPS-region and `G`-injectivity predicates | 7 (`MPOTensor.IsInjective`, `Kraus.HasEventuallyFullWordSpan`, `SingletonRegionTensorInjective` and four comparison or descent structures) and the pass-through `wordSpan_eq_top_iff_isNBlkInjective` | 54 files scripted, about 12 by hand, 24 occurrences in QICLean | the four rules R1–R4 |
| 7. Further families | idempotent transfer map `IsTransferIdempotent` (S1); `IsDeterministicallyGenerated` (S2); `IsTorusFlat` (S3); the `Lattice` bounded-change predicates (S4); the native `HasPEPSApproximation` (S5) | 9 | S1 48, S5 17, S3 15, S4 14, S2 3 modules | theorem-name renames of S1 |

Total consumers touched: about 400 module edits summed over the families (overlaps between
families, mostly in `MPS/MPDO` and `MPS/ParentHamiltonian`, not subtracted). Families 1, 2, 6 and
7 (S1) carry most of the scripted volume.

## A faithfulness finding

The blueprint entries `thm:cpgsv_multiblock_ft_source` and `thm:cpgsv_equal_case_source` (ch11),
marked `\leanok`, point to `fundamentalTheorem_proportional_canonicalForm` and
`fundamentalTheorem_equal_canonicalForm` (`SectorBNT/FundamentalCoord.lean:637, 612`), whose
hypothesis `IsBNTCanonicalForm` requires left-canonical basis tensors. CPSV16 Theorem 2.10 and
Corollary 2.11 have no gauge condition. Under the faithfulness rule these are stricter-hypothesis
variants; the source statements (T9, T10 of family 1, stated with `sorry`) are on presentations
with no gauge choice. Until they are proved, the two entries need the scope restriction stated and
a paper-gap note (decision 1.D4).

## Where two families meet

- `IsNormalTensor ↔ Kraus.IsNormal A ∧ spectralRadius (E_A) = 1` is proved in both
  `fam1_bnt_canonical/New.lean` (T1) and `fam6_injective_normal/New.lean`. It is added once, in
  whichever change lands first (family 1 step S0 or family 6 step 3); the glossary line saying
  that no equivalence relates the two names is removed with it.
- `HasInjectiveBlocks` is deleted by family 1 (step S1, one of the one-field wrappers); family 6
  lists it only as a cross-reference.
- Families 4 and 5 both restate statements about the parent-Hamiltonian ground space of
  `MPS/ParentHamiltonian` (`chainGroundSpace`, `KernelChainGroundSpace.lean`): family 5 deletes
  `IsFrustrationFree` and adds zero-space membership; family 4 adds the transport theorem
  `groundSpace_toMatrix'_parentHamiltonian` and restates the unique-ground-state theorems on it.
  `parentHamiltonianGroundSpaceES` (17 modules) is a hypothesis-free copy of `ManyBody.groundSpace`
  and belongs to #10948 (the `…ES` representation).
- Family 5 deletes `IsNNCPHGroundState` in favour of `IsNNCPH`; `IsNNCPH` itself (the
  nearest-neighbour commuting parent Hamiltonian of an MPS) was not examined by family 2, whose
  subject is the commuting form of an MPDO, and stays as it is.
- Family 2 and family 1 touch the same four `MPS/MPDO` files
  (`BNTSectorCommutingFamily`, `BNTPhysicalSectorGSNNCH`, `OrthogonalSectorAreaLaw`,
  `GSNNCHOrthogonalSectors`) without a semantic dependency: run one script after the other
  family's change has landed.
- Family 1 changes `IsVerticalCF` and the horizontal MPDO canonical-form predicates (they contain
  `IsBNT` and `IsBNTCanonicalForm`); `HasHorizontalCFMPVRepresentation` becomes equivalent with no
  hypothesis to the existence of a presentation and is left to the MPDO change.

## Order of application

1. **QICLean.** Pin move to `551c297e0` or later (needed by the reference commit itself). In the
   same QICLean change or the next: delete `Kraus.HasEventuallyFullWordSpan` and add
   `Kraus.isNBlkInjective_of_le`, `Kraus.isNBlkInjective_of_le_of_unital` (family 6, step Q1);
   optionally `zeroVector_tfae` (family 5, decision D6). Any pin move recompiles nearly the whole
   library; fold these into one move.
2. **Independent and narrow** (each its own change, any order, rebuild limited to the edited
   modules and their few importers): family 6 rules R1, R2, R4 (R3 after step 1) and its PEPS
   deletions; family 7 S2, S4; family 5 FF12, FF12′ and FF10.
3. **Families 4 and 5 together** (one change): `MPS/Tensor/GroundSpace/ParentHamiltonian.lean` has 1195
   transitive importers and `UniqueGroundState.lean` 866, so each forces a wide rebuild; doing
   FF1, FF2 and both steps of family 4 in one change pays it once, preferably together with the
   #10948 parent-interaction work.
4. **Family 1**, steps S0–S3 as one change and S4–S5, then S6–S7 as one change. `BNT/Basic`
   (1,244 importers), `CanonicalFormSepAux` (1,139), `Core/MultiBlock` (1,640) and `Definitions`
   (1,084) make every step a wide rebuild; the grouping keeps it to three.
5. **Family 2** with the F2 split of `MPS/Operator/Simple/CommutingForm.lean` (348 importers), and
   **family 3** (`AreaLaw.lean`, 507 importers) — both are in `MPS/MPDO` and can share a rebuild;
   both after family 1's S2–S4 have landed, because of textual overlaps in `MPS/MPDO`.
6. **Family 7 S1** (`MPS/Transfer/RenormalizationFixedPoint/Defs.lean`, most of `MPS/RFP` and `MPS/MPDO`) after family 3.
7. **Family 7 S3 and S5** with F1 (the split of `PEPS`) and #10944 E3 (configuration spaces),
   so that the PEPS modules are rewritten once.
8. Deferred, each with its own issue: family 6 D3 (union closure as a hypothesis, 47 PEPS
   modules) and D5 (nonzero bonds in the PEPS tensor type, with T.1); family 2 decision 3 (one
   structure for the sector families); family 3 D4–D6 (regional states, strong subadditivity of
   density matrices in QICLean); family 1 T9 and T10 (the source-faithful Fundamental Theorem on
   presentations).

## Status after round 3 (2026-11-27)

- **Family 1.** S0–S3 landed in rounds 1–2. S4 and S7: `IsBNTCanonicalForm` is now
  `IsLeftCanonicalBNTPresentation`, a presentation of `P.toTensor` with left-canonical basis
  tensors (`extends IsBNTSectorPresentation`), without the two line-246 weight fields; the
  module `MPS/Tensor/DirectSum/SectorBNT.lean` became
  `MPS/CanonicalForm/BNTPresentation/LeftCanonical.lean`. S5: T9, T10 and the equal case are
  proved on presentations (`MPS/FundamentalTheorem/Sectors/Presentation.lean`), and the ch11
  source entries point to them (decision 1.D4(b)). S6 (the D1 renames) is deferred: the
  tensor-types lane restates `IsCPSVCanonicalForm` in the same round.
- **Family 5.** FF9: `regionalTruncationInteraction` with
  `zeroSpace_regionalTruncationInteraction`. D3: the chain layer (`chainOperator`,
  `chainReplacement` and their lemmas) is deleted in favour of the truncation on a
  `BondInteraction`; the three-region lemmas keep the bare family and `chainTerm`.
- **Family 6.** The `pow_four` copies are deleted and two blocked-spelling theorems restated
  with `Kraus.IsNBlkInjective`. D6: `isNBlkInjective_of_le_of_canonical` stays, since every
  caller starts from a length that may be zero. D3: the union-closure hypothesis is stripped
  from the source-facing PEPS statements whose tensors carry positive bonds; only
  `regionInjectivityUnionClosure_of_overlap` remains as the concrete provider. D5 stays with
  the tensor-types plan T.1. In QICLean, `Kraus.isInjective_iff_isNBlkInjective_one` and
  `Kraus.IsInjective.eq_zero_of_forall_trace_mul_eq_zero` replace the TNLean copies.

## Open decisions

Each section ends with its decisions; the ones that change a public name or a blueprint status are
collected here with the recommendation.

| Decision | Recommendation |
|---|---|
| 1.D1 drop the source tag from the surviving canonical-form names (`CanonicalFormData`, `IsCanonicalForm`, `IsBasisOfNormalTensors`) | yes, after step S3 frees `IsCanonicalForm` |
| 1.D2 argument shape of the basis predicate | explicit dimension family, as in `SectorDecomposition` |
| 1.D3 name of the restated left-canonical presentation | `IsLeftCanonicalBNTPresentation` |
| 1.D4 blueprint status of the ch11 Fundamental Theorem entries, whose Lean statements require left-canonical basis tensors that CPSV16 Theorem 2.10 does not | keep them as scope-restricted entries and add the source entries (T9, T10) |
| 2.1 names of the commuting-form structures | `CommutingBond`, `CommutingForm` |
| 2.3 one structure for the proportional and exact sector families | yes, as a second step with proofs |
| 3.D1 form of the surviving mutual information | QICLean's bipartite mutual information on the cut, `mutualInfoChain` defined by it |
| 3.D4 mixed block states `reducedBlockState` | keep for now with the theorem identifying it with QICLean's `regionMatrix`; redefine with the regional-state work |
| 4.1 names of the restated unique-ground-state theorems | keep the source names (`parentHamiltonian_unique_gs`, …) with the new conclusion |
| 4.2 conclusion `groundSpace … = ℂ ∙ ψ ∧ ψ ≠ 0` or the line equation alone | the conjunction |
| 5.D1 `L ≤ N` in `bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree` | add it; the source's use has `N > L` |
| 5.D3 two formalizations of ALVV `def:FF-tH` | keep the interaction form, retire the chain layer |
| 6.D1 one spelling for fixed-length injectivity | keep `Kraus.IsNBlkInjective` (the source's `S_N(A) = M_D`), delete only the pass-through |
| 6.D2 the name `IsNormalTensor`, which does not say it adds `ρ(E_A) = 1` | keep the source's name, state the difference by the characterization theorem |
| 6.D5 nonzero bonds in the PEPS tensor type | in plan T.1 |
| 7.S1 survivor of the idempotent-transfer family | `IsTransferIdempotent`, defined as `IsIdempotentElem (Kraus.transferMap A)`; the source's blocking-isometry definition as the characterization theorem |
| 7.S3 survivor of torus flatness | `IsTorusFlat` |

## 1. Bases of normal tensors and canonical forms

Reference: HEAD = e8f8dd3202. Sources: Cirac, Pérez-García, Schuch, Verstraete,
arXiv:1606.00608 (CPSV16, `Papers/1606.00608/MPDO-22-12-17-2.tex`) and
arXiv:2011.12127 (CPSV21, `Papers/2011.12127/TN-Review-main.tex`); Pérez-García,
Verstraete, Wolf, Cirac, arXiv:quant-ph/0608197 (PGVWC07); Cirac, Pérez-García,
Schuch, Verstraete, arXiv:1703.09188 (CPSV17).

### The notions and their surviving definitions

The sources define four objects: a normal tensor; a tensor in canonical form,
`A^i = ⊕_k μ_k A_k^i` with normal blocks (CPSV16 eq. `II_CF1`, lines 237–244;
CPSV21 Definition 4.1); a basis of normal tensors of a tensor (CPSV16 lines 271–274;
CPSV21 Definition 4.2); and the two-layer presentation of a tensor by such a basis,
`A^i = ⊕_j ⊕_q μ_{j,q} X_{j,q} A_j^i X_{j,q}^{-1}`, with coefficient
`∑_q μ_{j,q}^N` (CPSV16 eq. `II_ABasicTensors`, `decBSV`, lines 281–301). CPSV16
Appendix A adds a gauge-fixed canonical form II (lines 1054–1077). A separate
notion, a canonical form with irreducible (possibly periodic) blocks, is used by
PGVWC07 Theorem 4 and CPSV17.

| Notion | Surviving definition (HEAD name) |
|---|---|
| normal tensor | `MPTensor.IsNormalTensor` (normality family; unchanged) |
| basis of normal tensors of `A` | `MPSTensor.IsCPSVBasisOfNormalTensors` (rename: D1; argument shape: D2) |
| two-layer presentation of `A` by a basis of normal tensors | `MPSTensor.IsBNTSectorPresentation A P` on the data `MPSTensor.SectorDecomposition` |
| canonical form | `MPTensor.CPSVCanonicalFormData A` / `IsCPSVCanonicalForm A`, on the shared shape `RetainedBlockReconstructionData A` (rename: D1) |
| canonical form II | `MPSTensor.CPSVCanonicalFormIIData A` / `IsCPSVCanonicalFormII A` |
| canonical form with irreducible blocks | `MPTensor.MPUCanonicalFormData A` (CPSV17) and its gauge-fixed form `MPSTensor.PGVWC07CanonicalFormData A` (names: D6) |
| line-246 weight convention for a canonical form | `MPTensor.CPSVCanonicalFormData.IsWeightNormalized` |
| left-canonical gauge of a presentation (a proof device) | `MPSTensor.IsBNTCanonicalForm P`, restated as a presentation of `P.toTensor` with left-canonical basis (S4; name: D3) |

### Inventory

Counts: modules of `TNLean/` (Archive excluded) in which the name occurs as a
whole component of an identifier, import lines excluded; occurrences likewise.
Measured by `count.py` (tokenizer; in this directory) on the `git archive` of
HEAD. Breakdown `dir modules/occurrences`; `MPS/x` is the second level. Prose
mentions in docstrings count.

| Name (file:line) | Definition | Source anchor | Modules / occ. at HEAD |
|---|---|---|---|
| `IsNormalTensor` (CanonicalForm/Definitions.lean:105) | irreducible ∧ ρ(E_A)=1 ∧ `IsPrimitive (transferMap A)` | CPSV16 233–235 | 100/301 [MPDO 36/84, ParentHamiltonian 15/28, CanonicalForm 13/78, MPU 9/25, Preparation 8/16, RFP 6/23, Symmetry 4/9, FundamentalTheorem 3/6, Spectral 3/11, BNT 1/3, Core 1/4, Overlap 1/14] |
| `IsCPSVBasisOfNormalTensors A blocks` (Definitions.lean:373) | `blocks : Fin g → Σ D, MPSTensor d D`; `∀ j, IsNormalTensor`; spans at every `N>0`; eventually linearly independent | CPSV16 271–274 | 40/103 [MPDO 21/46, ParentHamiltonian 8/16, CanonicalForm 6/26, RFP 4/7, BNT 1/8] |
| `IsBNT A g dim B` (BNT/Basic.lean:77) | same three clauses with `Kraus.IsNormal` blocks, explicit `dim` | docstring cites CPSV21 Def. 4.2 | 12/32 [MPDO 5/6, BNT 3/21, RFP 2/3, Symmetry 2/2 (prose)] |
| `SectorDecomposition d` (SharedInfra/SectorDecomposition.lean:143) | data: basis family, copies `>0`, weights `≠0` | CPSV16 281–301 | 107/513 [MPDO 36/145, FundamentalTheorem 23/142, RFP 14/21, Periodic 12/42, Preparation 12/78, CanonicalForm 5/16, SharedInfra 3/67, BNT 2/2] |
| `HasBNTSectorData P` (same file:759) | `∃ N₀, ∀ N > N₀, LI (mpvState (P.basis j) N)` | CPSV21 1846–1850 | 14/23 |
| `IsBNTSectorPresentation A P` (CanonicalForm/BNTRefinement.lean:42) | `0 < basisCount`, `SameMPV₂Pos A P.toTensor`, basis normal, `HasBNTSectorData P` | CPSV16 217–246, 265–301, 1135–1148 | 3/18 [MPDO 2/4, CanonicalForm 1/14] |
| `IsBNTCanonicalForm P` (FundamentalTheorem/SectorBNT/Basic.lean:107) | 8 fields: `basis_dim_pos`, `basis_irreducible`, `basis_left_canonical`, `basis_normalized_self_overlap`, `bnt_data`, `basis_distinct`, `weight_norm_le_one`, `weight_unit_exists` | CPSV16 271–301; CPSV21 1846–1884 | 57/245 [FundamentalTheorem 19/110, MPDO 17/50, RFP 11/42, Preparation 5/26, BNT 2/8, CanonicalForm 1/1, Periodic 1/7, PiAlgebra 1/1] |
| `PreparedBNTBlocks d` (SectorBNT/Supplier.lean:366), `.IsWeightNormalized` (:389) | weighted family of positive-dimensional, left-canonical, primitive, irreducible blocks, weights `≠0` | none | 3/11 [FundamentalTheorem 3/11] |
| `RetainedBlockReconstructionData A` (Definitions.lean:190) | `A^i = C† (⊕ μ_k A_k^i) C`, `CC†=1`, `μ_k≠0`, `D_k>0` | CPSV16 214–245; CPSV17 259–265 | 4/10 |
| `CPSVCanonicalFormData A`, `IsCPSVCanonicalForm A` (Definitions.lean:230, 241) | the above with normal blocks and `∑ D_k ≤ D` | CPSV16 eq. `II_CF1` | 42/181 and 41/120 [MPDO 23/68, ParentHamiltonian 9/25, CanonicalForm 5/20, RFP 4/7 for the latter] |
| `CPSVCanonicalFormData.IsWeightNormalized` (Definitions.lean:296) | `‖μ_k‖ ≤ 1`, `A ≠ 0 → ∃ k, ‖μ_k‖ = 1` | CPSV16 line 246 | 7/13 (name shared with `PreparedBNTBlocks.IsWeightNormalized`) |
| `CPSVCanonicalFormIIData`, `IsCPSVCanonicalFormII` (Definitions.lean:325, 338) | CF + left-canonical blocks + diagonal positive fixed point | CPSV16 1054–1077 | 18/92 and 3/12 |
| `MPSTensor.CanonicalForm d` (Core/MultiBlock.lean:33) | data: weights and one-site injective blocks, no reconstruction | blueprint `def:canonical_form` | 2 modules (definition; FundamentalTheorem/Multi.lean:155, 158); the token count 15/30 is prose naming the directory |
| `IsCanonicalForm μ A` (PiAlgebra/CanonicalFormSepAux.lean:172) | injective, left-canonical, antitone `‖μ‖`, `μ≠0`, `dim>0`, self-overlap → 1 | CPSV16 `II_CF1` context | 3/8 [CanonicalForm 1/1, RFP 1/1, PiAlgebra 1/6] |
| `IsNormalCanonicalForm μ A` (same file:243) | irreducible, left-canonical, primitive, antitone, `μ≠0`, `dim>0` | CPSV16 233–246 context | 5/21 [CanonicalForm 2/5, BNT 1/5, Periodic 1/2, PiAlgebra 1/9] |
| `IsNormalCanonicalFormBNT μ A` (BNT/Construction.lean:80) | the above + `BlocksNotGaugePhaseEquiv A` | CPSV16 264–301 | 3/24 [BNT 1/12, CanonicalForm 1/11, PiAlgebra 1/1] |
| one-field wrappers (CanonicalFormSepAux.lean:57, 63, 85, 105, 138) `HasInjectiveBlocks`, `HasIrreducibleBlocks`, `HasPrimitiveBlocks`, `IsLeftCanonicalBlockFamily`, `HasNormalizedSelfOverlap` | each is `∀ k, P (A k)` for one property `P` | none | 2/4, 22/96, 3/9, 19/81, 16/72 (ParentHamiltonian 12/59, 9/43, 9/43 for the three largest) |
| `HasOrderedNonzeroWeights μ` (:131) | antitone `‖μ‖` ∧ `μ≠0` | none | 3/5 |
| `BlocksNotGaugePhaseEquiv A` (BNT/Separation.lean:25, abbrev) | distinct blocks not gauge-phase equivalent | CPSV16 Prop. 2.7 (ii) | 66/182 |
| `IsMPUCanonicalBlock`, `MPUCanonicalFormData`, `IsMPUCanonicalForm` (MPU/MPUCanonicalForm.lean:39, 53, 66) | reconstruction with irreducible blocks of transfer spectral radius one (periodic allowed), `∑ D_k = D` | CPSV17 259–267 | 3/7, 3/14, 16/72 (all MPU) |
| `PGVWC07CanonicalFormData`, `IsPGVWC07CanonicalForm` (CanonicalForm/PGVWC07CanonicalForm.lean:66, 108) | irreducible blocks in unital gauge with diagonal dual fixed point, real weights in `(0,1]`, bond bijection | PGVWC07 Thm 4, lines 742–763 | 7/47, 5/24 |
| MPDO: `IsHorizontalCF` (MPDO/HorizontalBNT.lean:142), `IsSimpleCanonicalForm` (SimpleTensor.lean:188), `HasHorizontalCFMPVRepresentation` (HorizontalCFMPVRepresentation.lean:63), `HorizontalCFData` (PerCopyHorizontalCF.lean:35), `IsVerticalCF` (VerticalCF.lean:592) | statements about an `MPOTensor`, built from `IsBNTCanonicalForm` (first three) and `IsBNT` (`IsVerticalCF`) | CPSV16 §4, App. C | 24/75, 6/23, 2/3, 4/15, 9/12 (all MPDO) |
| `IsIsometryCanonicalForm` (RFP/StructuralFull.lean:506), `IsMPUCanonicalFormII` (MPU/CanonicalForm.lean:337) | renormalization-fixed-point isometry form; canonical form II of a matrix product unitary | CPSV16 Lemma charact-NT-pure-RFP; CPSV17 | 5/25; 95/530 |

#### Proved relations at HEAD

Normal tensors (all in CanonicalForm/NormalTensorGauge.lean unless noted):
`IsNormalTensor → Kraus.IsNormal` (`IsNormalTensor.isNormal`, :313);
`Kraus.IsNormal ∧ left-canonical → IsNormalTensor`
(`isNormalTensor_of_isNormal_leftCanonical`, :329, `[NeZero D]`);
irreducible ∧ primitive ∧ left-canonical → normal
(`isNormalTensor_of_isIrreducibleFamily_leftCanonical`, :355);
normal → self-overlap → 1 (`IsNormalTensor.selfOverlap_tendsto_one`, :388);
irreducible ∧ left-canonical ∧ self-overlap → 1 → primitive ∧ `Kraus.IsNormal`
(`isPrimitive_and_isNormal_of_irreducible_leftCanonical_selfOverlap_tendsto_one`,
Periodic/NormalizedSelfOverlap.lean:59); irreducible ∧ ρ=1 → trace-preserving gauge
(`exists_tpGauge_of_irreducible_spectralRadius_one`, :205).

Bases: `IsCPSVBasisOfNormalTensors → IsBNT` (`IsCPSVBasisOfNormalTensors.isBNT`,
BNT/Bridge.lean:86); converse absent. A basis is gauge-phase separated
(`IsCPSVBasisOfNormalTensors.blocks_not_gaugePhaseEquiv`, :524); separated normal
blocks are eventually independent
(`exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`,
:555); CPSV16 Prop. 2.7 (`isCPSVBasisOfNormalTensors_iff_canonicalForm_covered_and_minimal`,
CanonicalForm/BNTCharacterization.lean:214; specialization to CF data :356); every
CF has a basis (`CPSVCanonicalFormData.exists_isCPSVBasisOfNormalTensors`,
BNTExistence.lean:26).

Presentations: presentation → basis (`IsBNTSectorPresentation.isCPSVBasisOfNormalTensors`,
BNTRefinement.lean:72); uniqueness of the basis up to bijection and unit gauge phase
(`IsBNTSectorPresentation.equiv_of_sameMPV₂Pos`, :151); CF data with `0 < r` →
presentation (`CPSVCanonicalFormData.BNTRefinement.isBNTSectorPresentation`, :761).

Sector canonical form: `IsBNTCanonicalForm → IsBNT` (`IsBNTCanonicalForm.isBNT`,
Bridge.lean:125); → blockwise `Kraus.IsNormal` (`IsBNTCanonicalForm.basis_isNormal`,
NormalizedSelfOverlap.lean:185); CF data ∧ line-246 ∧ `A ≠ 0` → sector form with
exact coisometric reconstruction (`CPSVCanonicalFormData.exists_isBNTCanonicalForm_exact`,
`exists_isBNTCanonicalForm`, SectorBNT/CanonicalFormBridge.lean:145, 276); prepared
blocks → sector form (`PreparedBNTBlocks.exists_isBNTCanonicalForm_exact`,
PreparedReconstruction.lean:257; Supplier.lean:408, 512). No implication from
`IsBNTCanonicalForm` to `IsBNTSectorPresentation` is stated (T5 below supplies it).

Block families: `IsCanonicalForm` built from primitive injective blocks
(`IsCanonicalForm.of_peripheral_primitive`, CanonicalFormSepAux.lean:208);
`IsNormalCanonicalForm.ofSeparatedData` (:275); `IsNormalCanonicalFormBNT → IsBNT`
given blockwise `Kraus.IsNormal` (`IsNormalCanonicalFormBNT.isBNT`,
BNT/Construction.lean:281; the extra hypothesis is derivable);
`isBNT_of_separated_bnt_data` (:212).

Gauge-fixed forms: CF → CFII up to gauge
(`CPSVCanonicalFormData.exists_gaugeEquiv_canonicalFormIIData`,
CPSVCanonicalFormII.lean:69); `isPGVWC07CanonicalForm_toTensorFromBlocks`
(PGVWC07CanonicalForm.lean:323); MPU canonical form → normality of the normalized
flattening (`IsMPU.isNormalTensor_normalizedFlattening_of_mpuCanonicalForm`,
MPUCanonicalForm.lean:235). No theorem relates `PGVWC07CanonicalFormData` and
`MPUCanonicalFormData`.

### Verdicts

| Predicate | Verdict |
|---|---|
| `IsCPSVBasisOfNormalTensors` | survivor (the source's basis of normal tensors) |
| `IsBNT` | deleted. Equivalent to the survivor exactly under the hypothesis that every basis tensor has transfer spectral radius one: clause theorem T3, from T1 `IsNormalTensor A ↔ Kraus.IsNormal A ∧ ρ(E_A) = 1`. Both sources' basis consists of normal tensors in the normalized sense (CPSV21 Def. 4.1 asks for a primitive channel), so restating its consumers on the survivor adds no hypothesis absent from the source |
| `IsBNTSectorPresentation` | survivor (the source's two-layer presentation); characterization T4: nonempty basis, same vectors as `P.toTensor`, and the basis of `P` a basis of normal tensors of `P.toTensor` |
| `IsBNTCanonicalForm` | different notion, restated to unfold to the survivor (T5): a presentation of `P.toTensor` whose basis tensors are left-canonical, plus the line-246 weight fields. Four of its eight fields are consequences (`basis_dim_pos`, `basis_irreducible`, `basis_normalized_self_overlap` via T2; `basis_distinct` via `blocks_not_gaugePhaseEquiv`). The two weight fields are consumed by no proof at HEAD (only rebuilt after blocking, SectorBNT/Blocking.lean:346); they are dropped. Left-canonicality is a gauge choice that no source statement contains; it stays as the one extra field, used by the overlap estimates of the Fundamental Theorem proof. Name: D3 |
| `HasBNTSectorData` | survivor as the independence clause (it is the clause, not a second notion) |
| `CPSVCanonicalFormData` / `IsCPSVCanonicalForm` | survivor (rename D1) |
| `RetainedBlockReconstructionData` | survivor as the shared reconstruction shape of the two canonical-form notions |
| `CPSVCanonicalFormIIData` / `IsCPSVCanonicalFormII` | survivor; different notion (gauge-fixed); the name says so |
| `MPSTensor.CanonicalForm` | deleted: data without reconstruction, two modules, its two theorems are `rfl` and a forwarder to `fundamentalTheorem_multiBlock_global`; callers use `toTensorFromBlocks` |
| `IsNormalCanonicalForm` | deleted, T6: normal left-canonical blocks, nonzero weights, and an antitone indexing of `‖μ‖`. The ordering is consumed by no proof (`mu_antitone` occurs only in the definition and its one producer, NormalReduction/Main.lean:304); statements take `∀ k, IsNormalTensor (A k)`, `∀ k, IsLeftCanonical (A k)` and `∀ k, μ k ≠ 0` |
| `IsNormalCanonicalFormBNT` | deleted, T7: with normal blocks, gauge-phase separation is exactly "the blocks are a basis of normal tensors of their weighted direct sum". The one-representative scope restriction (`cpsv16_ft_one_copy_scope_restriction.tex`) then sits on the two theorems in SectorComparison/NormalityChain.lean that use it |
| `IsCanonicalForm` (PiAlgebra) | deleted, T8: `IsNormalCanonicalForm` plus one-site injective blocks (CPSV16 `defnbi`); the self-overlap field is a consequence. One consumer (RFP/Convergence.lean:73) |
| `PreparedBNTBlocks`, `PreparedBNTBlocks.IsWeightNormalized` | deleted: a weighted family of normal left-canonical blocks (T2) is `CPSVCanonicalFormData.ofBlocks` with left-canonical blocks; its weight predicate duplicates `CPSVCanonicalFormData.IsWeightNormalized` |
| five one-field wrappers and `HasOrderedNonzeroWeights` | deleted as abbreviations of `∀ k, …` (pass-throughs); the `.ofForall` constructors and `toHas…` projections with them |
| `BlocksNotGaugePhaseEquiv` | survivor |
| `MPUCanonicalFormData` / `IsMPUCanonicalForm` / `IsMPUCanonicalBlock` | different notion (irreducible, possibly periodic blocks, full support); the name names a source, not the difference (D6) |
| `PGVWC07CanonicalFormData` / `IsPGVWC07CanonicalForm` | different notion: gauge-fixed form of the previous one with real weights (D6) |
| MPDO predicates | different notions (statements about an MPO and its doubled tensor, with MPDO conditions); outside this family, but they consume it: `IsVerticalCF` contains `IsBNT` (S2 changes it to the survivor; its suppliers already hold the survivor), `IsHorizontalCF`, `IsSimpleCanonicalForm` and `HasHorizontalCFMPVRepresentation` contain `IsBNTCanonicalForm` and lose the line-246 weight fields with S4. `HasHorizontalCFMPVRepresentation M` is then equivalent with no hypothesis to `∃ P, IsBNTSectorPresentation M.toMPSTensor P` (by the left-canonical gauge lemma in New.lean) and should be deleted by the MPDO change |
| `IsIsometryCanonicalForm`, `IsMPUCanonicalFormII` | different notions, outside this family |

#### Faithfulness findings

1. The paper-level Fundamental Theorem entries `thm:cpgsv_multiblock_ft_source`
   (`fundamentalTheorem_proportional_canonicalForm`, SectorBNT/FundamentalCoord.lean:637)
   and `thm:cpgsv_equal_case_source` (`fundamentalTheorem_equal_canonicalForm`, :612),
   both `\leanok` in ch11, take `IsBNTCanonicalForm` hypotheses, whose definition
   requires left-canonical basis tensors. CPSV16 Theorem 2.10 and Corollary 2.11
   state the result for tensors in canonical form with no gauge condition. Under
   the faithfulness rule these Lean theorems are stricter-hypothesis variants. The
   source-faithful statements are T9 and T10 in New.lean (presentations, no gauge
   choice, no weight convention); the equal-case basis matching is already proved
   on presentations (`IsBNTSectorPresentation.equiv_of_sameMPV₂Pos`).
2. The line-246 fields of `IsBNTCanonicalForm` are never used, but they force
   hypotheses: `CPSVCanonicalFormData.exists_isBNTCanonicalForm(_exact)` take
   `data.IsWeightNormalized`, and `fundamentalTheorem_equal_ambient_canonicalForm`
   (CanonicalFormEqualAmbient.lean:68) takes `hNormA`, `hNormB` only to call them;
   these hypotheses disappear with S4. They also put the unit-weight convention
   into `IsSimpleCanonicalForm`, the subject of the QICLean note
   `cpsv16_unit_weight_rfp_scale_tension`.
3. The glossary states that no equivalence relates `Kraus.IsNormal` and
   `IsNormalTensor`; T1 is that equivalence under the spectral-radius clause.
4. `IsNormalCanonicalFormBNT.isBNT` takes blockwise `Kraus.IsNormal`, which its
   other hypothesis implies.

### Change list

#### Removed declarations and replacements

| Removed | Replacement |
|---|---|
| `IsBNT` | `IsCPSVBasisOfNormalTensors`; T3 for the clause |
| `IsCPSVBasisOfNormalTensors.isBNT`, `IsBNTCanonicalForm.isBNT`, `IsBNT.of_sameMPV₂Pos` (Bridge.lean:86, 125, 101) | none (translations); `IsBNTSectorPresentation.of_sameMPV₂Pos` and `isCPSVBasisOfNormalTensors` already cover the content |
| `isBNT_of_separated_bnt_data`, `IsNormalCanonicalFormBNT.isBNT`, `isBNT_basisDirectSum` (RFP/BNTDirectSumBasis.lean:91) | `exists_eventually_linearIndependent_of_normalTensor_blocks_not_gaugePhaseEquiv`; T7; `isCPSVBasisOfNormalTensors_basisDirectSum` |
| `IsCPSVBasisOfNormalTensors.blocks_dim_pos` | kept, proof becomes `(hBNT.blocks_normal j).bondDim_ne_zero`, moved to Definitions.lean |
| `IsBNTCanonicalForm.basis_isNormal` | `(h.basis_normal j).isNormal` (S4, scripted) |
| `IsNormalCanonicalForm`, `.toHasIrreducibleBlocks`, `.toIsLeftCanonicalBlockFamily`, `.ofSeparatedData`, `.overlap_tendsto_one` | T6 clauses; `IsNormalTensor.selfOverlap_tendsto_one` |
| `IsNormalCanonicalFormBNT`, `.ofSeparatedData` | T7 |
| `IsCanonicalForm` (PiAlgebra), `.of_peripheral_primitive` | T8 clauses |
| `HasInjectiveBlocks`, `HasIrreducibleBlocks`, `HasPrimitiveBlocks`, `IsLeftCanonicalBlockFamily`, `HasNormalizedSelfOverlap` and their `.ofForall` | `∀ k, …` (S1, scripted) |
| `HasOrderedNonzeroWeights` | `∀ k, μ k ≠ 0`; ordering dropped |
| `PreparedBNTBlocks`, `.IsWeightNormalized`, `.exists_isBNTCanonicalForm_exact` | `CPSVCanonicalFormData.ofBlocks` with `∀ k, IsLeftCanonical (blocks k)`; the CF supplier |
| `MPSTensor.CanonicalForm`, `CanonicalForm.toTensor_eq_toTensorFromBlocks`, `fundamentalTheorem_canonicalForm_sameStructure` | `toTensorFromBlocks`; `fundamentalTheorem_multiBlock_global` |
| fields `basis_dim_pos`, `basis_irreducible`, `basis_normalized_self_overlap`, `basis_distinct` of `IsBNTCanonicalForm` | theorems of the same names (call sites unchanged) |
| fields `weight_norm_le_one`, `weight_unit_exists`, `bnt_data` | dropped; dropped; `eventually_li` (inherited) |

Restated: `IsBNTCanonicalForm P` as `structure … extends IsBNTSectorPresentation
P.toTensor P` with `basis_left_canonical` (elaborated as
`RestatedBNTCanonicalForm` in New.lean). This needs `IsBNTSectorPresentation`
moved from BNTRefinement.lean down to CanonicalForm/Definitions.lean and
SectorBNT/Basic.lean importing Definitions and NormalTensorGauge (no import cycle:
checked on the HEAD import graph). Restated consequently:
`CPSVCanonicalFormData.exists_isBNTCanonicalForm(_exact)` and
`fundamentalTheorem_equal_ambient_canonicalForm` lose their normalization
hypotheses; the suppliers listed in §2 lose their weight arguments;
`IsVerticalCF` takes the survivor basis predicate; `nncph_implies_rfp`
(RFP/BeigiLoopBNTIdentification.lean:456) takes the survivor (the source's basis
of normal tensors) instead of `IsBNT`.

New statements: T9 `fundamentalTheorem_proportional_of_isBNTSectorPresentation`,
T10 `ft_sector_data_of_isBNTSectorPresentation`, via
`IsBNTSectorPresentation.exists_restated`.

#### Consumers

| Change | Modules / occurrences | How |
|---|---|---|
| deletions of §4 (11 predicates and wrappers) | 41 / 363 (union) | S1 scripted for the wrappers; IsBNT type rewrite scripted (S2: 7 files, 9 occ.); the rest by hand (flagged: 10 files, 50 occ. for T6–T8 predicates and `PreparedBNTBlocks`; 5 files, 7 occ. for deleted translations) |
| restatement of `IsBNTCanonicalForm` | 57 / 245 | field accesses unchanged; scripted `.bnt_data` (5 files, 10 occ.), `basis_isNormal` (6 files, 10 occ.); constructors by hand (12 files, 93 constructor lines flagged) |
| renames D1 (S6) | 89 / 508 in Lean; plus blueprint and docs | scripted |
| rename D3 (S7) | 57 / 245 in Lean | scripted |
| union of all family names touched | 166 / 1116 | |

The dry-run of `rewrite.py` (dryrun.txt) gives the per-rule numbers by directory.

#### Blueprint

`\uses`/`\ref` counts over `blueprint/src/chapter/*.tex`.

| Label (file) | Lean tag | Action |
|---|---|---|
| `def:bnt` (ch10_bnt_definitions_and_characterization) | `IsBNT` | merged into `def:bnt_cpsv`; 11 `\uses`, 3 `\ref` redirected |
| `thm:cpsv_bnt_is_bnt` (ch10_bnt_normal_blocks_and_overlap) | `IsCPSVBasisOfNormalTensors.isBNT` | replaced by the T1/T3 entry; 1 `\uses`, 1 `\ref` |
| `def:bnt_cpsv` | `IsCPSVBasisOfNormalTensors` | kept (27 `\uses`), tag renamed under D1 |
| `def:cpsv_bnt_sector_presentation` (ch10_bnt_sector_canonical_form) | `IsBNTSectorPresentation` | kept (6 `\uses`); add T4 |
| `def:sector_bnt_cf` | `IsBNTCanonicalForm` | restated prose: presentation in left-canonical gauge; 56 `\uses`, 11 `\ref` unchanged |
| `thm:sector_bnt_cf_is_bnt` | `IsBNTCanonicalForm.isBNT` | removed (0 `\uses`) |
| entries at ch10_bnt_sector_canonical_form.tex:1102, 1133 | `CPSVCanonicalFormData.exists_isBNTCanonicalForm(_exact)` | statements lose the weight hypothesis |
| `thm:cpgsv_multiblock_ft_source`, `thm:cpgsv_equal_case_source` (ch11) | FT on `IsBNTCanonicalForm` | finding 1: retarget to T9/T10 when proved (D4) |
| `def:is_normal_canonical_form`, `def:normal_cf_bnt`, `lem:cf_bnt_is_bnt_split`, `lem:normal_cf_bnt_is_bnt` (ch09_canonical_normal_forms_and_support_auxiliary) | deleted predicates | removed; 2 `\uses`, 4 `\ref` redirected to the T6/T7 entries |
| `def:is_canonical_form`, `thm:canonical_from_primitive` (ch26_mps_rfp_normal_isometry_canonical_forms) | `IsCanonicalForm` | removed; 3 `\uses`, 3 `\ref` redirected to the T8 entry |
| `def:canonical_form` (ch02_mps) | `MPSTensor.CanonicalForm` | removed or retagged to `IsCPSVCanonicalForm` (0 `\uses`, 0 `\ref`) |
| `def:cpsv_canonical_form` (ch09_canonical_forms_and_projectors_auxiliary), CFII entries | CF names | tags renamed under D1 |

#### Glossary (`docs/glossary.md`)

"Normality": `Kraus.IsNormal` and `MPTensor.IsNormalTensor` caveats (replace the
"no equivalence" sentences by T1, T2); "Basis-level normality" (one predicate; T3);
"`MPSTensor.IsBNTSectorPresentation`" (the sector form extends it). "Canonical
form": opening sentence replaced by the table of §1; subsections
"`MPSTensor.CanonicalForm`", "`MPSTensor.IsCanonicalForm`",
"`MPSTensor.IsNormalCanonicalForm`", "`MPSTensor.IsNormalCanonicalFormBNT`" removed;
"`MPSTensor.IsBNTCanonicalForm`" rewritten (left-canonical presentation, no weight
fields); "Retained-block reconstruction and literal CPSV canonical form" and
"`MPTensor.IsMPUCanonicalForm`" renamed under D1/D6; "MPDO canonical-form
predicates" (`IsVerticalCF` basis clause; `IsSimpleCanonicalForm` unit-weight
paragraph; `HasHorizontalCFMPVRepresentation`).

#### Paper-gap notes (`docs/paper-gaps/`)

To rewrite: `cpsv16_ft_one_copy_scope_restriction.tex` (its subject
`IsNormalCanonicalFormBNT` disappears; the restriction moves to the two
NormalityChain theorems), `cpsv16_cf_normalization_and_proportional_comparison.tex`
(line-246 fields leave the sector form), `tnlean_bnt_ft_theorem_surface.tex` (add
finding 1 and T9/T10), `cpsv16_nncph_ground_state_scope.tex` (IsBNT),
`rmp_nonperiodic_bnt_comparison_inputs.tex`, `cpsv16_nondominant_per_block_projection.tex`
(IsNormalCanonicalFormBNT). Rename-only under D1/D3: the other 15 of the 20 notes
that name `CPSVCanonicalFormData`, `IsCPSVCanonicalForm`, `CPSVCanonicalFormII*`,
`IsCPSVBasisOfNormalTensors` or `IsBNTCanonicalForm` (`grep -l`; e.g.
`cpgsv17_vertical_cf_grouping.tex`, `cpsv16_rfp_isometry_scope.tex`); S6/S7 cover them. QICLean-hosted notes cited by URL whose subject disappears after S4:
`cpsv16_unit_weight_rfp_scale_tension`, `cpsv16_global_vs_persector_unit_witness`.

#### Bridge modules

- `TNLean/MPS/CanonicalForm/BNTPresentation/Bridge.lean`: deleted. Of its four theorems three are
  translations to or from `IsBNT`; `blocks_dim_pos` moves to Definitions.lean.
  Direct importers (7): BNT.lean (aggregator), RFP/BNTDirectSumBasis.lean,
  RFP/ResidualIsometry.lean, MPDO/VerticalBNTConstruction.lean,
  MPDO/SourceBNTBlocking.lean, MPDO/BNTAlgebraTensorClause.lean,
  MPDO/BNTFusionTensorClauseFromRFP.lean; 253 modules downstream.
- `TNLean/MPS/CanonicalForm/BNTPresentation/PreparedReconstruction.lean`: relates two
  different objects (a canonical form of `A`, a sector presentation), so it is a
  theorem; its construction duplicates `BNTRefinement.isBNTSectorPresentation` up
  to the left-canonical gauge. Merged into CanonicalForm/BNTRefinement.lean as
  "a tensor in canonical form has a presentation in left-canonical gauge with an
  exact coisometric reconstruction" (no weight hypothesis). Direct importers:
  SectorBNT.lean (aggregator) and SectorBNT/CanonicalFormEqualAmbient.lean; 4 modules
  downstream.

### Order of application

Every step leaves the tree building; no QICLean code change is needed (only the
two QICLean paper-gap notes in §4, after S4).

| Step | Content | Kind | Rebuild |
|---|---|---|---|
| S0 | add T1–T8 and `exists_restated` next to their ingredients (NormalTensorGauge, NormalizedSelfOverlap, BNTRefinement) | additions | small |
| S1 | unwrap the five one-field wrappers and `HasOrderedNonzeroWeights` | scripted (`--stage S1`) + hand edits in CanonicalFormSepAux.lean and BNT/Construction.lean | wide: CanonicalFormSepAux has 1,139 downstream modules |
| S2 | delete `IsBNT`, Bridge.lean; `IsVerticalCF`, `nncph_implies_rfp` on the survivor | scripted type rewrite + 7 flagged sites | wide: BNT/Basic has 1,244 downstream |
| S3 | delete `IsNormalCanonicalForm`, `IsNormalCanonicalFormBNT`, PiAlgebra `IsCanonicalForm`, `PreparedBNTBlocks`, `MPSTensor.CanonicalForm`; restate their consumers with T6–T8 | by hand, 10 files flagged + Core/MultiBlock, FundamentalTheorem/Multi | wide (Core/MultiBlock 1,640 downstream) |
| S4 | restate `IsBNTCanonicalForm` (move `IsBNTSectorPresentation` to Definitions.lean); drop weight fields; merge CanonicalFormBridge into BNTRefinement; drop the normalization hypotheses of the CF suppliers and of `fundamentalTheorem_equal_ambient_canonicalForm` | scripted projections + 12 files of constructors by hand | 766 downstream of SectorBNT/Basic |
| S5 | prove T9, T10 (and `exists_restated`); retarget ch11 entries | proofs | small |
| S6 | renames D1 (after S3, which frees `IsCanonicalForm`); optional S6d for D2 | scripted | wide (Definitions 1,084 downstream) |
| S7 | rename D3 | scripted | 766 downstream |

S1, S2 and S0 are independent of each other. S3 needs S0 (T6–T8) and S1. S4 needs
S0 (T2) and should follow S2 (Bridge.lean imports the sector form). S6 must follow
S3. To keep rebuilds few, S1–S3 can land as one change and S6–S7 as one change. No
temporary abbreviation is needed: the restated sector form keeps its name until S7,
and the project keeps no deprecated aliases.

### Open decisions

- D1. Drop the source tag: `IsCPSVBasisOfNormalTensors → IsBasisOfNormalTensors`,
  `CPSVCanonicalFormData → CanonicalFormData`, `IsCPSVCanonicalForm → IsCanonicalForm`,
  CFII likewise. Recommendation: yes, once each is the only predicate of its notion
  (after S3). Collision check in dryrun.txt: only `IsCanonicalForm` exists today
  (3 files, removed by S3).
- D2. Argument shape of the basis predicate: a sigma family (HEAD) or an explicit
  dimension family as in `IsBNT` and `SectorDecomposition`. At least 50 of the
  roughly 80 applied occurrences wrap `fun j => ⟨dim j, B j⟩`. Recommendation:
  explicit family, done with S6 (`--stage S6d`: 24 files, 50 occ. scripted; 23
  files flagged).
- D3. Name of the restated sector form. Recommendation:
  `IsLeftCanonicalBNTPresentation` (says how it differs from
  `IsBNTSectorPresentation`); once T9/T10 carry the public theorems, consider
  making it internal to `FundamentalTheorem/SectorBNT`.
- D4. Blueprint status of ch11 until T9/T10 are proved: option (a) of the
  faithfulness rule, keep `\lean{…}` on the current theorems but drop `\leanok`
  and state the left-canonical restriction; or (b) keep them as scope-restricted
  entries and add the source entries. Recommendation: (b), with a note in
  `tnlean_bnt_ft_theorem_surface.tex`, since the restriction is removed by a
  gauge argument that is already available.
- D5. Keep `0 < P.basisCount` in the presentation (excludes the zero tensor) or
  allow the empty presentation of `0`. Recommendation: keep; it is the recorded
  nonzero-family convention and every consumer has a nonzero tensor.
- D6. Irreducible-block canonical forms: rename `MPUCanonicalFormData` to say
  "irreducible blocks" and record the implication PGVWC07 → MPU form (absent at
  HEAD). Recommendation: leave to the MPU family; not needed for this family.

### Lean statements (New.lean)

Elaborated against `worktrees/hot-main` (414a18fb88; the family's files differ
from HEAD only in BlockingViaAdjoint, CyclicSectors/FixedAdjoint and
KrausAdjointSetup, not used here) with
`lake env lean New.lean`; exit 0, output (elab_output.txt): three
"declaration uses `sorry`" warnings, for `exists_restated`, T9 and T10. Proved and
checked: T1 `isNormalTensor_iff_isNormal_and_spectralRadius_eq_one`, T2
`isNormalTensor_tfae_of_isLeftCanonical`, T3
`isCPSVBasisOfNormalTensors_iff_isBNT_of_spectralRadius_eq_one`, T4
`isBNTSectorPresentation_iff`, T5 `isBNTCanonicalForm_iff`, T6
`isNormalCanonicalForm_iff`, T7 `isNormalCanonicalFormBNT_iff`, T8
`isCanonicalForm_iff`, the restated structure `RestatedBNTCanonicalForm` with its
four derived field theorems, and `isBNTCanonicalForm_iff_restated`. Stated with
`sorry` (route in the docstrings): `IsBNTSectorPresentation.exists_restated` (gauge
each basis tensor by `IsNormalTensor.exists_tpGauge`; the presented vectors do not
change), T9 (then rescale weights and apply
`fundamentalTheorem_proportional_canonicalForm`), T10 (then
`ft_sector_bnt_equal_sector_data`, whose proof uses no weight field).

`rewrite.py` apply mode was tested on copies of four modules (applytest.diff); the
rewritten files were not elaborated, since each calls lemmas in unrewritten
modules. The unwrapped `HasNormalizedSelfOverlap` statement exceeds 100 characters
on one line and needs a manual line break.

## 2. The commuting form of a matrix product density operator

**Status: applied** in #11011 (round 1). The commuting form has one structure; the inventory, verdicts, change list and statements of this section are in the history of this file.

## 3. Mutual information on a chain

**Status: applied** in #11011 (round 1). Mutual information of a chain is QICLean’s; the inventory, verdicts and change list are in the history of this file.

## 4. Unique ground states

Reference revisions: TNLean HEAD `e8f8dd3202`; QICLean pinned by HEAD `d65bece64d`;
Lean checks against `worktrees/hot-main` (TNLean `414a18fb88`, QICLean `271884e2`).

Counting method, used throughout unless a row says otherwise: on the extraction of HEAD,
`grep -rlw <name> TNLean --include=*.lean` (Archive excluded, defining module included) for
modules, `grep -ow` summed over those files for occurrences, broken down by the first one or two
path components. Blueprint counts are `grep -n -w 'MPSTensor.<name>'` over
`blueprint/src/chapter/*.tex`. The helper is `count.sh` in this directory.

### What "unique ground state" means in the sources

* Pérez-García, Verstraete, Wolf, Cirac, quant-ph/0608197 (`Papers/quant-ph_0608197/MPSarchive.tex`),
  Theorem `uniqueGS`, lines 1272–1274 (setting lines 1252–1270): for an MPS `|ψ⟩` with property C1, `N ≥ 2L₀` and `L > L₀`,
  "`|ψ⟩` is the only ground state of `H_{G_L}`". The open-chain version, lines 1205–1208:
  "`|ψ⟩` is the unique ground state of `H = Σ_j h_{j,j+1}`". Both name the vector. Before the
  theorem (lines 1266–1267) the source records `H_{G_L}|ψ⟩ = 0` and that `H_{G_L}` is a sum of
  projections, so the ground energy is `0`.
* Pérez-García, Verstraete, Cirac, Wolf, arXiv:1001.3807 (`Papers/1001.3807/paper_v3.tex`),
  Theorem 3.5, lines 758–772: `H_par` "has `|M(A)⟩` as its unique and frustration free ground
  state". Names the vector.
* Cirac, Pérez-García, Schuch, Verstraete, arXiv:2011.12127 (`Papers/2011.12127/TN-Review-main.tex`),
  `thm:4:unique-gs-2L0` (lines 2041–2048) and `thm:4:unique-gs-L0_plus_1` (lines 2086–2094):
  "the parent Hamiltonian … has a unique ground state" (the vector is not named in the statement;
  the surrounding text, lines 2035–2038, uses the one-to-one correspondence `ψ' = R^{⊗N} ψ`).
* Fannes–Nachtergaele–Werner 1992 is cited in module docstrings as `[FNW92]`; there is no local
  copy under `Papers/`.

Every source statement is "the ground space of the Hamiltonian is the line through a nonzero
vector", named or not. None of them is a property of an abstract subspace.

### Inventory

#### Predicates and definitions

| Name | Definition (Lean) | Anchor | Modules at HEAD (occurrences) |
|---|---|---|---|
| `MPSTensor.HasUniqueGroundState` (`MPS/ParentHamiltonian/UniqueGroundState.lean:56`) | `Module.finrank ℂ S = 1` for any `S : Submodule ℂ V` | docstring "unique ground state (up to scalar)"; blueprint `def:has_unique_ground_state` ("one-dimensional ground space") | 7 (18): MPS/Examples 5, MPS/ParentHamiltonian 2, PEPS 0. Two more modules use it through definitional unfolding and are not found by name: `MPS/Symmetry/MPOSymmetry/RingEndpointComparison.lean:309`, `RingEndpointRightComparison.lean:195` (`exact groundSpace_unique_periodic` against a goal `Module.finrank ℂ (…) = 1`) |
| `MPSTensor.hasUniqueGroundState_iff_proportional` (`UniqueGroundState.lean:61`) | `[FiniteDimensional ℂ S] : HasUniqueGroundState S ↔ ∃ ψ₀ : S, ψ₀ ≠ 0 ∧ ∀ ψ : S, ∃ c, ψ = c • ψ₀` | blueprint `thm:has_unique_ground_state_iff_proportional` | 1 (1), no consumer. It is Mathlib's `finrank_eq_one_iff'` with the scalar on the other side and a superfluous finite-dimensionality hypothesis |
| `ManyBody.groundSpace H E₀` (QICLean `ManyBody/Hamiltonian/GroundSpace.lean:105`, pin) | `Module.End.eigenspace (toEuclideanLin H) E₀` on `EuclideanSpace ℂ n` | area law `00-introduction.tex` 44–47 | used as the unique-ground-state convention `groundSpace H E₀ = Submodule.span ℂ {Ω}` in `MPS/AreaLaw/Algorithm` (3 modules), `PEPS/Approximation` (`IsSquareGroundState`, `IsRangeSquareGroundState`) and `PEPS/AreaLaw` |
| `ManyBody.IsGapped H E₀ Δ` (QICLean `GroundSpace.lean:122`, pin) | `groundSpace H E₀ ≠ ⊥ ∧ ∀ μ eigenvalue, μ = E₀ ∨ E₀ + Δ ≤ μ` | same | 173 modules (624) by `grep -w IsGapped`: MPS/AreaLaw 85, PEPS/AreaLaw 60, PEPS/Approximation 25, Algebra 1, Lattice 2 |
| line equation with a nonzero vector, TNLean spelling: `S = mpvSubmodule A N` with `mpvSubmodule A N := Submodule.span ℂ {mpv A}` (`ChainGroundSpace.lean:31`) and `mpv A ≠ 0` | `S = ℂ ∙ ψ`, `ψ ≠ 0` | — | `mpvSubmodule` 19 (71): MPS/Examples 7, MPS/ParentHamiltonian 9, MPS/Symmetry 2, MPS/MPDO 1 |
| inline `Module.finrank ℂ (ground space) = 1` | Mathlib spelling, no name | — | 15 one-line statements in 10 modules (MPS/ParentHamiltonian 5, MPS/Examples 2, PEPS/ParentHamiltonian 4 …; script listing in the method note below) plus the 2 multi-line RingEndpoint theorems |
| `IsSquareGroundState`, `IsRangeSquareGroundState` (PEPS/Approximation) | `∃ h, … ∃ E₀, ‖Ω‖ = 1 ∧ IsGapped h.hamiltonian E₀ Δ ∧ groundSpace h.hamiltonian E₀ = span {Ω}` | polynomial-PEPS `eq:model` | 22 (48), 6 (28); audit row G6 |
| `IsFrustrationFreeGapped` (`PEPS/AreaLaw/Operators/FrustrationFree/Model.lean:67`) | structure with `isGapped : IsGapped h.hamiltonian 0 Δ`, `zeroSpace_eq : h.zeroSpace = span {Ω}`, … | FF note `eq:model` | 3 (26); audit row FF10, family 5 |
| `QICLean HasUniqueFixedPoint` (`Channel/Irreducible/Basic.lean:63`) and `finrank (eigenspace (transferMap A) 1) = 1` hypotheses (MPS/Symmetry 7 statements) | uniqueness of a channel fixed point | Wolf ch. 6 | different notion (fixed point of a channel, not a ground state); out of this family |

The subspaces `S` to which `HasUniqueGroundState` is applied:

| Call site | `S` | Ambient space | Hamiltonian present? |
|---|---|---|---|
| `parentHamiltonian_unique_gs` (`UniqueGroundState.lean:824`), `groundSpace_unique_periodic` (`:839`), `_injective` (`:858`), `_normal` (`:870`) | `chainGroundSpace A L N` | `NSiteSpace d N = (Fin N → Fin d) → ℂ` | yes: `ker (parentHamiltonian A L N) = chainGroundSpace A L N` for `0 < N`, `L ≤ N` (`ker_parentHamiltonian_eq_chainGroundSpace`, `KernelChainGroundSpace.lean:76`); at HEAD `parentHamiltonian A L N = Matrix.toLin' (parentRingInteraction A hLN).hamiltonian` (`parentHamiltonian_of_le`, `Defs.lean:344`) |
| `hasUniqueGroundState_chainGroundSpace_rotatePhysical` (`PhysicalDeformation.lean:436`) | `chainGroundSpace` of `A` (hypothesis) and of `Λ A` (conclusion) | `NSiteSpace` | yes, as above |
| `aklt_parentHamiltonian_two_unique_gs` (`AKLTParentHamiltonian.lean:341`), `akltTensorRMP_parentHamiltonian_two_unique_gs` (`AKLTReview.lean:356`) | `chainGroundSpace _ 2 N` | `NSiteSpace` | yes |
| `akltHamiltonian_hasUniqueGroundState` (`AKLTPolynomialHamiltonian.lean:364`) | `Module.End.eigenspace (akltHamiltonian N) (-(2N/3))` | `NSiteSpace` | yes, but as a linear map on `NSiteSpace`, not a QICLean matrix |
| `cluster_stabilizer_unique_gs` (`ClusterParentHamiltonian.lean:357`), `clusterSource_stabilizer_unique_gs` (`ClusterSourceGroundState.lean:301`) | `⨅ i, eigenspace (clusterChainStabilizer i) (±1)` | `NSiteSpace` | implicitly (`Σ ½(1 ∓ K_i)`); `clusterSource_hamiltonian_eigenspace_eq_mpvSubmodule` (`:433`) states the sum form |

None of these `S` is literally a `ManyBody.groundSpace H E₀`: all live on the function space
`NSiteSpace d N`, while `ManyBody.groundSpace` needs a `Matrix n n ℂ` and lives on
`EuclideanSpace ℂ n`.

#### Proved implications (HEAD)

| Statement | Hypotheses | Lemma, file:line |
|---|---|---|
| `HasUniqueGroundState S ↔ ∃ ψ₀ : S, ψ₀ ≠ 0 ∧ ∀ ψ, ∃ c, ψ = c • ψ₀` | `FiniteDimensional ℂ S` (superfluous) | `hasUniqueGroundState_iff_proportional`, `UniqueGroundState.lean:61` |
| `ker (parentHamiltonian A L N) = chainGroundSpace A L N` | `0 < N`, `L ≤ N` | `ker_parentHamiltonian_eq_chainGroundSpace`, `KernelChainGroundSpace.lean:76` |
| `parentHamiltonianGroundSpaceES A L N = chainGroundSpaceES A L N` | `0 < N`, `L ≤ N` | `parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES`, `KernelChainGroundSpace.lean:90` (no consumer) |
| `chainGroundSpace A L N = mpvSubmodule A N` | normal, `L₀`-block injective, `0 < L₀`, `2 ≤ N`, `L₀ < L ≤ N`, `L₀ + 1 ≤ N` | `chainGroundSpace_eq_mpvSubmodule_normal`, `UniqueGroundState.lean:808` |
| same | injective, `2 ≤ N`, `1 < L ≤ N` | `chainGroundSpace_eq_mpvSubmodule`, `PeriodicBoundaryReduction.lean:29` |
| `mpv A ≠ 0` on `N` sites | `L₀`-block injective, `0 < L₀`, `L₀ + 1 ≤ N` | `mpv_ne_zero_of_isNBlkInjective`, `Nonvanishing.lean:100` |
| `IsFrustrationFree A L N ψ ↔ toLp ψ ∈ (parentRingInteraction A hLN).zeroSpace` | `L ≤ N` | `isFrustrationFree_iff_mem_zeroSpace`, `Defs.lean:378` |
| projector gap ↔ `H.IsHermitian ∧ ‖Ω‖ = 1 ∧ IsGapped H E₀ Δ ∧ groundSpace H E₀ = span {Ω}` | `0 < Δ` | `isGapped_and_groundSpace_eq_span_iff`, QICLean `GroundSpace.lean:219` |
| line equations at the example call sites | as stated | `aklt_chainGroundSpace_two_eq_mpvSubmodule` (`AKLTParentHamiltonian.lean:328`), `akltHamiltonian_eigenspace_eq_mpvSubmodule` (`AKLTPolynomialHamiltonian.lean:351`), `akltTensorRMP_chainGroundSpace_two_eq_mpvSubmodule` (`AKLTReview.lean:349`), `cluster_iInf_eigenspace_eq_mpvSubmodule` (`ClusterParentHamiltonian.lean:344`), `clusterSource_iInf_eigenspace_eq_mpvSubmodule` (`ClusterSourceGroundState.lean:264`), `mixedEndpoint_periodic_groundSpace_eq` (`RingEndpointComparison.lean:279`), `mixedEndpoint_periodic_one_groundSpace_eq` (`RingEndpointRightComparison.lean:165`) |

Every one of the 10 theorems concluding `HasUniqueGroundState` is proved by first establishing a
line equation `S = ℂ ∙ ψ` and `ψ ≠ 0` and then applying `finrank_span_singleton`. The finite-rank
conclusion forgets the vector that the proof (and, for PGVWC07 and arXiv:1001.3807, the source)
names.

### Is the redirect of issue #10944 (G5) equivalent?

Checked in `New.lean` (elaborated, section 1):

1. `finrank K S = 1 ↔ ∃ v, v ≠ 0 ∧ S = K ∙ v` holds for every subspace of every vector space over a
   division ring, with no finite-dimensionality hypothesis
   (`Submodule.finrank_eq_one_iff_exists_eq_span_singleton`). So `HasUniqueGroundState` is the
   existential form of the line equation.
2. For a given vector the two forms are not interchangeable. `S = K ∙ v` gives `finrank K S = 1`
   only with `v ≠ 0` (`S = K ∙ 0 = ⊥`; the example `¬ HasUniqueGroundState (ℂ ∙ 0)` is checked);
   `finrank K S = 1` gives `S = K ∙ v` only with `v ∈ S` and `v ≠ 0`
   (`Submodule.eq_span_singleton_iff_mem_and_finrank_eq_one`). QICLean's convention always pairs
   the line equation with `‖Ω‖ = 1` or with `IsGapped` (whose first clause is `groundSpace ≠ ⊥`),
   so a faithful redirect must carry `Ω ≠ 0`.
3. At every call site both side conditions are already proved (section 2.2), so the redirect loses
   nothing; it strengthens the conclusions to what is proved.
4. The issue's "no statement content changes" does not hold for G5: the subspaces at the call sites
   are subspaces of `NSiteSpace`, not `ManyBody.groundSpace`. Putting the parent-Hamiltonian
   theorems through `groundSpace H 0 = span {Ω}` needs one new transport theorem,
   `groundSpace_toMatrix'_parentHamiltonian` (New.lean, elaborated):
   `ManyBody.groundSpace (toMatrix' (parentHamiltonian A L N)) 0 =
   (chainGroundSpace A L N).map (WithLp.linearEquiv 2 ℂ _).symm` for `0 < N`, `L ≤ N`.
   On HEAD `toMatrix' (parentHamiltonian A L N) = (parentRingInteraction A hLN).hamiltonian` by
   `parentHamiltonian_of_le` and `LinearMap.toMatrix'_toLin'` (written out at the end of New.lean,
   not elaborated: hot-main predates `parentRingInteraction`).
5. The AKLT and cluster example Hamiltonians are linear maps on `NSiteSpace`
   (`akltHamiltonian`, `Σ clusterChainStabilizer i`), not QICLean matrices. Restating those through
   `ManyBody.groundSpace` belongs to the Hamiltonian-spelling sweep (audit §7 item 6), not to G5.
   For them the line equation on the existing eigenspace is the survivor now.

Duplicates of `ManyBody.groundSpace` found on the way (boundary with family 5 and audit row G13):

* `parentHamiltonianGroundSpaceES A L N` (`Martingale/Transport.lean:148`, the transported kernel of
  `parentHamiltonian A L N`) equals `ManyBody.groundSpace (toMatrix' (parentHamiltonian A L N)) 0`
  for every `L`, `N`, with no hypothesis (`parentHamiltonianGroundSpaceES_eq_groundSpace`, New.lean,
  elaborated). Under the rule it is a second name for `ManyBody.groundSpace` and should be deleted
  with that characterization: 17 modules (60 occurrences): MPS/ParentHamiltonian 10, MPS/RFP 4,
  MPS/Symmetry 2, MPS/Examples 1.
* `chainGroundSpaceES` (`KernelChainGroundSpace.lean:83`) and
  `parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES` (`:90`): used only in their own module
  (1 module, 3 occurrences) and in the blueprint (`ch13_parent_hamiltonian_spectral_gap_hilbert_space_rowsum.tex:322,333`).
  A bridge with no consumer: delete.
* `chainGroundSpace A L N` is the source's intersection of local constraints (arXiv:1606.00608
  Def. 3.9). For `0 < N`, `L ≤ N` it is the zero space of `parentRingInteraction A hLN`
  transported to `NSiteSpace`; for `N = 0` or `L > N` it is `⊤` by convention. It is equivalent to
  the zero space only under that hypothesis, which makes it a family-5 question (zero space versus
  intersection of local constraints), not a family-4 one.
* `MPSTensor.groundSpace A L` (range of `Γ_L`, the source's `G_L`) is the local tensor space, a
  different notion that happens to share the word; audit row G13 keeps it. Not touched here.

### Verdicts

| Name | Verdict |
|---|---|
| `MPSTensor.HasUniqueGroundState` | **Deleted.** An abbreviation of Mathlib's `Module.finrank ℂ S = 1`, with no Hamiltonian in it. Characterization: `Submodule.finrank_eq_one_iff_exists_eq_span_singleton` (New.lean). |
| `MPSTensor.hasUniqueGroundState_iff_proportional` | **Deleted.** Same statement as Mathlib's `finrank_eq_one_iff'` (applied to `↥S`), plus a superfluous hypothesis; no consumer. |
| `ManyBody.groundSpace H E₀ = span {Ω}` with `Ω ≠ 0` (or `‖Ω‖ = 1`), and `IsGapped` where a gap is asserted | **Survivor** (QICLean convention, glossary row at `docs/glossary.md:3277`). For subspaces not yet expressed as `ManyBody.groundSpace` (the NSiteSpace eigenspaces of the examples), the survivor is the same line equation `S = ℂ ∙ ψ` with `ψ ≠ 0` on the existing subspace. |
| inline `Module.finrank ℂ (…) = 1` (15 + 2 statements) | Mathlib spelling of the same existential notion, not a second predicate. Kept; converted to line equations when their subspaces are restated as `ManyBody.groundSpace` (audit §7 item 6). The two RingEndpoint `_finrank` theorems are corollaries of their adjacent `_groundSpace_eq` theorems (open decision 3). |
| `mpvSubmodule A N` | Abbreviation of `ℂ ∙ mpv A`; 17 proof steps unfold it. Not a predicate; open decision 4. |
| `IsSquareGroundState`, `IsRangeSquareGroundState` | Source model classes stated with the survivor (audit G6, class (c)); unchanged. |
| `IsFrustrationFreeGapped` | Family 5 (audit FF10). |
| `parentHamiltonianGroundSpaceES` | Hypothesis-free equal to `ManyBody.groundSpace` (proved in New.lean): delete with characterization; hand to family 5 or the G13 follow-up, since its 17 consumers are the martingale gap modules. |

### Change list

#### Step 1, mechanical (`rewrite.py`, dry run in `dryrun.txt`)

| Rule | Files | Occurrences |
|---|---:|---:|
| A1 delete `HasUniqueGroundState`, `hasUniqueGroundState_iff_proportional` (`UniqueGroundState.lean:55–81`) | 1 | 2 declarations |
| A2 `HasUniqueGroundState (S)` → `Module.finrank ℂ (S) = 1` (with `↥` before a `⨅` argument) | 7 | 11 (10 conclusions, 1 hypothesis) |
| A3 drop `HasUniqueGroundState` from `rw [...]` lists | 4 | 5 |
| B1 blueprint: delete `def:has_unique_ground_state`, `thm:has_unique_ground_state_iff_proportional` (`ch13_parent_hamiltonian_injective_boundary.tex:535–555`) | 1 | 2 entries |
| B2 blueprint: drop `def:has_unique_ground_state` from `\uses` | 2 | 5 |

Total: 7 Lean modules (18 occurrences, all of them), 3 blueprint files. Residual occurrences after
the rules: 0. Apply mode was tested on copies of the 10 files (`applytest/`, diff in
`apply_test.diff`); the rewritten `UniqueGroundState`, `PhysicalDeformation`,
`AKLTParentHamiltonian`, `AKLTReview`, `ClusterParentHamiltonian` and `ClusterSourceGroundState`
elaborate against hot-main with no messages. (`AKLTPolynomialHamiltonian` at HEAD uses lemmas newer
than hot-main and was not elaborated; its change is the removal of one `rw` entry.) Statements keep
their meaning; this step alone is a complete deletion of the predicate.

#### Step 2, restatements (non-mechanical, statements in `New.lean`)

| Old | New | Consumers |
|---|---|---|
| — | `groundSpace_toMatrix'_parentHamiltonian_eq_map_ker`, `groundSpace_toMatrix'_parentHamiltonian` (new, in `KernelChainGroundSpace.lean` next to `ker_parentHamiltonian_eq_chainGroundSpace`); on HEAD stated with `(parentRingInteraction A hLN).hamiltonian` | — |
| `parentHamiltonian_unique_gs : HasUniqueGroundState (chainGroundSpace A L N)` | same name (open decision 1), conclusion `ManyBody.groundSpace (parentRingInteraction A hLN).hamiltonian 0 = ℂ ∙ toLp (mpv A) ∧ mpv A ≠ 0` (New.lean `groundSpace_parentHamiltonian_eq_span_mpv`) | `ClusterParentHamiltonian` (via `cluster_stabilizer_unique_gs`, deleted below), `_injective`, `_normal` |
| `groundSpace_unique_periodic` | same conclusion, proof one line from the above with `Kraus.isNBlkInjective_one_of_isInjective` (New.lean `…_of_isInjective`); the separate nonvanishing proof goes | `RingEndpointComparison:309`, `RingEndpointRightComparison:195`: reprove from `mixedEndpoint_periodic_groundSpace_eq` / `_one_groundSpace_eq` and `finrank_span_singleton`, or delete those two `_finrank` theorems (open decision 3) |
| `parentHamiltonian_unique_gs_injective`, `parentHamiltonian_unique_gs_normal` | same conclusion as `parentHamiltonian_unique_gs` (they are its `L = 2L₀` and `L = L₀ + 1` cases; `_normal` keeps `IsNormal`, which `thm:4:unique-gs-L0_plus_1` assumes) | none in code |
| `hasUniqueGroundState_chainGroundSpace_rotatePhysical` | `chainGroundSpace_rotatePhysical_eq_span : chainGroundSpace A L N = ℂ ∙ ψ → chainGroundSpace (rotatePhysical Λ A) L N = ℂ ∙ Λ^{⊗N} ψ` (renamed: the old name carries the deleted predicate) | none in code; module docstring `PhysicalDeformation.lean:48` |
| `aklt_parentHamiltonian_two_unique_gs` | restated like `parentHamiltonian_unique_gs` on the two-site AKLT parent Hamiltonian | `AKLTPolynomialHamiltonian`, `AKLTReview` (both consumers deleted below) |
| `akltHamiltonian_hasUniqueGroundState` | deleted; survivor `akltHamiltonian_eigenspace_eq_mpvSubmodule`; `akltHamiltonian_hasEigenvalue` reproved (New.lean, elaborated) | 1 (same module) |
| `akltTensorRMP_parentHamiltonian_two_unique_gs` | deleted (a "Bridge:" corollary); survivor `akltTensorRMP_chainGroundSpace_two_eq_mpvSubmodule` | none |
| `cluster_stabilizer_unique_gs` | deleted; survivor `cluster_iInf_eigenspace_eq_mpvSubmodule` with `mpv_ne_zero_of_isNBlkInjective` (New.lean example) | none |
| `clusterSource_stabilizer_unique_gs` | deleted; survivor `clusterSource_iInf_eigenspace_eq_mpvSubmodule` with `clusterSource_mpv_ne_zero` (New.lean example) | none |
| `chainGroundSpaceES`, `parentHamiltonianGroundSpaceES_eq_chainGroundSpaceES` | deleted (bridge without consumer) | 0 outside the module |

Step 2 touches 10 modules: `UniqueGroundState`, `PhysicalDeformation`, `KernelChainGroundSpace`,
`RingEndpointComparison`, `RingEndpointRightComparison`, `AKLTParentHamiltonian`,
`AKLTPolynomialHamiltonian`, `AKLTReview`, `ClusterParentHamiltonian`, `ClusterSourceGroundState`.
Downstream uses of the 10 restated or deleted theorems: 8 occurrences in 6 modules (measured by
`git grep -n -w <name> HEAD`, excluding the defining line).

#### Blueprint, glossary, paper-gap notes

* `\lean{…}` tags of family names: 12 in 5 files. `ch13_parent_hamiltonian_injective_boundary.tex:536,542`
  (entries deleted in step 1); `ch13_parent_hamiltonian_normal_closing_reverse.tex:632,664,685,703`
  (statement text: "the ground space is the line through `V^{(N)}(A)`, which is nonzero");
  `ch13_parent_hamiltonian_physical_deformation.tex:388` (new name);
  `ch15_examples_parent_hamiltonians.tex:302,371,611,814` (drop the deleted names from the `\lean`
  lists; the surviving line-equation names are already listed at 302, 371, 611);
  `ch15_examples_aklt.tex:574` (drop the deleted name). Also
  `ch13_parent_hamiltonian_spectral_gap_hilbert_space_rowsum.tex:322,333` for `chainGroundSpaceES`.
* Glossary: no entry for `HasUniqueGroundState`. The survivor is already described in the row
  `ManyBody.IsGapped`, `ManyBody.groundSpace` (`docs/glossary.md:3277`). For family 5: the section
  "Parent Hamiltonians on the ring" (`docs/glossary.md:1478`) cites
  `MPSTensor.toLp_mem_ker_parentHamiltonian_iff` and
  `MPSTensor.posSemidef_parentRingInteraction_term`, which do not exist at HEAD.
* Paper-gap notes with `\leanid` of affected names: `docs/paper-gaps/cpgsv21_normal_range_reduction.tex:331–332`
  (`_normal`, `_injective`: names kept, no edit if decision 1 is taken);
  `docs/paper-gaps/rmp_example_parent_hamiltonian_scope.tex:266` (`aklt_parentHamiltonian_two_unique_gs`, kept),
  `:308` (`clusterSource_stabilizer_unique_gs` → `clusterSource_iInf_eigenspace_eq_mpvSubmodule`),
  `:325` (`cluster_stabilizer_unique_gs` → `cluster_iInf_eigenspace_eq_mpvSubmodule`).
* Dated audits mentioning the names (`docs/audits/2026-05-08-mps-ft-paper-coverage.md:237,399`,
  `2026-10-05_scp10_*`) are records and are not edited.
* No bridge module is deleted or renamed: the family has none.

### Order of application

1. Step 1 is independent of everything else and needs no QICLean change. It edits
   `UniqueGroundState.lean`, which 866 non-aggregator modules import transitively (reverse import
   closure over HEAD, aggregator modules excluded), so it forces a wide rebuild. Do step 1 and
   step 2 in one pull request to pay for one rebuild.
2. Step 2 needs only declarations at the QICLean pin (`ManyBody.groundSpace`,
   `mem_groundSpace_iff_mulVec`). Within it, the transport theorem comes first; the four
   `UniqueGroundState` theorems, then `PhysicalDeformation`, then the two RingEndpoint modules,
   then the five example modules, are independent of each other after that.
3. The deletion of `parentHamiltonianGroundSpaceES` (17 modules) and the restatement of
   `chainGroundSpace` against the zero space are family 5 / G13 work; they do not block this family.
4. Side observation: HEAD uses `ManyBody.Interaction.zeroSpace` (`Defs.lean:378`,
   `PEPS/AreaLaw/Operators/FrustrationFree/Model.lean:79`), which is absent from the QICLean revision pinned
   in HEAD's `lake-manifest.json` (`d65bece64d`, and also from hot-main's `271884e2`); it exists
   only on the QICLean branch checked out in `worktrees/batch2-circuit`. A pin move precedes any
   build of HEAD.

### Open decisions

1. **Names of the restated source theorems.** Keep `parentHamiltonian_unique_gs`,
   `_injective`, `_normal`, `groundSpace_unique_periodic`, `aklt_parentHamiltonian_two_unique_gs`
   with their new conclusions, or rename to `groundSpace_parentHamiltonian_eq_span_mpv…`.
   Recommendation: keep the names. They name the source theorem (`uniqueGS`), the restated
   conclusion is still "unique ground state", and keeping them leaves two paper-gap
   notes and four blueprint tags unchanged.
2. **Conjunction `groundSpace … = ℂ ∙ ψ ∧ ψ ≠ 0` versus the line equation alone.**
   Recommendation: the conjunction, as in New.lean. The sources state that `ψ` is a (nonzero)
   ground state; the line equation alone admits `ψ = 0`, which would assert that `0` is not an
   eigenvalue. Do not add `H.PosSemidef` (that the energy `0` is the lowest is a separate
   frustration-free fact, family 5).
3. **RingEndpoint `_finrank` theorems** (`mixedEndpoint_periodic_groundSpace_finrank`,
   `mixedEndpoint_periodic_one_groundSpace_finrank`, blueprint `ch30_mpo_mixed_endpoint_comparison.tex:150,159`).
   They have no code consumer and follow from the adjacent `_groundSpace_eq` theorems.
   Recommendation: delete them, point the blueprint at `_groundSpace_eq`, and add the endpoint
   tensor's nonvanishing to that entry.
4. **`mpvSubmodule`.** Abbreviation of `ℂ ∙ mpv A` (19 modules, 71 occurrences, 17 unfolding
   steps). Recommendation: leave it in this family's pull request; it is a definition, not a
   predicate, and replacing it does not remove a lemma that has to be proved twice. Revisit in a
   later sweep that writes `ℂ ∙ mpv A` directly.
5. **Where the characterization theorem lives.**
   `Submodule.finrank_eq_one_iff_exists_eq_span_singleton` has no consumer after step 2.
   Recommendation: do not add it to the library; the blueprint entry it would honour is deleted,
   and the facts are Mathlib's `finrank_span_singleton` and
   `eq_span_singleton_of_mem_of_finrank_eq_one`. If a consumer appears, put it in QICLean
   `Algebra/` (or upstream to Mathlib).
6. **Examples' Hamiltonians as QICLean matrices.** The AKLT and cluster Hamiltonians are linear
   maps on `NSiteSpace`. Recommendation: leave them to the Hamiltonian-spelling sweep (audit §7
   item 6); in this family their survivors are the existing line equations.

### Files

* `New.lean`: characterization theorems, transport theorem, restated uniqueness theorems,
  deformation theorem, consumer rewrites. Elaborated against hot-main with no errors and no
  warnings (`elab_output.txt` is empty). Not elaborated: the HEAD-only form with
  `parentRingInteraction` (in a comment at the end of the file).
* `rewrite.py`, `dryrun.txt`: step 1.
* `applytest/`, `apply_test.diff`: apply-mode test on copies.
* `count.sh`: the module and occurrence counter.

Method note for the inline `finrank = 1` count: a scan of HEAD for lines matching
`finrank ℂ .*= 1` that also mention `ker`, `ground`, `regionParent`, `virtualBond`, excluding
`transferMap` and `adjointMap`; multi-line statements are missed, and the RingEndpoint pair was
added by hand.

## 5. Frustration-freeness

Reference: TNLean e8f8dd3202 (branch `batch/many-body-2`), read from the extraction
`scratchpad/notions/head`. Rows FF1–FF16 are those of
`docs/audits/2026-11-20_generic_many_body_notions.md` §1, re-mapped at e8f8dd3202 (the audit
read `0c76bc5a1`; several rows have since moved or been restated).

### The surviving notions and the QICLean pin

There are two notions, both in QICLean `QICLean/ManyBody/Hamiltonian/FrustrationFree.lean`:

* `ManyBody.Interaction.IsFrustrationFree Φ` (line 77 on QICLean `main`): some nonzero vector
  is a ground vector of every term at energies `e i` with `h_i ≥ e_i`. It is the unnormalized
  notion of PGVWC07 (quant-ph/0608197, `MPSarchive.tex` lines 311–326: "frustration free with
  respect to its ground state φ₀ if the latter minimizes the energy locally") and of SPWC09
  (arXiv:0909.5347, `main.tex` lines 796–808). It is a property of the interaction.
* `ManyBody.Interaction.zeroSpace Φ := ⨅ i, groundSpace (Φ.term i) 0` (line 105): the common
  kernel of the terms. "Ω is a frustration-free ground vector" (normalized form, positive
  terms, local minimum `0`: SPWC09 line 808 "w.l.o.g. equal to 0"; CPGSV21 arXiv:2011.12127,
  `TN-Review-main.tex` lines 537 and 2011) is `Ω ∈ Φ.zeroSpace`. It is a property of a vector.

The audit's §1.3 proposal (`IsFrustrationFree := (∀ i, PosSemidef) ∧ zeroSpace ≠ ⊥`) was not
adopted in QICLean; QICLean keeps the unnormalized definition and links the two by
`isFrustrationFree_of_zeroSpace_ne_bot` (positivity hypothesis), `zeroSpace_eq_groundSpace`,
`mem_zeroSpace_iff`, `mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero`,
`isFrustrationFree_iff_minEigenvalue`, `isFrustrationFree_iff_of_term_eq_sub`. Every TNLean
encoding below is either membership in a zero space or one of these two notions.

**Pin.** TNLean e8f8dd3202 pins QICLean `d65bece6` (`lake-manifest.json`, `lakefile.toml`).
That revision has `IsFrustrationFree` but **not** `zeroSpace`, `mem_zeroSpace_iff`,
`zeroSpace_eq_groundSpace`, `isFrustrationFree_of_zeroSpace_ne_bot` (`git show
d65bece6:…/FrustrationFree.lean`); they entered QICLean in `7324390cc` ("the martingale method,
gaps above the kernel, and commuting parent Hamiltonians"), which is an ancestor of QICLean
`origin/main` = `551c297e0` and of `batch2-circuit` HEAD `80e0a1782`, not of `d65bece6`.
TNLean e8f8dd3202 already uses `zeroSpace` (`MPS/ParentHamiltonian/Defs.lean:381–382`,
`PEPS/AreaLaw/Operators/FrustrationFree/Model.lean:79–154`), and 47 of its `import QICLean.…` lines name
modules absent at `d65bece6` (checked module by module with `git cat-file -e`), all present at
`551c297e0`. **Required pin move: QICLean `551c297e0` (origin/main) or later.** This is a
precondition of e8f8dd3202 itself, not only of this family; declaration-level agreement
with `551c297e0` was not checked.

### Inventory at e8f8dd3202

Counts: modules / occurrences of the name as a word (`count.py`: regex with identifier
boundaries over `TNLean/**/*.lean`, `Archive/` excluded, defining file included), broken down
by directory. "pattern" rows count the files matching the quoted text (`rewrite.py --dry-run`).

| Row | Declaration, `file:line` | Definition (one line) | Source anchor | Use at e8f8dd3202 | Relation to `zeroSpace` / `IsFrustrationFree` |
|---|---|---|---|---|---|
| FF1 | `MPSTensor.IsFrustrationFree`, `MPS/ParentHamiltonian/Defs.lean:373` | `∀ i : Fin N, localTerm A L N i ψ = 0` | PGVWC07 lines 311–326; CPGSV21 line 537 (glossary) | MPS/ParentHamiltonian 5/13 | for `L ≤ N`: `↔ toLp ψ ∈ (parentRingInteraction A hLN).zeroSpace`, `isFrustrationFree_iff_mem_zeroSpace` (`Defs.lean:378`). For `L > N` the terms are `0` and it holds for every `ψ` (the interaction is not formed). Equivalent under `L ≤ N` |
| FF1 (thms) | `parentHamiltonian_frustrationFree` `Basic.lean:243`; `isFrustrationFree_of_mem_chainGroundSpace` `ChainGroundSpace.lean:120`; `HasNNCPHGroundSpace.isFrustrationFree` `Commuting.lean:203`; `IsNNCPHGroundState.isFrustrationFree` `:172`; `bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree` `:317` | statements in FF1 | PGVWC07; CPSV16 Def. 3.9 lines 522–524 | 2/2, 3/3, 1, 1, 1/1 | `parentHamiltonian_frustrationFree` is a pass-through of `localTerm_annihilates_mpv` (`Basic.lean:225`), body `fun i => localTerm_annihilates_mpv A L N hLN i` |
| FF2 | `MPSTensor.IsNNCPHGroundState`, `Commuting.lean:108` | `IsNNCPH A N ∧ IsFrustrationFree A 2 N (mpv A)` | CPSV16 Thm 3.10(iii) line 539 | MPS/ParentHamiltonian 1/10, MPS/RFP 1/2 | **equivalent to `IsNNCPH A N` with no hypothesis**: the second conjunct holds for every `A`, `N` (`isFrustrationFree_mpv`, New.lean, elaborated). Consequently `rfp_implies_nncph_ground_state(_of_leftCanonical)` (`RFP/AppendixBChainCommutation.lean:126,180`) restate `rfp_implies_nncph(_of_leftCanonical)`, and `hasNNCPHGroundSpaces_iff_forall_isNNCPHGroundState_and_groundSpaceSpanning` (`Commuting.lean:252`) restates `…_isNNCPH_…` (`:276`) |
| FF3 | `Decorrelation.HasCommutingParentHam` | — | — | 0 (deleted in `0174d2c62d`) | done |
| FF4 | `TripartiteDecorrelation.CommutingParentHamiltonian` etc. | — | CPSV16 Def. D.2 | 0 in TNLean | done: QICLean `main` `CommutingParentHamiltonian.lean:267`, `HasCommutingParentHamiltonian a b P := ∃ Φ : Interaction X ![bᶜ, aᶜ], (∀ i, IsStarProjection (Φ.term i)) ∧ Commute … ∧ Φ.zeroSpace = range P`, Prop. D.3 at `:461` |
| FF5 | `LinearMap.frustration_free_ham_eq` | — | — | 0 | done (deleted) |
| FF6 | root namespace `FrustrationFree` (martingale method) | — | Nachtergaele 1996 Thm 2.1 | definitions 0 in TNLean (moved to QICLean `main` `ManyBody/Hamiltonian/Martingale/*`); consumers `NestedGroundProjections` 7/15, `martingaleDifference` 7/38, all MPS/ParentHamiltonian | gap family (#10946); its `Interaction` corollary would take `Φ.IsFrustrationFree` and nested regional zero spaces. Not planned here |
| FF7a | `ALVV.complementProd_apply_eq_self_iff`, `MPS/AreaLaw/ALVV/FrustrationFree.lean:31` | product of commuting complementary projections fixes `x` iff each factor kills `x` | ALVV Def. 5.10 | MPS/AreaLaw 2/3 | **assigned to #10944**; listed only |
| FF7b | `ALVV.restrictedTerm` `:50`, `regionalProjection` `:78`, `regionalReplacement` `:112`, `regionalReplacement_frustrationFree` `:189`, `sum_apply_eq_zero_iff` `:117` (private) | abstract families `h : ℕ → E →L[𝕜] E` with `hx : ∀ i < m, h i x = 0` | ALVV arXiv:1602.08828v2 Def. 5.10, Thm 5.14(1) | MPS/AreaLaw 5/52, 5/69, 4/12, 2/2, 1/3 | different notion: a common kernel of an abstract operator family on an inner product space, no sites. Not an encoding of `Interaction.zeroSpace` |
| FF8 | `ALVV.chainTerm` `FrustrationFreeChain.lean:194`, `chainOperator` `:200`, `chainReplacement` `:206`, `chainOperator_apply_eq_zero_iff` `:282`, `chainReplacement_frustrationFree` `:389`, `frustrationFree_regionalReplacement_chain` `:428` | `chainOperator h = ∑ i ∈ range m, toEuclideanCLM (h i)` for a bare family `h : Fin m → Matrix` with `hsupp : ∀ i, IsSupportedOn (h i) (interval L i (i+2))`; hypothesis `hΩ : chainOperator h Ω = 0` | ALVV Def. 5.10, Thm 5.14 | MPS/AreaLaw: `chainOperator` 3/33, `chainTerm` 2/74 (the `chain*` names 3 files/119 occurrences) | with `m = L - 1` the family is a `BondInteraction L q` and `chainOperator_apply_eq_zero_iff` is `zeroVector_tfae` (projections are positive). A second bond-family spelling beside FF9 (decision D3) |
| FF9 | `physicalFrustrationFreeTruncation`, `MPS/AreaLaw/PhysicalFrustrationFreeTruncation.lean:33` | `(∑ bonds outside [a,b)) + (1 − parity product 0) + (1 − parity product 1)` on `Φ : BondInteraction L q` | ALVV `def:FF-tH` lines 1467–1487, `thm:FF-tH` 1543–1550 | MPS/AreaLaw 2/25 | already on `BondInteraction`. Its private `regionalTruncationTerm` (`:79`, index `Fin (L-1) ⊕ Fin 2`) is the term family of an interaction; `physicalFrustrationFreeTruncation_kernel_iff` (`:115`) is "same zero space as Φ" for projection terms |
| FF10 | `PEPS.AreaLaw.FrustrationFree.IsFrustrationFreeGapped`, `PEPS/AreaLaw/Operators/FrustrationFree/Model.lean:67` | structure: `posSemidef`, `le_bound` (`h_X ≤ J`), `norm_eq_one`, `isGapped : IsGapped H 0 Δ`, `zeroSpace_eq : h.zeroSpace = span {Ω}` | frustration-free note `eq:model` (`docs/audits/2026-11-18_finite_range_frustration_free_area_law.tex`) | PEPS/AreaLaw 3/26 (+ the `Sweep` namespace inside it) | already restated on `zeroSpace` (on main since #10936). `iff_model` (`:143`) is the source's formulation for `Δ > 0`. `isFrustrationFree` (`:123`) concludes QICLean's notion. Pass-throughs: `isHermitian` `:97`, `mem_zeroSpace` `:107`, `mulVec_eq_zero` `:111`, `hamiltonian_mulVec_eq_zero` `:116` (decision D2) |
| FF11 | `MPSTensor.parentGroundStateFace`, `MPS/ParentHamiltonian/QuasiLocalParentGroundStateFace.lean:35` | states `φ` of the quasi-local algebra with `φ(τ_a h) = 0` for every `a : ℤ` | Nachtergaele cond-mat/9410110 lines 854–887; CPGSV21 lines 1996–1999 | MPS/ParentHamiltonian 27/46 | different notion: infinite-volume zero-energy states, not vectors. Name already says it. Keep |
| FF12 | AKLV: `aklv_frustrationFree_dimension_and_gap_bounds` (`AKLV/FrustrationFreeGapBounds.lean:34`), `exists_aklv_frustrationFree_chebyshev_filter` (`AKLV/FrustrationFreeFilter.lean:122`), `…_two_filter_approximant`/`…_per_cut_…`/`…_sequential_mps_approximation` (`AKLV/FrustrationFreeMPSApproximation.lean`), `exists_aklv_frustrationFree_physical_entropy_bound` (`AKLV/FrustrationFreeEntropy.lean:51`), `frustrationFree_twoSidedEnergyTruncation_ground_gap` (`AKLV/FrustrationFreeClipping.lean`), `exists_frustrationFree_chain_chebyshev_filter` (`AKLV/ChebyshevProjector.lean:241`) | inline bundle `(Φ : BondInteraction L q) (h0 : ∀ j, 0 ≤ Φ.term j) (h1 : ∀ j, Φ.term j ≤ 1) (hΩ : ‖Ω‖ = 1) (hzero : Φ.hamiltonian *ᵥ ofLp Ω = 0) (hgap : …)` | AKLV arXiv:1301.1162v1 §5 before eq. (4), Thm `t:ent` lines 820–846 | pattern `Φ.hamiltonian *ᵥ WithLp.ofLp Ω = 0`: 5 files / 8; pattern `toEuclideanLin H Ω = 0` (`H := Φ.hamiltonian`): 1 file / 3 | the bond family is already `BondInteraction` (the audit's H1 sweep has landed: `ManyBody.BondInteraction` in 228 MPS/AreaLaw modules). `hzero ↔ Ω ∈ Φ.zeroSpace` **under `h0`** (`hamiltonian_mulVec_eq_zero_iff_mem_zeroSpace'`, New.lean, elaborated) |
| FF12′ | physical detectability: `PhysicalDetectability.lean:367,383,394,407`, `PhysicalDetectabilityGap.lean:42,49`, `PhysicalRangeDetectability.lean:40,56,64`, `PhysicalFrustrationFreeTruncation.lean:121` | `toEuclideanCLM Φ.hamiltonian z = 0` with `hp : ∀ i, IsStarProjection (Φ.term i)` | ALVV `def:DLO`, `thm:FF-tH` | 4 files / 10 | same clause: `↔ z ∈ Φ.zeroSpace` under positivity (`zeroVector_tfae` clause 5) |
| FF13 | PEPS constraint families: `PositiveConstraints.lean:194,285,333`, `LatticeConstraints.lean:99,197,240`, `FiniteSetTruncationGap.lean:78,140`, `AmplificationProof.lean:380,514`, `Amplification/{LocalConstraintProducts:98, LatticeChannelSpatialOmission:152,219,274, ConstraintWordTruncation:397}` | `∀ i, 0 ≤ k i ∧ k i ≤ 1 ∧ k i *ᵥ ofLp Ω = 0` for the filtered constraints `k i`, supported on the connected component of `a i` | OpenAI area law, Prop. 4.3 (`03-quasilocal.tex` lines 220–334) | lattice level 7 files / 15; matrix-level lemmas `Amplification/ConstraintWordLists.lean:80,93`, `ChannelGroundVectors.lean:67,89` on bare `Matrix n n` | the constraints are an `Interaction` with supports the reachable components; then the bundle is `(∀ i, 0 ≤ κ.term i ≤ 1) ∧ Ω ∈ κ.zeroSpace` (definitional, `mem_zeroSpace_iff`). The matrix-level lemmas mention no sites: different (abstract) statements, stay (decision D4) |
| FF14 | `SweepContraction`, `RangeProjection` | — | ALVV §6.1 | definitions moved to QICLean `main` (`Analysis/Projection/SweepContraction.lean`, `Analysis/Support/ProjectionOrder.lean`); the duplicate `QuantumCircuit.supportProj_mem_supportedOperators` is gone, and `ManyBody.supportProj_mem_supportedOperators` (`Sites/Twirl.lean`) is the one statement; the sweep hypotheses are required only below `m` (#10940) | not a frustration-free encoding; done (#10939) |
| FF15 | `regionParentHamiltonian` | — | CPGSV21 lines 2003–2011 | `regionParentHamiltonian` 0 (replaced by `ManyBody.Interaction.ofPlace R h`, `RegionParentInteraction.lean:199–231`). Residual: `ker_regionParentHamiltonian` `:199` (PEPS/ParentHamiltonian 26/43), `place_stateCoeff_eq_zero` `:168` (1/2), `regionParentHamiltonian_stateCoeff_eq_zero` `:225` (1/1) | done for the Hamiltonian; the frustration-free vector statement is `toLp (stateCoeff A) ∈ (ofPlace R h).zeroSpace` (New.lean Part B). `ker_regionParentHamiltonian` names a deleted declaration (rename, decision D5) |
| FF16 | ring/open parent Hamiltonians: `localTerm` `Defs.lean:311` (17/144), `parentHamiltonian` `:318` (29/70) — now `Matrix.toLin'` of `parentRingInteraction A hLN` (`:290`); Euclidean copies `localTermES` `Martingale/Transport.lean:109` (39/288), `parentHamiltonianES` `:167` (68/286), `openParentHamiltonianES` `Martingale/OpenHamiltonian.lean:46` (79/377), `periodicInteractionHamiltonianES` `Martingale/PeriodicInteraction.lean:57` (30/206), `openInteractionHamiltonianES` `Martingale/OpenInteraction.lean:30` (61/236), `obcParentHamiltonian` `VaryingOBCProjectorKernel.lean:138` (5/14) | sums of placed translates of one positive local term | PGVWC07 Thms 9, 11; Nachtergaele (3.12) | as listed | a second representation of the Hamiltonian, tracked by #10948. The frustration-free step repeated on the copies is "a positive sum kills `x` iff every term does": `ProjectionGeometry.apply_eq_zero_of_sum_apply_eq_zero` 6/7, `WeightedPositiveKernel.apply_sum_eq_zero_iff` 10/15 — all instances of `zeroVector_tfae` once the copies are `Interaction.hamiltonian` |

### Verdicts

| Predicate / bundle | Verdict |
|---|---|
| `ManyBody.Interaction.IsFrustrationFree` (QICLean) | **survivor** (notion of the interaction) |
| `ManyBody.Interaction.zeroSpace` (QICLean) | **survivor** (frustration-free ground vectors, normalized form) |
| FF1 `MPSTensor.IsFrustrationFree` | **deleted; clause under `L ≤ N`**: `toLp ψ ∈ (parentRingInteraction A hLN).zeroSpace`. All five consumer modules have `hLN` in scope (checked in `Basic`, `ChainGroundSpace`, `KernelChainGroundSpace`, `Commuting`; `Commuting.lean:320` takes `L N` free and needs `hLN` added, see D1). The `L > N` reading (vacuous) is dropped: no consumer uses it |
| FF2 `MPSTensor.IsNNCPHGroundState` | **deleted with characterization theorem** `isNNCPHGroundState_iff : IsNNCPHGroundState A N ↔ IsNNCPH A N` (no hypothesis; elaborated). Its seven projection lemmas and the two `rfp_implies_nncph_ground_state*` theorems are pass-throughs and go. `HasNNCPHGroundSpace` is restated as `IsNNCPH B N ∧ ker = span` (`hasNNCPHGroundSpace_iff`, elaborated). `IsNNCPH` itself belongs to family 2 (commuting form) |
| FF7b ALVV abstract layer | **different notion** (abstract operator families); keep, candidate for QICLean `Analysis` (audit (b)) |
| FF8 ALVV chain layer | **clause**: with `m = L − 1` it is `BondInteraction` + `zeroSpace`; recommend merging into FF9 (D3) |
| FF9 `physicalFrustrationFreeTruncation` | **restated**: the truncation becomes an `Interaction` (`regionalTruncationInteraction`) whose zero space equals `Φ.zeroSpace` for projection terms (Part B, not elaborated) |
| FF10 `IsFrustrationFreeGapped` | **different notion with a name saying how**: the note's model (frustration free + gapped + unique zero vector + bounded terms), one source, one consumer theorem. Keep; delete pass-throughs (D2) |
| FF11 `parentGroundStateFace` | **different notion** (infinite-volume states); keep the name |
| FF12/FF12′ AKLV and physical-detectability bundles | **clause under positivity**: `hzero : Ω ∈ Φ.zeroSpace` replaces the three Hamiltonian spellings (`zeroVector_tfae`) |
| FF13 PEPS constraint bundle | **clause** on the lattice-level statements (D4); matrix-level lemmas unchanged |
| FF15 PEPS parent vector | **restated**: `toLp (stateCoeff A) ∈ (ofPlace R h).zeroSpace` |
| FF16 ES copies | **dual system**, owned by #10948; the frustration-free step there follows from `zeroVector_tfae` once merged |
| FF3, FF4, FF5, FF6 (defs), FF14 (defs) | **done** at e8f8dd3202 / QICLean `main` |
| FF7a | **assigned to #10944** |

Boundary with family 4 (unique ground states): `IsFrustrationFreeGapped.zeroSpace_eq : h.zeroSpace
= span {Ω}`, `groundSpace_eq`, `ker_parentHamiltonian_eq_chainGroundSpace` and
`HasUniqueGroundState` (G5, #10944) are uniqueness/ground-space statements and are not planned
here; this family only supplies `zeroSpace` membership and `zeroSpace_eq_groundSpace`.
Boundary with the gap family (#10946): every `hgap` (projector form `Δ(1 − |Ω⟩⟨Ω|) ≤ H`,
quadratic form `γ‖y‖² ≤ re⟨y, Hy⟩` in FF8, norm form in FF6/FF16) is theirs.

### Change list

#### Deleted (old → replacement)

| Removed | Replacement | Consumers |
|---|---|---|
| `MPSTensor.IsFrustrationFree` (`Defs.lean:373`) | `WithLp.toLp 2 ψ ∈ (parentRingInteraction A hLN).zeroSpace` | 5 modules / 12 occurrences (MPS/ParentHamiltonian) |
| `MPSTensor.isFrustrationFree_iff_mem_zeroSpace` (`Defs.lean:378`) | none (bridge between the two formulations) | 1 / 4 (defining file) |
| `MPSTensor.parentHamiltonian_frustrationFree` (`Basic.lean:243`) | `MPSTensor.toLp_mpv_mem_zeroSpace` | 2 / 2 |
| `MPSTensor.isFrustrationFree_of_mem_chainGroundSpace` (`ChainGroundSpace.lean:120`) | `MPSTensor.zeroSpace_parentRingInteraction_eq` (with `ker_parentHamiltonian_eq_chainGroundSpace`) | 3 / 3 (`BlockDiagonalChainGroundSpace:83`, `KernelChainGroundSpace:70`) |
| `MPSTensor.bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree` (`Commuting.lean:317`) | `…_of_forall_mem_zeroSpace` (Part B) | 1 / 1 |
| `MPSTensor.IsNNCPHGroundState` (`Commuting.lean:108`) | `MPSTensor.IsNNCPH` | 2 modules / 12 |
| `IsNNCPHGroundState.isNNCPH`, `.isFrustrationFree`, `IsNNCPH.isNNCPHGroundState`, `HasNNCPHGroundSpace.isNNCPHGroundState`, `HasNNCPHGroundSpace.isFrustrationFree` (`Commuting.lean:165–206`) | none (projections of a deleted conjunction) | defining file only, plus `RFP/AppendixBChainCommutation.lean:131,184` |
| `hasNNCPHGroundSpaces_iff_forall_isNNCPHGroundState_and_groundSpaceSpanning` (`Commuting.lean:252`) | `hasNNCPHGroundSpaces_iff_forall_isNNCPH_and_groundSpaceSpanning` (`:276`) | 1 (`RFP/NNCPHGroundSpace.lean:64`) |
| `rfp_implies_nncph_ground_state_of_leftCanonical`, `rfp_implies_nncph_ground_state` (`RFP/AppendixBChainCommutation.lean:126,180`) | `rfp_implies_nncph_of_leftCanonical`, `rfp_implies_nncph` | 1 (`RFP/NNCPHGroundSpace.lean:66`) |
| `IsFrustrationFreeGapped.isHermitian`, `.mem_zeroSpace`, `.mulVec_eq_zero`, `.hamiltonian_mulVec_eq_zero` (`Model.lean:97–118`), if D2 is taken | `(hff.posSemidef X).isHermitian`, `hff.zeroSpace_eq ▸ mem_span_singleton_self Ω`, `mem_zeroSpace_iff`, `mem_zeroSpace_iff_hamiltonian_mulVec_eq_zero` | pattern `hff.<name>`: 4 files / 19 (PEPS/AreaLaw/FrustrationFree) |
| `place_stateCoeff_eq_zero`, `regionParentHamiltonian_stateCoeff_eq_zero` (`RegionParentInteraction.lean:168,225`) | `toLp_stateCoeff_mem_zeroSpace_ofPlace` | 1 / 3 |

#### New or restated statements (`New.lean`)

Elaborated against hot-main (Part A, exit 0, `elab.txt`):

* `ManyBody.Interaction.zeroVector_tfae` — for positive terms, the six spellings of zero energy
  are equivalent (TFAE). Proposed for QICLean `FrustrationFree.lean`.
* `ManyBody.Interaction.hamiltonian_mulVec_eq_zero_iff_mem_zeroSpace` — the clause in Loewner
  form `∀ i, 0 ≤ Φ.term i` (the AKLV/ALVV spelling of positivity).
* `ManyBody.Interaction.isFrustrationFree_of_mem_zeroSpace` — a nonzero zero vector of positive
  terms gives `IsFrustrationFree`.
* `MPSTensor.isFrustrationFree_mpv` (no hypothesis), `MPSTensor.isNNCPHGroundState_iff`,
  `MPSTensor.hasNNCPHGroundSpace_iff`.

(Part A uses a stand-in `zeroSpace'` with the body of QICLean `main`'s `zeroSpace`, because
hot-main's QICLean `271884e2` lacks it.)

Written, not elaborated (Part B; needs e8f8dd3202 and QICLean `main`):

* `MPSTensor.posSemidef_parentRingInteraction_term` and
  `MPSTensor.toLp_mem_ker_parentHamiltonian_iff` — both cited by `docs/glossary.md` §"Parent
  Hamiltonians on the ring" (lines 1497–1502) **but absent at e8f8dd3202** (no match under
  `TNLean/`).
* `MPSTensor.toLp_mpv_mem_zeroSpace`, `MPSTensor.isFrustrationFree_parentRingInteraction`
  (hypothesis `mpv A ≠ 0`: the PGVWC07 statement "every MPS is the ground state of a
  frustration-free parent Hamiltonian", lines 311–330), `MPSTensor.zeroSpace_parentRingInteraction_eq`,
  `…_of_forall_mem_zeroSpace`.
* `aklv_frustrationFree_dimension_and_gap_bounds` restated (template for FF12).
* `regionalTruncationInteraction` and `zeroSpace_regionalTruncationInteraction` (FF9).
* `TNLean.PEPS.toLp_stateCoeff_mem_zeroSpace_ofPlace` (FF15).

#### Blueprint labels affected (`\lean{…}` of the names above)

* `def:is_frustration_free` (`ch13_parent_hamiltonian_injective_ground_spaces_local_parent_interaction.tex:3386`) → retag to `ManyBody.Interaction.zeroSpace` / the parent interaction; `lem:parent_hamiltonian_ff` (`:3438`) → `MPSTensor.toLp_mpv_mem_zeroSpace`, and a new entry for `isFrustrationFree_parentRingInteraction`.
* `def:is_nncph_ground_state` (`ch13_parent_hamiltonian_commuting_gap_local_terms.tex:368`) → delete or retag to `isNNCPHGroundState_iff`; `rem:nncph_ground_spaces_decomposition` (`:455`) drops six tags; `thm:chain_ground_space_implies_frustration_free` (`:515`) → `zeroSpace_parentRingInteraction_eq`.
* `thm:rfp_implies_nncph_ground_state` (`ch13_parent_hamiltonian_commuting_gap_rfp_ground_spaces.tex:317`) and `thm:left_canonical_rfp_chain_commutation` (`ch13_…_appendix_b_commutation.tex:350`) → retag to `rfp_implies_nncph*`; the `bntMPSVectorSpan_…_frustrationFree` tag in the same chapter.
* `thm:frustration_free_area_law_model_gapped` (`ch24_peps_area_law_frustration_free.tex:86`) drops the pass-through tags if D2 is taken.
* `thm:peps_region_parent_frustration_free` (`ch24_peps_region_parent_hamiltonian.tex:96`) → `toLp_stateCoeff_mem_zeroSpace_ofPlace`.
* `thm:physical_ff_regional_kernel` (`ch35_physical_detectability.tex:219`) → `zeroSpace_regionalTruncationInteraction`; `def:alvv_ff_chain_operators`, `lem:alvv_ff_chain_comparison`, `thm:alvv_ff_chain_replacement` (`ch35_alvv_frustration_free.tex:314,355,408`) under D3.
* `lem:aklv_frustration_free_filter`, `lem:aklv_ff_dimension_gap` (`ch35_aklv_frustration_free_{filter,mps}.tex`): statement text unchanged (`hΩ` is already "every term annihilates Ω"), tags unchanged.

#### Glossary

* §"Parent Hamiltonians on the ring" (`docs/glossary.md:1478–1506`): the `MPSTensor.IsFrustrationFree` entry is replaced by an entry on `MPSTensor.parentRingInteraction`, stating that frustration-free ground vectors are its zero space and pointing to QICLean `zeroSpace`/`IsFrustrationFree`. The "Sanctioned bridges" line cites two declarations that do not exist (`toLp_mem_ker_parentHamiltonian_iff`, `posSemidef_parentRingInteraction_term`); they are added by this plan (Part B).
* Table rows 3283–3284 (`IsFrustrationFreeGapped`, `FrustrationFreeAreaLaw`): unchanged unless D2 changes the structure.

#### Paper-gap notes

* `docs/paper-gaps/cpsv16_nncph_ground_state_scope.tex` (lines 85, 102, 119, 282, 288) names `IsNNCPHGroundState`, the `_isNNCPHGroundState_` iff and `rfp_implies_nncph_ground_state*`. Its "Scope restriction (ground vector)" says the predicate records commutation and zero energy of `V^{(N)}(A)`; the zero-energy part is automatic, so the restriction is just "length-two commutation without the spanning clause", already the content of `IsNNCPH`. Update the note and the docstring marker at `Commuting.lean:103`.
* No other note references a family-5 name (grep over `docs/paper-gaps/*.tex`).

#### Bridge modules

None to delete: the only bridge lemma is `isFrustrationFree_iff_mem_zeroSpace` (inside `Defs.lean`). No module is named for a frustration-free bridge.

### Order of application

1. **QICLean pin move to `551c297e0` or later** (precondition of e8f8dd3202 itself). Optionally
   add `zeroVector_tfae` and the Loewner-form clause to QICLean `FrustrationFree.lean` in the
   next QICLean pull request (independent of the rest; the TNLean steps can use the existing
   pairwise lemmas instead).
2. **FF2** (independent, small): `Commuting.lean` + 2 RFP modules. `Commuting.lean` has 137
   transitive importers; the RFP modules 3. Mechanical part: `rewrite.py` rules FF2-a…e
   (6 occurrences in 2 files), then hand edits in `Commuting.lean` (16 occurrences).
3. **FF1** (wide rebuild): `Defs.lean` has 1195 transitive importers, `Basic.lean` 997,
   `ChainGroundSpace.lean` 916. Edits are in 6 modules; add the Part B theorems to `Defs.lean`/
   `Basic.lean`, delete `IsFrustrationFree`. Do it together with FF2 (both touch
   `Commuting.lean`) and, if possible, in the same pull request as the #10948 parent-interaction
   work, to pay the rebuild once.
4. **FF12/FF12′** (independent, narrow: `AKLV/*`, `Physical*`; ≤ 8 transitive importers each):
   restate `hzero`; proofs convert with one `have`.
5. **FF9 then FF8** (D3): FF9 interaction first, then retire the chain layer.
6. **FF15** (narrow at the lemma level, but `RegionParentInteraction.lean` has 222 transitive
   importers) and **FF10 pass-throughs** (7 transitive importers).
7. **FF13** after D4.

### Open decisions

* **D1. `hLN` in `bntMPSVectorSpan_le_ker_parentHamiltonian_of_forall_frustrationFree`.** Its
  `L N` are free; the zero-space form needs `L ≤ N`. Recommendation: add `hLN`; the only
  consumer chain (Def. 3.9) has `N > L`.
* **D2. `IsFrustrationFreeGapped`.** Keep as the model of one source (it bundles distinct
  notions, has `iff_model`, and a dot-notation API used by `Sweep`). Recommendation: keep the
  structure, delete the four pass-throughs (`isHermitian`, `mem_zeroSpace`, `mulVec_eq_zero`,
  `hamiltonian_mulVec_eq_zero`); keep `isFrustrationFree`, `groundSpace_eq`, `gap`, `iff_model`,
  which combine two facts.
* **D3. Two formalizations of ALVV `def:FF-tH`.** FF8 (`chainReplacement`, bare `h : Fin m →
  Matrix` with bond intervals `Ico a b`) and FF9 (`physicalFrustrationFreeTruncation` on
  `BondInteraction`, site interval `[a, b)`, i.e. bonds `Ico a (b−1)`) define the same operator
  for `m = L − 1` up to that index shift and matrix/operator form (by inspection of the
  definitions; not proved). Recommendation: keep FF9 as the interaction form, prove the FF8
  statements on it, delete the chain layer (3 files, 119 occurrences of `chain*`); FF7b stays.
* **D4. FF13.** The filtered constraints are quasi-local (supported on a connected component),
  so their `Interaction` has non-local supports. Recommendation: restate only the lattice-level
  conclusions as `Ω ∈ κ.zeroSpace` for `κ : Interaction` with supports the reachable components;
  leave `ConstraintWordLists`/`ChannelGroundVectors` on bare matrices (they mention no sites).
* **D5. `ker_regionParentHamiltonian`** names a deleted declaration (26 modules). Recommendation:
  rename to `ker_hamiltonian_ofPlace` in the same pull request as FF15; mechanical.
* **D6. Proposed QICLean addition** `zeroVector_tfae`. Recommendation: add it (it collects
  existing lemmas into the source's proposition and replaces three spellings); not required for
  the TNLean steps.

### Measurement notes

* Module/occurrence counts: `count.py` over the extraction of e8f8dd3202 (identifier-boundary
  regex, `Archive/` excluded). Pattern counts and rule counts: `rewrite.py --dry-run`
  (`dryrun.txt`).
* Transitive importers: reverse closure of `^import TNLean…` lines over the same extraction.
* Pin facts: `git cat-file -e <rev>:<path>` and `git merge-base --is-ancestor` in
  `QICLean/worktrees/batch2-circuit`.
* Blueprint labels: environments whose `\lean{…}` contains a family name, in
  `blueprint/src/chapter/*.tex` of the extraction.

## 6. Injectivity and normality

**Status: applied** in #11011 (round 1), with the QICLean side in LionSR/QICLean#1230 (`HasEventuallyFullWordSpan` replaced by `IsNormal`). The inventory, verdicts and change list are in the history of this file.

## 7. Further families found by the dual-system test

### Method and what was excluded

Four scans over the HEAD extraction (`TNLean/`, without `Archive/`):

1. Module names containing `Bridge`, `Compat`, `Equiv`, `Iff`, `Legacy`, `Alt`, `Literal` or `Raw`:
   85 modules. Read from their module docstrings, all but the ones below name a mathematical
   object (matrix product unitary equivalence, local equivalence of pure states, semi-regular
   representations, compatible local states of the quasi-local algebra, circuit conversion) or a
   proof step; they are not dual systems. `MPS/AreaLaw/CanonicalIntervalRaw*` ("literal original
   target history") belongs to the area-law program and was not examined further.
2. Theorems named `is…_iff_is…`/`has…_iff_…` between two project predicates (`fam7_sweep/scan.py`,
   output `iff.tsv`): 16, of which 5 have no hypothesis binder. Those relating two formulations of
   one notion are families S1, S2 and S3 below; the others are characterizations with a
   hypothesis (`hasTrivialGauge_iff_*` of the L-symbol layer, `isWeakOnSiteSymmetry_iff_…`, the
   `basisDirectSum` clauses of the renormalization theorems) and are already in the form the rule
   asks for.
3. Predicate names (`Is…`, `Has…`) defined more than once (`dupnames.txt`): 15 names. Different
   objects with local names (`IsBondMatchedPair` on two example alphabets, `HasExteriorBufferLength`
   for fusion and for action reductions, `IsConsistent`, `IsNormalized`, `IsAllowed`, …) need
   nothing. The real duplicates are S1 (`IsZCL`), S4 (`HasBoundedChange`,
   `HasSourceBoundedChange`) and S5 (`HasPEPSApproximation`). `IsWeightNormalized` (canonical form
   and sector suppliers) belongs to family 1.
4. `PASS_THROUGH` of `scripts/check_pass_through_declarations.py` lists six lemma pass-throughs and
   no predicate.

Counts are modules (files) containing the name as a whole word, and occurrences, in the HEAD
extraction, measured with `fam7_sweep/cnt.sh`.

### S1. Idempotent transfer maps: five names for one notion

| Name | Definition | Source anchor | Modules (occ.) |
|---|---|---|---|
| `MPSTensor.IsTransferIdempotent A` (`MPS/RFP/Defs.lean:51`) | `transferMap A ∘ₗ transferMap A = transferMap A`, definitionally `IsIdempotentElem (Kraus.transferMap A)` | "transfer-map criterion" for CPSV16 Def. `defRFP` | 40 (147): MPS/RFP 25, MPS/MPDO 8, MPS/Examples 4, MPS/Symmetry 2, MPS/Preparation 1 |
| `MPSTensor.HasPhysicalBlockingIsometry A` (`MPS/RFP/Defs.lean:39`) | `∃ U, Uᴴ U = 1 ∧ ∀ i₁ i₂, A i₁ A i₂ = ∑ j U (i₁,i₂) j • A j` | CPSV16 eq. `AA=A`, Def. `defRFP`, lines 398–424 | 5 (13) |
| `MPSTensor.IsLocallyOrthogonal A` (`MPS/RFP/ZeroCorrelationLength.lean:174`) | `IsTransferIdempotent A` | Scope restriction of CPSV16 Def. 3.5 (the source notion is `IsBNTLocallyOrthogonal`) | 1 (5) |
| `MPSTensor.IsZCL A` (`…/ZeroCorrelationLength.lean:255`) | `IsLocallyOrthogonal A ∧ IsCID A` | Scope restriction of CPSV16 Def. 3.6 | 4 (8 incl. examples) |
| `MPOTensor.IsZCL M` (`MPS/MPDO/ZCL.lean:62`) | `transferMap M ∘ₗ transferMap M = transferMap M` (doubled index) | glossary: "not the physical-trace ZCL diagram of CPSV16 Def. 4.2" | 10 (35): MPS/MPDO 10 |

Proved relations, all without hypothesis:
`isTransferIdempotent_iff_hasPhysicalBlockingIsometry` (`RFP/Defs.lean:166`),
`zcl_iff_idempotent_transfer : IsZCL A ↔ IsTransferIdempotent A` (`ZeroCorrelationLength.lean:323`;
the content is idempotence ⇒ `IsCID`), `IsLocallyOrthogonal = IsTransferIdempotent` by definition,
`isZCL_iff_toMPSTensor_isTransferIdempotent` (`MPDO/ZCL.lean:68`, by `rw`),
`toMPOTensor_isZCL_iff_isTransferIdempotent` and `toMPOTensor_isZCL_iff_mps_isZCL`
(`MPDO/PureRecovery.lean:86,93`).

Verdict.

- Survivor: `MPSTensor.IsTransferIdempotent`, redefined as `IsIdempotentElem (Kraus.transferMap A)`
  so that Mathlib's idempotent API applies by unfolding (it already holds by `Iff.rfl`).
- `HasPhysicalBlockingIsometry`: equivalent with no hypothesis; deleted. The source's Definition
  `defRFP` is honoured by the characterization theorem `isTransferIdempotent_iff_exists_isometry`
  with the isometry clause written out (blueprint `def:physical_blocking_isometry` becomes the
  statement of `thm:physical_blocking_isometry_iff_transfer_idempotence`).
- `IsLocallyOrthogonal`: an abbreviation; deleted. Its Scope-restriction marker is obsolete because
  nothing claims to be Definition 3.5 any more; the source notion stays `IsBNTLocallyOrthogonal`.
- `MPSTensor.IsZCL`: equivalent with no hypothesis; deleted, with `IsTransferIdempotent.isCID` as
  the theorem carrying the content of `zcl_iff_idempotent_transfer`. The source's Definition 3.6
  remains `IsBNTZCL`/`IsPositiveGapBNTZCL`.
- `MPOTensor.IsZCL`: the same statement at `M.toMPSTensor`, and its name claims a notion (ZCL) the
  glossary says it is not; deleted, callers write `MPSTensor.IsTransferIdempotent M.toMPSTensor`.
- `IsCID` is a different notion (virtual-insertion surrogate, vacuous without a positive-definite
  fixed point) and keeps a name, but the name should say how it differs from `IsPhysicalCID`:
  proposed `IsVirtualCID` (1 module, 9 occ.).

Change list: 4 predicates deleted, 1 redefined, 1 renamed; theorems removed
`isTransferIdempotent_iff_hasPhysicalBlockingIsometry` (replaced by the written-out
characterization), `zcl_iff_idempotent_transfer` (replaced by `IsTransferIdempotent.isCID`),
`isZCL_iff_toMPSTensor_isTransferIdempotent`, `toMPOTensor_isZCL_iff_isTransferIdempotent`,
`toMPOTensor_isZCL_iff_mps_isZCL` (no successor; both sides are the survivor), and the renames
`ghz_isZCL`, `clusterBlocked_isZCL`, `clusterBlockedRMP_isZCL` → `…_isTransferIdempotent`,
`TransferRetractData.isZCL`, `transferRetractData_one_iff_isZCL`,
`blockedTransferMap_eq_transferMap_of_isZCL`, `blockedTransferMap_idempotent_of_isZCL`,
`transferRetractData_of_isZCL`, `hasBlockedAdjointFixedPointAlgebraTower_of_isZCL_of_isTP_of_posDef_fixed`,
`exists_hasBlockedAdjointFixedPointAlgebraTower_not_isZCL`, `exists_isPRFP_not_isZCL` (`isZCL` →
`isTransferIdempotent`). Consumers: 48 modules (union of the names above and of the theorem names) in MPS/RFP, MPS/MPDO, MPS/Examples, MPS/Symmetry,
MPS/Preparation (union of the rows above). Blueprint labels: `def:physical_blocking_isometry`,
`thm:physical_blocking_isometry_iff_transfer_idempotence`, `eq:corr_physical_blocking_isometry`,
`thm:renormalization_flow` (ch26 physical blocking); `def:is_locally_orthogonal`,
`def:is_zcl`, `def:is_cid`, `thm:zcl_iff_idempotent_transfer` (ch26 zero correlation length);
`def:mpo_is_zcl`, `thm:mpo_is_zcl_iff_to_mps_rfp` (ch21 foundations); `eq:rfp_transfer_retract`
(ch21 fusion isometries); the ch15 GHZ entry `MPSTensor.ghz_isZCL` and the ch21 entries of
`toMPOTensor_isZCL_*`. Glossary: `MPOTensor.IsZCL` removed, `MPOTensor.IsSourceZCL` and
`MPOTensor.TransferRetractData` caveats rewritten. Paper-gap note to update:
`docs/paper-gaps/cpsv16_pure_zcl_local_orthogonality_scope.tex` (the single-block convention it
documents disappears; it keeps only the statement that the BNT-level theorem is
`IsPositiveGapBNTZCL`). Rebuild: `MPS/Transfer/RenormalizationFixedPoint/Defs.lean` is imported by most of `MPS/RFP` and
`MPS/MPDO`; one change.

### S2. Deterministic sequential generation: two names

`MPSPreparation.IsTransitionGenerated` (`MPS/Preparation/SequentialTransition.lean:189`; 2 modules,
7 occ.) and `IsDeterministicallyGenerated` (3 modules, 13 occ.) are equivalent under `[NeZero d]`
only, an instance, by `isTransitionGenerated_iff_isDeterministicallyGenerated` (`:371`). Verdict:
`IsTransitionGenerated` is deleted; arXiv:quant-ph/0608197 scheme 3 (lines 1555–1567) becomes the
written-out characterization `isDeterministicallyGenerated_iff_exists_transition`.
`IsTransitionInteraction` stays (a property of the interaction, a different object). Blueprint:
`def:seqanc_transition` turns into the statement of `thm:seqanc_transition_deterministic`
(ch31). Glossary entry "`IsTransitionInteraction` and `IsTransitionGenerated`" shortened.
Consumers: `SequentialTransition.lean`, `SequentialResources.lean:337`.

### S3. Flatness of torus bond labels: two conventions

`TNLean.PEPS.IsTorusBondFlat p` (`PEPS/TorusBondFlatConnection.lean:37`; 6 modules, 23 occ.,
all PEPS) and `IsTorusFlat a b` (`PEPS/TorusParallelSection.lean:115`; 10 modules, 32 occ.: PEPS 4,
PEPS/ParentHamiltonian 5, PEPS/Examples 1) are flatness of one group-valued connection, the first
with the vertical labels in the insertion convention, the second as transports:
`isTorusBondFlat_iff_isTorusFlat : IsTorusBondFlat p ↔ IsTorusFlat p.1 (fun v ↦ (p.2 v)⁻¹)`, no
hypothesis. The gauge lemmas (`IsTorusBondFlat.torusBondGauge`,
`isTorusBondFlat_torusBondGauge_iff`, `isTorusBondFlat_closure_iff`) are proved for the first
only, the transport lemmas for the second only. Verdict: one predicate. Recommendation: keep
`IsTorusFlat` (more consumers, and the parallel-section theory is stated on it) and delete
`IsTorusBondFlat`; the native convention is honoured by `isTorusFlat_iff_bond`, and the three gauge
lemmas are restated on `IsTorusFlat p.1 (p.2 ·)⁻¹`. Blueprint: `eq:peps_bond_flat`,
`eq:peps_bond_gauge`, `thm:peps_bond_flat_transport`, `thm:peps_bond_tree_closure`
(ch24 four-cut geometry). Glossary entry "`IsTorusParallelSection` and `IsTorusFlat`" gains the
characterization. Assigned with F1 (the PEPS split) so that the module is touched once.

### S4. Bounded changes of sheet stacks: a named instance with restated lemmas

`TNLean.PEPS.EncodedFrame.HasBoundedChange` (`PEPS/Approximation/SheetStackChange.lean:86`) and
`HasSourceBoundedChange` (`…/SheetStackSourceBoundedChange.lean:52`) are
`Lattice.HasBoundedChange` and `Lattice.HasSourceBoundedChange` (`Lattice/Sheet/StackChange.lean:268`,
`StackSourceBoundedChange.lean:71`) at `ref := fun F ↦ F.regRef Ω`, but their bodies restate the
existential instead of applying the general predicate, so the general lemmas do not apply by
unfolding; 14 lemmas are re-proved as one-line forwarders (`mono`, `of_perm`, `perm_left`,
`perm_right`, `liftOne`, `liftTwo`, `exists_isBoundedChange_of_frame_eq`, and the same seven for the
source-bounded form). `Lattice/Sheet/SheetStack.lean:62,70` already has the correct form
(`abbrev … := Lattice.HasBoundedChange (refFamily Ω) …`). Consumers: 14 modules
(PEPS/Approximation 10, Lattice/Sheet 2, MPS/AreaLaw 2). Verdict: a named special case is kept
only if it is defined by the general predicate: redefine both PEPS predicates as applications of
the Lattice ones, delete the 14 forwarders (dot-notation callers then resolve to the Lattice lemmas
by unfolding; 9 explicit-name calls are rewritten), keep the frame-specific theorems. Blueprint:
`def:peps_bounded_change`, `thm:peps_bounded_change_closure`, `thm:peps_protocol_event_segments`
(ch24 sheet stacks) point to the Lattice declarations for the closure statements. Not checked in
Lean (the dot-notation resolution after the redefinition needs the build).

### S5. Approximation by a PEPS: three formulations

`TNLean.PEPS.Approximation.HasPEPSApproximation` (`PEPS/Approximation/Basic.lean:83`, the native
target), `Approximation.Pinned.HasPEPSApproximation` (`SourceApproximation.lean:32`, adapted from an
external development with its own `State`, `Vertex`, `LocalTensor`, `Tensor`, `contractPEPS`) and
the vector form `Vector.PhaseErrorAtMost`, with one-directional transfer theorems
(`hasPEPSApproximation_of_pinned`, `hasPEPSApproximation_of_vector`, `…_max`). 7 modules use the
`Pinned` namespace, 11 modules the predicate name. Verdict: the native predicate survives; the
`Pinned` and `Vector` copies are a second system for the statement of polynomial-PEPS Theorem 1.1
and their configuration and state types are copies of the kind #10944 E3 deletes. Recommendation:
delete them together with E3, rewriting the two modules that consume them
(`PinnedNestedFilters`, `PinnedZeroFloorOptimizer`, and the transfer theorems of `SourceApproximation`, `SquareGridSource`, `SquareGridColumn`, `SquareGridContraction`, `RegionalStates`) on the native types; blueprint
`def:peps_source_approximation_constraints` (ch24 square grid) and the entries of
`ch24_peps_edge_crossing_budget.tex` that name `Pinned.*`.

### Ranking by consumers touched

S1 48 modules; S5 17 (modules naming `Pinned.`, `HasPEPSApproximation` or `PhaseErrorAtMost`); S3 15; S4 14; S2 3.

### Scriptable part

S1's renames of theorem names (`…isZCL…` → `…isTransferIdempotent…` in the twelve names above)
and of `HasPhysicalBlockingIsometry`-free call sites are token renames; the replacement of
`MPOTensor.IsZCL M` by `MPSTensor.IsTransferIdempotent M.toMPSTensor` and of `IsZCL A` by
`IsTransferIdempotent A` needs the argument and the namespace (MPS and MPO uses of the bare name
`IsZCL` coexist), and is done by hand in 15 modules. `fam7_sweep/rewrite.py` performs the token
renames and reports the remaining occurrences per rule.
