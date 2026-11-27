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

Plan items F2 ("one structure for the commuting form") and F4 (one definition per
notion). Reference commit e8f8dd3202. All paths below are relative to the
repository root; `MPDO/` abbreviates `TNLean/MPS/MPDO/`.

### Source

arXiv:1606.00608 (CPSV16), `Papers/1606.00608/MPDO-22-12-17-2.tex`.

* Definition 4.8 (`defrhoNComm`, lines 829--850): a density operator of `N` spins
  is a Gibbs state of a nearest-neighbour commuting Hamiltonian (GSNNCH) if
  `ρ^{(N)} ∝ ⊕_x n_x ∏_j τ_j(B^{(x)})` (equation `rhoNCommv2`, lines 843--850), with
  natural multiplicities `n_x`, `B^{(x)} ≥ 0` on two sites, `[B^{(x)}, τ_1 B^{(x)}] = 0`,
  and mutually orthogonal one-site spaces for distinct `x` (lines 838--842). The
  definition concerns one chain length.
* Proposition C.8 (`3to4`, lines 1569--1594, Case I "`K` injective", line 1374):
  if `K` satisfies SAL then `σ^{(N)}(K) ∝ ∏_n B_{n,n+1}` (equation `expression`,
  lines 1571--1576), `B_{n,n+1} ≥ 0` acting on nearest neighbours and commuting.
  The proof builds one bond `B` from the operators `η_{k,h}`, the same for every `n`
  and every `N`.
* Proposition `4to2` (lines 1597--1619): if `K` generates operators "of the form
  (`expression`)" and has ZCL, then it satisfies SAL. Line 1567 announces the
  equivalence of the two. The reading "one bond for every chain length" is
  recorded in `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`, lines 35--39.
* Equation `ApprhoNComm` and Proposition `prop3to4` (lines 1641--1665, 1786--1796):
  the GSNNCH form of a simple tensor, assembled from the commuting forms of the
  normal blocks on orthogonal sectors.

### Inventory

Counting method: modules are files under `TNLean/` (excluding `TNLean/Archive/`
and the root `TNLean.lean`) of the HEAD extraction matched by
`grep -rlw --include='*.lean' NAME TNLean`; occurrences by `grep -ow` over those
files (`-w` treats `.` as a boundary, so dotted uses are counted). Every use is in
`MPS/MPDO` except where stated.

| Declaration (file:line) | Definition, one line | Source anchor in docstring | Modules | Occ. |
|---|---|---|---|---|
| `CommutingFormData d N` (`MPDO/CommutingForm.lean:195`) | `hN : 2 ≤ N`, `bond`, `bond_pos : bond.PosSemidef`, `bond_comm : ∀ i j : Fin N, τ_i B τ_j B = τ_j B τ_i B`; with `bondAt`, `product`, `Realizes ρ := ∃ c > 0, ρ = c • product` | none (Section 4.4/C.2 in module header) | 3 | 19 |
| `HasCommutingForm M` (`CommutingForm.lean:247`) | `∀ N ≥ 2, ∃ data : CommutingFormData d N, data.Realizes (mpo M N)` (bond may depend on `N`) | "weaker than 4to2, lines 1597--1619" | 2 | 6 |
| `TranslationInvariantBondData d` (`MPDO/CommutingFormBridge.lean:60`) | `bond`, `bond_pos`, `bond_comm : ∀ {N} (hN : 2 ≤ N) i j, τ_i B τ_j B = τ_j B τ_i B` | "chain-independent ingredient of `ρ = c ∏ B_{i,i+1}`" | 12 | 76 |
| `TranslationInvariantBondData.toCommutingFormData` (`CommutingFormBridge.lean:80`) | the same bond read at one length | — | 10 | 36 |
| `EtaLocalStructureData M` (`CommutingFormBridge.lean:136`) | `bondData : TranslationInvariantBondData d`, `realizes_mpo : ∀ N hN, (bondData.toCommutingFormData hN).Realizes (mpo M N)` | C.8, lines 1569--1594 | 19 | 76 |
| `GSNNCHData d N` (`CommutingForm.lean:289`) | sectors `x`, multiplicities, orthogonal one-site projections, positive supported bonds `B^{(x)}`, `[τ_0 B^{(x)}, τ_1 B^{(x)}] = 0`; `Realizes ρ := ∃ c > 0, ρ = c • ∑_x n_x ∏_j τ_j B^{(x)}` | Def. 4.8, lines 829--850 | 7 | 73 |
| `HasGSNNCHFormAt ρ`, `HasGSNNCHForm M` (`CommutingForm.lean:395, 403`) | `∃ data, data.Realizes ρ`; `∀ N ≥ 2, HasGSNNCHFormAt (mpo M N)` | Def. 4.8 | 2; 7 | 13; 10 |
| `IsGSNNCHAt ρ`, `IsGSNNCH M` (`CommutingForm.lean:410, 417`) | `ρ ≥ 0 ∧ tr ρ = 1 ∧ HasGSNNCHFormAt ρ`; `∀ N ≥ 2, IsGSNNCHAt (normalizedMPO M N)` | Def. 4.8 | 2; 5 | 5; 11 |
| `OrthogonalCommutingSectorFamily K` (`MPDO/GSNNCHOrthogonalSectors.lean:58`) | orthogonal projections `P_s`, `bondData : Fin g → TranslationInvariantBondData d`, supports, `mpo (K s) N = product` (scalar one) | Def. 4.8; `prop3to4` (scope restriction) | 5 | 27 |
| `ProportionalOrthogonalCommutingSectorFamily K` (`GSNNCHOrthogonalSectors.lean:98`) | the same with `(... ).Realizes (mpo (K s) N)` (positive scalar) | `ApprhoNComm`, lines 1641--1665 | 2 | 18 |
| `PhysicalSectorFactorization K` (`MPDO/PhysicalSectorFactorization.lean:54`) | the factorization `σ̃ = ⊕ ⊗_n η_{k_n,k_{n+1}}` of equation `sigmaNK2` | C.2, lines 1581--1590 | 114 (MPS/MPDO 108, MPS/Symmetry 5, aggregator 1) | 955 |
| `commutingBoundaryAlgebra M` (`MPDO/Boundary.lean:76`) | `Subalgebra.centralizer ℂ (Set.range M.toMPSTensor)` | arXiv:2504.16985, lines 175--182 | 10 (MPS/MPDO 4, MPS/Symmetry 6) | 22 |

Proved relations at HEAD (all without hypotheses unless stated):

* `TranslationInvariantBondData.toCommutingFormData` (`CommutingFormBridge.lean:80`):
  a length-independent bond gives per-length data at each `N ≥ 2`.
* `EtaLocalStructureData.hasCommutingForm` (`:208`) and the pass-through
  `hasCommutingForm_of_etaLocalStructure` (`:216`): `EtaLocalStructureData M → HasCommutingForm M`.
  No converse (the bond of `HasCommutingForm` may vary with `N`).
* `EtaLocalStructureData.hasGSNNCHForm` (`:203`) and the pass-through
  `hasGSNNCHForm_of_etaLocalStructure` (`:222`).
* `GSNNCHData.ofCommutingFormData` (`CommutingForm.lean:359`),
  `CommutingFormData.hasGSNNCHFormAt_of_realizes` (`:428`): per-length data realizing `ρ`
  gives a one-sector GSNNCH presentation.
* `GSNNCHData.bondAt_comm` (`MPDO/GSNNCHSectorSum.lean:115`): at a fixed length,
  commutation of the two neighbouring translates implies commutation of all
  translates. Hence the field `bond_comm` of `CommutingFormData` and the field
  `neighboring_comm` of `GSNNCHData` say the same thing about one bond.
* `isGSNNCH_of_hasGSNNCHForm` (`GSNNCHSectorSum.lean:300`): `HasGSNNCHForm M` and
  nonvanishing traces give `IsGSNNCH M`.
* `nonempty_etaLocalStructureData_of_isSAL` (`MPDO/InverseMapActiveSectorRecurrence.lean:299`):
  Proposition C.8, hypotheses `K.IsInjective`, `IsSAL K`.
* `EtaLocalStructureData.isSAL_of_isSourceZCL` (`MPDO/CyclicActiveAreaLaw.lean:92`):
  Proposition `4to2`, hypotheses `IsMPDO K`, `K.IsInjective`, `K.IsSourceZCL`.
* `PhysicalSectorFactorization.etaLocalStructureData` (`MPDO/PhysicalSectorEtaLocalStructure.lean:50`):
  a factorization with positive `η` gives the commuting form with scalar one.
* `OrthogonalCommutingSectorFamily.toProportional` (`GSNNCHOrthogonalSectors.lean:171`),
  `.toGSNNCHData` (`:190`); a sector of a proportional family is an
  `EtaLocalStructureData` by the anonymous constructor `⟨F.bondData s, F.realizes_mpo s⟩`
  (`MPDO/OrthogonalSectorAreaLaw.lean:307`).
* Pass-throughs from `EtaLocalStructureData` to its `bondData`:
  `pairBond` (`MPDO/CommutingOverlappingCoordinates.lean:318`),
  `nonempty_fixedProductTensorData`, `fixedProductTensorData`
  (`MPDO/FixedBondProductEtaTensor.lean:203, 212`),
  `exists_positive_eta_pairBond_decomposition` (`MPDO/CommutingBondEtaDecomposition.lean:328`);
  and restatements of the field `realizes_mpo`: `formAt_realizes`,
  `exists_positive_scalar_mpo_eq_product`, `formAt_bondAt_comm`,
  `positive_commuting_product_form` (`CommutingFormBridge.lean:157--199`).

### The three structures

The "three data structures for one commuting form" are `CommutingFormData`,
`TranslationInvariantBondData` and `EtaLocalStructureData`.

* `EtaLocalStructureData M` is the source's notion: one positive bond whose
  translates commute, realizing `σ^{(N)}(M)` up to a positive scalar at every
  `N ≥ 2` (equation `expression`, read as in `4to2`). It is a bond plus a property
  of `M`.
* `TranslationInvariantBondData d` is exactly the bond part of it. It is used on
  its own (12 modules: the fixed-product representative, the Bravyi--Vyalyi
  decomposition, liftings), so it is the parent, not a duplicate; what is
  duplicated is every fact about the bond, restated on `EtaLocalStructureData`
  through `bondData` (the four pass-throughs above).
* `CommutingFormData d N` is the same bond read at one length. Every one of its
  36 constructions outside the two hand files is `X.toCommutingFormData hN` for an
  `X : TranslationInvariantBondData d`; it exists only to name `bondAt` and
  `product`. Its single use as an independent object is `HasCommutingForm`, which
  no theorem consumes (6 occurrences, all in the two defining modules), and the
  one-sector GSNNCH presentation. At a fixed length it is the one-sector case of
  `GSNNCHData`: the theorem `exists_oneSector_gsnnchData_iff` in `New.lean` proves
  this equivalence with no hypothesis.

### Verdict

| Predicate / structure | Verdict |
|---|---|
| `TranslationInvariantBondData` | **Survivor**, renamed `CommutingBond` (the name says what it is; "translation invariant" is implied by being one two-site matrix). Receives `bondAt hN i`, `product hN`, `bondAt_comm`, `product_posSemidef`, `toGSNNCHData hN`. |
| `EtaLocalStructureData` | **Survivor** (the source's notion), renamed `CommutingForm` and declared `structure CommutingForm (M) extends CommutingBond d` with the single field `realizes_mpo : ∀ N (hN : 2 ≤ N), ∃ c : ℝ, 0 < c ∧ mpo M N = c • toCommutingBond.product hN`. The η of the old name names a step of the proof, not the object. Through `extends`, every fact about the bond is available on the form by dot notation, so the pass-throughs disappear without call-site changes. `Nonempty (CommutingForm M) ≃` old data with no hypothesis (`equivEtaLocalStructureData`, verification only). |
| `CommutingFormData` | **Deleted**. Not equivalent to the survivor (one length versus all lengths); it is the one-sector case of Definition 4.8 at one length, characterized by `exists_oneSector_gsnnchData_iff`. All uses become `CommutingBond.bondAt`/`product`. |
| `HasCommutingForm` | **Deleted**: a weaker, different notion (bond may depend on `N`) with no consumer. The paper-gap note already records that it is not the hypothesis of `4to2`. |
| `GSNNCHData`, `HasGSNNCHFormAt`, `HasGSNNCHForm` | **Survivor** for Definition 4.8 (a different notion: sector sum at one length). Unchanged. |
| `IsGSNNCHAt`, `IsGSNNCH` | **Clause under a hypothesis.** `IsGSNNCH` is invariant under every nonzero complex rescaling of `M` (`isGSNNCH_smul_iff`), `HasGSNNCHForm` only under positive rescaling. For a tensor generating MPDOs they agree up to nonvanishing traces: `isGSNNCH_iff_hasGSNNCHForm (hM : IsMPDO M) : IsGSNNCH M ↔ HasGSNNCHForm M ∧ ∀ N ≥ 2, tr (mpo M N) ≠ 0` (in `New.lean`, proved). Kept as the density-operator reading of Definition 4.8 (Examples 4.12 and the four-cycle obstruction state `¬ IsGSNNCH`). |
| `ProportionalOrthogonalCommutingSectorFamily`, `OrthogonalCommutingSectorFamily` | Second step (open decision 3): one structure `OrthogonalCommutingSectorFamily K` with field `form : ∀ s, CommutingForm (K s)` replaces the proportional family; the exact family is the special case of scalar one. |
| `PhysicalSectorFactorization` | Different notion (the `η` factorization of `sigmaNK2`, a property of the tensor, not of the operators). Unchanged; its constructor `translationInvariantBondData` is renamed `commutingBond`. |
| `commutingBoundaryAlgebra` | Different notion (centralizer of the letters of `M`, arXiv:2504.16985); "commuting" refers to boundaries commuting with the tensor. Unchanged, outside this family. |

### Statements on the survivor (in `New.lean`, elaborated)

* `CommutingBond`, `CommutingBond.bondAt`, `.bondAt_comm`, `.product`, `.toGSNNCHData`,
  `.toGSNNCHData_unnormalizedState`, `.product_posSemidef`.
* `CommutingForm M extends CommutingBond d`; `CommutingForm.hasGSNNCHForm`,
  `CommutingForm.mpo_posSemidef`.
* Proposition C.8: `nonempty_commutingForm_of_isSAL (K) (hK : K.IsInjective) (hSAL : IsSAL K)`.
* Proposition `4to2`: `CommutingForm.isSAL_of_isSourceZCL (hMPDO) (hK) (F) (hZCL)`.
* Line 1567: `isSAL_iff_nonempty_commutingForm (K) (hMPDO : IsMPDO K) (hK : K.IsInjective)
  (hZCL : K.IsSourceZCL) : IsSAL K ↔ Nonempty (CommutingForm K)` — new; its hypotheses
  are the union of those of C.8 and `4to2`, which is the source's setting
  (Case I, MPDO, ZCL on both sides of line 1567).
* `exists_oneSector_gsnnchData_iff`: characterization replacing `CommutingFormData`.
* `isGSNNCH_iff_hasGSNNCHForm` (clause under `IsMPDO`), with `hasGSNNCHFormAt_smul_ofReal`.
* `OrthogonalCommutingSectorFamily` with field `form` (second step).

### Change list

#### Deleted declarations → replacement

| Removed | Replacement |
|---|---|
| `CommutingFormData` (+ `.bondAt`, `.bondAt_comm`, `.product`, `.Realizes`) | `CommutingBond.bondAt hN`, `.bondAt_comm hN`, `.product hN`; `Realizes` written out as `∃ c : ℝ, 0 < c ∧ ρ = c • B.product hN` |
| `HasCommutingForm` | none (no consumer) |
| `TranslationInvariantBondData.toCommutingFormData`, `_bond`, `_hN`, `_bondAt` | `CommutingBond.bondAt`, `.product` |
| `GSNNCHData.ofCommutingFormData`, `_unnormalizedState` | `CommutingBond.toGSNNCHData hN`, `CommutingBond.toGSNNCHData_unnormalizedState` |
| `CommutingFormData.hasGSNNCHFormAt_of_realizes` | `CommutingForm.hasGSNNCHForm`; at one length `exists_oneSector_gsnnchData_iff` |
| `EtaLocalStructureData.formAt`, `formAt_realizes`, `formAt_bondAt_comm`, `exists_positive_scalar_mpo_eq_product`, `positive_commuting_product_form` | the field `CommutingForm.realizes_mpo`, `CommutingBond.bondAt_comm`, `bond_pos` |
| `EtaLocalStructureData.hasCommutingForm`, `hasCommutingForm_of_etaLocalStructure` | none |
| `hasGSNNCHForm_of_etaLocalStructure` (pass-through) | `CommutingForm.hasGSNNCHForm` |
| `EtaLocalStructureData.pairBond`, `.nonempty_fixedProductTensorData`, `.fixedProductTensorData`, `.exists_positive_eta_pairBond_decomposition` (pass-throughs) | the `CommutingBond` declarations, reached by dot notation through `extends` |
| module `MPDO/CommutingFormBridge.lean` | deleted: structures move to `MPDO/CommutingForm.lean`; `PhysicalSectorFactorization.commutingBond` moves to `MPDO/PhysicalSectorBondPairwise.lean` (the module that proves the commutation it uses) |

#### Renamed

| Old | New |
|---|---|
| `TranslationInvariantBondData` | `CommutingBond` |
| `EtaLocalStructureData` (field `bondData`) | `CommutingForm` (parent projection `toCommutingBond`) |
| `PhysicalSectorFactorization.translationInvariantBondData` | `PhysicalSectorFactorization.commutingBond` |
| `PhysicalSectorFactorization.etaLocalStructureData` | `PhysicalSectorFactorization.commutingForm` |
| `liftedTranslationInvariantBondData`, `liftedEtaLocalStructureData` | `liftedCommutingBond`, `liftedCommutingForm` |
| `nonempty_etaLocalStructureData_of_isSAL`, `…_of_recurrentSupport`, `exists_etaLocalStructureData_lifted_supported{,_of_physicalSectorFactorization}`, `exists_etaLocalStructureData_supported_of_twoSidedPhysicalSlice` | `etaLocalStructureData` → `commutingForm` in each name |
| every lemma in namespaces `TranslationInvariantBondData.*`, `EtaLocalStructureData.*` | namespaces `CommutingBond.*`, `CommutingForm.*` (e.g. `CommutingForm.isSAL_of_isSourceZCL`) |
| module `MPDO/PhysicalSectorEtaLocalStructure.lean` | `MPDO/PhysicalSectorCommutingForm.lean` |

#### Consumers (measured by `rewrite.py` on the HEAD extraction, `dryrun.txt`)

* Lean: 25 modules changed by the script plus the module rename, all in
  `MPS/MPDO` (238 changed lines in `diff -ru` of a test application, `applytest.diff`);
  2 modules rewritten by hand (`CommutingForm.lean`, `CommutingFormBridge.lean`).
  Per rule: `(X.toCommutingFormData hN).product/.bondAt → X.product/.bondAt hN`
  28 occurrences in 9 files; `x.bondData.f → x.f` 63 in 13; `x.bondData →
  x.toCommutingBond` 10 in 5; constructor field 2 in 2; renames
  `EtaLocalStructureData` 101 in 21 files, `TranslationInvariantBondData` 100 in 12,
  derived lemma names 36 + 4 + 6; imports 3 + aggregator 1.
* No module outside `MPS/MPDO` names any of the removed or renamed declarations.
* Hand edits left after the script (listed at the end of `dryrun.txt`):
  `GSNNCHOrthogonalSectors.lean` (the field `realizes_mpo` of the proportional
  family uses `.Realizes`; `mpo_posSemidef_of_two_le` uses `ofCommutingFormData`,
  replaced by `CommutingBond.product_posSemidef`), the two hand modules, blueprint
  and paper-gap prose.

#### Blueprint

`\lean{}` tags (grep of `blueprint/src/chapter/*.tex` with `%`-continuations joined):

* `ch21_mpdo_rfp_gsnnch_definitions.tex`: entries `def:mpdo_commuting_form_data`
  (`CommutingFormData`) and `def:mpdo_has_commuting_form` (`HasCommutingForm`) are
  deleted; `thm:mpdo_commuting_form_data_has_gsnnch_form` is restated for
  `CommutingBond.toGSNNCHData` and `exists_oneSector_gsnnchData_iff`. The three labels
  are referenced 9, 3 and 2 times in 2 files (`\uses`, `\ref`), all to be repointed.
  Five tags of `ProportionalOrthogonalCommutingSectorFamily` and one of
  `toProportional` change in the second step.
* `ch21_mpdo_rfp_commuting_form_bond_products.tex`: 40 tags; renamed by the script;
  delete `toCommutingFormData{,_bond,_hN,_bondAt}` (entry
  `def:mpdo_translation_invariant_bond_to_commuting_form_data` restated as the
  definitions `CommutingBond.bondAt`, `.product`), the six tags of
  `thm:mpdo_eta_local_structure_has_commuting_form` (restated as
  `CommutingForm.mpo_posSemidef` and the field), and the four pass-through tags.
* `ch21_mpdo_rfp_commuting_form_cyclic_active_markov.tex`: 11 tags renamed; delete
  `hasGSNNCHForm_of_etaLocalStructure`; add an entry for
  `isSAL_iff_nonempty_commutingForm` (line 1567 of the source).
* Renames only: `ch21_mpdo_rfp_simple_local_commuting_physical_bonds.tex`,
  `ch21_mpdo_rfp_simple_local_coherent_positive_rephasing.tex`,
  `ch21_mpdo_rfp_simple_local_structure_capstone.tex`.

#### Glossary

`docs/glossary.md` has no entry for the commuting form or for GSNNCH (grep for
`Commuting|GSNNCH|EtaLocal|TranslationInvariantBond` finds only
`commutingBoundaryAlgebra`, unaffected). Add one entry under the MPDO sections:
`MPOTensor.CommutingBond` and `MPOTensor.CommutingForm` (source `expression`, lines
1571--1576, one bond for all lengths), `GSNNCHData`/`HasGSNNCHForm` (Definition 4.8),
the clause `isGSNNCH_iff_hasGSNNCHForm`, and the theorem
`isSAL_iff_nonempty_commutingForm`.

#### Paper-gap notes

* `docs/paper-gaps/cpsv16_commuting_form_to_sal.tex`: §"Present formal distinction"
  (lines 78--94) describes `HasCommutingForm`; replace by one sentence that the
  library's commuting form fixes one bond for all lengths; leanids renamed by the
  script; five mentions of the proportional family change in the second step.
* `docs/paper-gaps/cpsv16_gsnnch_sector_decomposition.tex`: two mentions of
  `CommutingFormData` and one of `Realizes`.
* `docs/paper-gaps/cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`: leanids renamed;
  the file name and the citation key `gap:cpgsv17_mpdo_sal_zcl_eta_local_structure`
  stay (open decision 4).
* Dated notes in `docs/audits/` are records and are not edited.

### Order of application

1. **One change, one wide rebuild.** `MPDO/CommutingForm.lean` has 348 transitive
   importers (MPS/ParentHamiltonian 102, MPS/Symmetry 97, MPS/MPDO 93,
   MPS/Preparation 16, MPS/RFP 10, MPS/MPU 9, others 21), because it also holds the
   general `ChainOperator`, `windowComplementEquiv` and
   `reindex_placeAlong_ringWindow_windowComplement` (used in 54, 6, 6 modules,
   mostly `MPS/Symmetry`). Any edit to it rebuilds all 348. Do the F2 split by
   object (move those general declarations to their own module) in the same
   change, so the rebuild is paid once and later edits of the commuting-form part
   rebuild only its own dependents (the bridge has 138 transitive importers).
2. Hand step: in `CommutingForm.lean` replace `CommutingFormData`/`HasCommutingForm`
   by `CommutingBond`, `CommutingForm` and `CommutingBond.toGSNNCHData`; append
   `PhysicalSectorFactorization.commutingBond` to `PhysicalSectorBondPairwise.lean`;
   delete `CommutingFormBridge.lean`; restate the two `GSNNCHOrthogonalSectors`
   uses. Then `rewrite.py --apply`, regenerate the import aggregators, build.
3. Blueprint, glossary and paper-gap prose (no rebuild).
4. Second step, independent of 1--3 once they land: merge the two sector families
   (2 + 5 modules; open decision 3).

No QICLean change is needed (`ManyBody.placeAlong`, `ManyBody.ringWindow` are used
as they are).

### Dependencies on the basis-of-normal-tensors family

`MPDO/BNTSectorCommutingFamily.lean`, `MPDO/BNTPhysicalSectorGSNNCH.lean`,
`MPDO/OrthogonalSectorAreaLaw.lean` and `MPDO/GSNNCHOrthogonalSectors.lean` state
results over `MPSTensor.SectorDecomposition`, `commonWeightAbsorbedBasisMPOTensor`,
`SameMPV₂Pos` and `WordTupleSpanTop`. Renames in that family touch the same
signatures (`hasGSNNCHForm_of_bntSectorSAL`,
`hasGSNNCHForm_of_commonWeightAbsorbedBasisMPOTensor`,
`isSAL_of_commonWeightAbsorbedBasisMPOTensor_of_orthogonalCommutingSectorFamily`).
There is no semantic dependency in either direction; only textual conflicts in
those four files. Apply one family's script after the other has landed.

### Open decisions

1. **Names.** Recommendation: `CommutingBond` and `CommutingForm`. The alternative
   of keeping `TranslationInvariantBondData`/`EtaLocalStructureData` and only
   deleting `CommutingFormData` saves the renames (about 240 occurrences, all scripted)
   but keeps a name that describes a proof step.
2. **The commutation field.** The source requires only
   `[B_{n-1,n}, B_{n,n+1}] = 0`. For one bond and `N ≥ 3` this is the same
   three-site condition at every length (translation plus `GSNNCHData.bondAt_comm`);
   at `N = 2` it follows for `B ≥ 0` from the Bravyi--Vyalyi decomposition already
   formalized (`Matrix.exists_positive_etaPair_decomposition_of_overlappingLifts_commute`,
   which uses only the length-three commutation). Recommendation: later, replace
   the field by the three-site condition `Commute (B ⊗ 1) (1 ⊗ B)` and prove the
   all-length commutation once; not needed for removing the duplicates.
3. **Sector families.** The proportional family carries exactly
   `∀ s, CommutingForm (K s)` plus supports (the anonymous constructor at
   `OrthogonalSectorAreaLaw.lean:307` already builds the form). Recommendation: one
   structure with field `form : ∀ s, CommutingForm (K s)`; the scalar-one family
   becomes the property `∀ s N hN, mpo (K s) N = (F.form s).product hN`, and
   `toGSNNCHData` for general scalars goes through the existing rescaling
   `OrthogonalCommutingSectorFamily.coefficientRoot` (Definition 4.8 allows the
   bonds to depend on `N`). Touches `GSNNCHOrthogonalSectors`, `GSNNCHSectorRescaling`,
   `OrthogonalSectorAreaLaw`, `BNTSectorCommutingFamily`, `PhysicalSectorActiveBond`;
   needs proof work in the first two, so it is a separate step.
4. **Paper-gap file name** `cpgsv17_mpdo_sal_zcl_eta_local_structure.tex`: keep the
   slug (it is a citation key in blueprint bibliographies); rename only the
   leanids inside.
5. **`IsGSNNCHAt`/`IsGSNNCH`.** Keep, with `isGSNNCH_iff_hasGSNNCHForm` as the clause
   under `IsMPDO`; deleting them would lose the complex-rescaling invariance used in
   the Example 4.12 statements.

### Files

* `New.lean` — new statements; elaborated against hot-main (414a18fb88), output in
  `elab_final.txt` (`exit 0`, no errors, no warnings, no `sorry`: every
  declaration in the file is checked, including the proofs of
  `exists_oneSector_gsnnchData_iff` and `isGSNNCH_iff_hasGSNNCHForm`). The file uses
  hot-main's placement `embedLocalOperator 2 N hN i`; at e8f8dd3202 the one-line body
  of `place` is `placeAlong (X := fun _ ↦ Fin d) (ringWindow hN i)`, otherwise identical.
* `rewrite.py` — mechanical part; `dryrun.txt` — its dry run on the HEAD extraction;
  `applytest.diff` — the Lean diff of a test application on copies of the affected files.
* `count.sh`, `importers.py` — the counting scripts used above.

## 3. Mutual information on a chain

Reference: TNLean HEAD `e8f8dd3202`; QICLean pinned by HEAD `d65bece64d` (from `lake-manifest.json`);
elaboration against `worktrees/hot-main` (TNLean `414a18fb88`, QICLean `271884e2df`). The five
TNLean files of this family (`MPS/MPDO/{AreaLaw,MutualInfoBridge,MutualInfoMonotone,MutualInfoAreaLaw,PureAreaLaw}.lean`)
are byte-identical at hot-main and HEAD (checked with `diff` of `git show`).

### Source

CPSV16 (arXiv:1606.00608), `Papers/1606.00608/MPDO-22-12-17-2.tex`:

* lines 789–799 (Section 4.4, label `MixedMutual`): entropic quantities are taken of the normalized
  state `ρ^{(N)}(M)/tr ρ^{(N)}(M)`; "the mutual information between a part of the chain of length
  `L` and the rest is defined as `I_L = S_L + S_{N-L} - S_N`, where `S_L` is the von Neumann entropy
  of the reduced state of `L` neighboring spins"; line 799: for pure states it is twice the
  entanglement entropy.
* line 801–806: Proposition `PropILILp1` (monotonicity `I_L ≤ I_{L+1}` for `L < ⌊N/2⌋` and the limit).
* line 811: Definition `def:area-law` (SAL: `I_1 = I_2 = …`); line 815: `I_L = I_{L+1}`.
* Appendix C, line 1319: proof of `PropILILp1` by strong subadditivity of contiguous segments, and the
  bound `I_L ≤ 4 log D`; line 1340: data processing "between A and B" (the bipartite reading).

The source's notion is the bipartite mutual information of the normalized state across the cut
after the first `L` sites. The displayed formula uses `S_{N-L}` for the entropy of the complement,
which is legitimate only because the periodic operator is translation invariant.

### How `mutualInfoChain` relates to QICLean

* **To QICLean's bipartite mutual information `_root_.mutualInformation`** (alias
  `Entropy.mutualInformation`, `QICLean/Entropy/VonNeumann/Entropy.lean:777`, defined on
  `Fin dA × Fin dB`): equal, with no hypothesis beyond the positivity argument that both carry
  for Hermiticity (`MPOTensor.mutualInfoChain_eq_mutualInformation`, `MPDO/MutualInfoBridge.lean:209`).
  It is **not** a definitional equality and **not** a pure reindexing: the state is reindexed by
  `chainBipartitionEquiv d N L (N-L) _ : (Fin N → Fin d) ≃ Fin (d^L) × Fin (d^(N-L))`
  (`finCongr` to `Fin (L + (N-L))`, then `MPOTensor.blockSplitEquiv`, then `finFunctionFinEquiv` on each factor),
  and then
  - the joint term and the first marginal match by reindexing only
    (`vonNeumannEntropy_submatrix_equiv`, `bipartitionedNormalizedMPO_traceRight`, `:146`);
  - the second marginal is the state of the *last* `N-L` sites, while `mutualInfoChain` uses the
    *first* `N-L` sites; they agree by translation invariance of the periodic operator
    (`bipartitionedNormalizedMPO_traceLeft`, `:172`, through `window_block_entropy`,
    `MutualInfoMonotone.lean:137`, and `mpo_submatrix_finRotate_pow`, `AreaLaw.lean:146`).
* **To `ManyBody.regionMutualInformation ψ R T`** (`QICLean/ManyBody/Entropy/RegionEntropy.lean:142` at the pin):
  a different quantity. QICLean's regional mutual information takes a *vector* `ψ` (its regional
  states are `regionMatrix (|ψ⟩⟨ψ|) R`); `mutualInfoChain` is defined for a mixed state. They meet
  only on doubled tensors: `mutualInfoChain_doubledTensor` (`PureAreaLaw.lean:327`) gives
  `I_L(A⊗Ā) = 2 S_L(A)` (source line 799), and `2 S_L` is QICLean's regional mutual information of
  the normalized vector for the cut `[0,L) | [L,N)`.
* **QICLean has no mixed-state regional entropy or mutual information.** It has the mixed-state
  regional matrix `ManyBody.regionMatrix ρ R` (`QICLean/ManyBody/Sites/RegionMatrix.lean`, at hot-main
  `FiniteProduct.reducedMatrix`), but entropies of regions (`regionEntropy`, `regionMutualInformation`,
  `regionEntropy_ssa`) are stated for vectors only.
* **Reduced block state vs `ManyBody.regionMatrix`**: equal after a reindexing, no hypothesis. New
  theorem `reducedBlockState_eq_reducedMatrix` (in `New.lean`, proof checked):
  `reducedBlockState M N L hL = (regionMatrix (normalizedMPO M N) (interval N 0 L)).submatrix e.symm e.symm`
  with `e = prefixConfigEquiv hL : RegionConfig (fun _ ↦ Fin d) (interval N 0 L) ≃ (Fin L → Fin d)`
  (site `i ↦ i.val`); the traced variables are matched by
  `suffixConfigEquiv : RegionConfig … (interval N 0 L)ᶜ ≃ (Fin (N-L) → Fin d)` (site `i ↦ i.val - L`).
* **Relation to `Lattice/RegionalEntropyBridge`** (issue #10915, step 4.0): that module identified the
  finite-domain *pure* regional state and entropy with `ManyBody.regionState`/`regionEntropy`; it no
  longer exists at HEAD (deleted in `e18efb4687`) and never mentioned `blockEntropy`,
  `reducedBlockState` or `mutualInfoChain` (0 matches in its last version). The pure-state chain
  analogues `MPSTensor.pureBlockEntropy`/`reducedPureBlockState` are the MPDO-side copy of the same
  pure regional entropy (statement `pureBlockEntropy_eq_regionEntropy` in `New.lean`, not proved);
  they belong to that regional-entropy work and are not planned here.

### Inventory

Counts: modules = `grep -rlw --include='*.lean' <name> TNLean` on the HEAD extraction, `TNLean/Archive`
excluded; occurrences = `grep -row` (word matches, `M.name` and `MPOTensor.name` included). Every
module of this family lies in `MPS/MPDO`; all other top-level directories have 0.

| Declaration | Definition (one line) | Source anchor | Modules (MPS/MPDO) | Occ. |
|---|---|---|---|---|
| `MPOTensor.mutualInfoChain` (`AreaLaw.lean:443`) | `blockEntropy M N L + blockEntropy M N (N-L) - blockEntropy M N N` | CPSV16 l.797 | 19 | 70 |
| `MPOTensor.mutualInfoChain_eq` (`AreaLaw.lean:451`) | the same formula, `rfl` | l.797 | 2 | 3 |
| `MPOTensor.mutualInfoChain_eq_mutualInformation` (`MutualInfoBridge.lean:209`) | `mutualInfoChain = Entropy.mutualInformation (bipartitionedNormalizedMPO …)` | l.792–797, 1338–1340 | 4 | 7 |
| `MPOTensor.blockEntropy` (`AreaLaw.lean:399`) | `vonNeumannEntropy (reducedBlockState M N L hL)` | l.797 | 13 | 79 |
| `MPOTensor.reducedBlockState` (`AreaLaw.lean:378`) | `MPOTensor.blockReducedState d L (N-L) (normalizedMPO M N reindexed)` | l.797 | 30 | 229 |
| `MPOTensor.blockReducedState` (`AreaLaw.lean:261`) | `partialTraceRight (ρ.submatrix (MPOTensor.blockSplitEquiv d L K).symm …)` | — | 7 | 31 |
| `MPOTensor.blockSplitEquiv`, `MPOTensor.blockReindexEquiv` (`AreaLaw.lean:254, 372`) | `(Fin (L+K) → Fin d) ≃ (Fin L → Fin d) × (Fin K → Fin d)`; `finCongr` | — | 7; 6 | 33; 31 |
| `MPOTensor.chainBipartitionEquiv` (`MutualInfoBridge.lean:32`) | `(Fin N → Fin d) ≃ Fin (d^L) × Fin (d^K)` | — | 3 | 22 |
| `MPOTensor.bipartitionedNormalizedMPO` (`MutualInfoBridge.lean:41`) | `normalizedMPO M N` reindexed by `chainBipartitionEquiv` | l.792–797 | 4 | 56 |
| `biSplitEquiv`, `tripartiteSplitEquiv` (`MutualInfoMonotone.lean:49, 39`) | flattened two- and three-block splits | — | 4; 6 | 12; 69 |
| `periodicCutLeftFactor`, `periodicCutRightFactor` (`MutualInfoBridge.lean:50, 60`) | operator-Schmidt factors at the cut | — | 1; 1 | 3; 3 |
| `MPSTensor.pureBlockEntropy`, `reducedPureBlockState`, `normalizedPureState` (`AreaLaw.lean:595, 567, 551`) | pure analogues | l.597–600 | 3; 3; 2 | 26; 22; 13 |
| `ThermodynamicLimitCounterexample.parityMutualInfoAfterCut` (`:627`) | `mutualInfoChain parityTensor (L+K+1) L` | l.801–806 | 1 | — |
| `CPSVExample410CorrelatedFlip.mutualInfoOne/Two` (`:424, 430`) | closed-form numbers from window weights | Ex. 4.10, l.900–905 | 1 | — |
| QICLean `_root_.mutualInformation` / `Entropy.mutualInformation` | bipartite `S(A)+S(B)-S(AB)` on `Fin dA × Fin dB` | Wolf Ch. 8 | `Entropy.mutualInformation`: MPS/MPDO 4, PEPS/AreaLaw 1 | 23 |
| QICLean `ManyBody.regionMutualInformation` | `regionEntropy ψ R + regionEntropy ψ T - regionEntropy ψ (R ∪ T)` (vector `ψ`) | — | Lattice 6, MPS/AreaLaw 7, PEPS/Approximation 21, PEPS/AreaLaw 22 | 277 |
| QICLean `ManyBody.regionMatrix` | `partialTraceRight (ρ.submatrix (splitEquiv R).symm …)` | — | 0 | 0 |

Proved relations at HEAD (all hypothesis lists are those of the Lean statements):

* `mutualInfoChain_eq` (`AreaLaw.lean:451`): the formula, `rfl`.
* `mutualInfoChain_eq_mutualInformation` (`MutualInfoBridge.lean:209`): equality with the bipartite
  mutual information; hypothesis `(mpo M N).PosSemidef` only (needed to state either side).
* `bipartitionedNormalizedMPO_traceRight`/`_traceLeft` (`:146`, `:172`): marginals are the first-`L`
  and first-`(N-L)` reduced states (the second by translation invariance); hypothesis `L ≤ N`.
* `mutualInfoChain_doubledTensor` (`PureAreaLaw.lean:327`): `I_L(A⊗Ā) = 2 S_L(A)`; hypothesis
  `tr (pureState A N) ≠ 0`.
* Consequences: `mutualInfoChain_monotone` (`MutualInfoMonotone.lean:373`; `2L+1 ≤ N`, PSD, `tr ≠ 0`),
  `_nonneg` (`:398`; PSD, `tr ≠ 0`), `_symm` (`:412`; PSD), `_zero` (`:432`; PSD, `tr ≠ 0`),
  `_le_two_log_bondDim` (`MutualInfoAreaLaw.lean:60`; PSD, `tr ≠ 0`),
  `IsMPDO.mutualInfoChain_le_four_log_bondDim` (`:107`), `_le_of_bipartitioned_channel_image`
  (`LocalPurificationAreaLaw.lean:313`), `_smul` (`AreaLawScaling.lean:64`),
  `_changePhysicalBasis_of_isometry` (`PhysicalSupportSALTransport.lean:201`),
  `_eq_of_isSAL` (`AreaLaw.lean:486`).

### Verdicts

* **Survivor: QICLean's bipartite mutual information**, and `MPOTensor.mutualInfoChain` stays as a
  *named special case* of it: redefined as
  `_root_.mutualInformation (bipartitionedNormalizedMPO M N L (N - L) _) _`, so its facts (data
  processing, operator-Schmidt bound, subadditivity) follow by unfolding.
* **`mutualInfoChain_eq` becomes the characterization theorem** carrying the source's displayed
  formula `I_L = S_L + S_{N-L} - S_N` (l.797); it is the one place where translation invariance
  enters. Its proof is the present body of `mutualInfoChain_eq_mutualInformation`.
* **`mutualInfoChain_eq_mutualInformation`: deleted** (holds by `rfl` after the redefinition).
* **`MPS/MPDO/Entropy/MutualInfoBridge`: dissolved** (the architecture table's "deleted in F2"): its
  definitions and marginal theorems move to `AreaLaw.lean`, the operator-Schmidt decomposition to
  `MutualInfoAreaLaw.lean`.
* **`ManyBody.regionMutualInformation`: different notion** (pure vector, arbitrary regions); its name
  already says it is regional. No change.
* **`reducedBlockState`/`MPOTensor.blockReducedState`/`blockEntropy`**: equal to QICLean's `regionMatrix` on the
  prefix interval after reindexing (checked). Under the rule this is a second spelling of the
  regional matrix; see open decision D4. `blockEntropy` itself is a named special case of
  `vonNeumannEntropy` (passes).
* **`parityMutualInfoAfterCut`**: named special case of `mutualInfoChain` (passes).
  **`mutualInfoOne/Two`**: named numbers of one example, not a notion (pass).
* **SSA transport lemmas** in `MutualInfoMonotone` (`ssa_cast_ineq`, `traceC_corr`, `traceC_mat`,
  `traceAC_mat`, `traceA_mat`, `vonNeumannEntropy_trace{C,AC,A}_eq_blockEntropy`,
  `vonNeumannEntropy_tripartiteSplit_eq_blockEntropy`): translations between QICLean's tripartite
  SSA on `Fin dA × Fin dB × Fin dC` and contiguous blocks. They stay until QICLean has strong
  subadditivity for regional matrices of a density matrix (D5).

### Change list

Deleted: `MPOTensor.mutualInfoChain_eq_mutualInformation` (1 declaration); module
`TNLean/MPS/MPDO/Entropy/MutualInfoBridge.lean` (13 declarations, 12 moved unchanged).

Restated (old → new):

| Old | New |
|---|---|
| `def mutualInfoChain … := blockEntropy … + blockEntropy … - blockEntropy …` | `def mutualInfoChain … := _root_.mutualInformation (bipartitionedNormalizedMPO M N L (N - L) _) ((normalizedMPO_isHermitian M N hM).submatrix _)` |
| `theorem mutualInfoChain_eq … := rfl` | same statement, proof from the two marginal theorems (translation invariance) |
| `mutualInfoChain_le_two_log_bondDim`, `mutualInfoChain_le_of_bipartitioned_channel_image`, `isSAL_of_isRFPViaTS…` calc (`RFPViaTSSAL.lean:418–435`) | same statements; the bridge steps disappear |
| `mutualInfoChain_nonneg` (SSA proof) | same statement; optionally proved by `Entropy.subadditivity` |

Moved unchanged into `AreaLaw.lean` (needed before the definition, or by the formula theorem):
`biSplitEquiv`, `normalizedMPO_comp_finRotate_pow`, `append_glue`, `window_block_entropy` (from
`MutualInfoMonotone.lean`); `chainBipartitionEquiv`, `bipartitionedNormalizedMPO`,
`bipartitionedNormalizedMPO_posSemidef`, `_trace`, `append_sub_self` (private),
`reducedBlockState_full`, `bipartitionedNormalizedMPO_traceRight`, `_traceLeft` (from the bridge).
Moved into `MutualInfoAreaLaw.lean`: `periodicCutLeftFactor`, `periodicCutRightFactor`,
`bipartitionedNormalizedMPO_hasOperatorSchmidtDecomposition`,
`operatorSchmidtRank_bipartitionedNormalizedMPO_le` (their only consumer).

Consumers (measured by `rewrite.py --dry-run`, output in `dryrun.txt`):

* R1 tactic unfoldings `mutualInfoChain` → `mutualInfoChain_eq`: 12 modules, 19 occurrences.
* R2 deleted `rw [mutualInfoChain_eq_mutualInformation …]` lines: 2 modules, 2 occurrences.
* R3 import of the bridge replaced: 4 modules (incl. the aggregator `TNLean/MPS/MPDO.lean`).
* Manual: 3 term-mode uses become `rfl` or vanish (`LocalPurificationAreaLaw.lean:347`,
  `RFPViaTSSAL.lean:425, 434`) and 1 docstring (`RFPViaTSSAL.lean:385`); module docstrings of
  `AreaLaw.lean` and `MutualInfoAreaLaw.lean`.
* Untouched: the other 51 word occurrences of `mutualInfoChain` (statements, the definition,
  docstrings, comments) keep their text.
  All 19 modules using `mutualInfoChain` are in `MPS/MPDO`.

Blueprint (`grep \lean{…}` in `blueprint/src/chapter/*.tex`):

* `def:mutual_info_chain` (`ch21_mpdo_rfp_area_law_mixed_state_bounds.tex:42`,
  `\lean{MPOTensor.mutualInfoChain, MPOTensor.mutualInfoChain_eq}`): split into the definition
  (bipartite mutual information of `σ^{(N)}(M)` between the first `L` and the remaining `N-L` spins,
  `\lean{MPOTensor.mutualInfoChain}`) and a lemma with the formula `I_L = S_L + S_{N-L} - S_N`
  (`\lean{MPOTensor.mutualInfoChain_eq}`, `\uses{def:mutual_info_chain, def:block_entropy}`, proof by
  translation invariance, `\leanok`).
* Unchanged labels (same Lean names): `lem:sal_const`, `prop:mutual_info_monotone`,
  `lem:mutual_info_chain_nonneg`, `lem:mutual_info_chain_symm`, `lem:mutual_info_chain_zero`,
  `thm:local_channel_image_mutual_info_bound`, `thm:mpdo_finite_chain_mutual_information_two_log`,
  `thm:mpdo_finite_chain_mutual_information_four_log`, `lem:mutual_info_doubled`,
  `prop:pure_mutual_info_bound`, `thm:mpdo_sal_physical_isometry_transport`. No blueprint entry cites
  a declaration of `MutualInfoBridge`.

Glossary (`docs/glossary.md`): no heading mentions `mutualInfoChain`, `blockEntropy` or `IsSAL`
(grep). Recommendation: one short entry `MPOTensor.mutualInfoChain` stating that it is QICLean's
bipartite mutual information across the contiguous cut, with the formula theorem.

Paper-gap notes: `docs/paper-gaps/cpsv16_rfp_sal_data_processing.tex:126` cites
`\leanid{MPOTensor.mutualInfoChain_eq_mutualInformation}` → cite `MPOTensor.mutualInfoChain`
(definition) instead. `cpgsv17_mpdo_mutual_information_bound.tex` cites no name of this family.

Other docs: `docs/many_body_circuit_architecture.md:736` (bridge table row) → "dissolved";
`docs/audits/2026-08-27_mpdo_fin_append_mathlib_shadow_removal.md:12,25` mention the bridge file
(dated audit; leave). No `docs/audits/*.json` inventory pins any file of this family; no script
mentions the names.

### Order of application

1. One change, independent of every other family and of QICLean: moves, redefinition, formula
   theorem, deletion of the bridge, `rewrite.py --apply`, the four manual edits, blueprint,
   paper-gap note, architecture table. Editing `AreaLaw.lean` forces a rebuild of the modules
   importing it: 507 TNLean modules transitively (`MutualInfoMonotone`: 467; the bridge: 6;
   `MutualInfoAreaLaw`: 2), measured from the `import` lines at HEAD. Because the formula theorem lives
   in `AreaLaw.lean`, no consumer needs a new import (four consumers — `AreaLawScaling`,
   `CPSVExample412Literal`, `LocalOrthogonalSumAreaLaw`, `KatoDeformedRFPObstruction` — do not import
   `MutualInfoMonotone`).
2. Afterwards, with QICLean changes first (D4, D5): regional-matrix entropy and SSA in QICLean;
   then the block states and the SSA transport lemmas.

### Open decisions

* **D1. Form of the survivor.** (a) QICLean's bipartite mutual information on the flattened cut
  (above); (b) a regional form `S(regionMatrix ρ [0,L)) + S(regionMatrix ρ [L,N)) - S(ρ)`, which
  needs a mixed-state regional mutual information that QICLean lacks; (c) delete `mutualInfoChain`
  and write the bipartite mutual information at every call site (most of the 51 non-tactic
  occurrences, each then carrying a Hermiticity witness and a cut equation). *Recommendation: (a).*
* **D2. Home of the formula theorem.** `AreaLaw.lean` (no import changes; about 235 lines move there: bridge lines 30–45 and 99–256,
  `MutualInfoMonotone.lean` lines 47–51 and 107–162) or
  `MutualInfoMonotone.lean` (four consumers gain an import). *Recommendation: `AreaLaw.lean`.*
* **D3. `Entropy.mutualInformation` vs `_root_.mutualInformation`.** QICLean carries an alias (a
  pass-through) and a `Fin dA × Fin dB`-only index type, which forces `finFunctionFinEquiv` into
  `chainBipartitionEquiv` and `Fintype.equivFin` into QICLean's `jointMatrix`. *Recommendation:*
  write the name QICLean keeps; ask QICLean to delete the alias and to state `mutualInformation` on
  arbitrary finite factors, after which `chainBipartitionEquiv` is `MPOTensor.blockSplitEquiv` up to `finCongr`.
  Not blocking.
* **D4. Mixed block states.** `reducedBlockState` (30 modules, 229 occurrences) equals QICLean's
  `regionMatrix` of the prefix interval after `prefixConfigEquiv` (checked). Deleting it would put
  subtype-indexed configurations into the word calculus of 30 modules. *Recommendation:* add the
  characterization theorem now; later redefine `MPOTensor.blockReducedState`/`reducedBlockState` as that
  reindexed regional matrix (named special case), together with the regional-state work; do not
  delete.
* **D5. SSA transport lemmas.** They exist because QICLean's region SSA (`Entropy.regionEntropy_ssa`)
  is for vectors. *Recommendation:* generalize region entropy and SSA to density matrices in QICLean
  first; then `ssa_block_entropy` is region SSA on three intervals plus translation invariance, and
  the nine transport lemmas (and their blueprint tags at `ch21_…_mixed_state_bounds.tex:95–98`) go.
* **D6. Pure chain entropies.** `pureBlockEntropy` is QICLean's `regionEntropy` of the normalized
  vector on the prefix interval (stated in `New.lean`, not proved). *Recommendation:* hand to the
  regional-entropy work (#10915 line); `mutualInfoChain_doubledTensor` stays as the source's remark
  (l.799).

### Lean check (`New.lean`)

Command: `cd worktrees/hot-main && timeout 600 lake env lean …/fam3_mutual_info/New.lean`
(about 1 min 45 s, no module built). Output, complete:

```
New.lean:253:8: warning: declaration uses `sorry`
```

Checked (statement and proof elaborate, namespace `MPOTensor.F4`): the redefinition
`mutualInfoChain`; `mutualInfoChain_eq` (characterization); restated `mutualInfoChain_nonneg` (new
proof by subadditivity), `_monotone`, `_symm`, `_zero`, `_le_two_log_bondDim`,
`_le_of_bipartitioned_channel_image` (bridge-free proof); `IsSAL` with `isSAL_iff` proving it is the
present `MPOTensor.IsSAL`; `prefixSiteEquiv`, `suffixSiteEquiv`, `prefixConfigEquiv`,
`suffixConfigEquiv`, `reducedBlockState_eq_reducedMatrix` (with hot-main's name
`FiniteProduct.reducedMatrix`, the pin's `ManyBody.regionMatrix`). Statement only (`sorry`):
`pureBlockEntropy_eq_regionEntropy` (out of scope, D6). Not checked: the rewritten consumer modules
(they would need a rebuild of the redefinition); `rewrite.py --apply` was tested on copies of the 16
affected files and produced exactly the diffs listed above.

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
| FF14 | `SweepContraction`, `RangeProjection` | — | ALVV §6.1 | definitions moved to QICLean `main` (`Analysis/SweepContraction.lean`, `Analysis/SupportProjectionOrder.lean`); remaining duplicate `QuantumCircuit.supportProj_mem_supportedOperators`, `Circuit/SupportProjection.lean:27` (Circuit 1, MPS/AreaLaw 1, PEPS/AreaLaw 1) of QICLean `ManyBody.supportProj_mem_supportedOperators` (`Sites/Twirl.lean:505`) | not a frustration-free encoding; tracked by #10939; listed only |
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

Reference: TNLean HEAD `e8f8dd3202`, QICLean pin `d65bece64d`. Elaboration against
`worktrees/hot-main` (`414a18fb88`, QICLean `271884e2`).

### How the numbers were measured

* Module and occurrence counts: `count.py` (this directory) over the read-only HEAD
  extraction `notions/head/TNLean/**/*.lean`, `TNLean/Archive/` excluded, one regular
  expression per row (`patterns.tsv`), modules grouped by top-level directory, two levels
  under `MPS/`. A module counts if the pattern occurs anywhere in it, docstrings included.
  `Kraus.IsInjective` and `Kraus.IsNormal` are counted qualified only; unqualified uses
  inside `namespace Kraus` (QICLean) are not counted.
* `MPOTensor.IsInjective` is used almost only through dot notation (`K.IsInjective`); its
  count is the one measured by rule R1 of `rewrite.py` (receivers of `.IsInjective` in
  `TNLean/MPS/MPDO/`, the only directory where the abbreviation is used).
* Blueprint counts: `\lean{…}` arguments in `blueprint/src/chapter/*.tex` containing the name.

### Inventory

#### Matrix product states

| Predicate | Definition (Lean) | Source anchor | Modules at HEAD |
|---|---|---|---|
| `Kraus.IsInjective A` (QICLean `Kraus/Injectivity.lean:41`) | `span ℂ (range A) = ⊤` | arXiv:1804.04964 `paper_normal.tex:196-205`; PVWC07 `MPSarchive.tex:888-895` (`L = 1`) | 316 modules / 1142 occ: MPS/Symmetry 101, MPS/MPDO 64, MPS/ParentHamiltonian 36, MPS/Preparation 31, MPS/Examples 16, MPS/Core 12, MPS/Chain 9, MPS/FundamentalTheorem 8, MPS/RFP 8, MPS/Structure 8, MPS/MPU 7, MPS/CanonicalForm 4, PEPS 3, Spectral 3, MPS/BNT 2, PiAlgebra 2, MPS 1, MPS/Overlap 1 |
| `Kraus.IsNBlkInjective A N` (QICLean `:97`) | `wordSpan A N = ⊤` | arXiv:0909.5347 `main.tex:387-391` (`S_n(A)`); PVWC07 `:888-908` (`Γ_L` injective, condition C1) | 144 / 630: MPS/ParentHamiltonian 59, MPS/Examples 15, MPS/CanonicalForm 13, MPS/Preparation 11, MPS/Core 10, MPS/MPDO 9, MPS/Symmetry 7, PEPS 6, MPS/Chain 3, Wielandt 3, MPS/Periodic 2, MPS 1, MPS/BNT 1, MPS/FundamentalTheorem 1, MPS/MPU 1, MPS/Overlap 1, MPS/RFP 1 |
| `Kraus.IsNormal A` (QICLean `:168`) | `∃ N, 0 < N ∧ IsNBlkInjective A N` | arXiv:0909.5347 `main.tex:416-421` (property (b)); arXiv:2011.12127 `TN-Review-main.tex:1815-1830` | 233 / 554: MPS/Preparation 45, MPS/Examples 43, MPS/MPDO 24, MPS/Symmetry 24, Wielandt 18, MPS/FundamentalTheorem 17, MPS/ParentHamiltonian 16, MPS/RFP 12, MPS/Core 9, MPS/MPU 8, MPS/CanonicalForm 7, MPS/Periodic 5, MPS/BNT 2, MPS 1, MPS/Chain 1, Spectral 1 |
| `Kraus.HasEventuallyFullWordSpan A` (QICLean `:232`) | `∀ᶠ N in atTop, wordSpan A N = ⊤` | none (QICLean helper) | 3 / 5: Wielandt 2, MPS/Examples 1; QICLean 24 occ |
| `MPTensor.IsNormalTensor A` (`MPS/CanonicalForm/Definitions.lean:105`) | structure: `Kraus.IsIrreducibleFamily A`, spectral radius of `transferMap A` is `1`, `IsPrimitive (transferMap A)` | arXiv:1606.00608 `MPDO-22-12-17-2.tex:233-235` (Definition NT) | 100 / 301: MPS/MPDO 36, MPS/ParentHamiltonian 15, MPS/CanonicalForm 13, MPS/MPU 9, MPS/Preparation 8, MPS/RFP 6, MPS/Symmetry 4, MPS/FundamentalTheorem 3, Spectral 3, MPS/BNT 1, MPS/Core 1, MPS/Overlap 1 |
| `MPOTensor.IsInjective K` (`MPS/MPDO/SimpleLocalInverseMaps.lean:30`; the glossary names `SimpleLocalStructure.lean`, stale) | `abbrev … := Kraus.IsInjective K.toMPSTensor` | arXiv:1606.00608 `:1628-1658` | 34 files / 130 occurrences, all MPS/MPDO (R1) |
| `MPSChainTensor.IsInjective A` (`MPS/Chain/Defs.lean:45`) | `∀ k, Kraus.IsInjective (A k)` | arXiv:1804.04964 `:145, 196-205` | 6 modules (unqualified in `MPS/Chain` 3, `PEPS` 3) |
| `MPSChainTensor.IsWindowInjective A L` (`PEPS/CycleMPSChainArc.lean:184`) | every cyclic window of `L` sites has full arc-product span | arXiv:1804.04964 `:1928-1940` | 5 / 23: PEPS 5 |
| `MPSTensor.IsInjectiveOn B S` (`MPS/Preparation/SupportedPolar.lean:117`) | entries vanish off `S` and `span (range B)` contains every unit of `S` | arXiv:2307.01696 footnote | 19 / 53: MPS/Preparation 19 |
| `VaryingBondChain.IsBlockInjective A hN` (`MPS/Preparation/VaryingBondBlocks.lean:104`) | every block-corner unit lies in the span of the padded blocked tensor | arXiv:2307.01696 footnote | 2 / 7: MPS/Preparation 2 |
| `PropBlockInjective A` (`MPS/MPDO/BiCFDerivation/Selectors.lean:533`) | `∃ L S, (∀ k, IsNBlkInjective (A k) L) ∧ HasBlockSelectorWords A S` | arXiv:1606.00608 `:340-345` | 1 / 7 |
| `HasInjectiveBlocks A` (`PiAlgebra/CanonicalFormSepAux.lean:57`) | structure with one field `∀ k, Kraus.IsInjective (A k)` | none | 2 / 4: MPS/BNT 1, PiAlgebra 1 |
| `IsCPSVBasisOfNormalTensors`, `IsBNT` | basis-level normality | family 1 (BNT/canonical form) owns these | 40 / 103 and 12 / 32 |

Three spellings of "injective after blocking `N` sites" are used in statements:
`Kraus.IsNBlkInjective A N` (144 modules / 630 occ), `Kraus.IsInjective (Kraus.blockTensor A N)`
(46 / 109: MPS/Preparation 26, MPS/MPDO 5, MPS/Symmetry 5, MPS/CanonicalForm 4, MPS/Core 4,
MPS/MPU 1, MPS/ParentHamiltonian 1) and `Kraus.wordSpan A N = ⊤` (28 / 99: Wielandt 10,
MPS/ParentHamiltonian 7, MPS/Examples 5, MPS/CanonicalForm 3, MPS/Core 2,
MPS/FundamentalTheorem 1). Translations between them: `isNBlkInjective_iff_blockTensor_isInjective`
23 modules / 56 occ, `wordSpan_eq_top_iff_isNBlkInjective` 14 / 26.

#### PEPS

| Predicate | Definition (Lean) | Source anchor | Modules at HEAD |
|---|---|---|---|
| `TNLean.PEPS.IsVertexInjective A` (`PEPS/Defs.lean:90`) | `∀ v, LinearIndependent ℂ (A.component v)` | arXiv:1804.04964 `:979-981` | 41 / 169: PEPS 41 |
| `TNLean.PEPS.Tensor.IsInjective A` (`PEPS/Defs.lean:106`) | structure: `IsVertexInjective A`, `∀ e, 0 < A.bondDim e` | same; nonzero bonds a Local fix (`peps_injective_ft_section3_route.tex`) | 11 / 13 |
| `RegionBlockedTensorInjective A R` (`PEPS/RegionBlock/Basic.lean:157`) | linear independence of the contraction over `R`, indexed by boundary configurations | arXiv:1804.04964 `:1205-1210, 1324-1402` | 74 / 424 |
| `SingletonRegionTensorInjective A v` (`PEPS/SingletonRegion.lean:56`) | `LinearIndependent ℂ (singletonRegionTensorFamily A v)`, where the family is `A.component v` | `:981-1009` | 1 / 4 (its own module) |
| `VertexComplementTensorInjective A v` (`PEPS/VertexComplement/Basic.lean:95`) | linear independence of the contraction over `V \ {v}` | `:1207` | 3 / 3 |
| `EdgeMiddleTensorInjective A e` (`PEPS/EdgeMiddlePhysical/Basic.lean:172`) | linear independence of the contraction over `V \ {u, v}` | `:981-1009` (`eq:block_to_mps`) | 2 / 20 |
| `EdgeBlockedThreeSiteInjective A e` (`…/Basic.lean:255`) | endpoints injective and middle injective | same | 8 / 50 |
| `IsTwoBlockInjective A` (`PEPS/TwoInjectiveComparison/Basic.lean:91`) | linear independence of an abstract two-block tensor | Lemma `inj_equal_tensors_2` | 5 / 32 |
| `IsRectangularInjective A` (`PEPS/CycleMPSTwoSiteCounterexample.lean:53`) | linear independence for `Dₗ × Dᵣ` matrices | `:196-205` | 1 / 7 (counterexample module) |
| `IsGInjective ρ T` (`PEPS/GInjective.lean:80`) | `T ∘ ρ g = T` and `T` injective on `ρ`-invariants | arXiv:1001.3807 `paper_v3.tex:1278-1296` | 98 / 472: PEPS 96, MPS/Examples 1, MPS/Symmetry 1 |
| `RegionInjectivityData V` (`PEPS/InjectiveRegion.lean:51`) | a record with one field `IsInjective : Finset V → Prop`; instances only `regionInjectivityDataOf A` (= `RegionBlockedTensorInjective A`) and the conjunction `regionInjectivityDataPair` | `:1407-1545` | 29 / 121; `regionInjectivityDataOf` 46 / 265 |
| `RegionInjectivityUnionClosure κ` (`…InjectiveRegion.lean:63`) | Lemma `injective_union` as a hypothesis | `:1322-1404` | 47 / 205 |
| `NormalPEPSBlockingHypotheses ι G` (`PEPS/NormalBlocking.lean:676`) | edge blockings and one-site separation regions for `ι` | `:1576-1583` | 7 / 14 |
| `NormalPEPSPairHypotheses A B` (`PEPS/NormalBondDimension.lean:287`) | blocking hypotheses at the pair assignment, plus nonzero bonds of `A` and `B` | `:1576-1583`, `:1318` | 5 / 20 |
| `IsNormalCycleArcMPS L A` (`PEPS/CycleFundamentalTheorem.lean:103`) | every arc of `L` sites injective, nonzero bonds | `:1597-1622` | 1 / 10 |
| `IsNormalTorusRectanglePEPS A` (`PEPS/NormalTorusRectanglePEPS.lean:51`) | every non-wrapping `2×3`, `3×2` torus rectangle injective, nonzero bonds | `:1453-1471` | 3 / 20 |
| `IsNormalSquareLatticeRectanglePEPS A` (`PEPS/NormalSquareUnconditionalFundamentalTheorem.lean:115`) | same on the open square lattice | `:1453-1471` | 1 / 6 |
| `IsNormalTorusArcWindowPEPS L K A` (`PEPS/TorusWindowComplement.lean:484`) | every cyclic `L × K` window injective, nonzero bonds | `:2297-2318` | 6 / 15 |
| `SingletonRegionInjectivityComparison κ A`, `SingletonRegionInjectivityFromVertexInjectivity κ A` (`PEPS/Injectivity/Region/SingletonRegion.lean`), `EdgeMiddleRegionInjectivityComparison`, `EdgeMiddleKernelDescentData` (`PEPS/EdgeMiddlePhysical/Basic.lean:206, 270`) | implications stored as structures | `:981-1009` | 3 / 9, 1 / 6, 1 / 17, 2 / 6 |

#### Proved relations (file:line at HEAD)

| Relation | Hypotheses | Lemma |
|---|---|---|
| `IsInjective A → IsNBlkInjective A 1` | none | `Kraus.isNBlkInjective_one_of_isInjective`, QICLean `Kraus/Injectivity.lean:175` |
| `IsInjective A ↔ wordSpan A 1 = ⊤` | none | new, `Kraus.isInjective_iff_wordSpan_one_eq_top` (`New.lean`) |
| `IsInjective A → IsNormal A` | none | `Kraus.IsInjective.isNormal`, QICLean `:196` |
| `IsNBlkInjective A N ↔ IsInjective (blockTensor A N)` | none | `Kraus.isNBlkInjective_iff_blockTensor_isInjective`, QICLean `Kraus/Blocking.lean:108` |
| `wordSpan A N = ⊤ ↔ IsNBlkInjective A N` | none (`Iff.rfl`) | `MPSTensor.wordSpan_eq_top_iff_isNBlkInjective`, `Wielandt/SpanGrowth/CumulativeSpan.lean:58` |
| `IsNBlkInjective A L → L ≤ m → IsNBlkInjective A m` | `0 < L` | `MPSTensor.isNBlkInjective_of_le`, `Wielandt/SpanGrowth/CumulativeSpan.lean:48` |
| same | `∑ A A† = 1` | `isNBlkInjective_of_le_of_unital`, `MPS/CanonicalForm/FixedLengthIntertwiner.lean:173`, and again `isNBlkInjective_of_ge_of_unital`, `Wielandt/SpanGrowth/CumulativeToWordSpan.lean:47` (same statement, explicit `A`) |
| same | PGVWC07 canonical form | `isNBlkInjective_of_le_of_canonical`, `MPS/CanonicalForm/InjectivePeriodicCuts.lean:144` |
| same, for `wordSpan` | `∑ A† A = 1` | `Kraus.wordSpan_eq_top_of_ge_of_isTP`, QICLean `Kraus/Injectivity.lean:204` |
| `IsNormal A → IsNBlkInjective A (D^4)` | `[NeZero D]` | `isNBlkInjective_pow_four_of_isNormal`, `MPS/ParentHamiltonian/CompactNormalParentGap.lean:41`; with `∑ A† A = 1`: `isNBlkInjective_pow_four_of_isNormal_leftCanonical`, `MPS/CanonicalForm/SectorComparison/NormalityChain.lean:217`; for `IsNormalTensor`: `IsNormalTensor.isNBlkInjective_pow_four`, `MPS/Core/CommonNormalBlocking.lean:30`, and the private `IsNormalTensor.isNBlkInjective_cap_pow_four`, `MPS/ParentHamiltonian/CPSVOriginalRange.lean:294` |
| `IsNormal A ↔ HasEventuallyFullWordSpan A` | QICLean states it under `IsTP` | `Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP`, QICLean `:237`; the hypothesis is not needed: new `MPSTensor.hasEventuallyFullWordSpan_iff_isNormal` |
| `IsNormalTensor A → IsNormal A` | none | `IsNormalTensor.isNormal`, `MPS/CanonicalForm/NormalTensorGauge.lean:313` |
| `IsNormal A → IsNormalTensor A` | `[NeZero D]`, left canonical | `isNormalTensor_of_isNormal_leftCanonical`, `:329` |
| `IsNormalTensor A ↔ IsNormal A ∧ spectralRadius (E_A) = 1` | none | new, `MPSTensor.isNormalTensor_iff_isNormal_and_spectralRadius_eq_one` (`New.lean`) |
| `IsInjectiveOn B univ ↔ IsInjective B` | none | `MPSTensor.isInjectiveOn_univ_iff`, `MPS/Preparation/SupportedPolar.lean:122` |
| `IsBlockInjective A hN ↔ ∀ k, IsInjectiveOn (chainBlockTensor (zeroPad A) hN k) (blockCorner A ℓ k)` | `∀ k, 0 < ℓ k` | `→`: `IsBlockInjective.isInjectiveOn`, `VaryingBondBlocks.lean:111`; `↔`: new `VaryingBondChain.isBlockInjective_iff_forall_isInjectiveOn` |
| `MPSChainTensor.IsInjective A → IsWindowInjective A 1`; `IsNBlkInjective B L → IsWindowInjective (const B) L` | `[NeZero n]` | `PEPS/CycleMPSChainArc.lean:207, 190` |
| `IsVertexInjective A → MPSChainTensor.IsInjective (A.reindexMPSChain hn hDim)` on the cycle | `3 ≤ n`, uniform bonds | `Tensor.isInjective_reindexMPSChain`, `PEPS/CycleMPSConstantDescription.lean:151` |
| `IsVertexInjective (cycleTensorOfMPS hn A) ↔ IsInjective A` | `3 ≤ n` | new, `TNLean.PEPS.isVertexInjective_cycleTensorOfMPS_iff` |
| `IsNBlkInjective A L → RegionBlockedTensorInjective (cycleTensorOfMPS hn A) (arc s L)` | `0 < L < n`, `0 < D` | `regionBlockedTensorInjective_cycleTensorOfMPS`, `PEPS/CycleMPSInjectivity.lean:451` |
| `IsVertexInjective A ↔ ∀ v, SingletonRegionTensorInjective A v` | none (`Iff.rfl`) | new; HEAD has only `→`, `IsVertexInjective.singletonRegionTensorInjective`, `PEPS/SingletonRegion.lean:64` |
| `IsVertexInjective A → RegionBlockedTensorInjective A R` | `∀ e, 0 < A.bondDim e` | `regionBlockedTensorInjective_of_isVertexInjective`, `PEPS/RegionBlock/KernelDescent.lean:576` |
| `IsVertexInjective A → VertexComplementTensorInjective A v` | positive bonds | `PEPS/VertexComplement/Injective.lean:136`, transported from the region theorem |
| `IsVertexInjective A → EdgeBlockedThreeSiteInjective A e` | positive bonds | `PEPS/EdgeMiddlePhysical/KernelDescent.lean:724`, by a second kernel descent (731 lines) |
| `IsTwoBlockInjective (regionTwoBlock A R) ↔ RegionBlockedTensorInjective A R` | none | `PEPS/NormalEdgeGauge.lean:95` |
| `IsGInjective (trivial) T ↔ Function.Injective T` | none | `isGInjective_trivial_iff`, `PEPS/GInjective.lean:122` |
| `IsGInjective ρ T ↔ invariance ∧ ∃ L, L ∘ T = Π_U` | finite `G`, `|G|` invertible | `isGInjective_iff_exists_leftInverse`, `:98` |
| `Function.Injective (siteMap a) ↔ LinearIndependent (four-leg components)` | none | `siteMap_injective_iff`, `:166` |
| `IsInjective A ↔ Function.Injective (X ↦ (tr (A^i X))_i)` | none | new, `Kraus.isInjective_iff_injective_traceMap`; with `isGInjective_trivial_iff` this is trivial-group `G`-injectivity of an MPS tensor written with matrices |
| `RegionInjectivityUnionClosure (regionInjectivityDataOf A)` | positive bonds | `regionInjectivityUnionClosure_of_overlap`, `PEPS/NormalSquareInjectivity.lean:111` |

### Answers to the questions

* **`IsNormalTensor` against `Kraus.IsNormal`.** They are not equivalent: `Kraus.IsNormal`
  is invariant under rescaling, `IsNormalTensor` fixes the spectral radius at one. With no
  further hypothesis, `IsNormalTensor A ↔ Kraus.IsNormal A ∧ ρ(E_A) = 1`
  (`isNormalTensor_iff_isNormal_and_spectralRadius_eq_one`, elaborated). Left-canonical
  normalization or irreducibility is not needed; irreducibility follows from normality. The
  glossary sentence "There is no equivalence theorem between `Kraus.IsNormal` and
  `MPTensor.IsNormalTensor`" stays true, but the exact relation is now this theorem.
* **`IsNBlkInjective A n` against `IsInjective (blockTensor A n)`.** Not a pass-through: the
  body of `IsNBlkInjective` is `wordSpan A n = ⊤`, and the equivalence with the blocked
  tensor is a proof through the reindexing `Fin (d^n) ≃ (Fin n → Fin d)` (QICLean
  `Blocking.lean:108`). It holds with no hypothesis. `wordSpan_eq_top_iff_isNBlkInjective`
  is the pass-through.
* **MPS injectivity against PEPS injectivity on a cycle.** One notion on two carriers:
  `IsVertexInjective (cycleTensorOfMPS hn A) ↔ Kraus.IsInjective A`
  (`isVertexInjective_cycleTensorOfMPS_iff`, elaborated; HEAD had only the site-dependent
  forward direction `Tensor.isInjective_reindexMPSChain`). The window notion is also stated
  twice: `MPSChainTensor.IsWindowInjective` on chains and `IsNormalCycleArcMPS` /
  `NormalCycleArcInjectivityHypotheses` on cycle tensors. Two closed-chain Fundamental
  Theorems use them: the graph route `fundamentalTheorem_normalMPS_cycle` (`n ≥ 3L`,
  `PEPS/CycleFundamentalTheorem.lean:165`) and the chain route
  `fundamentalTheorem_normalMPSChain_of_overlap` (`n ≥ 2L + 1`,
  `PEPS/CycleMPSChainOverlapCapstone.lean:467`). These are the source's two proofs with two
  different size bounds (Section 3 and Section `normal_alt`), so both theorems stay. No
  lemma about injectivity is proved twice for the two carriers at HEAD. The bridge
  between them is the carrier question of plan T.1.
* **`IsGInjective` with trivial `G`.** `isGInjective_trivial_iff` gives injectivity of `T`.
  For a four-leg PEPS site map this is the vertex condition of `IsVertexInjective`
  (`siteMap_injective_iff`). For an MPS tensor with matrices it is `Kraus.IsInjective`
  (`isInjective_iff_injective_traceMap`, elaborated). `IsGInjective` is a generalization
  with a parameter `ρ`, not a second name.
* **"Injective after blocking `L` sites" against normality.** `Kraus.IsNormal A` is by
  definition `∃ L > 0, IsNBlkInjective A L`. For `D > 0` it is equivalent to injectivity
  at the fixed length `D^4`, to eventual fullness, and to injectivity of some positive
  blocking (`MPSTensor.normality_tfae`, elaborated). For PEPS, "normal" means
  "injective after blocking certain regions". Each fixed-lattice structure names its own
  family of regions, and those families differ: a non-wrapping `2 × 3` rectangle is not a
  cyclic window. So those structures are different notions.

### Verdicts

| Predicate | Verdict |
|---|---|
| `Kraus.IsInjective` | survivor |
| `Kraus.IsNormal` | survivor |
| `Kraus.IsNBlkInjective` | survivor as the name of the source's `S_N(A) = M_D` / "`Γ_N` injective" (see D1). The spelling `Kraus.IsInjective (Kraus.blockTensor A N)` stays only as the right side of the characterization theorem and where a one-site theorem is applied to the blocked tensor. Theorems stated that way only to be converted back are restated. |
| `Kraus.HasEventuallyFullWordSpan` | equivalent to `Kraus.IsNormal` with no hypothesis: deleted (QICLean). Characterization: `hasEventuallyFullWordSpan_iff_isNormal`, clause 2 of `normality_tfae`. Not caught by the primitivity change (that change removed `HasEventuallyFullKrausRank`; this QICLean name dates from 2026-08-21). |
| `MPTensor.IsNormalTensor` | different notion (normal and spectral radius one): survivor. Add the characterization theorem. The name does not say it includes the normalization (D2). |
| `MPOTensor.IsInjective` | abbreviation: deleted. Callers write `Kraus.IsInjective K.toMPSTensor` (R1). |
| `MPSChainTensor.IsInjective` | survivor: injectivity of a site-dependent chain, sitewise `Kraus.IsInjective`, the source's "injective MPS". |
| `MPSChainTensor.IsWindowInjective` | survivor (different notion: windows). Carrier duplication with `IsNormalCycleArcMPS` is deferred to T.1 (D4). |
| `MPSTensor.IsInjectiveOn` | different notion (support `S`), name says how; survivor. |
| `VaryingBondChain.IsBlockInjective` | equivalent only under `∀ k, 0 < ℓ k` to sitewise `IsInjectiveOn`. This is a clause of arXiv:2307.01696's standing assumption: add `isBlockInjective_iff_forall_isInjectiveOn` and keep the definition. Blocks of length zero are the degenerate reading. |
| `PropBlockInjective` | proof data for arXiv:1606.00608 `:340-345`, not a notion of injectivity; family 1. The prefix `Prop` says nothing; rename to `HasCommonBlockInjectiveSelectors` (optional). |
| `HasInjectiveBlocks` | a structure wrapping `∀ k, Kraus.IsInjective (A k)`: deleted, inlined (family 1 owns `PiAlgebra` canonical-form split conditions; cross-reference). |
| `TNLean.PEPS.IsVertexInjective` | survivor (vertex condition; admits zero bonds) |
| `TNLean.PEPS.Tensor.IsInjective` | survivor (the source's injective PEPS, with the nonzero-bond convention); see D5 |
| `RegionBlockedTensorInjective` | survivor (injectivity of a region) |
| `SingletonRegionTensorInjective` and `singletonRegionTensorFamily` | definitionally the vertex clause of `IsVertexInjective`: deleted. `IsVertexInjective.singletonRegionTensorInjective` (a `simpa` pass-through) is deleted. |
| `SingletonRegionInjectivityComparison`, `SingletonRegionInjectivityFromVertexInjectivity` | bridge structures (an implication kept as a hypothesis): deleted. Every instance is `regionInjectivityDataOf A`, where the implication is the theorem `regionBlockedTensorInjective_of_isVertexInjective`. |
| `VertexComplementTensorInjective` | special case of `RegionBlockedTensorInjective` at `V \ {v}`, already derived from it by transport: survivor as a named special case. Its only lemma is a transport. Optional: delete and use the region predicate (3 consumers). |
| `EdgeMiddleTensorInjective`, `EdgeBlockedThreeSiteInjective` | `EdgeMiddleTensorInjective` is the region predicate at `V \ {u, v}` up to the same kind of transport. Its 731-line kernel descent repeats `RegionBlock/KernelDescent.lean` (594 lines) for one region. That is a dual system by the test. Restate `IsVertexInjective.edgeBlockedThreeSiteInjective` as a transport of the region theorem, as was done for the vertex complement. Delete `EdgeMiddlePhysical/KernelDescent.lean`, `EdgeMiddleKernelDescentData` and the bridge structure `EdgeMiddleRegionInjectivityComparison`. `EdgeBlockedThreeSiteInjective` survives (the source's assertion that the blocked chain is injective). |
| `IsTwoBlockInjective` | abstract carrier of Lemma `inj_equal_tensors_2`, related to regions by an `iff` with no hypothesis: survivor (abstract lemma input) |
| `IsRectangularInjective` | local to a counterexample module: survivor |
| `IsGInjective` | survivor (generalization with parameter `ρ`) |
| `RegionInjectivityData`, `RegionInjectivityUnionClosure` | an interface with two instances. Union closure is a theorem for both (from positive bonds), yet it is carried as a hypothesis in 47 modules (see D3) |
| `NormalPEPSBlockingHypotheses`, `NormalPEPSPairHypotheses`, the four fixed-lattice structures | different notions (different region families); survivors. Their `bondDim_pos` fields are the nonzero-bond convention (D5). |

### Change list

#### Deleted or restated declarations

| Removed | Replacement | Consumers (measured) |
|---|---|---|
| `MPOTensor.IsInjective` (abbrev) | `Kraus.IsInjective K.toMPSTensor` | 34 files / 130 occurrences, MPS/MPDO (R1); blueprint `def:mpdo_injective_inverse_layer` in `ch21_mpdo_rfp_simple_local_inverse_map_factorization.tex:3` |
| `MPSTensor.wordSpan_eq_top_iff_isNBlkInjective` (`Iff.rfl`) | none; the two sides are one proposition | 14 files / 26 occurrences (R2); blueprint `lem:wordspan_blk_inj` (`ch08_wielandt_cumulative_bound.tex:522`) removed; its 6 other occurrences (`\uses`/`\ref`) redirected to `def:l_blk_injective` (`ch02_mps.tex:778`) |
| `MPSTensor.isNBlkInjective_of_ge_of_unital`, `MPSTensor.isNBlkInjective_of_le_of_unital` (two copies of PVWC07 `:896-898`) | one QICLean theorem `Kraus.isNBlkInjective_of_le_of_unital` next to `Kraus.wordSpan_eq_top_of_ge_of_isTP` (both TNLean callers import neither copy's module, so the survivor must sit below both) | 5 files / 9 occurrences (R3); blueprint `thm:wordspan_propagation_unital` (`ch08_wielandt_word_span_and_block_injectivity.tex:12`) retargeted |
| `MPSTensor.isNBlkInjective_smul` (copy of `isNBlkInjective_smul_iff`) | `(isNBlkInjective_smul_iff hz _ _).2` | 4 files / 8 occurrences (R4); 4 lines to reflow |
| `Kraus.HasEventuallyFullWordSpan`, `Kraus.hasEventuallyFullWordSpan_iff_exists_pos_of_isTP`, `Kraus.HasEventuallyFullWordSpan.blockTensor`, `MPSTensor.isNormal → HasEventuallyFullWordSpan` (`Wielandt/SpanGrowth/InvertibleWordSpan.lean:43`) | `Kraus.IsNormal` | QICLean 24 occ; TNLean 3 modules / 5 occ (hand) |
| `SingletonRegionTensorInjective`, `singletonRegionTensorFamily`, `IsVertexInjective.singletonRegionTensorInjective`, `SingletonRegionInjectivityComparison`, `SingletonRegionInjectivityFromVertexInjectivity` and its `ofSingletonComparison` | `LinearIndependent ℂ (A.component v)`; `regionBlockedTensorInjective_of_isVertexInjective` | `PEPS/Injectivity/Region/SingletonRegion.lean` deleted (156 lines); 3 modules use the comparison structures (`RegionBlock/UnionClosure.lean`, `EdgeMiddlePhysical/Basic.lean` 5 theorems); blueprint `thm:peps_singletonRegionTensorInjective`, `thm:peps_singletonRegionInjectivityFromVertexInjectivity`, the definition block at `ch24_peps_ft_edge_middle.tex:404-405` |
| `EdgeMiddleKernelDescentData`, `edgeMiddleKernelDescentData`, `edgeMiddleKernelCondition*`, `initial_kernelCondition` (edge version), `EdgeMiddleRegionInjectivityComparison` and its 8 theorems | `regionBlockedTensorInjective_of_isVertexInjective` at `edgeMiddleVertices e`, transported as in `VertexComplement/Injective.lean` | `EdgeMiddlePhysical/KernelDescent.lean` (731 lines) deleted; 6 modules / 26 occ of the `edgeBlockedThreeSiteInjective` lemmas keep their statements; blueprint 9 `\lean` entries in `ch24_peps_ft_edge_middle.tex` and `ch24_peps_ft_edge_kernel_gauges_kernel_descent_recovery.tex` (`def:peps_edgeMiddleRegionInjectivityComparison`, `thm:peps_edgeMiddleTensorInjective_of_kernelDescent`, `thm:peps_edgeBlockedThreeSiteInjective*`, `thm:peps_edgeMiddleTensorInjective_*`) |
| `HasInjectiveBlocks` | `∀ k, Kraus.IsInjective (A k)` | 2 modules / 4 occ (hand; family 1 region) |
| `IsNormalTensor.isNBlkInjective_pow_four`, private `isNBlkInjective_cap_pow_four` | `isNBlkInjective_pow_four_of_isNormal hA.isNormal` (moved below `MPS/ParentHamiltonian`, next to its TP form in `MPS/CanonicalForm/NormalBlocks/NormalityChain.lean`) | 2 modules / 4 occ; blueprint `lem:spc_aux_normal_fourth_power_blocking` (`ch12_symmetry_spt_compact_limits.tex:1667`) retargeted |
| `exists_pos_blockTensor_isInjective_le_pow_four_of_isNormal_leftCanonical`, `blockTensor_isInjective_mul_of_blockTensor_isInjective`, `IsNormalTensor.blockTensor_isInjective_of_bondDim_le` | restated with `Kraus.IsNBlkInjective` conclusions. Callers that need the blocked tensor apply `isNBlkInjective_iff_blockTensor_isInjective` once | 1 / 4, 5 / 8, 2 / 2; blueprint `thm:bounded_injective_blocking_normal_left_canonical`, `lem:spc_aux_bounded_normal_fourth_power_blocking` |

Added (in `New.lean`, all elaborated): `Kraus.isInjective_iff_wordSpan_one_eq_top`,
`Kraus.wordSpan_eq_top_iff_isInjective_blockTensor` (only if D1 is decided the other way),
`Kraus.isInjective_iff_injective_traceMap`,
`MPSTensor.isNormalTensor_iff_isNormal_and_spectralRadius_eq_one`,
`MPSTensor.normality_tfae`, `MPSTensor.hasEventuallyFullWordSpan_iff_isNormal`,
`TNLean.PEPS.isVertexInjective_cycleTensorOfMPS_iff`,
`TNLean.PEPS.isVertexInjective_iff_forall_singletonRegionTensorInjective` (the evidence for
deletion, not kept), `VaryingBondChain.isBlockInjective_iff_forall_isInjectiveOn`.

#### Glossary (`docs/glossary.md` headings)

* `### Kraus.IsNormal`: bridges `Kraus.IsInjective.isNormal`, `normality_tfae`. Replace the
  caveat with the characterization of `IsNormalTensor`.
* `### MPTensor.IsNormalTensor`: meaning "normal (`Kraus.IsNormal`) with spectral radius
  one", sanctioned characterization `isNormalTensor_iff_isNormal_and_spectralRadius_eq_one`.
* `#### Kraus.IsNBlkInjective`: drop `wordSpan_eq_top_iff_isNBlkInjective`; record the three
  spellings rule.
* `#### MPOTensor.IsInjective`: deleted (and its stale "Defined in" line).
* `#### TNLean.PEPS.IsVertexInjective`: replace the bridge `singletonRegionTensorInjective`
  with `isVertexInjective_cycleTensorOfMPS_iff`.
* `#### TNLean.PEPS.IsGInjective`: add `isInjective_iff_injective_traceMap` as the MPS form
  of the trivial case.
* The closing paragraph listing `SingletonRegionTensorInjective`,
  `VertexComplementTensorInjective`, edge-middle predicates: shortened to the survivors.

#### Paper-gap notes to update

* `docs/paper-gaps/peps_injective_ft_section3_route.tex` lines 125, 133 (singleton family),
  607 (vertex complement; unchanged) and the edge-middle kernel descent paragraph.
* `docs/paper-gaps/peps_normal_ft_section3_route.tex` lines 765, 2165 (unchanged names;
  check the edge-middle references).
* `docs/paper-gaps/peps_gaugeConsistency_connectivity_gap.tex` line 271 (unchanged name).
* No note mentions `MPOTensor.IsInjective`, `HasEventuallyFullWordSpan` or `HasInjectiveBlocks`.

#### Modules deleted or merged

* `TNLean/PEPS/Injectivity/Region/SingletonRegion.lean`: deleted. Its importers (`RegionBlock/UnionClosure.lean`,
  `EdgeMiddlePhysical/Basic.lean`, `TNLean/PEPS.lean`) drop the import.
* `TNLean/PEPS/FundamentalTheorem/Injective/EdgeMiddleKernelDescent.lean`: deleted (2 importers).
* No module is named for a bridge between two formulations of one object in this family.

### Order of application

1. **QICLean first (step Q1).** Delete `HasEventuallyFullWordSpan` (24 occurrences; QICLean's
   Wielandt users switch to `IsNormal`). Add `Kraus.isNBlkInjective_of_le` (positive length,
   moved from `MPS/Tensor/Words/WordSpan.lean`, a leaf module) and
   `Kraus.isNBlkInjective_of_le_of_unital`. Then bump the pin in TNLean. The bump recompiles every
   module importing `QICLean.Kraus.Injectivity`, which is nearly the whole library. Fold it
   into an already planned pin bump.
2. **Independent, cheap, mechanical (one change):** R1, R2, R4 of `rewrite.py`; R3 after Q1.
   R1 touches only MPS/MPDO (34 files). R2 touches MPS/CanonicalForm, MPS/ParentHamiltonian,
   MPS/MPDO and Wielandt. Neither changes a definition that other modules unfold, so
   only the edited modules and their dependants rebuild.
3. **Independent, by hand:** the new characterization theorems (`New.lean`), placed in
   `NormalTensorGauge.lean`, `NormalityChain.lean`, `CycleMPSFundamentalTheorem.lean`,
   `VaryingBondBlocks.lean`. Also the `pow_four` and blocked-spelling restatements, and
   `HasInjectiveBlocks`.
4. **PEPS, by hand:** delete `SingletonRegion.lean` and the comparison structures. Then give
   the edge-middle injectivity the vertex-complement treatment and delete the second
   kernel descent. Local to `PEPS/RegionBlock`, `PEPS/EdgeMiddlePhysical` and their 6
   consumers.
5. **Deferred:** D3 (union-closure hypotheses, 47 PEPS modules) and D5 (nonzero bonds in the
   tensor type, with T.1). If D1 is taken the other way, it comes last: 133 files, and
   blueprint and paper-gap edits.

### Open decisions

* **D1. One spelling for fixed-length injectivity.** Under the rule, `IsNBlkInjective` is a
  second name either for the equation `wordSpan A N = ⊤` or for `IsInjective (blockTensor A N)`.
  Deleting it in favour of the equation is definitional, so the script can do it (R5 with `--nblk`:
  133 files / 591 occurrences, 26 sites by hand). It also needs 129 declarations renamed
  (`isNBlkInjective` in the name), 60 blueprint `\lean` entries in 43 chapter files,
  10 paper-gap notes, and dot-notation uses of `.span_eq_top` that the script cannot type.
  *Recommendation:* keep `Kraus.IsNBlkInjective` as the one name: it is the source's
  `S_N(A) = M_D` and PVWC07's condition C1. Its facts follow by unfolding to `wordSpan`, and
  `Kraus.IsNormal` is defined through it. Delete only the pass-through (R2), and
  restate theorems written with the blocked spelling only for conversion. The primitivity
  TFAE clause `∃ n, 0 < n ∧ wordSpan A n = ⊤` then reads `Kraus.IsNormal A` with no change.
* **D2. Name of `IsNormalTensor`.** The name does not say that it adds the normalization
  `ρ(E_A) = 1`. The primitivity precedent removed a name for that reason, but there it had
  a QICLean replacement. *Recommendation:* keep the name (the source's own term, 100 modules /
  301 occurrences, 19 blueprint entries), and state the difference once in its docstring and the
  glossary through the characterization theorem. Later, where a consumer uses only
  `.isNormal` (93 dot uses of `isNormal`), weaken its hypothesis to `Kraus.IsNormal`.
* **D3. Union closure as a hypothesis.** `RegionInjectivityUnionClosure (regionInjectivityDataOf A)`
  is a theorem from positive bonds (`regionInjectivityUnionClosure_of_overlap`), but 47 PEPS
  modules carry `RegionInjectivityUnionClosure κ` as a hypothesis (109 occurrences at abstract
  `κ`/`ι`). *Recommendation:* keep the abstract interface for now (it lets one argument serve a
  tensor and a pair). Strip the hypothesis from source-facing statements whose
  tensors carry positive bonds, and add a follow-up issue.
* **D4. Chain against cycle-graph carriers.** `MPSChainTensor.IsWindowInjective` and
  `IsNormalCycleArcMPS` state window injectivity on two carriers; one direction of the bridge
  is proved only for uniform bonds. *Recommendation:* leave to plan T.1 (tensor types).
  `isVertexInjective_cycleTensorOfMPS_iff` is the one-site case.
* **D5. Nonzero bonds.** `Tensor.IsInjective` against `IsVertexInjective` is the
  convention-versus-raw pattern that the degenerate-reading rule discourages. There are 215
  positivity hypotheses `∀ e, 0 < A.bondDim e` in 59 PEPS modules. *Recommendation:* bake
  `0 < bondDim e` into `TNLean.PEPS.Tensor` within T.1. Then `Tensor.IsInjective` becomes
  `IsVertexInjective`, and the `bondDim_pos` fields of six structures and the bridge
  hypotheses go away. Until then keep both.
* **D6. The `isNBlkInjective_of_le_of_canonical` variant** (3 modules) proves monotonicity from
  the PGVWC07 canonical form. *Recommendation:* replace by `isNBlkInjective_of_le` where the
  caller has a positive length. Keep it only if a caller needs length zero.

### Files and checks

* `New.lean`: every theorem listed in 4.1 "Added" elaborates against `worktrees/hot-main`
  with no `sorry`: `lake env lean New.lean` exits 0 with no messages (`elab_final.txt`).
  Two earlier runs fixed instance and rewrite errors (`elab1.txt`, `elab2.txt`).
* `rewrite.py --root <tree>` (dry run by default; `--apply` writes; `--nblk` adds R5):
  `dryrun.txt` is the dry run against the HEAD extraction, with and without R5. Apply mode
  was tested on copies of 10 affected files; the diff was as intended. It also found that
  the old `rw [IsInjective, Kraus.IsInjective, …]` must drop the first entry, which the rule
  now does.
* `count.py` and `patterns.tsv` regenerate the module counts (`counts.txt`).

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
