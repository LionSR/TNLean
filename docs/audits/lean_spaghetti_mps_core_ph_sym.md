# Lean Spaghetti Audit 2

Method notes: line counts come from raw files; `sorry` counts are **actual placeholders** after stripping comments/docstrings; `simp without only` counts only plain `simp` tactic uses, not `@[simp]` attributes; `decide` usage was checked across all audited files and none was found.

## Global Summary

- Audited files: 34
- Actual `sorry`s: 6 total across 4 files (`DegenerateGS`, `Martingale`, `UniqueGroundState`, `StructuralForm`)
- Files over 500 lines that should be split: `Symmetry/StringOrder.lean` (575), `Symmetry/StringOrderAux.lean` (829)
- Worst proof-fragility hotspots: `ParentHamiltonian/WrappingWindow.lean`, `Symmetry/StringOrderAux.lean`, `ParentHamiltonian/CyclicWindow.lean`, `ParentHamiltonian/UniqueGroundState.lean`
- No audited file uses `decide`; `omega` usage is concentrated in `ParentHamiltonian/*` and is especially heavy in `CyclicWindow.lean` and `WrappingWindow.lean`.

## TNLean/MPS/Core

### `TNLean/MPS/Core/Blocking.lean`

- Size / placeholders: 261 lines, 0 actual `sorry`.
- Long proofs >50 lines: `sum_evalWord_conjTranspose_mul_evalWord` (80 lines, 95-179).
- Automation counts: plain `simp` 13, `omega` 0, `decide` 0.
- Long proof: `sum_evalWord_conjTranspose_mul_evalWord` ([TNLean/MPS/Core/Blocking.lean:95](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Core/Blocking.lean:95), 80 lines). It is private and internal-only; worth splitting into one lemma for the block-diagonal trace rewrite and one for the final canonicality step.
- No actual `sorry`, no TODO/FIXME/HACK, no dead commented-out code. Plain `simp` is used 13 times; no `omega`/`decide`.

### `TNLean/MPS/Core/BlockingInfrastructure.lean`

- Size / placeholders: 261 lines, 0 actual `sorry`.
- Long proofs >50 lines: `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks` (61 lines, 68-137).
- Automation counts: plain `simp` 3, `omega` 0, `decide` 0.
- Long proof: `sameMPV₂_blockTensor_of_sameMPV₂_toTensorFromBlocks` ([TNLean/MPS/Core/BlockingInfrastructure.lean:68](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Core/BlockingInfrastructure.lean:68), 61 lines). The proof is structurally okay but dense enough to merit an intermediate lemma around `sameMPV₂` transport through blocking.
- Otherwise clean: no `sorry`, no TODOs, no dead code, 3 plain `simp`, no `omega`/`decide`.

### `TNLean/MPS/Core/BlockingTransfer.lean`

- Size / placeholders: 103 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 3, `omega` 0, `decide` 0.
- No `sorry` and no >50-line proof. The file is compact; 3 plain `simp`, no `omega`/`decide`.
- No dead commented code or stale TODOs. No obvious copy-paste problem.

### `TNLean/MPS/Core/CPPrimitive.lean`

- Size / placeholders: 121 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 2, `omega` 0, `decide` 0.
- No `sorry` and no long proof. Internal-only helper: `invariance_implies_complement_zero` ([TNLean/MPS/Core/CPPrimitive.lean:35](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Core/CPPrimitive.lean:35)) is not referenced outside the file.
- Otherwise clean: 2 plain `simp`, no TODOs, no `omega`/`decide`, no dead code.

### `TNLean/MPS/Core/Correlations.lean`

- Size / placeholders: 109 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Clean small file. No `sorry`, no long proof, no TODOs, no dead code, no `omega`/`decide`.

### `TNLean/MPS/Core/MultiBlock.lean`

- Size / placeholders: 155 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 9, `omega` 0, `decide` 0.
- No `sorry` and no >50-line proof. The file relies on 9 plain `simp` calls but nothing looks excessive for its size.
- No dead code or stale TODOs. No obvious copy-paste proof block.

### `TNLean/MPS/Core/TPGauge.lean`

- Size / placeholders: 144 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 3, `omega` 0, `decide` 0.
- No `sorry` and no long proof. 3 plain `simp`, no `omega`/`decide`.
- File-local helper lemmas are reasonable; no stale comments or dead code.

### `TNLean/MPS/Core/Transfer.lean`

- Size / placeholders: 57 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 2, `omega` 0, `decide` 0.
- Very small and clean. No `sorry`, no long proof, 2 plain `simp`, no TODOs, no dead code.

## TNLean/MPS/ParentHamiltonian

### `TNLean/MPS/ParentHamiltonian/Basic.lean`

- Size / placeholders: 134 lines, 0 actual `sorry`.
- Long proofs >50 lines: `mpv_window_mem_groundSpace` (52 lines, 56-109).
- Automation counts: plain `simp` 3, `omega` 8, `decide` 0.
- Long proof: `mpv_window_mem_groundSpace` ([TNLean/MPS/ParentHamiltonian/Basic.lean:56](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Basic.lean:56), 52 lines). It is arithmetic-heavy and would read better if the cyclic-index arithmetic were pulled into standalone lemmas.
- Uses `omega` 8 times in 134 lines. Internal-only helper: `trace_evalWord_append_comm` ([TNLean/MPS/ParentHamiltonian/Basic.lean:44](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Basic.lean:44)). No `sorry`, no TODOs, no dead code.

### `TNLean/MPS/ParentHamiltonian/Commuting.lean`

- Size / placeholders: 73 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Clean definition/API file. No `sorry`, no long proofs, no TODOs, no dead code, no `simp`/`omega`/`decide` concerns.

### `TNLean/MPS/ParentHamiltonian/CyclicWindow.lean`

- Size / placeholders: 241 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 16, `omega` 36, `decide` 0.
- No `sorry`, but this is one of the clearer spaghetti hotspots despite its moderate size: 16 plain `simp` and 36 `omega` uses in 241 lines.
- Copy-paste/mirror pattern: `contiguousRestrictₗ_restrictLast` ([TNLean/MPS/ParentHamiltonian/CyclicWindow.lean:56](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/CyclicWindow.lean:56)) and `contiguousRestrictₗ_restrictFirst` ([TNLean/MPS/ParentHamiltonian/CyclicWindow.lean:84](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/CyclicWindow.lean:84)) are near-mirror proofs with repeated window/cast arithmetic. A generic “peel left/right site from contiguous window” lemma would remove a lot of duplication.
- No true commented-out code blocks and no stale TODOs.

### `TNLean/MPS/ParentHamiltonian/Decorrelation.lean`

- Size / placeholders: 239 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- No `sorry`, no long proof, no `simp`/`omega` pressure. The file looks structurally fine.
- One TODO at [TNLean/MPS/ParentHamiltonian/Decorrelation.lean:136](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Decorrelation.lean:136) about tensor-product locality constraints. This reads as an active design TODO, not obviously stale.

### `TNLean/MPS/ParentHamiltonian/Defs.lean`

- Size / placeholders: 152 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 3, `decide` 0.
- No `sorry` and no long proof. Internal-only helper: `offset_mod_eq` ([TNLean/MPS/ParentHamiltonian/Defs.lean:96](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Defs.lean:96)) is not referenced outside this file.
- Light arithmetic only: 3 `omega`, 0 plain `simp` hits under the stricter count, no dead code or TODOs.

### `TNLean/MPS/ParentHamiltonian/DegenerateGS.lean`

- Size / placeholders: 141 lines, 1 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 3, `omega` 2, `decide` 0.
- Actual `sorry`: `parentHamiltonian_gs_eq_bnt_span` ([TNLean/MPS/ParentHamiltonian/DegenerateGS.lean:135](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/DegenerateGS.lean:135)). The nearby TODO references issue `#195` and is still active, not stale.
- This `sorry` is not independently closable from only nearby lemmas today: `bnt_mem_groundSpace` gives the easy inclusion, but the reverse inclusion still depends on unresolved uniqueness machinery from `UniqueGroundState`. Once those upstream theorems are finished, this theorem should collapse to a short assembly argument.
- No long proof. One private helper (`groundSpace_block_le_assembled`) is file-local by design. No dead commented-out code beyond a prose proof note.

### `TNLean/MPS/ParentHamiltonian/GroundSpace.lean`

- Size / placeholders: 75 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 6, `omega` 1, `decide` 0.
- Small, clean API file. No `sorry`, no long proof, 6 plain `simp`, only 1 `omega`, no dead code or stale TODOs.

### `TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean`

- Size / placeholders: 369 lines, 0 actual `sorry`.
- Long proofs >50 lines: `groundSpace_intersection` (107 lines, 253-362).
- Automation counts: plain `simp` 16, `omega` 3, `decide` 0.
- Long proof: `groundSpace_intersection` ([TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean:253](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/IntersectionProperty.lean:253), 107 lines). This is the main hotspot in the file and would benefit from being cut into inclusion lemmas plus a separate finrank argument.
- No `sorry`. Moderate automation: 16 plain `simp`, 3 `omega`. No dead code or stale TODOs.

### `TNLean/MPS/ParentHamiltonian/Martingale.lean`

- Size / placeholders: 68 lines, 1 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Actual `sorry`: `parentHamiltonian_gapped` ([TNLean/MPS/ParentHamiltonian/Martingale.lean:60](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Martingale.lean:60)).
- The TODO at [TNLean/MPS/ParentHamiltonian/Martingale.lean:59](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/Martingale.lean:59) is broad and aging: it names the intended literature route but leaves no decomposition into formalizable sublemmas.
- This `sorry` is not closable by nearby lemmas; the missing martingale estimate and spectral-gap packaging are not present locally.

### `TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean`

- Size / placeholders: 430 lines, 3 actual `sorry`.
- Long proofs >50 lines: `allZero_contradiction` (57 lines, 158-217); `chainGroundSpace_eq_mpvSubmodule` (61 lines, 294-356).
- Automation counts: plain `simp` 10, `omega` 11, `decide` 0.
- Actual `sorry`s: `chainGroundSpace_eq_mpvSubmodule_normal` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:357](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:357)), `parentHamiltonian_unique_gs_injective` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:404](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:404)), and `parentHamiltonian_unique_gs_normal` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:424](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:424)).
- Two wrapper sorries are almost mechanically closable once the upstream equalities exist: the commented proof scripts at [TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:400](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:400) and [TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:420](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:420) already spell out the intended 3-line proof.
- The remaining non-wrapper `sorry` (`chainGroundSpace_eq_mpvSubmodule_normal`) is not locally closable; the file itself says the range-reduction step is missing.
- Stale comment: the TODO at [TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:91](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:91) says `chainGroundSpace` will be defined once periodic window maps are in place, but the very next definition already does that via `cyclicRestrictₗ`.
- True commented-out code block: lines [400](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:400)-[423](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:423) contain two disabled proof scripts. These should either become live proofs once dependencies land or be removed.
- Long proofs: `allZero_contradiction` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:158](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:158), 57 lines) and `chainGroundSpace_eq_mpvSubmodule` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:294](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:294), 61 lines). The file also has 10 plain `simp` and 11 `omega` uses.
- Unused helper candidate: `eq_zero_of_trace_evalWord_mul_eq_zero` ([TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:267](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/UniqueGroundState.lean:267)) appears to have no references inside or outside the file.

### `TNLean/MPS/ParentHamiltonian/WrappingWindow.lean`

- Size / placeholders: 357 lines, 0 actual `sorry`.
- Long proofs >50 lines: `wrapping_window_matEq` (73 lines, 181-264); `boundary_matrix_commutes` (87 lines, 265-357).
- Automation counts: plain `simp` 14, `omega` 70, `decide` 0.
- This is the heaviest arithmetic hotspot in `ParentHamiltonian`: 14 plain `simp`, 70 `omega`, two `set_option maxHeartbeats 800000` escapes, and two long proofs.
- Long proofs: `wrapping_window_matEq` ([TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:181](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:181), 73 lines) and `boundary_matrix_commutes` ([TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:265](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:265), 87 lines).
- Copy-paste pattern: `cyclicCfg_last_eq`, `cyclicCfg_window_site`, and `cyclicCfg_complement_site` ([TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:65](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:65)-[104](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/ParentHamiltonian/WrappingWindow.lean:104)) repeat the same offset-normalization / `omega` skeleton and should share a helper about the wrapped index formula.
- Internal-only helpers: the five private theorems from `cyclicCfg_last_eq` through `wrapping_window_matEq` are only used in this file. They are justified, but the amount of file-local scaffolding is a sign the proof should be decomposed differently.

## TNLean/MPS/RFP

### `TNLean/MPS/RFP/Assembly.lean`

- Size / placeholders: 43 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Clean tiny bridge file. No `sorry`, no long proof, no TODOs, no dead code, no automation issues.

### `TNLean/MPS/RFP/Convergence.lean`

- Size / placeholders: 105 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- No `sorry` and no long proof.
- The TODO at [TNLean/MPS/RFP/Convergence.lean:29](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Convergence.lean:29) is underspecified (“formalize the convergence in operator norm”). It reads stale/aging because it names no missing lemmas or next step.

### `TNLean/MPS/RFP/Decorrelation.lean`

- Size / placeholders: 379 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- No actual `sorry` despite the docstring calling that out explicitly. No long proof and no automation hotspots.
- Main spaghetti signal is API duplication, not proof fragility: `HasCommutingParentHam.pAX_comp_pK` through `.pK_comp_pAX` ([TNLean/MPS/RFP/Decorrelation.lean:175](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Decorrelation.lean:175)-[207](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Decorrelation.lean:207)) and the `IsDecorrelated` monotonicity/empty/union lemmas ([TNLean/MPS/RFP/Decorrelation.lean:294](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Decorrelation.lean:294)-[367](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Decorrelation.lean:367)) are template-like and could be reduced with small generic helpers.

### `TNLean/MPS/RFP/Defs.lean`

- Size / placeholders: 158 lines, 0 actual `sorry`.
- Long proofs >50 lines: `isRFP_of_kraus_isometry` (62 lines, 46-112).
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Long proof: `isRFP_of_kraus_isometry` ([TNLean/MPS/RFP/Defs.lean:46](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/Defs.lean:46), 62 lines). It is self-contained but worth splitting if this file grows.
- No `sorry`, no TODOs, no automation smell.

### `TNLean/MPS/RFP/StructuralForm.lean`

- Size / placeholders: 111 lines, 1 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Actual `sorry`: `rfp_nt_structural` ([TNLean/MPS/RFP/StructuralForm.lean:52](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/StructuralForm.lean:52)). The TODO at [50](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/RFP/StructuralForm.lean:50) is precise and still active, not stale.
- This `sorry` is not closable from nearby lemmas: the file explicitly depends on missing theory for rank-1 idempotent CPTP maps and rectangular Kraus freedom. The two downstream theorems are thin wrappers and are already fine.

### `TNLean/MPS/RFP/ZeroCorrelationLength.lean`

- Size / placeholders: 133 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 3, `decide` 0.
- No `sorry`, no long proof. Only 3 `omega` calls, no dead code, no stale TODOs.

## TNLean/MPS/Symmetry

### `TNLean/MPS/Symmetry/CocycleCoboundary.lean`

- Size / placeholders: 105 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- No `sorry`, no long proof, no TODOs, no dead code, no automation concerns.

### `TNLean/MPS/Symmetry/Defs.lean`

- Size / placeholders: 80 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 3, `omega` 0, `decide` 0.
- Small and clean. No `sorry`, no long proof. 3 plain `simp`; no `omega`/`decide`.

### `TNLean/MPS/Symmetry/GaugeUniqueness.lean`

- Size / placeholders: 107 lines, 0 actual `sorry`.
- Long proofs >50 lines: `gauge_unique_up_to_scalar` (71 lines, 23-98).
- Automation counts: plain `simp` 6, `omega` 0, `decide` 0.
- Long proof: `gauge_unique_up_to_scalar` ([TNLean/MPS/Symmetry/GaugeUniqueness.lean:23](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/GaugeUniqueness.lean:23), 71 lines).
- No `sorry`, but the proof would benefit from extracting the “commutes with all generators implies scalar” center argument. 6 plain `simp`, no `omega`/`decide`.

### `TNLean/MPS/Symmetry/OnSiteSymmetry.lean`

- Size / placeholders: 42 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 2, `omega` 0, `decide` 0.
- Tiny and clean. No `sorry`, no long proof, 2 plain `simp`, no TODOs or dead code.

### `TNLean/MPS/Symmetry/StringOrder.lean`

- Size / placeholders: 575 lines, 0 actual `sorry`.
- Long proofs >50 lines: `gaugePhaseEquiv_twisted_of_hasStringOrder` (52 lines, 147-206).
- Automation counts: plain `simp` 15, `omega` 0, `decide` 0.
- This file is over the 500-line threshold (575 lines) and should be split. Natural cut points: (1) spectral-radius/gauge-phase lemmas, (2) local-symmetry/string-order equivalence, (3) same-phase/SPT invariance.
- Long proof: `gaugePhaseEquiv_twisted_of_hasStringOrder` ([TNLean/MPS/Symmetry/StringOrder.lean:147](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrder.lean:147), 52 lines). The rest of the file is not individually huge, but the module bundles too many conceptually different results.
- 15 plain `simp`, no `omega`/`decide`, no `sorry`. Internal-only helper: `twistedTransfer_virtual_rep_fixed` ([TNLean/MPS/Symmetry/StringOrder.lean:442](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrder.lean:442)) is not used outside this file.

### `TNLean/MPS/Symmetry/StringOrderAux.lean`

- Size / placeholders: 829 lines, 0 actual `sorry`.
- Long proofs >50 lines: `twistedTPGaugeSetup_hasEigenvalue` (101 lines, 254-361); `virtualUnitary_of_gaugePhaseEquiv_twisted` (260 lines, 362-631); `boundaryState_invariant_of_virtualUnitary` (137 lines, 680-829).
- Automation counts: plain `simp` 93, `omega` 0, `decide` 0.
- Largest spaghetti hotspot in the audit. The file is 829 lines and should be split aggressively: TP-gauge transport/setup, gauge-phase to virtual-unitary normalization, and boundary-state invariance are three separate topics.
- Long proofs: `twistedTPGaugeSetup_hasEigenvalue` ([TNLean/MPS/Symmetry/StringOrderAux.lean:254](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:254), 101 lines), `virtualUnitary_of_gaugePhaseEquiv_twisted` ([TNLean/MPS/Symmetry/StringOrderAux.lean:362](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:362), 260 lines), and `boundaryState_invariant_of_virtualUnitary` ([TNLean/MPS/Symmetry/StringOrderAux.lean:680](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:680), 137 lines).
- Automation smell: 93 plain `simp` calls and a `set_option maxHeartbeats 800000` at [42](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:42). This is the strongest sign of brittle proof search in the audited set.
- Copy-paste pattern: long conjugation/sum-transport calculations recur across `virtualUnitary_of_gaugePhaseEquiv_twisted` and `boundaryState_invariant_of_virtualUnitary` (for example the repeated `transferMap_apply`/`Finset.smul_sum`/`Matrix.mul_assoc` rewrites around [420](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:420)-[429](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:429) and [745](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:745)-[793](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderAux.lean:793)). That should become a reusable transport lemma.

### `TNLean/MPS/Symmetry/StringOrderDefs.lean`

- Size / placeholders: 458 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 12, `omega` 0, `decide` 0.
- Not over 500 lines (458), but already dense. No `sorry` and no >50-line proof.
- Internal-only helpers not referenced outside the file: `stringOrderParam_eq_trace_mixedTransfer` ([TNLean/MPS/Symmetry/StringOrderDefs.lean:147](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderDefs.lean:147)), `stringOrderParam_one_eq_one` ([TNLean/MPS/Symmetry/StringOrderDefs.lean:157](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderDefs.lean:157)), and `stringOrderBoundaryParam_one_one` ([TNLean/MPS/Symmetry/StringOrderDefs.lean:200](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/StringOrderDefs.lean:200)).
- 12 plain `simp`, no `omega`/`decide`, no dead code.

### `TNLean/MPS/Symmetry/SymmetricMPS.lean`

- Size / placeholders: 39 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 0, `omega` 0, `decide` 0.
- Tiny and clean. No `sorry`, no long proof, no TODOs, no dead code.

### `TNLean/MPS/Symmetry/VirtualRepresentation.lean`

- Size / placeholders: 156 lines, 0 actual `sorry`.
- Long proofs >50 lines: none.
- Automation counts: plain `simp` 1, `omega` 0, `decide` 0.
- No `sorry`, no long proof. Private helpers `twistedTensor_gaugeEquiv` ([TNLean/MPS/Symmetry/VirtualRepresentation.lean:55](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/VirtualRepresentation.lean:55)) and `gauge_product_intertwines` ([TNLean/MPS/Symmetry/VirtualRepresentation.lean:70](/Users/siruilu/Library/Mobile Documents/com~apple~CloudDocs/Research/Agent-Physics/MPSLean/TNLean/MPS/Symmetry/VirtualRepresentation.lean:70)) are internal-only but used locally, so not dead.
- Otherwise clean: 1 plain `simp`, no TODOs, no `omega`/`decide`.
