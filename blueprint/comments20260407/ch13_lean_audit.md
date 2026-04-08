# Chapter 13 audit: `ch13_algebraic_ft.tex`

## Scope

Read:

- `blueprint/src/chapter/ch13_algebraic_ft.tex` (full file)
- all files in `TNLean/MPS/Chain/`
- `TNLean/PEPS/FundamentalTheorem.lean`
- the tagged declaration source files needed to identify the actual Lean statements

Checks performed:

- extracted every `\lean{...}` tag in chapter 13
- checked non-PEPS tags against the built environment with `import TNLean`
- checked PEPS source directly with `lake env lean TNLean/PEPS/FundamentalTheorem.lean`
- searched for empty `\lean{}` tags
- checked direct `sorry` usage in the tagged declaration files

## Global findings

- Empty `\lean{}` tags: none.
- Non-PEPS tags: all checked names resolve in the built environment.
- PEPS tags: the declarations exist in `TNLean/PEPS/FundamentalTheorem.lean`, but `import TNLean.PEPS.FundamentalTheorem` currently fails because the `.olean` is not built/present. The source file itself elaborates, with `sorry` warnings on the theorem declarations.
- `\leanok` that should be `\notready` because the tagged declaration itself uses `sorry`: none found outside PEPS.
- `\notready` that are attached to sorry-free declarations:
  - `MPSChainTensor.fundamentalTheorem_blockedChain` is sorry-free, but the blueprint statement is much stronger than the actual Lean theorem, so this is not a safe mechanical `\notready -> \leanok` change.

## High-priority mismatches

### `physRealize_mul`

- Blueprint statement is strictly weaker than Lean.
- Blueprint: assumes `{A^i}` is a basis of `M_D(C)` (`d = D^2` and linear independence) and proves multiplicativity only in that basis case.
- Lean: `MPSTensor.physRealize_mul` proves multiplicativity for every injective tensor `A`, with no basis/linear-independence hypothesis.
- Consequence: the theorem statement in the blueprint should be strengthened, and Remark `rem:physRealize_mul_general` is outdated relative to Lean.

### `virtual_bond_gauge`

- This is the largest statement mismatch in the chapter.
- Blueprint states a fixed-length non-TI chain theorem:
  - arbitrary chain length `n >= 3`
  - same chain state
  - any bond position `k`
  - conclusion phrased as equality of blocked physical-realisation maps `O_{A,k}` and `O_{B,k}`
  - uniqueness up to scalar
- Lean `MPSTensor.virtual_bond_gauge` is only a 3-site theorem:
  - inputs `A B : Fin 3 -> MPSTensor d D`
  - hypotheses `hA : ∀ k, IsInjective (A k)`, `_hB : ∀ k, IsInjective (B k)`
  - hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`, not `SameState`
  - conclusion is equality of `virtualInsertCoeff` trace expressions at the middle bond, not equality of `physRealize` maps
  - no uniqueness clause
- Also omitted in blueprint: Lean requires `[NeZero D]`.

### `chainCombinedTensor_isInjective`

- The tag is attached to a theorem whose mathematical content does not match the blueprint lemma title/body.
- Blueprint lemma `blocking_preserves_injectivity` states injectivity of the physically blocked tensor whose entries are products
  `A_0^{i_0} ... A_{m-1}^{i_{m-1}}`.
- Lean `MPSTensor.chainCombinedTensor_isInjective` says:
  if one site tensor `A k` is injective, then the combined tensor
  `chainCombinedTensor A`, which just repackages the entries `A k i`, is injective.
- This is not the same object as the blocked product tensor.

### `fundamentalTheorem_injective_chain`

- Blueprint states the paper-level fixed-length theorem:
  - both chains injective
  - `n >= 3`
  - same chain state
  - uniqueness up to common scalar
- Lean `MPSChainTensor.fundamentalTheorem_injective_chain` states:
  - only `A` injective
  - hypothesis `SameMPV (chainCombinedTensor A) (chainCombinedTensor B)`, stronger than same-state
  - no `n >= 3`
  - conclusion only `GaugeEquiv A B`
- The displayed conjugation convention differs too:
  - blueprint: `B_k^i = Z_k^{-1} A_k^i Z_{k+1}`
  - Lean `GaugeEquiv`: `B k i = Z k * A k i * (Z (cyclicSucc k))⁻¹`
  - these are equivalent up to renaming inverses, but not literally the same formula.

### `fundamentalTheorem_blockedChain`

- This tag is attached to a theorem with a very different statement.
- Blueprint corollary claims a normal-MPS fixed-length theorem for original non-TI site tensors, from same state, recovering site-by-site gauges.
- Lean `MPSChainTensor.fundamentalTheorem_blockedChain` only says:
  - for single tensors `A B`
  - if `A` is `L`-block injective
  - and the blocked constant chains satisfy `SameMPV` on their combined tensors
  - then the blocked chains are gauge equivalent.
- Lean says nothing about:
  - same-state bridge
  - non-TI chains
  - recovering gauges for the original unblocked site tensors.
- Status note: the Lean declaration is sorry-free, but the blueprint theorem is not a match for it.

## Tag-by-tag audit

Legend:

- `Match`: blueprint matches Lean up to harmless notation/packaging
- `Partial`: same mathematical result, but blueprint omits hypotheses or states a specialization/repackaging
- `Mismatch`: the tagged Lean declaration does not match the blueprint statement

| Blueprint tag | Verdict | Findings |
| --- | --- | --- |
| `MPSTensor.IsInjective.exists_rightInverse` | Match | Blueprint matches the Lean theorem: injectivity gives a linear right inverse of the linear-combination map. |
| `MPSTensor.decompositionMap` | Match | Correctly describes a chosen right inverse. |
| `MPSTensor.IsInjective.exists_decomposition` | Match | Correct. |
| `MPSTensor.physRealize` | Match | Definition matches. The blueprint also mentions linearity; in Lean that is a separate theorem `physRealize_linear`, not part of this definition. |
| `MPSTensor.physRealize_spec` | Match | Correct. |
| `MPSTensor.physRealize_mul` | Mismatch | Blueprint weakens Lean by adding an unnecessary basis hypothesis. Lean proves multiplicativity for every injective tensor. |
| `MPSTensor.chainCombinedTensor_isInjective` | Mismatch | Blueprint states injectivity of a blocked product tensor; Lean proves injectivity of the repackaged combined tensor `chainCombinedTensor`. |
| `Matrix.isScalar_of_commute_span_eq_top` | Partial | Blueprint states the special case “commutes with all of `M_D`”; Lean is more general: commuting with a spanning set suffices. |
| `MPSTensor.virtual_bond_gauge` | Mismatch | Blueprint paper statement is much stronger/different than the formalized 3-site `SameMPV` theorem. Missing `[NeZero D]`; no uniqueness in Lean. |
| `MPSTensor.tensor_proportional` | Match | The formal hypotheses and conclusion agree with the blueprint. |
| `MPSChainTensor.fundamentalTheorem_injective_chain` | Mismatch | Blueprint uses same-state at fixed length and includes uniqueness; Lean uses stronger `SameMPV` hypothesis and only concludes `GaugeEquiv`. |
| `MPSTensor.SameMPVFrom` | Match | Correct. Same bond dimension is implicit in the Lean type. |
| `MPSTensor.sameMPV_of_sameMPVFrom_of_injective` | Partial | Missing Lean hypothesis `[NeZero D]`. |
| `MPSTensor.fundamentalTheorem_singleBlock_finiteLength` | Partial | Missing Lean hypothesis `[NeZero D]`. |
| `MPSChainTensor.ti_tensors_collapse_to_single_gauge` | Partial | Lean assumes `0 < n` and `SameMPV` on combined tensors, not same-state at `n >= 3`; Lean has no uniqueness clause. `IsUnit Z` is used instead of `Z : GL`. |
| `MPSChainTensor.fundamentalTheorem_blockedChain` | Mismatch | Tagged Lean theorem is an endpoint about blocked constant chains, not the blueprint’s normal-MPS fixed-length theorem on original site tensors. |
| `MPSTensor.perBlockLinearExtension` | Partial | Blueprint matches the idea, but Lean also carries `[∀ k, NeZero (dim k)]` in the surrounding section. The “unique” part is not encoded in this declaration itself, only in the construction it chooses from. |
| `MPSTensor.perBlockLinearExtension_mul` | Match | Correct. |
| `MPSTensor.perBlockLinearExtension_bijective` | Partial | Missing Lean assumption `[∀ k, NeZero (dim k)]`. |
| `MPSTensor.piAlgEquiv` | Partial | Missing Lean assumption `[∀ k, NeZero (dim k)]`. |
| `MPSTensor.piAlgEquiv_decomposition` | Match | Correct at the level of mathematical content; Lean also carries the dimension-equality witness `hDeq`. |
| `MPSTensor.piTrace_mul_right_eq_zero` | Match | Correct. |
| `MPSTensor.piTraceMulRightPi_ker_eq_bot` | Match | Correct. The blueprint states injectivity; Lean states kernel `= ⊥`. |
| `MPSTensor.fundamentalTheorem_multiBlock_full` | Match | Correct. |
| `MPSTensor.perBlock_sameMPV_iff_gaugeEquiv` | Match | Correct. |
| `MPSTensor.IsCanonicalForm` | Match | Blueprint matches the bundled Lean structure: injective blocks, left-canonical, strictly ordered nonzero weights, normalized self-overlap. |
| `MPSTensor.IsNormalCanonicalForm` | Partial | Blueprint says “canonical-form conditions plus irreducible and primitive.” Lean does not literally extend `IsCanonicalForm`; it stores irreducible, left-canonical, primitive, strict nonzero weights, and `dim_pos`. |
| `MPSTensor.per_block_sameMPV_of_canonical_form` | Partial | Lean hypothesis is `SameMPV₂ (toTensorFromBlocks μ A) (toTensorFromBlocks μ B)`, not plain `SameMPV`; also requires `[∀ k, NeZero (dim k)]`. |
| `MPSTensor.fundamentalTheorem_canonicalForm` | Partial | Same issue as above: Lean uses `SameMPV₂` and `[∀ k, NeZero (dim k)]`. |
| `MPSTensor.fundamentalTheorem_canonicalForm_explicit` | Partial | Same issue as above: Lean uses `SameMPV₂` and `[∀ k, NeZero (dim k)]`. |
| `MPSChainTensor.ti_reduction_corollary` | Match | Correct. |
| `MPSChainTensor.ti_reduction_of_sameState` | Partial | Blueprint omits the explicit bridge hypothesis `SameStateBridgeHyp d D`. The prose alludes to the bridge, but the Lean theorem takes it as a formal argument. |
| `MPSTensor.gauge_ratio_commutes` | Match | Same content. Lean packages it pointwise in `i` rather than as a single `∀ i` conclusion. |
| `MPSTensor.gauge_ratio_isScalar` | Match | Correct. |
| `MPSTensor.gaugeMatrix_projective_mul` | Match | Correct. |
| `TNLean.PEPS.edgeGaugeAt` | Match in source | Source declaration matches the blueprint. Additional note: `TNLean.PEPS.FundamentalTheorem` is not currently available as a built importable module. |
| `TNLean.PEPS.gaugeVertex` | Match in source | Source declaration matches the blueprint. Same importability note as above. |
| `TNLean.PEPS.applyGauge` | Match in source | Source declaration matches the blueprint. Same importability note as above. |
| `TNLean.PEPS.GaugeEquiv` | Match in source | Source declaration matches the blueprint. Same importability note as above. |
| `TNLean.PEPS.applyGauge_stateCoeff` | Match in source | Statement matches. `\notready` is correct: the theorem uses `sorry`. Same importability note as above. |
| `TNLean.PEPS.GaugeEquiv.sameState` | Match in source | Statement matches. `\notready` is correct: the theorem uses `sorry`. Same importability note as above. |
| `TNLean.PEPS.localTensorEval` | Match in source | Definition matches. Same importability note as above. |
| `TNLean.PEPS.localGauge_exists` | Partial in source | Blueprint is too terse. Lean also requires `hDim : A.bondDim = B.bondDim` and concludes an explicit family of edge gauges satisfying a concrete formula. `\notready` is correct. |
| `TNLean.PEPS.gaugeConsistency` | Partial in source | Blueprint omits Lean hypothesis `hDim : A.bondDim = B.bondDim`. `\notready` is correct. |
| `TNLean.PEPS.fundamentalTheorem_PEPS` | Match in source | High-level statement matches. `\notready` is correct: the proof still uses `sorry`. |
| `TNLean.PEPS.gauge_unique_up_to_scalar` | Partial in source | Blueprint gives the headline result; Lean states a more concrete theorem with explicit gauge families `X`, `Y`, connectedness, injectivity, and dimension equality hypotheses. `\notready` is correct. |

## Readiness audit

### `\notready` that look correct

- `TNLean.PEPS.applyGauge_stateCoeff`
- `TNLean.PEPS.GaugeEquiv.sameState`
- `TNLean.PEPS.localGauge_exists`
- `TNLean.PEPS.gaugeConsistency`
- `TNLean.PEPS.fundamentalTheorem_PEPS`
- `TNLean.PEPS.gauge_unique_up_to_scalar`

Reason: `lake env lean TNLean/PEPS/FundamentalTheorem.lean` reports direct `sorry` warnings on those theorem declarations.

### `\notready` that need manual review

- `MPSChainTensor.fundamentalTheorem_blockedChain`

Reason:

- the tagged Lean declaration is sorry-free
- but the blueprint theorem statement does not match the tagged Lean declaration

So this is not a safe “flip to `\leanok`”; it needs a statement/tag decision first.

### `\leanok` that should become `\notready`

- None found among the tagged declarations audited here.

## Specific answers to requested spot-checks

### `physRealize_mul`: does the blueprint weaken the Lean theorem?

Yes.

- Blueprint adds a basis hypothesis (`d = D^2` and linear independence).
- Lean proves multiplicativity for every injective tensor, with no basis hypothesis.

### `virtual_bond_gauge`: does the blueprint statement match Lean?

No.

- Blueprint states a chain-level fixed-length same-state theorem with bond index `k`, blocked physical-realisation maps, and uniqueness up to scalar.
- Lean only proves a 3-site `SameMPV` theorem about equality of `virtualInsertCoeff` trace expressions on the middle bond.

### Empty `\lean{}` tags

- None in `blueprint/src/chapter/ch13_algebraic_ft.tex`.
