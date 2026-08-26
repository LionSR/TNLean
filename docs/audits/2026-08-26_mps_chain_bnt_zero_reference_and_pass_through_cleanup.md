# MPS chain, fixed-point, and BNT zero-reference and pass-through retirement

Date: 2026-08-26. Area: `TNLean/MPS/Chain/`, `TNLean/MPS/Irreducible/`, and
`TNLean/MPS/BNT/`.

This audit records the repository-local pass-through exception of
`docs/project_conventions.md` §Style together with a zero-reference deletion
slice of the open ledger entry S2 (`docs/proof_debt_ledger.md`, issue #4564).
Consumer counts were taken by `rg -w` over `TNLean`, `blueprint/src`, `docs`,
and `scripts`, then confirmed by a full `lake build` and by
`leanblueprint checkdecls` on a freshly regenerated declaration list.

## Pass-throughs

| Removed | Replacement |
|---|---|
| `IsInjectiveChain` (root namespace, `TNLean/MPS/Chain/Defs.lean`) | `MPSChainTensor.IsInjective`, which it abbreviated verbatim |
| `MPSTensor.eventually_linearIndependent_of_overlap_tendsto_orthonormal` | `MPSTensor.eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal` applied with the same argument list; the `Fin g` index type is already a `Finite` instance, so no adapter is needed |
| `MPSTensor.bntFamilies_eventually_linearIndependent` | `MPSTensor.eventually_linearIndependent_of_finite_overlap_tendsto_orthonormal`; it was a second forwarding layer over the lemma above |
| `MPSTensor.propBlockInjective_of_blocksNotGaugePhaseEquiv_directSum` | `propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords A hBlk (hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv A hIrr hLeft hOverlap hBlocks hBlk hBlk3 hInj hL)` |
| `MPSTensor.propBlockInjective_of_blocksNotGaugePhaseEquiv_directSum_c1` | the same composition with `hasPairBlockSeparatingWords_threeBlock_of_blocksNotGaugePhaseEquiv_c1` and `hBlk1` |
| `MPSTensor.exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors` | `⟨L + (r - 1) * (L + (L + L)), wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors …⟩` at the use site |
| `MPSTensor.exists_wordTupleSpanTop_of_blocksNotGaugePhaseEquiv_directSum_selectors_c1` | the same existential packaging at length `(L₀ + 1) + (r - 1) * ((L₀ + 1) + ((L₀ + 1) + (L₀ + 1)))` |

The three-layer chain in `TNLean/MPS/BNT/Basic.lean` had five live call sites
(two in `Basic.lean`, one in `Construction.lean`, two in
`PermutationRigidityPrimitive.lean`); all were rewritten to the surviving
finite-index lemma, which is the only one of the three carrying a proof.

## Zero-reference declarations with no survivor

| Removed | Replacement |
|---|---|
| `MPSChainTensor.cyclicRotation_eq_iterate_cyclicShift` | none; no consumer ever needed the iterate form. `cyclicRotation` itself is blueprint-cited and retained, as is the `@[simp]` evaluation lemma `cyclicRotation_apply` |
| `MPSTensor.exists_twoBlock_decomp_of_posSemidef_fixedPoint` | none; the canonical-form recursion uses the strict variant `exists_twoBlock_decomp_of_posSemidef_fixedPoint_strict`, which is what the blueprint tag `thm:two_block_decomp` names |

## Blueprint

The lemma node `lem:bnt_overlap_orthonormal_li` in
`blueprint/src/appendix/ft_mps/ch10_bnt_normal_and_gram_support.tex` carried
`\lean{}` tags for both retired forwarding lemmas and stated the $\{1,\ldots,g\}$
special case of the finite-index lemma directly above it. The node was deleted
and its ten references across five files repointed to
`lem:bnt_finite_index_overlap_orthonormal_li`, whose statement ("let $I$ be a
finite index set") subsumes every use. The lead-in sentence, which promised two
consequences, was made singular.

No other blueprint tag named a removed declaration.

## Retained on purpose

`MPSTensor.exists_twoBlock_decomp_of_lowerZero`
(`TNLean/MPS/Structure/InvariantSubspaceDecomp.lean`) loses its only
application with the non-strict fixed-point decomposition. It is retained
because it is blueprint-cited in
`blueprint/src/chapter/ch09_canonical_ft_reduction.tex`. The section docstring
in `TNLean/MPS/Irreducible/FixedPointProjection.lean` was retargeted to the
strict form, which is what the surviving theorem actually applies.

`docs/paper-gaps/pgvwc07_direct_sum_input.tex` cited the retired selector datum
through `\leanid{}`; the citation was moved to the surviving general theorem
`MPSTensor.propBlockInjective_of_common_blockInjective_of_pairBlockSeparatingWords`
so the footnote still substantiates its claim. The stale caveat in
`docs/glossary.md` describing the retired root alias was removed.

## Imports

No import was removed. `TNLean/MPS/BNT/DirectSumSelectors.lean` keeps its four
imports: the surviving length-`L` and Condition-C1 span theorems still consume
`MPDO.BiCFDerivation.Selectors` and the file-level `variable {d L : ℕ}`.
