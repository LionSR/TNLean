# One definition per notion of primitivity (2026-11-16)

Issue #10724, the first case of follow-on F4 of
`docs/many_body_circuit_architecture.md`, asked that the nine predicate names
around primitivity be reduced to the three notions they cover, under the rule
"one definition per notion": a source's formulation is honoured by a theorem
whose statement is the source's, not by a predicate per source.

## The notions that remain

| Notion | Definition |
|---|---|
| The peripheral spectrum is `{1}` | `_root_.IsPrimitive`, applied to `Kraus.transferMap A` |
| Some positive word length spans the matrix algebra | `Kraus.IsNormal` |
| Left-canonical, with a fixed point and spectral radius below one on its complement | `Kraus.HasComplementaryFixedPointGap`, with the reducible abbreviation `MPSTensor.IsPrimitiveMPS` |

`MPSTensor.IsPrimitiveMPS` and `Kraus.HasComplementaryFixedPointGap` are two
names of the third notion. Which name survives is not decided; it needs a
QICLean change, and this audit leaves both untouched.

## Proposition 3 of arXiv:0909.5347

The source introduces three properties of a channel
(`Papers/0909.5347/main.tex:403-430`) and proves them equivalent
(Proposition 3, `:501-509`). The proposition is now the single theorem
`MPSTensor.primitivity_tfae` of `TNLean/Wielandt/Primitivity/Equivalence.lean`:
for `[NeZero D]` and `∑ i, (A i)ᴴ * A i = 1`, a `List.TFAE` of

1. `∃ q, 0 < q ∧ ∀ φ, φ ≠ 0 → Kraus.vectorSpreadSpan A φ q = ⊤`;
2. `∃ n, 0 < n ∧ Kraus.wordSpan A n = ⊤`, which is `Kraus.IsNormal A` by
   definition;
3. `∃ ρ, ρ.PosDef ∧ Kraus.transferMap A ρ = ρ ∧
   (∀ σ, Kraus.transferMap A σ = σ → ∃ c, σ = c • ρ) ∧
   IsPrimitive (Kraus.transferMap A)`.

Clause 3 is the source's literal one. The former predicate
`IsStronglyIrreduciblePaper` added an irreducibility conjunct; irreducibility
is now a conclusion (`MPSTensor.isIrreducibleMap_transferMap_of_isNormal`).

## Removed predicates

| Removed | Replacement |
|---|---|
| `MPSTensor.IsPeripherallyPrimitive A` | `IsPrimitive (Kraus.transferMap A)`, of which it was an abbreviation |
| `MPSTensor.HasPrimitiveFixedPoint A` | `Kraus.HasPrimitiveFixedPoint A`, of which it was an abbreviation |
| `MPSTensor.HasEventuallyFullKrausRank A` | `Kraus.IsNormal A`, to which it was definitionally equal |
| `MPSTensor.IsPrimitivePaper A` | clause 1 of `primitivity_tfae`, written out where a statement is about vector spreading; `Kraus.IsNormal A` where it was a hypothesis |
| `MPSTensor.IsStronglyIrreduciblePaper A` | clause 3 of `primitivity_tfae`; the separate conclusions `IsIrreducibleMap (Kraus.transferMap A)`, `IsPrimitive (Kraus.transferMap A)` and a positive-definite fixed matrix where it was destructured |

## Removed theorems and their replacements

Translations between a removed name and its target are deleted without a
successor; theorems with content are restated on the target.

| Removed | Replacement |
|---|---|
| `hasEventuallyFullKrausRank_iff_isNormal` | none; both sides are `Kraus.IsNormal A` |
| `isStronglyIrreduciblePaper_of` | none (anonymous-constructor forwarder) |
| `isPrimitivePaper_of_hasEventuallyFullKrausRank`, `isPrimitivePaper_of_isNormal` | `exists_vectorSpreadSpan_eq_top_of_isNormal` |
| `isIrreducibleTensor_of_isPrimitivePaper` | `isIrreducibleFamily_of_isNormal`, with `isIrreducibleMap_transferMap_of_isNormal` for the transfer map |
| `isPeripherallyPrimitive_of_isPrimitivePaper` | `isPrimitive_transferMap_of_isNormal` |
| `isStronglyIrreduciblePaper_of_isPrimitivePaper`, `isStronglyIrreduciblePaper_of_hasEventuallyFullKrausRank`, `isNormal_implies_stronglyIrreducible` | `exists_posDef_fixedPoint_of_isNormal`, `isPrimitive_transferMap_of_isNormal`, `isIrreducibleMap_transferMap_of_isNormal` |
| `hasEventuallyFullKrausRank_of_isStronglyIrreduciblePaper` | `isNormal_of_isIrreducibleMap_of_isPrimitive` |
| `hasEventuallyFullKrausRank_of_isPrimitiveMPS_of_posDef` | `isNormal_of_isPrimitiveMPS_with_posDef` (kept) |
| `isPrimitiveMPS_of_isStronglyIrreduciblePaper` | `exists_isPrimitiveMPS_posDef_of_isIrreducibleMap_of_isPrimitive`; from normality, `exists_isPrimitiveMPS_posDef_of_isNormal` |
| `isStronglyIrreduciblePaper_of_isPrimitiveMPS_of_posDef` | `Kraus.HasComplementaryFixedPointGap.isIrreducibleMap_of_posDef` and `Kraus.HasComplementaryFixedPointGap.isPrimitive`, which were its body |
| `primitivePaper_iff_hasEventuallyFullKrausRank`, `primitivePaper_iff_stronglyIrreducible`, `hasEventuallyFullKrausRank_iff_stronglyIrreducible`, `primitivePaper_iff_exists_simple_peripheral_fixedPoint`, `hasEventuallyFullKrausRank_iff_exists_simple_peripheral_fixedPoint`, `isStronglyIrreduciblePaper_of_simple_peripheral_fixedPoint` | `primitivity_tfae` |
| `hasEventuallyFullKrausRank_of_isPrimitivePaper`, `isNormal_of_isPrimitivePaper` | `((primitivity_tfae A hNorm).out 1 2).mp` |
| `wolf_theorem_6_8_conjunction` | `primitivity_tfae`; its conjuncts were three names of clause 2 and the strengthened clause 3 |
| `isPrimitivePaper_stochasticFamily` | `exists_vectorSpreadSpan_stochasticFamily_eq_top` |
| `CyclicWielandt.isPrimitivePaper` | `exists_vectorSpreadSpan_eq_top_of_isNormal` applied to `CyclicWielandt.isNormal` |
| `qIndex_le_iIndex_of_isPrimitivePaper` | `qIndex_le_iIndex`; for every channel, `qIndex_le_iIndex_of_tracePreserving` |
| `exists_nonzero_trace_word_of_isPrimitivePaper_sharp`, `..._sharp_pos` | `exists_nonzero_trace_word_of_isNormal_sharp`, `..._sharp_pos` |
| `vectorSpreadSpan_eq_top_of_isPrimitivePaper_of_eigenvector` | `vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector` |
| `vecMulVec_mem_wordSpan_of_isPrimitivePaper_of_noninvertible_eigenvector` | `vecMulVec_eigenvector_exact_wordSpan`, of which it was an instance |
| `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector` | `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_noninvertible_eigenvector` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` | `wordSpan_eq_top_of_isNormal_of_noninvertible_eigenvector` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit` | `wordSpan_eq_top_of_isNormal_of_mem_wordSpan_one_of_isUnit` |
| `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit`, `iIndex_le_of_isPrimitivePaper_of_isUnit` | `wordSpan_eq_top_of_isNormal_of_isUnit`, `iIndex_le_of_isNormal_of_isUnit` (already present) |
| `iIndex_le_general_of_isPrimitivePaper` | `iIndex_le_general_of_isNormal` |

All names are in the namespace `MPSTensor` unless qualified.

The following keep their names and change a hypothesis from
`IsPrimitivePaper A` or `HasEventuallyFullKrausRank A` to `Kraus.IsNormal A`:
`qIndex_le_iIndex`, `wolf_theorem_6_15`,
`iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector`,
`iIndex_le_sq_of_noninvertible_eigenvector`,
`iIndex_le_of_mem_wordSpan_one_of_isUnit`. `stochasticFamily_primitive_and_indices`
keeps its name and states its first conjunct as the written-out clause 1.

## Hypotheses of the Wielandt bounds

The source states Lemma 1, Lemma 2 and Theorem 1 for a primitive channel,
that is, for a trace-preserving family satisfying clause 1. The former Lean
statements took the normalization and `IsPrimitivePaper A`, and used the
normalization only to pass to normality through Proposition 3. They now take
`Kraus.IsNormal A`. Where the proof does not use the normalization
(Lemma 1, Lemma 2(b), all three cases of Theorem 1) it is dropped, so those
statements cover the source's hypotheses and more. Lemma 2(a),
`vectorSpreadSpan_eq_top_of_isNormal_of_eigenvector`, keeps the
normalization, which its proof uses.

## Modules

| Module | Change |
|---|---|
| `TNLean/Wielandt/Primitivity/PrimitiveBridge.lean` | deleted; its one surviving theorem is `exists_isPrimitiveMPS_posDef_of_isIrreducibleMap_of_isPrimitive` in `StronglyIrreducibleToFullRank.lean` |
| `TNLean/Wielandt/Primitivity/PeripheralCriterion.lean` | deleted; its three theorems are clause 3 of `primitivity_tfae` in `Equivalence.lean` |
| `TNLean/Wielandt/Inequality/MatrixSpanSharpBound.lean` | deleted; its one theorem was an instance of `vecMulVec_eigenvector_exact_wordSpan` |

The coherent prerequisite allowlist `scripts/coherent_tn_prerequisites.json`
drops the two deleted modules it named; their content is in the already
listed `TNLean.Wielandt.Primitivity.StronglyIrreducibleToFullRank` and
`TNLean.Wielandt.RectangularSpan.Universality`. Its recorded baseline commit
is unchanged, so an export needs a new baseline once this change is on `main`.

## Blueprint

In `blueprint/src/chapter/ch08_wielandt_cumulative_bound.tex` the three
definition entries for the source's properties are replaced by a paragraph of
prose, the equivalence entries are merged into the one entry
`thm:wielandt_proposition_three`, and the entries for Lemma 1, Lemma 2 and
Theorem 1 are stated for a normal tensor. Removed labels and where their
dependencies now point:

| Removed label | Redirected to |
|---|---|
| `def:eventually_full_kraus_rank` | `def:normal` |
| `def:paper_primitive`, `def:strongly_irreducible_paper` | the statement using the property; `thm:wielandt_proposition_three` |
| `thm:wolf_6_8_kraus_span`, `thm:wolf_6_8_conjunction`, `rem:wolf_6_8_pairwise`, `thm:wielandt_literal_peripheral_criterion` | `thm:wielandt_proposition_three` |
| `thm:strongly_irreducible_of_paper_primitive` | `thm:normalized_normal_strongly_irreducible` |
| `thm:rank_one_noninvertible_eigenvector_primitive` | `lem:rank_one_noninvertible_eigenvector` |
| `cor:wielandt_case2_generator` | `thm:wielandt_case2_normal_generator` |
