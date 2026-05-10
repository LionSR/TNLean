# Wielandt-bound source-faithfulness audit (Issue #1449)

**Audit date**: 2026-05-07
**Source**: Sanz-Perez-Garcia-Wolf-Cirac, *A quantum version of Wielandt's inequality*, arXiv:0909.5347, Theorem 1
**Blueprint**: `blueprint/src/chapter/ch07_wielandt.tex`
**Formal**: `TNLean/Wielandt/SourceTheorems/WielandtInequality.lean`

---

## 1. Theorem statement: paper vs. formal

### Paper statement (Theorem 1, p.4)

For a primitive quantum channel E_A on M_D(C) with Kraus operators {A_k}_{k=1}^d:

- S_n(A) = span{A_{k_1}...A_{k_n}} (exact-length word span)
- i(A) = min{n : S_n(A) = M_D(C)} (full-Kraus-rank index)
- d = number of linearly independent Kraus operators = dim S_1(A)
- q(E_A) <= i(A), and:

1. **General**: i(A) <= (D^2 - d + 1) D^2
2. **Invertible**: if S_1(A) contains an invertible element, i(A) <= D^2 - d + 1
3. **Non-invertible with eigenvalue**: if S_1(A) contains a non-invertible element with a nonzero eigenvalue, i(A) <= D^2

### Formal statement (`WielandtInequality.lean`)

| Paper concept | Formal identifier | Match? |
|---|---|---|
| S_n(A) | `wordSpan A n` | YES |
| i(A) | `iIndex A` = `sInf {n | wordSpan A n = top}` | YES |
| d | `krausRank A` = `finrank C (wordSpan A 1)` | YES |
| q(E_A) | `qIndex A` | YES |
| q <= i | `qIndex_le_iIndex_of_isPrimitivePaper` | YES |
| General bound | `iIndex_le_general_of_isPrimitivePaper` | YES |
| Case (2): invertible in S_1(A) | `iIndex_le_of_mem_wordSpan_one_of_isUnit` | YES |
| Case (3): non-invertible in S_1(A) with eigenvalue | `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector` | YES |

### Verdict: **Fully faithful.** The formal theorem matches the paper's statement in all three cases.

---

## 2. One-step subspace: deviation resolved

The previous deviation note (`docs/paper-gaps/quantum_wielandt_deviation.tex`, #1049) flagged that cases (2) and (3) were originally formalized only for a **single Kraus operator** (`A i0`), whereas the paper allows the special matrix to be an arbitrary element of S_1(A).

This has been resolved. The current `WielandtInequality.lean` contains:

- **One-step subspace variants** (paper-faithful):
  - `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_isUnit`
  - `iIndex_le_of_mem_wordSpan_one_of_isUnit`
  - `wordSpan_eq_top_of_isPrimitivePaper_of_mem_wordSpan_one_of_noninvertible_eigenvector`
  - `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector`

- **Single-generator corollaries** (convenience):
  - `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit`
  - `iIndex_le_of_isPrimitivePaper_of_isUnit`
  - `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector`
  - `iIndex_le_sq_of_noninvertible_eigenvector`

The one-step subspace proofs use the one-step augmentation technique (`oneStepAugment A X`), which adjoins X as a redundant first generator. Since X is in S_1(A), the exact word spans and Kraus rank are preserved, and the existing single-generator theorems apply.

### Verdict: **Deviation resolved.** The paper-facing theorem correctly uses the paper's hypothesis (X in S_1(A), not necessarily a Kraus operator).

---

## 3. Kraus rank vs. linearly independent Kraus count

The paper writes d for "the number of linearly independent Kraus operators." The proof of Lemma 1 uses dim T_1(A) = d (i.e., dim S_1(A) = d). The formalization defines:

```
krausRank A := finrank C (wordSpan A 1)   -- = dim S1(A)
```

This is not a deviation -- it is the paper's own invariant definition. The replacement of d by kr(A) = dim S_1(A) is faithful.

### Verdict: **No discrepancy.** d = dim S_1(A) is the paper's own working convention.

---

## 4. Wielandt declarations imported by MPS pipeline

Below is the complete inventory of Wielandt imports used by the canonical-form, BNT, and fundamental-theorem files.

### Direct Wielandt imports by MPS pipeline files

| MPS file | Wielandt import | Key declaration used |
|---|---|---|
| `FundamentalTheorem/FiniteLength.lean` | `Wielandt.WielandtBound` | `wordSpan_eq_top_of_isInjective` |
| `CanonicalForm/Existence.lean` | `Primitivity.StronglyIrreducibleToFullRank` | `isNormal_of_isPrimitiveMPS_with_posDef` |
| `CanonicalForm/SectorComparison/TPPrimitiveReduction.lean` | `SpanGrowth.VectorToMatrixSpan` | vector-to-matrix lemmas |
| | `SpanGrowth.CumulativeSpan` | `cumulativeSpan` API |
| | `RectangularSpan.Basic` | `wielandt_lemma2b_conditional` |
| | `Primitivity.ToNormal` | spectral-gap consequences |
| | `Primitivity.StronglyIrreducibleToFullRank` | primitive-to-normal |
| `ParentHamiltonian/UniqueGroundState.lean` | `SpanGrowth.CumulativeToWordSpan` | `cumulativeSpan_eq_wordSpan_of_one_mem_wordSpan_one` |
| `ParentHamiltonian/IntersectionProperty.lean` | `SpanGrowth.CumulativeToWordSpan` | same |
| `ParentHamiltonian/WrappingWindow.lean` | `SpanGrowth.VectorToMatrixSpan` | vector-to-matrix lemmas |
| `Algebra/BurnsideMatrix.lean` | `SpanGrowth.CumulativeSpan` | `cumulativeSpan` API |

### Wielandt declarations NOT imported by MPS pipeline

These are the **standalone paper-level** declarations -- correct as-is:

| File | Status |
|---|---|
| `SourceTheorems/WielandtInequality.lean` | **Standalone paper-facing** Theorem 1. Not on FT critical path. |
| `SourceTheorems/EigenvectorSpreading.lean` | Standalone paper-facing Lemma 2(a). |
| `SourceTheorems/MatrixSpanExistence.lean` | Standalone paper-facing Lemma 2(b). |
| `SourceTheorems/MatrixSpanSharpBound.lean` | Standalone sharp bound. |
| `SourceTheorems/NonzeroTraceWord.lean` | Standalone Lemma 1. |
| `Primitivity/Equivalence.lean` | Standalone Proposition 3 full equivalence. |
| `Primitivity/PaperDefinitions.lean` | Paper-facing definition layer (`iIndex`, `qIndex`, `IsPrimitivePaper`). |
| `QuantumWielandt.lean` | Backward-compatible auxiliary (uses aperiodicity). |
| `RankOne/ExtractionFull.lean` | Contains `wielandt_lemma2b` (existential Lemma 2(b)). Not directly imported by MPS pipeline. |
| `Channel/WolfChapter6Index.lean` | Documentation-only index. |

### Verdict: **Correct separation.** The paper-facing theorems live in `SourceTheorems/` and are not accidentally imported by the MPS pipeline. The pipeline uses a narrower set of Wielandt lemmas (`CumulativeSpan`, `CumulativeToWordSpan`, `VectorToMatrixSpan`, `ToNormal`, `ImpliesIrreducible`, `StronglyIrreducibleToFullRank`).

---

## 5. Redundancy check: cumulative-span declarations

The Wielandt layer has both cumulative-span statements (T_n(A)) and exact-word-span statements (S_n(A)). The cumulative variants are **not redundant** -- they serve as intermediate lemmas in the proof of Lemma 2(b). Specifically:

- `cumulativeSpan_eq_top` (Lemma 1 in cumulative form) -> used to get nonzero trace
- `cumulativeVectorSpan_eq_top` (eigenvector spreading) -> feeds into exact-word-span
- `wielandt_lemma2b` (`ExtractionFull.lean`) -> existential fixed-length conclusion

The cumulative-span variety in `WielandtBound.lean` is imported by `FiniteLength.lean` (which uses `wordSpan_eq_top_of_isInjective` that depends on cumulative-to-exact conversion). This is a legitimate dependency.

### Verdict: **No dead proof paths.** All main declarations are either (a) directly used by MPS pipeline, or (b) standalone paper-facing theorems, or (c) corollaries of paper-facing theorems.

---

## 6. Theorem classification

### Theorem-level paper-facing statements (keep as-is)

| Declaration | File | Reason |
|---|---|---|
| `iIndex_le_general_of_isPrimitivePaper` | `WielandtInequality.lean` | Theorem 1, case (1) -- general bound |
| `qIndex_le_iIndex_of_isPrimitivePaper` | `WielandtInequality.lean` | Theorem 1, q <= i (Prop. 3/Prop. 1) |
| `iIndex_le_of_mem_wordSpan_one_of_isUnit` | `WielandtInequality.lean` | Theorem 1, case (2) -- paper-faithful |
| `iIndex_le_sq_of_mem_wordSpan_one_of_noninvertible_eigenvector` | `WielandtInequality.lean` | Theorem 1, case (3) -- paper-faithful |
| `isNormal_of_isPrimitiveMPS_of_posDef` | `QuantumWielandt.lean` | Primitive -> normal (Proposition 3) |
| `wielandt_lemma2b` | `RankOne/ExtractionFull.lean` | Lemma 2(b) -- existential |

### Convenience corollaries (keep)

| Declaration | Reason |
|---|---|
| `wordSpan_eq_top_of_isPrimitivePaper_of_isUnit` | Single-generator variant of case (2) |
| `iIndex_le_of_isPrimitivePaper_of_isUnit` | Same |
| `wordSpan_eq_top_of_isPrimitivePaper_of_noninvertible_eigenvector` | Single-generator variant of case (3) |
| `iIndex_le_sq_of_noninvertible_eigenvector` | Same |

### Auxiliary lemmas (internal -- used by pipeline, not paper-facing)

| Declaration | File | Used by |
|---|---|---|
| `cumulativeSpan_eq_top` | `SpanGrowth/NonzeroTraceProduct.lean` | Pipeline |
| `eigenvector_spreading` | `SpanGrowth/EigenvectorSpreading.lean` | Pipeline & SourceTheorems |
| `wielandt_blocked_assembly` | `RectangularSpan/Basic.lean` | `wielandt_lemma2b` |
| `isNormal_of_isPrimitiveMPS_with_posDef` | `Primitivity/StronglyIrreducibleToFullRank.lean` | `Existence.lean`, `TPPrimitiveReduction.lean` |

### Verdict: **No retirements needed.** Every declaration has a clear role: paper-facing theorem, convenience corollary, or pipeline internal. No dead declarations found.

---

## 7. Summary

| Criterion | Status |
|---|---|
| Uses paper's i(A) = min{n : S_n(A) = M_D(C)} | YES (`iIndex`) |
| Uses paper's d = dim S_1(A) | YES (`krausRank`) |
| Case (2) hypothesis: "S_1(A) contains invertible" | YES (`_of_mem_wordSpan_one_` variants) |
| Case (3) hypothesis: "S_1(A) contains non-invertible with eigenvalue" | YES (`_of_mem_wordSpan_one_` variants) |
| General bound matches (D^2 - d + 1) D^2 | YES |
| MPS pipeline uses correct subset of declarations | YES |
| No redundant cumulative-span declarations | YES |
| No dead proof paths | YES |
| Deviation #1049 resolved | YES |

### Follow-up actions

- None required. All three cases of Theorem 1 are correctly formalized with paper-faithful hypotheses.
- The `_of_isPrimitivePaper_of_isUnit` and `_of_isPrimitivePaper_of_noninvertible_eigenvector` single-generator variants are legitimate convenience corollaries.
- The `SourceTheorems/` files correctly serve as standalone documentation entry points.
- No retirements needed. (Issue #1509 renamed the directory from `PaperResults/` to `SourceTheorems/` in PR #1519.)
