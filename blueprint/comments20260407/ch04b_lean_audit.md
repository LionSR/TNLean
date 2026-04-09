# Audit: `blueprint/src/chapter/ch04b_entropy.tex`

Scope reviewed on 2026-04-08:

- Full blueprint file: `blueprint/src/chapter/ch04b_entropy.tex`
- Entropy-related Lean files:
  - `TNLean/Analysis/Entropy.lean`
  - `TNLean/Axioms/Entropy.lean`
- `TNLean/Channel/` listing

Summary:

- All 12 `\lean{}` tags in this chapter resolve to existing Lean declarations.
- The main problems are status-tag accuracy and blueprint statements that are broader than the tagged Lean declarations.
- The sorry-inventory note is correct: `strong_subadditivity` is an **axiom** in Lean and the blueprint currently gives it **no** status tag.

## Findings

### 1. `strong_subadditivity` is axiomatized in Lean, but the blueprint gives it no `\notready`

- Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:127-135`
- Lean: `TNLean/Axioms/Entropy.lean:55-65`

The tag `\lean{strong_subadditivity}` resolves, but the declaration is

```lean
axiom strong_subadditivity ...
```

so this result is not fully formalized. The blueprint theorem has no `\leanok` and no `\notready`; that is inconsistent with the actual Lean status. This should be marked `\notready` (or otherwise explicitly marked as axiomatized).

### 2. `Matrix.traceA_ABC_isHermitian` does not justify the full blueprint lemma

- Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:110-123`
- Lean tag target: `TNLean/Analysis/Entropy.lean:203-210`
- Related Lean declarations:
  - `TNLean/Analysis/Entropy.lean:213-221` (`traceC_ABC_isHermitian`)
  - `TNLean/Analysis/Entropy.lean:224-232` (`traceAC_ABC_isHermitian`)
  - `TNLean/Analysis/Entropy.lean:245-260` (`Matrix.traceLeft_isHermitian`, `Matrix.traceRight_isHermitian`)

The blueprint lemma says one tagged declaration covers:

- tripartite traces over `A`, `C`, and `AC`
- bipartite traces over `A` and `B`

But `\lean{Matrix.traceA_ABC_isHermitian}` only proves the `tr_A` tripartite case. The other four facts are separate Lean theorems. So the current `\leanok` is misleading for the statement as written.

There is also a declaration-kind mismatch here: the blueprint uses `lemma`, while the tagged Lean declaration is a `theorem`.

### 3. `densityMatrices_eigenvalues_le_one` is overstated in the blueprint

- Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:47-57`
- Lean: `TNLean/Analysis/Entropy.lean:97-103`

The blueprint states:

> Each eigenvalue of a density matrix lies in `[0, 1]`.

But the tagged Lean theorem only proves the **upper bound**

```lean
(i : Fin D) : hρ.1.isHermitian.eigenvalues i ≤ 1
```

for a fixed index `i`. The lower bound comes separately from positivity (`hρ.1.eigenvalues_nonneg`) and is not part of this declaration. So the blueprint statement does not match the tagged signature exactly, and `\leanok` is too strong for the statement as written.

### 4. `thm:mutual_information_nonneg` is untagged and should be marked `\notready`

- Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:161-174`
- Repo search: no `mutual_information_nonneg`, `mutualInformation_nonneg`, or `subadditivity` theorem implementing this result

This theorem has no `\lean{}` tag and no status marker. Since it is not formalized in the current codebase, it should be marked `\notready`.

### 5. There are declaration-kind mismatches between blueprint and Lean

- `densityMatrices_eigenvalues_sum_one`
  - Blueprint: `lemma` at `blueprint/src/chapter/ch04b_entropy.tex:37-45`
  - Lean: `theorem` at `TNLean/Analysis/Entropy.lean:87-94`
- `Matrix.traceA_ABC_isHermitian`
  - Blueprint: `lemma` at `blueprint/src/chapter/ch04b_entropy.tex:110-123`
  - Lean: `theorem` at `TNLean/Analysis/Entropy.lean:203-210`

Per the project blueprint guide, these should match exactly. The label prefixes (`lem:`) are also inconsistent with the Lean declaration kinds.

### 6. `IsSSAEquality` and `mutualInformation` are stated on density matrices/states in the blueprint, but Lean only assumes Hermitian matrices

- `IsSSAEquality`
  - Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:137-146`
  - Lean: `TNLean/Analysis/Entropy.lean:280-287`
- `mutualInformation`
  - Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:150-159`
  - Lean: `TNLean/Analysis/Entropy.lean:304-309`

These blueprint statements are mathematically natural, but they do not match the Lean signatures exactly:

- `IsSSAEquality` takes `(ρ_ABC) (hρ_ABC : ρ_ABC.IsHermitian)`
- `mutualInformation` takes `(ρ_AB) (hρ_AB : ρ_AB.IsHermitian)`

So the blueprint narrows the domain compared to Lean.

### 7. `IsSSAEquality` has an incorrect `\uses`

- Blueprint: `blueprint/src/chapter/ch04b_entropy.tex:137-140`
- Lean definition body: `TNLean/Analysis/Entropy.lean:280-287`

The blueprint says

```tex
\uses{thm:strong_subadditivity}
```

but the Lean definition of `IsSSAEquality` does not depend on the SSA theorem/axiom. It only uses von Neumann entropy and the three partial traces. This should cite the defining ingredients, not `thm:strong_subadditivity`.

## Per-tag audit

| Blueprint tag | Exists? | Lean declaration | Statement vs Lean signature | Status check |
|---|---|---|---|---|
| `\lean{vonNeumannEntropy}` | Yes | `noncomputable def`, `TNLean/Analysis/Entropy.lean:74-76` | Match. Blueprint is a standard mathematical restatement of the eigenvalue formula. | `\leanok` correct |
| `\lean{vonNeumannEntropy_nonneg}` | Yes | `theorem`, `TNLean/Analysis/Entropy.lean:109-115` | Match: density matrix implies nonnegative entropy. | `\leanok` correct |
| `\lean{densityMatrices_eigenvalues_sum_one}` | Yes | `theorem`, `TNLean/Analysis/Entropy.lean:87-94` | Statement matches, but blueprint uses `lemma` instead of `theorem`. | `\leanok` fine; declaration kind mismatched |
| `\lean{densityMatrices_eigenvalues_le_one}` | Yes | `theorem`, `TNLean/Analysis/Entropy.lean:97-103` | Mismatch: Lean proves only `λ_i ≤ 1` for each `i`; blueprint states `0 ≤ λ_i ≤ 1`. | `\leanok` misleading as written |
| `\lean{vonNeumannEntropy_le_log_dim}` | Yes | `theorem`, `TNLean/Analysis/Entropy.lean:122-157` | Match up to equivalent hypotheses `D ≥ 1` vs `0 < D`. | `\leanok` correct |
| `\lean{Matrix.traceA_ABC}` | Yes | `noncomputable def`, `TNLean/Analysis/Entropy.lean:176-180` | Match. | `\leanok` correct |
| `\lean{Matrix.traceC_ABC}` | Yes | `noncomputable def`, `TNLean/Analysis/Entropy.lean:185-189` | Match. | `\leanok` correct |
| `\lean{Matrix.traceAC_ABC}` | Yes | `noncomputable def`, `TNLean/Analysis/Entropy.lean:194-198` | Match. | `\leanok` correct |
| `\lean{Matrix.traceA_ABC_isHermitian}` | Yes | `theorem`, `TNLean/Analysis/Entropy.lean:203-210` | Mismatch: blueprint statement bundles five theorems, tag certifies only the `tr_A` tripartite case. | `\leanok` misleading as written |
| `\lean{strong_subadditivity}` | Yes | `axiom`, `TNLean/Axioms/Entropy.lean:55-65` | Mathematical statement matches. | Missing `\notready`; sorry-inventory note is correct |
| `\lean{IsSSAEquality}` | Yes | `def`, `TNLean/Analysis/Entropy.lean:280-287` | Near-match, but Lean assumes only Hermitian, not density-matrix. | `\leanok` acceptable; statement should be made exact |
| `\lean{mutualInformation}` | Yes | `noncomputable def`, `TNLean/Analysis/Entropy.lean:304-309` | Near-match, but Lean assumes only Hermitian, not state/density-matrix. | `\leanok` acceptable; statement should be made exact |

## Formalization-speak / Lean jargon

I did not find obvious banned formalization-speak or Lean-jargon in the prose of this chapter. The chapter is generally written in standard mathematical language.

## Mathematical issues

- I did not find an obvious mathematical error in the entropy statements themselves.
- The main problems are blueprint-to-Lean fidelity issues:
  - over-broad statements attached to narrower tags
  - missing `\notready` on unformalized material
  - incorrect declaration kinds / dependencies

## Relevant files consulted

- `blueprint/src/chapter/ch04b_entropy.tex`
- `TNLean/Analysis/Entropy.lean`
- `TNLean/Axioms/Entropy.lean`
- `TNLean/Channel/PartialTrace.lean`
- `TNLean/Channel/` directory listing
