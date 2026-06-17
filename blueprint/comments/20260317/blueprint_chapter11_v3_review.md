
# Blueprint Review — Chapter 11 (Basis of Normal Tensors), v2 → v3

This document reviews Chapter 11 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter10_review.md`, `blueprint_chapter11_review.md`,
`blueprint_review_comprehensive_reference.md`, `full_ft_verification.md`).

---

## Chapter numbering map

v3 Chapter 11 = v2 Chapter 10 (Basis Normal Tensors). The chapter is
renumbered +1 due to the new Chapter 5 (Schwarz Inequalities) inserted
in v3.

v3 has 14 numbered statements (11.1–11.14) vs v2's 12 (10.1–10.12).
The 2 new items are: Remark 11.8 (coefficient-instantiation remark) and
Remark 11.14 (Newton–Girard orphan status).

| v2 | v3 | Content | Change |
|---|---|---|---|
| Def 10.1 | Def 11.1 | Basis of normal tensors | Renumbered; **naming corrected**; **c_j removed** |
| Def 10.2 | Def 11.2 | CF with BNT separation | Renumbered; **wording rewritten** |
| Def 10.3 | Def 11.3 | Normal CF with BNT separation | Renumbered; **ref updated (8.28→9.29)** |
| Thm 10.4 | Thm 11.4 | Cross-overlap decay | Renumbered; **"CF-BNT predicate" replaced**; **ref updated (6.15→7.15, 6.17→7.17)** |
| Thm 10.5 | Thm 11.5 | CF-BNT yields BNT | Renumbered; **proof rewritten (Gram matrix clarified)**; **"CF-BNT predicate" replaced** |
| Remark 10.6 | Remark 11.6 | Normality gap | Renumbered; **expanded with bridge path** |
| Thm 10.7 | Thm 11.7 | BNT permutation, proportional | Renumbered; **σ→π permutation fix**; **ket notation**; **g_A/g_B notation kept** |
| — | Remark 11.8 | Coefficient instantiation | **New** |
| Thm 10.8 | Thm 11.9 | BNT permutation, span case | Renumbered; **proof rewritten**; **meta-commentary removed** |
| Thm 10.9 | Thm 11.10 | Coefficient ratio decay | Renumbered; **ref updated (Def 9.8→10.9)** |
| Remark 10.10 | Remark 11.11 | Strict-dominance regime | Renumbered |
| Thm 10.11 | Thm 11.12 | Newton–Girard trace recursion | Renumbered; **proof expanded** |
| Thm 10.12 | Thm 11.13 | Equal power sums → equal multisets | Renumbered |
| — | Remark 11.14 | Newton–Girard orphan status | **New** |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. [CPGSV21, Def 4.2] cited. Permutation rigidity matches [CPGSV21, Thm 4.1]. |
| Internal consistency | Mostly improved. σ overload fixed; CF-BNT abbreviation expanded. **Remark 11.6 contradicts Remark 2.20 (see 11-S5).** |
| v2 → v3 changes | Substantial: naming fix, coefficient notation fix, new remark on coefficient instantiation, Remark 11.6 expanded, Remark 11.14 added, proof rewrites for Thms 11.5/11.9. |
| AI language | Much improved. "CF-BNT predicate" mostly eliminated. One residual instance (see 11-AI1). Meta-commentary in Thm 10.8 proof removed. **Remark 11.6 uses the non-standard phrase "in the normal-canonical sense" (see 11-S5).** |
| Formalization readiness | Improved. Remark 11.8 closes the coefficient-instantiation gap. Gram matrix proof now cites Lemma 2.32. |
| Open items from prior review | 13 of 16 cleanup items addressed (including 0a via Remark 2.20). See Prior Review Items below. |
| FT critical path | **Yes.** Theorem 11.5 (CF-BNT yields BNT) is load-bearing for Theorem 12.5 (equal-MPV FT). Theorem 11.7 is load-bearing for Theorem 12.2. |
| **New issues** | **Chapter title overcorrected to "Bases" (11-S6). Remark 11.6 contradicts Remark 2.20 by presenting a single notion of normality as two distinct senses (11-S5). Remark 11.8 convergence gap (11-S4). Gram matrix route via Def 2.30/Lemma 2.32 may be unnecessary (11-F2).** |

---

# v2 → v3 Changes — Substantive

## 1. Chapter title and Definition 11.1: naming corrected

v2 title: "Basis Normal Tensors." v3 title: "Bases of Normal Tensors."
v2 Definition 10.1 title: "Basis Normal Tensor (BNT)." v3 Definition 11.1
title: "Basis of Normal Tensors (BNT)."

v2's body text read: "A basis normal tensor (BNT) decomposition for a total
tensor A_tot consists of..." v3 reads: "A basis of normal tensors (BNT) for
a total tensor A_tot consists of..."

This directly addresses cleanup item 0 from the v2 review: the preposition
"of" is restored. However, the chapter title was overcorrected to the
plural "Bases" — see 11-S6.

## 2. Definition 11.1: coefficient notation c_j removed

v2's condition 2 read: "|V^{(N)}(A_tot)⟩ = ∑_j c_j |V^{(N)}(A_j)⟩."
The v2 review (cleanup item 1) flagged that c_j suggests N-independent
coefficients, whereas the actual coefficients are μ_j^N.

v3's condition 2 reads: "at each system size N, the MPV of A_tot lies in
the span of the block MPVs {|V^{(N)}(A_j)⟩}."

This replaces the problematic c_j with a span condition, as recommended
in the v2 review. This directly addresses cleanup item 1.

## 3. Definition 11.2: wording rewritten

v2's Definition 10.2 read: "A canonical form with BNT separation extends
the canonical form (Definition 9.8) with the additional requirement that
distinct blocks are not gauge-phase equivalent: for j ≠ k with D_j = D_k,
A_j and A_k are not gauge-phase equivalent."

v3's Definition 11.2 reads: "A family is in canonical form with BNT
separation if it satisfies Definition 10.9 and, in addition, distinct
blocks of the same bond dimension are not gauge-phase equivalent."

The rewrite is cleaner and avoids the redundant restatement of the
non-equivalence condition. The cross-reference is correctly updated
(9.8 → 10.9).

## 4. Theorem 11.4: "CF-BNT predicate" replaced

v2's Theorem 10.4 title: "Cross-overlap decay for distinct CF-BNT blocks."
Body: "If ((μ_k), (A_k)) satisfies the CF-BNT predicate..."

v3's Theorem 11.4 title: "Cross-overlap decay for distinct blocks in
canonical form with BNT separation." Body: "If ((μ_k), (A_k)) is in
canonical form with BNT separation..."

This replaces the code-style "CF-BNT predicate" with standard mathematical
language. Theorem references updated from 6.15/6.17 to 7.15/7.17
(correct v3 numbering).

This addresses cleanup items 5 (expand CF-BNT on first use) and 16
(rewrite AI-generated phrasing) from the v2 review.

## 5. Theorem 11.5 proof: Gram matrix clarified

v2's proof wrote: "The overlap matrix G_{jk}(N) = O_{A_j A_k}(N)
converges to the identity."

v3's proof writes: "Consider the Gram matrix G_{jk}(N) =
⟨V^{(N)}(A_j)|V^{(N)}(A_k)⟩. By Lemma 2.32, G_{jk}(N) =
O̅_{A_j A_k}(N), so the same convergence statements hold after
conjugation."

This addresses cleanup item 3 from the v2 review (overlap/inner-product
conflation). The Gram matrix is now correctly defined as the inner
product ⟨V|V⟩, and Lemma 2.32 is cited. However, see 11-S3 for the
precise content of the conjugation step, and 11-F2 for whether this
route through Definition 2.30 and Lemma 2.32 is necessary at all.

## 6. Remark 11.6: expanded with bridge path

v2's Remark 10.6 stated the gap but did not explain how to close it.
v3's Remark 11.6 adds: "This gap is closable: primitivity of the transfer
map implies eventual full Kraus rank by [SPGWC10, Proposition 3], and
the bridge from a primitive transfer map to eventual block injectivity
is available via the Wielandt theory of Chapter 8. It is simply not
built into Definition 11.3 itself."

This directly addresses cleanup item 4 from the v2 review. However, the
remark now contradicts v3's own Remark 2.20 — see 11-S5 for detailed
analysis.

## 7. Theorem 11.7: σ overload fixed

v2's Theorem 10.7 concluded: "there is a permutation σ ∈ S_g" — clashing
with σ for the spin configuration index in the same equation.

v3's Theorem 11.7 uses π throughout: "there is a permutation π of the
common block index set."

This directly addresses cleanup item 5 from the v2 review.

## 8. Remark 11.8: coefficient instantiation (NEW)

v3 adds Remark 11.8 after Theorem 11.7:

"In the canonical-form application, the abstract data above come from
block-diagonal assemblies A_tot = ⊕_j μ_j A_j, B_tot = ⊕_k ν_k B_k,
and Theorem 2.24 gives the coefficient arrays a_{N,j} = μ_j^N and
b_{N,k} = ν_k^N. Definition 11.2 supplies injectivity, TP normalization,
and the within-family overlap limits, so the theorem isolates the abstract
permutation argument from this canonical-form packaging."

This directly addresses cleanup item 7 (connect abstract hypotheses to
CF-BNT setting) and cleanup item 13a from the v2 Chapter 11 review
(add coefficient-instantiation remark). It also partially addresses
cleanup item 6 (rewrite Theorem 10.7 in terms of CF data) — Remark 11.8
provides the bridge rather than rewriting the theorem itself.

## 9. Theorem 11.9 proof: rewritten, meta-commentary removed

v2's Theorem 10.8 proof contained:
- "The overlap orthonormality hypotheses are assumed directly, rather
  than derived from proportional MPVs together with coefficient
  convergence." (meta-commentary)
- "The irreducible-TP variant uses the same matching argument with the
  irreducible-TP overlap decay theorems in place of the injective ones."
  (road-map sentence without proof content)

v3's Theorem 11.9 proof replaces both with an actual proof sketch:
"For each family, the Gram matrix converges to the identity by Lemma 2.32
together with the self-overlap and off-diagonal decay hypotheses. Hence
for all sufficiently large N both families of MPV vectors are linearly
independent. At such an N, the equality of spans in the statement forces
the two common subspaces to have the same dimension, so g_A = g_B. The
span equality then gives change-of-basis matrices between the two
families, and the same mixed-overlap matching argument shows that the
mixed-overlap matrix has exactly one nonzero entry in each row and column.
This produces the permutation π, while Theorems 7.15 and 7.17 upgrade
each nonzero match to equality of bond dimensions and gauge-phase
equivalence."

This directly addresses cleanup items 9 (state or remove the
irreducible-TP variant) and 16 (rewrite AI phrasing) from the v2 review.

## 10. Theorem 11.12 proof: expanded

v2's proof was a single sentence: "The Newton–Girard identities express
the coefficients of the characteristic polynomial recursively in terms
of the power-sum traces tr(A^k). Equal power sums give equal coefficients,
hence equal characteristic polynomials."

v3's proof explicitly states the recursion formula: "Let e_m denote the
mth elementary symmetric polynomial in the eigenvalues, with e_0 = 1.
The Newton–Girard recursion m·e_m = ∑_{i=1}^{m} (-1)^{i-1} e_{m-i}
tr(A^i) expresses the coefficients of the characteristic polynomial in
terms of the power-sum traces tr(A^i)."

This directly addresses cleanup item 12 from the v2 review (state the
Newton–Girard recursion explicitly).

## 11. Remark 11.14: Newton–Girard orphan status (NEW)

v3 adds: "Theorems 11.12 and 11.13 are auxiliary results retained for
potential future use. The current route to Theorem 12.5 uses linear
independence of the block MPV family supplied by a basis of normal
tensors, rather than Newton–Girard identities, to match the weight
multiset."

This directly addresses cleanup item 13 from the v2 review (Newton–
Girard confirmed orphaned) and the orphan status discussion in the
comprehensive reference.

## 12. Ket notation adopted

v2 used component notation V^{(N)}(A_j)_σ throughout Theorems 10.7–10.8.
v3 uses ket notation |V^{(N)}(A_j)⟩ in Definitions 11.1–11.3 and
Theorem 11.5 proof, while keeping component notation in Theorem 11.7
(where the σ index appears in the proportionality equation). This is
a minor but systematic change — the ket notation is more natural for
the span and linear-independence conditions in the BNT definition.

---

# v2 → v3 Changes — Non-substantive

- All internal cross-references updated for v3 numbering:
  - Definition 9.8 → Definition 10.9
  - Definition 8.28 → Definition 9.29
  - Theorem 6.15 → Theorem 7.15
  - Theorem 6.17 → Theorem 7.17
- v2's section title "BNT permutation rigidity" → v3's "Permutation
  rigidity for bases of normal tensors" (more descriptive, avoids using
  BNT as a standalone adjective).

---

# Unchanged from v2

- **Theorem 11.7 (= v2 Thm 10.7) hypothesis structure:** The
  overloaded hypotheses remain. The theorem still takes explicit
  A_tot, B_tot, coefficient arrays, convergence conditions, and
  proportionality as free-standing hypotheses rather than packaging
  them via the CF-BNT predicate. Remark 11.8 mitigates this by
  explaining the instantiation, but the theorem statement itself is
  unchanged.

- **Theorem 11.10 (= v2 Thm 10.9) and Remark 11.11 (= v2 Remark 10.10):**
  Content unchanged apart from renumbering and the Definition 10.9
  cross-reference update.

- **Theorem 11.13 (= v2 Thm 10.12):** Content unchanged.

- **Block count notation g:** v3 Chapter 11 continues to use g_A, g_B
  for the block counts, matching v2 Chapter 10. Chapter 12 (= v2
  Chapter 11) also uses g in v3. The notation inconsistency between
  Chapter 10 (which uses r in Theorems 10.15–10.17, inherited from the
  algebraic Chapter 10) and Chapter 11 (which uses g) persists but is
  now less confusing since the chapters are adjacent.

---

# Forward Reference Verification

| Reference in Ch 11 | Target | Verified? |
|---|---|---|
| Definition 2.19 (normal tensor) | Def 11.1 condition 1 | ✔ (v3 p.8) |
| Remark 2.20 (equivalence of normality) | Relevant to Remark 11.6 | ✔ (v3 p.8) — **Remark 11.6 contradicts this; see 11-S5** |
| Theorem 2.24 (MPV decomposition) | Thm 11.5 proof, Remark 11.8 | ✔ (v3 p.12) |
| Definition 2.30 (MPV inner product) | Thm 11.5 proof (Gram matrix) | ✔ (v3 p.10) |
| Definition 2.31 (MPV overlap) | Thm 11.5 proof via Lemma 2.32 | ✔ (v3 p.10) |
| Lemma 2.32 (overlap = conjugate inner product) | Thm 11.5 proof, Thm 11.9 proof | ✔ (v3 p.10) |
| Definition 10.9 (canonical form predicate) | Def 11.2 | ✔ (v3 p.62) |
| Definition 9.29 (normal canonical form) | Def 11.3 | ✔ (v3 p.55) |
| Theorem 7.15 (rectangular overlap decay) | Thm 11.4, Thm 11.7, Thm 11.9 | ✔ (v3 p.38) |
| Theorem 7.17 (same-dim overlap decay) | Thm 11.4, Thm 11.7, Thm 11.9 | ✔ (v3 p.38) |
| [CPGSV21, Definition 4.2] | Def 11.1 | ✔ (correct citation) |
| [CPGSV21, Theorem 4.1] | after Thm 11.7 | ✔ (correct citation) |
| [SPGWC10, Proposition 3] | Remark 11.6 | ✔ |
| Theorem 12.5 | Remark 11.14 | ✔ (v3 p.71) — equal-MPV FT, uses BNT linear independence |

All forward references verified. ✔

---

# Prior Review Items — Status Check

The v2 review (`blueprint_chapter10_review.md`) had 16 cleanup items
(0, 0a, 1–16). The v2 Chapter 11 review (`blueprint_chapter11_review.md`)
had 9 cleanup items (1–9) that concerned Ch 10 material. The
comprehensive reference had formalization notes 10-F1 through 10-F5
and orphan status entries.

| v2 cleanup item | Description | v3 status |
|---|---|---|
| 0 | Fix naming: "basis of normal tensors" | **Fixed.** Def 11.1 and body text corrected. **Chapter title overcorrected to plural "Bases" (see 11-S6).** |
| 0a | Add "equivalence of normality" remark | **Fully addressed by Remark 2.20** (v3 p.8), which explicitly states: "every subsequent use of 'normal' in this blueprint refers to this single notion; Definition 9.29 employs the spectral formulation, but it describes the same class of tensors." This was not present in v2. **However, Remark 11.6 contradicts Remark 2.20 (see 11-S5).** |
| 1 | Fix Def 10.1 coefficient notation (c_j → a_{N,j}) | **Fixed.** Condition 2 rephrased as span condition; c_j removed. |
| 2 | Clarify Thm 10.4 proof (TP normalization) | **Improved.** Proof now says "Definition 11.2 supplies injectivity and TP normalization for each block, which are the hypotheses required by the spectral-gap theorems." |
| 3 | Fix overlap/inner-product conflation in Thm 10.5 | **Fixed.** Gram matrix now defined as ⟨V|V⟩; Lemma 2.32 cited for the conjugation. See 11-S3 for minor residual and 11-F2 for whether this route is necessary. |
| 4 | Expand Remark 10.6 (normality gap bridge) | **Fixed** in content (names [SPGWC10, Prop 3] and Chapter 8 Wielandt theory). **Wording contradicts Remark 2.20 (see 11-S5).** |
| 5 | Fix σ overload in Thm 10.7 | **Fixed.** π used throughout. |
| 6 | Rewrite Thm 10.7 in terms of CF data | **Mitigated.** Theorem unchanged but Remark 11.8 provides the connection. |
| 7 | Add remark connecting Thm 10.7's hypotheses to CF-BNT | **Fixed.** Remark 11.8. |
| 8 | Clarify MPV-subspace hypothesis of Thm 10.8 | **Fixed.** v3 Theorem 11.9 states: "span_ℂ{|V^{(N)}(A_j)⟩} = span_ℂ{|V^{(N)}(B_k)⟩}" — explicit span equality at each N. |
| 9 | State or remove irreducible-TP variant in Thm 10.8 | **Fixed.** Removed. Proof rewritten without meta-commentary. |
| 10 | Specify which CF predicate in Thm 10.9 | **Fixed.** Theorem 11.10 cites "the canonical form predicate of Definition 10.9." |
| 11 | Define μ_{j,q} in Remark 10.10 | **Not addressed.** Remark 11.11 still references "the coefficient attached to block j can take the form ∑_q μ_{j,q}^N" without defining μ_{j,q} or giving a cross-reference. |
| 12 | State Newton–Girard recursion explicitly | **Fixed.** Theorem 11.12 proof now gives the formula. |
| 13 | Theorems 10.11–10.12 orphaned; note status | **Fixed.** Remark 11.14 explicitly states they are retained for potential future use and that the current route uses BNT linear independence. |
| 13a | Thm 10.9 not cited downstream; add application lemma | **Partially addressed.** Remark 11.8 shows the instantiation (a_{N,j} = μ_j^N) but does not explicitly cite Theorem 11.10 as the convergence source. See 11-S4. |
| 14 | Note Thm 10.12's equal-cardinality hypothesis | **Not addressed.** Theorem 11.13 still writes "Let α, β : {1,...,n} → ℂ" using the same n for both, which implicitly assumes equal cardinality but does not state this as an explicit hypothesis. |
| 15 | Note deviation from [CPGSV21, Prop IV.3] | **Not addressed.** The blueprint still builds BNT separation into the CF predicate rather than characterizing BNT post hoc, without flagging this as a deviation. Low priority. |
| 16 | Rewrite AI-generated phrasing | **Mostly fixed.** "CF-BNT predicate" replaced in theorem statements. "Collected here" replaced. Meta-commentary in Thm 10.8 proof removed. Residual: Remark 11.6's "in the normal-canonical sense" (see 11-S5). |

**From the v2 Chapter 11 review (cleanup items concerning Ch 10 content):**

| v2 Ch 11 item | Description | v3 status |
|---|---|---|
| 2 | Add coefficient-instantiation remark for Thm 11.1 | **Fixed.** Remark 11.8 in Ch 11 + Remark 12.3 in Ch 12 both serve this purpose. |
| 4 | Harmonize notation (g vs r, c_j vs c_N, σ) | **Partially fixed.** σ→π done. c_j removed from Def 11.1. g vs r persists (see Unchanged section). |
| 5 | Expand CF-BNT on first use | **Fixed.** Definition 11.2 and chapter preamble use full expansion. |
| 6 | Fix "Basis Normal Tensor" naming | **Fixed.** |
| 9 | Decide on Newton–Girard status | **Decided.** Remark 11.14 retains them as auxiliary. |

**From the comprehensive reference:**

| Item | Description | v3 status |
|---|---|---|
| Orphaned Thms 10.11–10.12 | Newton–Girard | **Documented.** Remark 11.14. |
| Orphaned Thm 10.9 | Coefficient decay not cited | **Partially addressed.** See 11-S4. |
| 10-F3 (overlap/inner product in Thm 10.5) | Lean needs conjugation | **Addressed.** Lemma 2.32 now cited. See 11-F2 for whether this is the right approach. |
| 10-F5 (Newton–Girard in Mathlib) | Low priority | **Still low priority.** Orphan status confirmed. |
| σ overload across Ch 9–10 | Notation inconsistency | **Fixed in Ch 11.** Ch 10 reviewed separately. |

---

# Statement-by-Statement Analysis

## §11.1 — Basis of normal tensors

**Definition 11.1 (Basis of Normal Tensors).**

Correctness: ✔. Matches [CPGSV21, Definition IV.2].

The three conditions are: normality, span inclusion at every N, eventual
linear independence. v3 correctly uses the span formulation for condition 2
(no explicit coefficients).

⚠️ **11-S2 (minor).** Condition 2 says "the MPV of A_tot lies in the span
of the block MPVs." In [CPGSV21, Def IV.2], the condition is: "the MPV of
A_tot is a linear combination ∑_j c_j(N) |V^{(N)}(A_j)⟩ for all N." The
span formulation is mathematically equivalent but hides the N-dependence
of the coefficients. For the Lean formalization, this is fine — the span
condition is simpler to state. But the proof of Theorem 11.5 (and
downstream in Theorem 12.5) relies on the specific form c_j(N) = μ_j^N,
which comes from Theorem 2.24 and is not an arbitrary element of the span.
The connection is made by Remark 11.8, so this is acceptable.

**Definition 11.2 (Canonical form with BNT separation).**

Correctness: ✔. Reference to Definition 10.9 verified.

**Definition 11.3 (Normal canonical form with BNT separation).**

Correctness: ✔. Reference to Definition 9.29 verified.

**Theorem 11.4 (Cross-overlap decay).**

Correctness: ✔. Two cases: D_j ≠ D_k uses Theorem 7.15 (rectangular
overlap decay); D_j = D_k uses Theorem 7.17 (same-dimension, not
gauge-phase equivalent). Both references verified.

**Theorem 11.5 (CF-BNT yields BNT).**

Correctness: ✔.

Proof: Each block is injective, hence normal (blocking length 1). MPV
decomposition via Theorem 2.24 gives the span condition with explicit
coefficients μ_k^N. Gram matrix convergence to identity: diagonal from
self-overlap hypothesis, off-diagonal from Theorem 11.4.

⚠️ **11-S3.** The proof writes: "By Lemma 2.32, G_{jk}(N) =
O̅_{A_j A_k}(N), so the same convergence statements hold after
conjugation."

The precise content of Lemma 2.32 (verified against the PDF image on
p.10) is: O_{AB}(N) = conj(⟨V(A)|V(B)⟩), i.e., the overlap is the
complex conjugate of the inner product. The overlap is defined as
O_{AB}(N) = ∑_σ V(A)_σ · conj(V(B)_σ) — bar on the B-side (second
argument), matching the transfer map convention F_{AB}(X) = ∑ A^i X (B^i)†.
The inner product is ⟨V(A)|V(B)⟩ = ∑_σ conj(V(A)_σ) · V(B)_σ — bar
on the A-side (first argument), the standard physics convention.

So: G_{jk} = ⟨V(A_j)|V(A_k)⟩ = conj(O_{A_j A_k}(N)). The proof's
claim that convergence "holds after conjugation" is correct (complex
conjugation preserves limits), but compressed. It should be more
explicit: since O_{A_j A_j}(N) → 1 (self-overlap, real), we have
G_{jj}(N) = conj(1) = 1. Since O_{A_j A_k}(N) → 0 for j ≠ k
(Theorem 11.4), G_{jk}(N) = conj(0) = 0.

See also 11-F2 for whether this entire route through Definition 2.30
and Lemma 2.32 is necessary.

**Remark 11.6 (Normality gap).**

⚠️ **11-S5 (should fix).** This remark says: "Definition 11.3 uses
'normal' in the normal-canonical sense, not the eventual block-injective
predicate of Definition 2.19."

This contradicts v3's own Remark 2.20 (p.8), which explicitly states:
"every subsequent use of 'normal' in this blueprint refers to this single
notion; Definition 9.29 employs the spectral formulation, but it describes
the same class of tensors." Definition 9.29's conditions (irreducible +
TP + primitive transfer map) are *equivalent* to eventual block injectivity
(Definition 2.19) by [SPGWC10, Proposition 3], and Remark 2.20 says so.

The phrase "in the normal-canonical sense" is not standard terminology. It
sounds like there are two different mathematical notions of normality,
which there are not — there is one notion with two equivalent
characterizations (algebraic: eventual full Kraus rank; spectral: primitive
transfer map).

What Remark 11.6 is trying to say is a narrower, legitimate point:
Definition 11.3 references Definition 9.29, which *encodes* normality via
the spectral characterization (primitive transfer map). The BNT definition
(Definition 11.1) requires normality via the algebraic characterization
(eventual block injectivity, Definition 2.19). Although these are
equivalent, the equivalence is not a tautology — it must be invoked
as a proof step. In Lean, the type-level distinction means the
formalization needs an explicit lemma converting between the two
characterizations.

**Recommended rewrite:** "Definition 11.3 references the normal canonical
form predicate (Definition 9.29), which encodes normality via the spectral
characterization (primitive transfer map). Definition 11.1 requires
normality via the algebraic characterization (eventual block injectivity,
Definition 2.19). These are equivalent by Remark 2.20, but the
equivalence must be invoked explicitly: the Wielandt theory of Chapter 8
provides the implication from primitivity to eventual block injectivity
needed in the formalization."

This makes clear that: (a) there is one notion of normality, (b) the
remark is about a proof obligation, not a mathematical gap.

## §11.2 — Permutation rigidity for bases of normal tensors

**Theorem 11.7 (Permutation rigidity — proportional MPV).**

Correctness: ✔. The proof correctly identifies the limiting mixed-overlap
matrix argument and invokes Theorems 7.15/7.17 for the upgrade.

⚠️ **11-S1 (carried from v2).** The theorem statement is still
overloaded. It separately hypothesizes:
(a) TP normalization (∑_i (A_j^i)† A_j^i = 1)
(b) self-overlap → 1 and cross-overlap → 0
(c) coefficient arrays with nonzero limits
(d) proportionality with nonzero limit

In the CF-BNT application, all of (a)–(d) follow from the CF-BNT
predicate + Theorem 2.24. Remark 11.8 explains this connection, so
the theorem's abstractness is now documented. The v2 review recommended
rewriting the theorem in terms of CF data (cleanup item 6). v3 chose
instead to keep the abstract form and add the remark. This is defensible
for the Lean formalization (where the abstract form is the actual
lemma statement), but the theorem reads more like a specification than
a mathematical result.

**Remark 11.8 (Coefficient instantiation).**

Correctness: ✔. The remark correctly identifies a_{N,j} = μ_j^N and
b_{N,k} = ν_k^N from Theorem 2.24, and notes that Definition 11.2
supplies the remaining hypotheses.

⚠️ **11-S4.** The remark shows where the coefficient arrays come from
but does not address convergence. The abstract Theorem 11.7 requires
a_{N,j} → a_j^∞ ≠ 0. But if a_{N,j} = μ_j^N, this does NOT converge to
a nonzero limit in general (since |μ_j| ≠ 1 when the canonical form has
strict weight ordering |μ_0| > |μ_1| > ...). The convergence hypotheses
of Theorem 11.7 are satisfied only after rescaling by the dominant weight:
work with (μ_j/μ_0)^N as the coefficient array, with the overall μ_0^N
factor absorbed into the proportionality constant c_N. Theorem 11.10
provides the decay (μ_k/μ_0)^N → 0 for k ≥ 1.

The remark should note this rescaling step. Currently it presents
a_{N,j} = μ_j^N as if this directly satisfies the convergence hypotheses,
which it does not.

This is a presentation gap, not a mathematical error: the formal Lean
proof handles the rescaling through the abstract hypotheses.

**Theorem 11.9 (Permutation rigidity — span case).**

Correctness: ✔. The proof is now a genuine proof sketch rather than
meta-commentary.

The span-equality hypothesis is now clearly stated:
span_ℂ{|V^{(N)}(A_j)⟩ : 1 ≤ j ≤ g_A} = span_ℂ{|V^{(N)}(B_k)⟩ : 1 ≤ k ≤ g_B}.

The proof correctly argues: Gram matrix → identity ⇒ linear independence
⇒ same dimension ⇒ g_A = g_B ⇒ change-of-basis ⇒ mixed-overlap
matching ⇒ permutation + gauge-phase equivalence via Theorems 7.15/7.17.

## §11.3 — Coefficient convergence

**Theorem 11.10 (Coefficient ratio decay).**

Correctness: ✔. Trivially correct: |μ_k/μ_0| < 1 ⇒ (μ_k/μ_0)^N → 0.

**Remark 11.11 (Strict-dominance regime).**

Correctness: ✔.

⚠️ **11-L2 (carried from v2).** The μ_{j,q} notation is still
undefined. The remark references "the coefficient attached to block j
can take the form ∑_q μ_{j,q}^N, where the μ_{j,q} are the individual
weights contributed by that block." This is a forward reference to the
periodic setting of [CPGSV21, Eq. (72a)] / the new Chapter 12 §12.4,
but μ_{j,q} is not defined anywhere in the blueprint. The remark
is illustrative (it says "in the more general periodic setting") so
this is low priority.

## §11.4 — Newton–Girard identities

**Theorem 11.12 (Newton–Girard trace recursion).**

Correctness: ✔. The recursion formula is now stated explicitly.

**Theorem 11.13 (Equal power sums → equal multisets).**

Correctness: ✔.

⚠️ **11-L3 (carried from v2).** The equal-cardinality hypothesis (both
functions α, β : {1,...,n} → ℂ use the same n) is implicit in the
notation but not stated as an explicit hypothesis. The conclusion
"the multisets {α_i} and {β_i} are equal" requires same cardinality.
This is low priority since the notation makes it clear.

**Remark 11.14 (Newton–Girard orphan status).**

Correctness: ✔. The remark correctly identifies Theorem 12.5 as the
consumer and notes the BNT linear independence route. Forward reference
to Theorem 12.5 verified (v3 p.71).

---

# Cross-Chapter Consistency

## Dependency chain verification

Theorem 11.5 depends on:
- Theorem 2.24 (MPV decomposition) ← Chapter 2 ✔
- Lemma 2.32 (overlap = conjugate inner product) ← Chapter 2 ✔
- Theorem 11.4 (cross-overlap decay) ← within chapter ✔

Theorem 11.7 depends on:
- Theorem 7.15 (rectangular overlap decay) ← Chapter 7 ✔
- Theorem 7.17 (same-dimension overlap decay) ← Chapter 7 ✔

Theorem 11.9 depends on:
- Lemma 2.32 ← Chapter 2 ✔
- Theorems 7.15, 7.17 ← Chapter 7 ✔

Theorems 11.12–11.13 depend on: standard linear algebra (no upstream).

All chains acyclic. ✔

## Downstream consumers (verified against Chapter 12)

| Ch 11 result | Used by (Ch 12) | Verified? |
|---|---|---|
| Thm 11.4 (cross-overlap decay) | Thm 12.2 proof | ✔ |
| Thm 11.5 (CF-BNT yields BNT) | Thm 12.5 proof | ✔ |
| Def 11.1 (BNT definition) | Thm 12.5 proof | ✔ |
| Thm 11.7 (permutation rigidity) | Thm 12.2 proof | ✔ |
| Remark 11.6 | Thm 12.4 proof | ✔ |
| Thm 11.12–11.13 | None | ✔ (orphaned, documented) |

## Cross-chapter issues

**11-C1. Normality: Remark 11.6 contradicts Remark 2.20.** Remark 2.20
(v3 p.8) states that there is one notion of normal tensor with two
equivalent characterizations, and that "every subsequent use of 'normal'
in this blueprint refers to this single notion." Remark 11.6 then says
Definition 11.3 uses "'normal' in the normal-canonical sense" as if this
were a different sense. The remark should be rewritten to present the
issue as a proof obligation (the equivalence must be invoked), not as a
gap between two notions. See 11-S5.

**11-C2. Block count g vs r.** Chapter 11 uses g (matching [CPGSV21]).
Chapter 10 uses r in the block-separation theorems (inherited from the
algebraic setting). Chapter 12 uses g. The inconsistency persists at
the Ch 10 / Ch 11 boundary but is less confusing now that both BNT
chapters (11, 12) use g consistently.

**11-C3. Bridging argument now in Chapter 12.** The bridging lemma
proposed in `full_ft_verification.md` is now incorporated directly into
Theorem 12.5's proof (v3 p.71). This is verified: Theorem 12.5 applies
Theorem 12.2 (= proportional FT) with c_N = 1, then uses BNT linear
independence from Theorem 11.5 + Definition 11.1 to match weights, then
absorbs the phase. Remark 12.7 confirms this recovers [CPGSV21,
Corollary IV.5].

---

# Literature Alignment

## [CPGSV21, Definition IV.2] (BNT definition)

v3 Definition 11.1 matches. The three conditions correspond directly.
The "span" formulation for condition 2 is equivalent to [CPGSV21]'s
linear combination formulation. ✔

## [CPGSV21, Theorem IV.1] (Proportional FT / permutation rigidity)

v3 Theorem 11.7 corresponds to this result. The overlap-and-decomposition
approach is the blueprint's own proof technique; the paper uses a different
route. The mathematical content aligns. ✔

## [CPGSV21, Proposition IV.3] (BNT characterization)

The paper characterizes when canonical-form data yield a BNT post hoc.
The blueprint builds BNT separation into the predicate (Definition 11.2)
rather than proving it as a characterization. This deviation is not
flagged by the blueprint. Low priority (same as v2 cleanup item 15).

## Remaining deviations (documented)

1. **Newton–Girard status:** Now explicitly documented in Remark 11.14.
2. **BNT separation built into predicate:** Not flagged but standard for
   the Lean formalization approach.

---

# AI-Language Audit

**"CF-BNT predicate" → "canonical form with BNT separation":** Fixed in
theorem titles and statements throughout. The abbreviation "CF-BNT" still
appears (e.g., Theorem 11.4 title: "...in canonical form with BNT
separation") but is now used as a shorthand after the full expansion, which
is acceptable.

⚠️ **11-AI1.** The chapter preamble reads: "This chapter also contains the
auxiliary results on coefficient convergence and the Newton–Girard
identities." The phrase "also contains" is organizational meta-language.
A mathematician would write: "The chapter concludes with auxiliary results
on coefficient convergence and Newton–Girard identities." Minor.

⚠️ **11-AI2.** Remark 11.6: "in the normal-canonical sense" is not
standard mathematical terminology. It reads as if "normal-canonical" is a
technical modifier creating a separate sense of "normal." A mathematician
would not write this. See 11-S5 for the recommended rewrite.

**"Collected here" (v2 preamble):** Fixed. ✔

**Meta-commentary in Thm 10.8 proof:** Removed. ✔

**"The overlap-orthonormal hypotheses are assumed directly...":** Removed. ✔

**"The irreducible-TP variant uses the same matching argument...":**
Removed. ✔

**"Basis Normal Tensor" as compound noun:** Fixed. ✔

---

# Formalization Notes

**11-F1. BNT as Lean structure (from comprehensive reference 10-F1).**
Definition 11.1 defines a BNT as a triple (normality, span, eventual
linear independence). In Lean this is a structure with proof-carrying
fields. The span formulation (condition 2) maps naturally to
`Submodule.mem` or `span_le`. v3's formulation is cleaner for Lean than
v2's explicit-coefficient version.

**11-F2. Gram matrix route: is Definition 2.30 / Lemma 2.32 necessary?**

Theorem 11.5 and Theorem 11.9 both prove linear independence of block
MPV vectors. The current proof route is:

  Gram matrix G_{jk} = ⟨V(A_j)|V(A_k)⟩   [Definition 2.30]
    = conj(O_{A_j A_k}(N))               [Lemma 2.32]
    → δ_{jk}                              [overlap convergence]
  ⇒ G invertible ⇒ linear independence.

An alternative route uses only the overlap (Definition 2.31):

  The overlap matrix M_{jk} = O_{A_j A_k}(N) → δ_{jk}.
  Hence M is eventually invertible.
  If ∑_j c_j |V(A_j)⟩ = 0, take the overlap of each side with V(A_k):
    ∑_j c_j O_{A_k A_j}(N) = 0 for each k.
  Since M^T is invertible, c_j = 0 for all j.

This second route avoids Definition 2.30 (MPV inner product), Lemma 2.32,
and the conjugation step entirely. The overlap convention (bar on B in
O_{AB}, matching the transfer map F_{AB}(X) = ∑ A^i X (B^i)†) is
natural for the spectral-gap chapters, while the inner product convention
(bar on A in ⟨V(A)|V(B)⟩) is natural for the Gram matrix. These two
conventions are related by Lemma 2.32 (O_{AB} = conj(⟨V(A)|V(B)⟩)),
which is why the conjugation step arises.

However, in Lean, the standard `LinearIndependent` API works with the
inner product, so the Def 2.30 / Lemma 2.32 route may be more natural
for the formalization.

**Decision for the formalization agent:** If Lean's `LinearIndependent`
or `Finset.linearIndependent` naturally consumes a Gram matrix built from
the inner product, keep Definition 2.30 and Lemma 2.32. If the agent
finds it easier to argue linear independence directly from the overlap
matrix, Definition 2.30 and Lemma 2.32 can be dropped and the proof
rewritten to use only the overlap. Either way, the mathematical content
is identical.

**11-F3. Coefficient-instantiation bridge (from comprehensive reference).**
Remark 11.8 provides the bridge between the abstract Theorem 11.7 and
the CF-BNT application. For Lean, this translates to a lemma that
constructs the abstract data from CF-BNT data. The remark identifies the
ingredients (Theorem 2.24, Definition 11.2) but does not state a formal
lemma. The formalization agent should extract this as a standalone lemma.

**11-F4. Newton–Girard in Mathlib.** Theorems 11.12–11.13 are standard
results. Remark 11.14 confirms they are not on the critical path. The
formalization agent may use Mathlib's `Polynomial.sum_pow_eq_esymm`
or equivalent if available.

**11-F5. Normality equivalence as Lean lemma.** The rewrite recommended
for Remark 11.6 (see 11-S5) corresponds to a Lean lemma converting
between the spectral normality predicate (primitive transfer map, as in
Definition 9.29) and the algebraic normality predicate (eventual block
injectivity, as in Definition 2.19). This lemma already exists
conceptually in the blueprint (via Theorems 8.49, 8.59, 9.27, per
Remark 2.20) but is not stated as a standalone conversion lemma.

---

# Cleanup Checklist

## Must fix

(None.)

## Should fix

**11-S1.** Theorem 11.7: the overloaded hypotheses remain from v2.
Remark 11.8 mitigates but does not resolve the fundamental issue that the
theorem reads as a specification rather than a mathematical statement.
If keeping the abstract form, consider at minimum adding a brief sentence
in the theorem statement itself: "The canonical-form application of these
hypotheses is described in Remark 11.8."

**11-S2.** Definition 11.1 condition 2: the span formulation is correct but
the connection to the explicit coefficients c_j(N) = μ_j^N (from
Theorem 2.24) used in the proofs should be noted. The current formulation
makes the BNT definition self-contained at the cost of hiding the
coefficient structure that downstream proofs rely on.

**11-S3.** Theorem 11.5 proof: "By Lemma 2.32, G_{jk}(N) = O̅_{A_j A_k}(N),
so the same convergence statements hold after conjugation" — should be
more explicit. The precise content of Lemma 2.32 is O_{AB} =
conj(⟨V(A)|V(B)⟩), so G_{jk} = conj(O_{A_j A_k}). The self-overlap is
real (under TP normalization), so conj(1) = 1; the cross-overlap decays
to 0, so conj(0) = 0. State this. See also 11-F2 for whether the
Gram-matrix route is necessary at all.

**11-S4.** Remark 11.8: the coefficient arrays a_{N,j} = μ_j^N do not
converge to nonzero limits in the raw form (since |μ_j| ≠ 1 in general).
The remark should note that the convergence hypotheses of Theorem 11.7
are satisfied after normalizing by the dominant weight (e.g., working with
(μ_j/μ_0)^N, with Theorem 11.10 providing the k ≥ 1 decay), or
alternatively that the proportionality constant c_N absorbs the overall
scaling. Currently the remark presents the instantiation a_{N,j} = μ_j^N
without addressing the convergence issue.

**11-S5.** Remark 11.6: contradicts Remark 2.20. The phrase "uses 'normal'
in the normal-canonical sense, not the eventual block-injective predicate
of Definition 2.19" presents a single notion of normality as two distinct
senses, directly contradicting Remark 2.20's statement that "every
subsequent use of 'normal' in this blueprint refers to this single
notion." The phrase "in the normal-canonical sense" is not standard
terminology.

Recommended rewrite: "Definition 11.3 references the normal canonical
form predicate (Definition 9.29), which encodes normality via the spectral
characterization (primitive transfer map). Definition 11.1 requires
normality via the algebraic characterization (eventual block injectivity,
Definition 2.19). These are equivalent by Remark 2.20, but the
equivalence must be invoked explicitly: the Wielandt theory of Chapter 8
provides the implication from primitivity to eventual block injectivity
needed in the formalization."

**11-S6.** Chapter title: "Bases of Normal Tensors" should be "Basis of
Normal Tensors" (singular). The chapter defines a single mathematical
object — "a basis of normal tensors" — and develops its theory. The
standard mathematical convention for chapter titles uses the singular
(as in "Spectral Gap," "Canonical Form," etc.). The v2 review's
recommendation to use the plural was an overcorrection: it correctly
identified the missing preposition "of" but unnecessarily pluralized.

## Low priority

**11-L1.** Remark 11.6: add a specific theorem reference for the Wielandt
bridge (instead of "the Wielandt theory of Chapter 8").

**11-L2.** Remark 11.11: define μ_{j,q} or give a specific reference to
[CPGSV21, Eq. (72a)] and/or Section 12.4.

**11-L3.** Theorem 11.13: note the equal-cardinality hypothesis (same n)
explicitly.

**11-L4.** Note the deviation from [CPGSV21, Proposition IV.3]:
the blueprint builds BNT separation into the CF predicate rather than
characterizing BNT post hoc. (Carried from v2 cleanup item 15.)

## Acceptable as-is

- Theorem 11.7's abstract formulation (with Remark 11.8 as bridge)
  is acceptable for a Lean-oriented blueprint, even though it reads
  differently from a pure mathematics document.

- The span formulation of Definition 11.1 condition 2 is cleaner for
  Lean than the explicit-coefficient version.

- The chapter preamble's "also contains" (11-AI1) is very minor.

- Block count notation g in Chapter 11 (vs r in Chapter 10) is
  documented and acceptable since g matches the physics literature.

---

# Final Assessment

v3 Chapter 11 addresses 13 of 16 cleanup items from the v2 review
(including item 0a, which is fully resolved by Remark 2.20 in Chapter 2).
The most important improvements are:

1. **Naming corrected:** "Basis of Normal Tensors" in Definition 11.1 and
   body text, matching [CPGSV21]. (Chapter title overcorrected to plural;
   see 11-S6.)
2. **Coefficient notation fixed:** Definition 11.1 uses span condition
   instead of problematic c_j.
3. **Remark 11.8 (coefficient instantiation):** Closes the gap between
   the abstract Theorem 11.7 and the CF-BNT application.
4. **Remark 11.6 expanded:** Names the normality bridge explicitly
   ([SPGWC10, Prop 3] + Wielandt theory). However, the wording
   contradicts Remark 2.20 (see 11-S5).
5. **σ overload fixed:** π used for permutations.
6. **Theorem 11.9 proof rewritten:** Meta-commentary removed, replaced
   with actual proof sketch.
7. **Remark 11.14:** Newton–Girard orphan status documented, with forward
   reference to Theorem 12.5 confirming the BNT linear independence route.
8. **Newton–Girard recursion stated:** Theorem 11.12 now gives the formula.
9. **Gram matrix proof clarified:** Lemma 2.32 cited in Theorem 11.5.
10. **Remark 2.20 (in Chapter 2):** Fully resolves the "two meanings of
    normal" cross-chapter issue that was tracked since the v2 review.

The "should fix" items are:

- **11-S5:** Remark 11.6 contradicts Remark 2.20 by presenting one notion
  of normality as two distinct senses. Rewrite to frame the issue as a
  proof obligation.
- **11-S6:** Chapter title should be singular "Basis of Normal Tensors."
- **11-S4:** Remark 11.8 does not address the convergence issue (μ_j^N
  does not converge to a nonzero limit without rescaling by the dominant
  weight).
- **11-S3:** Theorem 11.5 proof could be more explicit about conjugation.
  The necessity of the Gram-matrix route (via Def 2.30 / Lemma 2.32)
  vs a direct overlap-based argument is flagged for the formalization
  agent (11-F2).
- **11-S1:** Theorem 11.7 hypotheses still overloaded (mitigated by
  Remark 11.8).
- **11-S2:** Definition 11.1 span condition hides the coefficient
  structure used downstream.

The 3 unaddressed v2 items are all low priority: μ_{j,q} undefined
(11-L2), equal-cardinality implicit (11-L3), [CPGSV21, Prop IV.3]
deviation not flagged (11-L4).

**Priority for the formalization agent:**
1. Rewrite Remark 11.6 to align with Remark 2.20 (11-S5).
2. Fix chapter title to singular (11-S6).
3. Fix Remark 11.8 convergence gap (11-S4).
4. Decide whether Definition 2.30 / Lemma 2.32 route is needed for the
   Gram matrix argument, or whether direct overlap-based argument suffices
   (11-F2). If keeping Def 2.30 / Lemma 2.32, expand the conjugation
   step in Theorem 11.5 proof (11-S3).
5. Consider adding a cross-reference in Theorem 11.7's statement to
   Remark 11.8 (11-S1).
