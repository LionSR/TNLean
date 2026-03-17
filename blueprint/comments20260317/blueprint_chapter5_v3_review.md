
# Blueprint Review — Chapter 5 (Schwarz Inequalities and Multiplicative Domains), v2 → v3

This document reviews Chapter 5 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter4_review.md`, `blueprint_chapters2to6_review_consolidated.md`,
`blueprint_review_comprehensive_reference.md`, `blueprint_chapter4_v3_review.md`).

---

## Chapter numbering map

v3 Chapter 5 is a **new chapter** that did not exist in v2. It contains:

- Material moved from v2 Chapter 4 §4.2 (Kadison–Schwarz inequality) and
  §4.3 (Multiplicative domain), renumbered as v3 §5.1 and §5.2.
- Genuinely new content in §§5.2.1–5.2.4 (full multiplicative-domain
  structure, Schwarz inequality for normal operators, order/spectral
  interval preservation, Wolf Example 5.3).

The v2 → v3 theorem number mapping is:

| v2 | v3 | Content | Change |
|---|---|---|---|
| Def 4.12 | Def 5.1 | Kraus map | Renumbered only |
| Def 4.13 | Def 5.2 | Adjoint Kraus map | Renumbered only |
| Def 4.14 | Def 5.3 | Unital Kraus map | Renumbered only |
| Def 4.15 | Def 5.4 | Trace-preserving Kraus map | Renumbered only |
| Thm 4.16 | Thm 5.5 | Kadison–Schwarz inequality | Renumbered only |
| Thm 4.17 | Thm 5.6 | KS for adjoint | Renumbered only |
| Thm 4.18 | Thm 5.7 | Hilbert–Schmidt contraction | Renumbered only |
| Thm 4.19 | Thm 5.8 | KS gap decomposition | Renumbered only |
| Thm 4.20 | Thm 5.9 | KS equality ⟹ Kraus commutation | Renumbered only |
| Thm 4.21 | Thm 5.10 | KS equality for peripheral eigenvectors | Renumbered only |
| Thm 4.22 | Thm 5.11 | One-sided multiplicative identity | Renamed + renumbered |
| — | Defs 5.12–5.13 | Right/left/full multiplicative domains | **New** |
| — | Thm 5.14 | Multiplicative-domain characterization | **New** |
| — | Defs 5.15–5.17 | Subalgebra structure, restriction | **New (mislabeled)** |
| — | Thm 5.18 | CP Schwarz for normal operators | **New** |
| — | Thm 5.19 | Schwarz for normal ops (positive maps) | **New** |
| — | Thms 5.20–5.21 | Monotonicity, adjoint preservation | **New** |
| — | Thm 5.22 | Order interval preservation | **New** |
| — | Thm 5.23 | Spectral interval contractivity | **New** |
| — | Def 5.24, Thms 5.25–5.27 | Wolf Example 5.3 | **New** |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. Follows [Wol12, Ch. 5] throughout. Two issues: missing dependency for Thm 5.19, imprecise proof in Thm 5.25. |
| Internal consistency | One structural issue: Defs 5.15–5.17 are theorems mislabeled as definitions. |
| v2 → v3 changes | Major: new chapter split from v2 Ch 4, plus substantial new content (§§5.2.1–5.2.4). |
| AI language | Clean. No significant issues. |
| Formalization readiness | Several gaps: missing proof sketches for Defs 5.15–5.17, missing dependency lemmas for Thm 5.19, duplicate definitions. |
| Open items from prior review | 4-D resolved. 4-F confirmed in Ch 4 scope (already tracked). |

---

# v2 → v3 Changes

## Substantive changes

**1. New chapter created.** The Kadison–Schwarz and multiplicative-domain
material is separated from the channel/spectral theory of Chapter 4 into
its own chapter. This is a clean organizational improvement.

**2. Theorem 5.11 renamed (resolves 4-D).** v2's "One-sided
multiplicative-domain identity" (Thm 4.22) is now "Left multiplicative
identity from KS equality" (Thm 5.11). This directly addresses
consolidated review item 4-D.

**3. New §5.2.1: Full multiplicative-domain structure.** Definitions
5.12–5.13 (right/left/full multiplicative domains), Theorem 5.14
(characterization via KS equality), and Definitions 5.15–5.17 (subalgebra
structure, ∗-homomorphism property). This material corresponds to
[Wol12, Thm. 5.7 and Eqs. (5.11)–(5.12)].

**4. New §5.2.2: Schwarz inequality for normal operators.** Theorems
5.18–5.19. Theorem 5.19 is [Wol12, Prop. 5.1].

**5. New §5.2.3: Positive maps preserve order and spectral intervals.**
Theorems 5.20–5.23. Theorem 5.23 is [Wol12, Eq. (5.21)].

**6. New §5.2.4: Wolf Example 5.3.** Definition 5.24, Theorems 5.25–5.27.
A positive Schwarz map that is not CP. Illustrative; not on FT critical
path.

## Non-substantive changes

**7. Definitions 5.1–5.4 duplicated from Chapter 4.** These restate the
Kraus map, adjoint Kraus map, unital, and TP definitions. In v2 they were
Defs 4.12–4.15 in the same chapter. The chapter split creates
duplication.

## FT critical path assessment

Theorems 5.5–5.11 (KS inequality, gap decomposition, Kraus commutation,
peripheral eigenvector equality, left multiplicative identity) are on the
FT critical path. They are used in:
- Chapter 4 §4.5.2 (Lemma 4.33: peripheral closure via adjoint fixed
  point, uses Thms 5.9–5.11 implicitly)
- Chapter 7 (Theorem 7.12: spectral radius ≥ 1 implies gauge-phase
  equivalence, cites Thms 5.9–5.10 explicitly)

The new §§5.2.1–5.2.3 content (full multiplicative domain, normal-operator
Schwarz, order preservation) likely supports the spectral gap and
canonical form arguments but no explicit forward references to Thms
5.12–5.23 were found in later chapters of v3.

Wolf Example 5.3 (§5.2.4) is **not on the FT critical path**. It is
illustrative, showing the gap between positive and CP maps.

---

# Review Items: Prior Status Check

## From blueprint_chapter4_review.md (v2 review, §§4.2–4.3)

The original v2 review of §§4.2–4.3 identified several items. These now
fall in Chapter 5's scope.

| # | Item | Status in v3 |
|---|---|---|
| 4-D | Thm 4.22 "One-sided multiplicative-domain identity" terminology | ✅ **Resolved.** Renamed to "Left multiplicative identity from KS equality" (Thm 5.11). |
| 4-F | Lemma 4.44 "weighted Kadison–Schwarz equality" phrase | Not in Ch 5 scope. Remains in Ch 4 (Lemma 4.33). The Ch 4 v3 review confirmed this is resolved in v3. |
| — | KS requires CP (noted in original review) | ✅ Chapter 5 consistently states the KS inequality for *unital Kraus maps* (CP by construction). Hypothesis is explicit. |

## From consolidated review

| # | Item | Status in v3 |
|---|---|---|
| 4-D | "One-sided multiplicative-domain identity" terminology | ✅ **Resolved.** |

## From comprehensive reference

| # | Item | Status in v3 |
|---|---|---|
| Part II | No AI-language items specific to §§4.2–4.3 | N/A |
| 4-F4 | KS requires CP | ✅ Now in Ch 5 scope. Hypothesis explicit in Thm 5.5. |

---

# Forward Reference Verification

All forward references from Chapter 5 checked against v3 PDF:

| Reference | Target | Status |
|---|---|---|
| Def 5.1 → Definition 4.4 | CP map definition | ✅ Correct, Def 4.4 exists in v3 Ch 4. |
| §5.1 preamble → Remark 4.14 | Transfer map is CP | ✅ Correct, Remark 4.14 in v3 Ch 4. |
| Thm 5.14 → Theorem 5.11 | Left mult identity | ✅ Internal, same chapter. |
| Thm 5.18 → Theorem 5.6 | KS for adjoint | ✅ Internal, same chapter. |
| Thm 5.19 proof → Theorem 5.5 | KS inequality | ✅ Internal, same chapter. |
| Thm 5.22 → Theorem 5.20 | Monotonicity | ✅ Internal, same chapter. |
| Thm 5.23 → Theorem 5.22 | Order intervals | ✅ Internal, same chapter. |
| Defs 5.15–5.17 → [Wol12, Thm. 5.7] | Literature | ✅ Correct Wolf reference. |
| Thm 5.19 → [Wol12, Prop. 5.1] | Literature | ✅ Correct Wolf reference. |
| Thm 5.22 → [Wol12, Eq. (5.21)] | Literature | ✅ Correct Wolf reference. |

References *to* Chapter 5 from later chapters (verified):

| Source | Target | Status |
|---|---|---|
| Remark 4.32 (Ch 4) → Theorem 5.10 | KS equality for peripheral eigenvectors | ✅ Cited by number. |
| Lemma 4.33 (Ch 4) → Thms 5.9, 5.11 | Kraus commutation, multiplicative-domain powers | ⚠️ Used implicitly ("multiplicative-domain powers") without citing theorem numbers. |
| Theorem 7.12 (Ch 7) → Thms 5.9, 5.10 | KS equality, Kraus commutation | ✅ Cited by number. |

---

# Statement-by-Statement Analysis

## §5.1: Kadison–Schwarz inequality

### Definitions 5.1–5.4 (Kraus map, adjoint, unital, TP)

Correct. Identical to v2 Defs 4.12–4.15.

**Issue: duplication.** These definitions restate material now living in
Chapter 4 (Remark 4.14 already establishes the transfer map as a Kraus
map). In v2 they were in the same chapter, so no duplication existed.
The chapter split creates the same pattern as the known duplications
Def 8.1/2.23 and Def 8.14/4.23 (comprehensive reference, Part III, §N-4).
Should be cross-references.

### Theorem 5.5 (Kadison–Schwarz inequality)

Correct. Standard [Wol12, Eq. (5.2)]. Proof via 2×2 block matrix +
Schur complement. Unchanged from v2 Thm 4.16.

### Theorem 5.6 (KS for adjoint)

Correct. Applies Thm 5.5 to {K_i†}. Unchanged from v2 Thm 4.17.

### Theorem 5.7 (Hilbert–Schmidt contraction)

Correct. Requires both unital and TP. Clean proof. Unchanged from v2
Thm 4.18.

### Theorem 5.8 (KS gap decomposition)

Correct. Standard algebraic identity. Unchanged from v2 Thm 4.19.

### Theorem 5.9 (KS equality implies Kraus commutation)

Correct. PSD summands vanishing. Unchanged from v2 Thm 4.20.

### Theorem 5.10 (KS equality for peripheral eigenvectors)

Correct. Requires both unital and TP. Proof: tr(G) = 0 forces G = 0.
Unchanged from v2 Thm 4.21.

### Theorem 5.11 (Left multiplicative identity from KS equality)

Correct. Renamed from "One-sided multiplicative-domain identity" (v2
Thm 4.22). The new name is accurate: the result establishes
E(X†Y) = E(X)†E(Y), which is the left multiplicative identity.
Proof unchanged.

## §5.2: Multiplicative domain

### Definitions 5.12–5.13 (Right/left/full multiplicative domains)

**New in v3.** Correct. These are [Wol12, Eqs. (5.11)–(5.12)]. The
convention is stated clearly: 𝒜_R controls right multiplication,
𝒜_L controls left multiplication.

### Theorem 5.14 (Multiplicative-domain characterization)

**New in v3.** Correct. The two-sided characterization
X ∈ 𝒜_R(E) ⟺ E(XX†) = E(X)E(X)† and
X ∈ 𝒜_L(E) ⟺ E(X†X) = E(X)†E(X). This is [Wol12, Thm. 5.7].
Proof correctly chains Thm 5.11 and its X† variant.

### Definition 5.15 (One-sided multiplicative domains are subalgebras)

**New in v3. Mislabeled.** This is a theorem, not a definition. It asserts
that 𝒜_R(E) and 𝒜_L(E) are unital subalgebras of M_D(ℂ). No proof
sketch is given. For Lean, this requires showing:
(a) closure under addition (immediate from linearity),
(b) closure under multiplication (requires chaining the
    multiplicativity property),
(c) containment of 𝟙 (from unitality of E).

### Definition 5.16 (Multiplicative domain is a ∗-subalgebra)

**New in v3. Mislabeled.** This is a theorem asserting that 𝒜(E) =
𝒜_R ∩ 𝒜_L is a ∗-subalgebra. No proof sketch. For Lean, the key
additional step beyond Def 5.15 is closure under adjoint: if
X ∈ 𝒜(E), then X† ∈ 𝒜(E). This follows from Thm 5.14's
characterization.

### Definition 5.17 (Restriction to multiplicative domain is a ∗-homomorphism)

**New in v3. Mislabeled.** This is a theorem asserting that E|_{𝒜(E)}
is a ∗-algebra homomorphism. No proof sketch. For Lean, this requires
verifying multiplicativity (from the definition of 𝒜(E)) and
preservation of adjoints (from Thm 5.21 or the Kraus commutation
relation). This is the culminating algebraic statement of
[Wol12, Thm. 5.7].

### §5.2.2: Schwarz inequality for normal operators

### Theorem 5.18 (CP Schwarz inequality for normal operators)

**New in v3.** Correct but **redundant**. The statement says: if E* is
the adjoint Kraus map of a TP family and A is normal, then the Schwarz
gap E*(A†A) − E*(A†)E*(A) ≥ 0. The proof says "this is exactly
Theorem 5.6." Indeed, Theorem 5.6 gives the Schwarz inequality for the
adjoint Kraus map for *all* A, not just normal A. The normality
hypothesis is unused. Theorem 5.18 adds nothing beyond Thm 5.6.

Its role is as a stepping stone to Theorem 5.19 (the positive-map
generalization, where normality *is* needed). This should be made
explicit — as written, it looks like normality buys something here,
when it does not.

### Theorem 5.19 (Schwarz inequality for normal operators, positive maps)

**New in v3.** Correct statement: positive T with T(𝟙) ≤ 𝟙 satisfies
the Schwarz inequality for normal A. This is [Wol12, Prop. 5.1].

**Issue: proof has missing dependencies.** The proof says: "Restrict T
to the commutative ∗-subalgebra generated by 𝟙, A, A†, and A†A. On
this domain the map is completely positive, so [...] Theorem 5.5 applies."

This argument invokes two non-trivial facts not stated in the blueprint:

(a) **A positive map restricted to a commutative C*-subalgebra is
    completely positive.** This is [Wol12, Prop. 1.6]. It uses
    the structure theory of commutative C*-algebras and the fact
    that n-positivity = positivity on commutative domains.

(b) **A CP map on a subalgebra extends to a CP map on the full
    matrix algebra.** This is [Wol12, Prop. 1.7] (Arveson extension).
    Needed because Theorem 5.5 is stated for maps on M_D(ℂ), not
    on subalgebras.

For Lean formalization, both (a) and (b) are required lemmas. They
should either be stated in the blueprint (in Chapter 4, which develops
CP theory) or explicitly cited as external dependencies.

### §5.2.3: Positive maps preserve order and spectral intervals

### Theorem 5.20 (Positive maps are monotone)

**New in v3.** Correct. Immediate from the definition of positivity.

### Theorem 5.21 (Positive maps preserve adjoints)

**New in v3.** Correct. Standard fact: positive maps send Hermitian to
Hermitian, hence preserve the decomposition A = B + iC.

### Theorem 5.22 (Order intervals are preserved)

**New in v3.** Correct. This is [Wol12, Eq. (5.21)].

**Issue: proof is compressed.** The proof says "Apply monotonicity to the
inequalities a𝟙 ≤ A ≤ b𝟙. The scalar bounds are preserved because
a ≤ 0 ≤ b and T(𝟙) ≤ 𝟙." The actual argument for the lower bound is:
T(a𝟙) = a·T(𝟙), and since a ≤ 0 and T(𝟙) ≤ 𝟙, we get a·T(𝟙) ≥ a·𝟙.
This is not just "monotonicity" — it is a separate scalar-times-sub-unital
inference. The upper bound b·T(𝟙) ≤ b·𝟙 uses b ≥ 0 similarly.
Should be expanded for formalization.

### Theorem 5.23 (Spectral interval contractivity)

**New in v3.** Correct. Follows from Thm 5.22 and the spectral
theorem for Hermitian matrices.

### §5.2.4: Wolf Example 5.3

### Definition 5.24 (Wolf Example 5.3 map)

**New in v3. Mislabeled.** This introduces a specific illustrative map,
not a general concept. Wolf labels it "Example 5.3," and the blueprint
should follow suit: "Example 5.24" rather than "Definition 5.24." The
same applies to the entire §5.2.4 block (Def 5.24 + Thms 5.25–5.27),
which collectively constitute an *example* of a Schwarz map that is
not CP.

The map is T(A) = ½A^T + ¼tr(A)𝟙. This is [Wol12, Ex. 5.3].

**Minor: Heisenberg/Schrödinger notation.** Wolf defines this as T*
(Heisenberg picture). The blueprint writes it as T. The map is not
self-adjoint (the transpose is not self-adjoint w.r.t. Hilbert–Schmidt
on the full matrix algebra), so T ≠ T*. The conclusions (positive,
Schwarz, not CP) hold for both T and T*, so this is harmless, but it
is a notational discrepancy with the source.

### Theorem 5.25 (Wolf Example 5.3 is positive)

**New in v3.** Correct conclusion, imprecise proof.

**Issue: "convex combination" is incorrect.** The proof says "It is a
convex combination of the transpose map and the map A ↦ tr(A)𝟙." But
the coefficients are ½ and ¼, which sum to ¾ ≠ 1. This is a conic
(nonnegative) combination, not a convex combination. The positivity
conclusion follows from the fact that nonneg linear combinations of
positive maps are positive. The same imprecise language appears in
Wolf's original text.

For Lean, the proof needs: the positive cone of linear maps is closed
under nonneg scalar multiplication and addition.

### Theorem 5.26 (Wolf Example 5.3 satisfies Schwarz)

**New in v3.** Correct. The shift-invariance trick F(A + λ𝟙) = F(A) and
the 2×2 computation for traceless A follow Wolf's proof exactly.

### Theorem 5.27 (Wolf Example 5.3 is not CP)

**New in v3.** Correct. The Choi matrix test on the antisymmetric vector
is the standard argument.

---

# Cross-Chapter Consistency

## References from Chapter 5

| Reference | Target | Status |
|---|---|---|
| Def 5.1 → Def 4.4 | CP map | ✅ |
| §5.1 preamble → Remark 4.14 | Transfer map is CP | ✅ |

## Cross-chapter reference gap

**Lemma 4.33 (Ch 4, §4.5.2) uses Chapter 5 material implicitly.** The
proof says "multiplicative-domain powers give E(X^n) = μ^n X^n" without
citing Theorem 5.9 or 5.11 by number. For the formalization agent, the
Lean proof term needs the explicit reference chain: Thm 5.9 (Kraus
commutation) → iterate to get E(X^n) = μ^n X^n.

## Duplication

Definitions 5.1–5.4 (Kraus map, adjoint, unital, TP) duplicate content
from Chapter 4. In v2, these were Defs 4.12–4.15 in the same chapter as
the KS material, so no duplication existed. The chapter split creates
the duplication. Recommendation: replace with cross-references to
Chapter 4 (same pattern as the known duplications Def 8.1/2.23 and
Def 8.14/4.23).

---

# Literature Alignment

## [Wol12, Chapter 5]

| Blueprint | Wolf | Match |
|---|---|---|
| Thm 5.5 | Eq. (5.2) | ✅ |
| Thm 5.8 | Proof of Eq. (5.2) | ✅ |
| Thm 5.10 | (standard; follows from KS + trace preservation) | ✅ |
| Thm 5.11 | Part of Thm. 5.4 proof | ✅ |
| Defs 5.12–5.13 | Eqs. (5.11)–(5.12) | ✅ |
| Thm 5.14 | Thm. 5.7 | ✅ |
| Defs 5.15–5.17 | Thm. 5.7 (algebraic conclusions) | ✅ Statement matches; proof missing. |
| Thm 5.19 | Prop. 5.1 | ✅ Statement matches; proof dependencies missing. |
| Thm 5.22 | Eq. (5.21) | ✅ |
| Thm 5.23 | Eq. (5.21) | ✅ |
| Def 5.24, Thms 5.25–5.27 | Ex. 5.3 | ✅ Minor notation difference (T vs T*). |

No deviations from the literature. All new results correspond to
specific Wolf results and are correctly attributed.

---

# AI-Language Audit

## From comprehensive reference Part II

No AI-language items from the catalogue apply to this chapter. The
material was in v2 §§4.2–4.3, which had no flagged AI-language issues.

## New items in v3 Chapter 5

| Phrase | Location | Assessment |
|---|---|---|
| "This chapter collects the Schwarz-inequality material" | Chapter preamble | Mildly organizational but acceptable. "Collects" is slightly passive; "develops" or "presents" would be more standard. |
| "Wolf Example 5.3 map" | Def 5.24 | Slightly unusual as a definition name. Acceptable: clearly identifies the source. |

No serious AI-language issues in this chapter.

---

# Formalization Notes

## From comprehensive reference Part IV

| # | Note | Status in v3 |
|---|---|---|
| 4-F4 | KS requires CP | ✅ Now in Ch 5. Thm 5.5 explicitly requires unital Kraus map (which is CP by definition). |

## New formalization notes for Chapter 5

**5-F1. Definitions 5.15–5.17 need proof terms.** These are labeled
"Definition" but assert mathematical facts (subalgebra closure, ∗-closure,
homomorphism property). Each requires a Lean proof:
- Def 5.15: 𝒜_R and 𝒜_L are closed under multiplication and contain 𝟙.
- Def 5.16: 𝒜(E) is closed under adjoint.
- Def 5.17: E restricted to 𝒜(E) is multiplicative and adjoint-preserving.

**5-F2. Theorem 5.19 requires two unstated lemmas.** The proof of the
Schwarz inequality for positive maps on normal operators depends on:
(a) Positive maps on commutative C*-subalgebras are CP
    [Wol12, Prop. 1.6].
(b) CP extension from subalgebra to full matrix algebra
    [Wol12, Prop. 1.7] (Arveson extension).
These should be stated in the blueprint (likely in Chapter 4) or
explicitly cited as external Lean dependencies.

**5-F3. Theorem 5.22 proof: scalar-times-sub-unital step.** The step
T(a𝟙) = a·T(𝟙) ≥ a·𝟙 (for a ≤ 0, T(𝟙) ≤ 𝟙) is a separate Lean
lemma, not just "monotonicity."

**5-F4. Theorem 5.18 is a trivial specialization of Theorem 5.6.** The
normality hypothesis is unused. In Lean, Thm 5.18 can be proved as a
one-line corollary of Thm 5.6. The formalization agent should not
build a separate proof.

**5-F5. Wolf Example 5.3 (§5.2.4): concrete 2×2 computations.** The
proofs of Thms 5.25–5.27 require explicit matrix calculations in M_2(ℂ).
In Lean, this is either `decide` / `norm_num` style automation or
explicit computation with matrix entries. Not on the FT critical path.

---

# Cleanup Checklist

## Must fix

1. **Defs 5.15–5.17: relabel as Theorems and add proof sketches.**
   These assert mathematical facts and have no proofs. Each needs at
   minimum a one-line proof sketch for Lean.

2. **Thm 5.19: state the missing dependency lemmas.** The proof relies
   on [Wol12, Props. 1.6 and 1.7] (positivity on commutative domains
   is CP; Arveson extension). These should be stated somewhere in the
   blueprint (Chapter 4 is the natural location) or flagged as external
   Lean dependencies.

## Should fix

3. **Lemma 4.33 cross-reference gap.** The proof of Lemma 4.33 (Ch 4)
   uses "multiplicative-domain powers" without citing Thms 5.9/5.11.
   Add explicit theorem citations.

4. **Defs 5.1–5.4: replace with cross-references.** These duplicate
   definitions from Chapter 4 (Remark 4.14, Defs 4.12–4.15 in v2).
   Should be cross-references, not restatements.

5. **Thm 5.22 proof: expand the scalar bound argument.** The step
   "scalar bounds are preserved because a ≤ 0 ≤ b and T(𝟙) ≤ 𝟙" is
   too compressed for formalization. Write out T(a𝟙) = a·T(𝟙) ≥ a·𝟙
   explicitly.

6. **Thm 5.25 proof: "convex combination" → "nonnegative linear
   combination."** Coefficients ½ + ¼ = ¾ ≠ 1.

7. **Def 5.24: relabel as "Example 5.24."** Wolf labels this
   "Example 5.3"; the blueprint should not elevate an illustrative
   example to a "Definition." The entire §5.2.4 block is an example,
   not a definition.

## Low priority

8. **Thm 5.18: add a remark explaining its role.** As stated, it adds
   a normality hypothesis to Thm 5.6 that isn't needed. Its purpose
   is as a stepping stone to Thm 5.19. A one-line remark ("for CP
   maps, normality is not needed; the interest is in the extension to
   positive maps in Theorem 5.19") would clarify.

9. **Def 5.24: T vs T\* notation.** Wolf defines the map as T*. The
   blueprint writes T. Harmless (the conclusions hold either way) but
   differs from the source.

10. **Chapter preamble: "collects" → "develops" or "presents."** Very
    minor.

## Acceptable as-is

11. **Wolf Example 5.3 not on FT critical path.** Illustrative only.
    No action needed beyond the proof fixes noted above.

12. **Theorem 5.23 correctly adds the hypothesis a ≤ 0 ≤ b.** This
    matches Wolf's "interval containing zero." No issue.

---

# Final Assessment

Chapter 5 is mathematically sound. The existing material (Thms 5.5–5.11)
is correct and unchanged from v2, and the new material (§§5.2.1–5.2.4)
correctly extends the KS framework following [Wol12, Chapter 5].

The main issues are structural rather than mathematical:
- Definitions 5.15–5.17 are theorems without proofs (must fix).
- Theorem 5.19 relies on unstated lemmas (must fix for Lean).
- Definition 5.24 is an example mislabeled as a definition (should fix).
- Definitions 5.1–5.4 duplicate Chapter 4 (should fix).
- One cross-chapter implicit reference in Lemma 4.33 (should fix).
- Minor proof wording issues in Thms 5.22 and 5.25 (should fix).

**No mathematical errors found. Six items to fix for Lean formalization
readiness, of which two are "must fix" (Defs 5.15–5.17 proofs, Thm 5.19
dependencies).**
