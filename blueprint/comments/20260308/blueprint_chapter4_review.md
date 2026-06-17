
# Blueprint Review – Chapter 4 (Positive Maps, Channels, and Spectral Structure)

This document synthesizes the finalized reviews of **Sections 4.1–4.7** of Chapter 4 of `blueprint20260302`.  
It merges the previously produced section‑level review files into a **single coherent chapter review**, while preserving the **full finalized discussions without compression**, as required by the standing rules of this project.

The purpose of Chapter 4 in the blueprint is to introduce the **operator‑theoretic framework of completely positive maps and quantum channels** that underlies the analysis of MPS transfer operators used in later chapters.

The chapter builds the following conceptual chain:

1. positive maps and quantum channels
2. Kadison–Schwarz inequality
3. equality structure and multiplicative‑domain arguments
4. irreducibility of transfer maps
5. existence of fixed points
6. spectral structure of channels
7. primitivity and periodicity

These tools form the **operator‑algebraic backbone** used later for Perron–Frobenius–type arguments for MPS transfer operators.

The synthesis below preserves the detailed statement‑by‑statement analyses produced during the review process and adds light transitions between sections to ensure readability while keeping the content unchanged.

---


# Blueprint Review – Chapter 4 (Positive Maps and Quantum Channels)

This document records the **full assessment of Chapter 4** of `blueprint20260302`, following the same review protocol used for Chapters 2 and 3.

The review follows the protocol specified in `blueprint_review_protocol.md` and includes:

- global section assessment
- statement-by-statement analysis
- comparison with literature (primarily Wolf 2012)
- identification of redundancies
- identification of missing assumptions or definitions
- stylistic issues typical of AI‑generated text
- cross‑chapter consistency checks

---

# Section 4.1 — Positive Maps and Channels

Chapter 4 begins with:

> “This chapter develops the theory of positive maps and quantum channels on matrix algebras, following [Wol12].”

This framing is appropriate. The mathematical structure largely follows the material in **Michael Wolf's "Quantum Channels & Operations" lecture notes**, which are a standard reference for finite-dimensional quantum channels.

---

# Global Assessment of Section 4.1

Section 4.1 introduces:

1. positive maps  
2. trace-preserving maps  
3. completely positive maps  
4. quantum channels  
5. density matrices and their properties  

Overall evaluation:

| Aspect | Evaluation |
|---|---|
Mathematical correctness | Correct |
Alignment with literature | Mostly correct |
Structural quality | Over‑fragmented |
Conceptual ordering | Slightly inefficient |

Most statements are standard facts from linear algebra and quantum information theory. The mathematics is correct but the exposition introduces **too many trivial theorems as separate statements**.

---

# Statement‑by‑Statement Analysis

## Definition 4.1 — Positive Map

Definition:

E : M_D(C) → M_D(C) is positive if

X ≥ 0 ⇒ E(X) ≥ 0.

Assessment:

Correct.

This matches the standard definition of positivity used in operator theory and in Wolf’s notes.

No issues.

---

## Definition 4.2 — Trace‑Preserving Map

Definition:

tr(E(X)) = tr(X)

Assessment:

Correct.

However the presentation is slightly awkward.

In most treatments the equivalent formulation

E*(I) = I

is also introduced. This becomes important later when discussing fixed points and dual channels.

Recommendation:

Add a remark stating the equivalence between trace preservation and unitality of the adjoint map.

---

## Definition 4.3 — Completely Positive Map

The blueprint defines complete positivity through the **Kraus representation**

E(X) = Σ_i K_i X K_i†

and then states that this is equivalent to positivity of E ⊗ id_n.

Assessment:

This reverses the logical structure normally used in mathematics.

Standard approach:

Definition: complete positivity via tensor positivity  
Theorem: Kraus / Stinespring representation

The blueprint defines CP maps through Kraus form and then cites Choi’s theorem.

This is common in physics texts but logically inverted.

Recommendation:

Swap the logical order.

---

## Theorem 4.4 — CP Maps Are Positive

Statement:

Completely positive maps are positive.

Assessment:

Correct but trivial.

The proof is immediate from the definition.

Recommendation:

Downgrade this theorem to a remark.

---

# Density Matrices

## Definition 4.6 — Density Matrices

Definition:

D_D = { ρ ≥ 0 , tr ρ = 1 }

Assessment:

Correct.

This is the standard definition.

---

## Theorem 4.7 — Density Matrices Are Compact

Argument used:

- PSD cone is closed
- trace constraint bounds entries
- Heine–Borel theorem

Assessment:

Mathematically correct.

However the explanation

“PSD matrices with trace 1 have entry norms bounded by 1”

requires justification.

The bound follows from

|ρ_ij|² ≤ ρ_ii ρ_jj ≤ 1

using the Cauchy–Schwarz inequality for positive semidefinite matrices.

So the reasoning is valid but slightly under‑explained.

---

## Theorem 4.8 — Density Matrices Are Convex

Correct.

However this is trivial and could be merged into a single proposition about the density matrix set.

---

## Theorem 4.9 — Density Matrices Are Nonempty

Example given:

ρ = I / D.

Correct but extremely trivial.

---

## Theorem 4.10 — Channels Preserve Density Matrices

Proof uses:

- positivity of the channel
- trace preservation

Assessment:

Correct.

---

# Structural Issues in Section 4.1

The section suffers from **over‑fragmentation**.

Instead of grouping results, several extremely basic statements are separated into individual theorems.

Typical textbook presentation:

“The set of density matrices is a nonempty compact convex subset of M_D(C).”

and prove all properties in a single statement.

---

# Missing Definitions

Two notions appear implicitly but are never introduced explicitly.

1. Loewner order (operator order)

A ≥ B

2. Positive semidefinite matrices

Wolf introduces these definitions before discussing positive maps.

The blueprint assumes familiarity with the concepts.

Recommendation:

Add a short definition of operator order and positive semidefinite matrices.

---

# Alignment with the Literature

The chapter claims to follow Wolf 2012.

This is largely accurate, but Wolf’s notes introduce the material in a slightly different order.

Wolf’s order:

1. positive operators  
2. operator order  
3. positive maps  
4. completely positive maps  
5. Kraus representation  
6. quantum channels  

The blueprint skips directly to CP maps.

This is acceptable but slightly abrupt pedagogically.

---

# AI‑Style Language Issues

Example phrase:

“entry norms bounded by 1”

More natural phrasing would be

“matrix entries are bounded”.

This is a minor stylistic issue.

---

# Section 4.1 Final Assessment

| Category | Evaluation |
|---|---|
Correctness | Correct |
Clarity | Acceptable |
Structure | Fragmented |
Literature alignment | Mostly correct |

No mathematical errors were detected.

Main improvements needed:

- reduce trivial theorem fragmentation
- correct the logical definition of CP maps
- introduce operator order explicitly

---

# Cross‑Chapter Consistency (Chapters 2–4)

One duplication exists.

Lemma 2.7 in Chapter 2 states that the MPS transfer map is positive.

The transfer map

E_A(X) = Σ_i A_i X A_i†

is exactly a Kraus map.

Therefore Lemma 2.7 is a special case of the CP‑map framework introduced in Chapter 4.

Recommendation:

Move Lemma 2.7 into Chapter 4 or explicitly reference Chapter 4 when stating it.

---

# Conceptual Overlap with Earlier Chapters

Chapter 3 implicitly uses the transfer operator when discussing injectivity.

Chapter 4 formalizes the same structure as a Kraus map.

This is not duplication but rather a conceptual clarification.

Earlier chapters used the transfer operator algebraically.

Chapter 4 provides the operator‑algebra interpretation.

---

# Structural Role of Chapter 4

Chapter 4 introduces the operator‑theoretic machinery required for later chapters, including:

- irreducible channels
- peripheral spectrum
- primitive maps
- fixed‑point projections
- Perron–Frobenius structure

These results are later used in the classification of MPS tensors.

Thus Chapter 4 plays the role of a **technical operator‑theory foundation** for the remainder of the blueprint.

---

# Final Conclusion

Section 4.1 is mathematically correct and consistent with the literature.

However it requires moderate restructuring for clarity.

The main issues are structural rather than mathematical.


---


# Blueprint Review – Chapter 4 (Section 4.2)
## Kadison–Schwarz Inequality

This document records the finalized review and assessment of **Section 4.2 of Chapter 4** of `blueprint20260302`.

The review follows the protocol defined in `blueprint_review_protocol.md` and preserves the finalized discussion **without compression**, as agreed.  
The section is analyzed with respect to:

- mathematical correctness
- literature consistency
- statement-by-statement verification
- structural issues
- missing assumptions
- cross‑chapter consistency
- AI‑style language issues

---

# Global Assessment of Section 4.2

Section 4.2 introduces the **Kadison–Schwarz inequality for completely positive maps** and its version for adjoint maps.

The section serves as a key technical tool for later spectral arguments in the blueprint.

Overall evaluation:

| Aspect | Evaluation |
|---|---|
Mathematical correctness | correct |
Literature alignment | correct |
Logical structure | good |
Clarity | slightly compressed |
AI‑style language | minimal |

Unlike Section 4.1, this section is structurally sound and follows the standard proof strategy used in the literature.

The main mathematical result is the inequality

E(X†X) ≥ E(X)†E(X)

for **unital completely positive maps**.

---

# Statement‑by‑Statement Review

## Definition 4.11 — Kraus Map

Definition:

E(X) = Σᵢ Kᵢ X Kᵢ†

Assessment:

Correct.

This is the standard representation of completely positive maps.

However there is a **minor duplication** with Definition 4.3 in the earlier part of the chapter.

Definition 4.3 already introduced completely positive maps through Kraus form.

Definition 4.11 introduces Kraus maps again.

This is slightly redundant.

Recommendation:

Clarify that a **Kraus map is simply a CP map written explicitly in Kraus representation**.

---

## Definition 4.12 — Adjoint Kraus Map

Definition:

E*(X) = Σᵢ Kᵢ† X Kᵢ

Assessment:

Correct.

The blueprint remarks that when the Kraus operators are the MPS tensors

Kᵢ = Aᵢ

then the adjoint Kraus map corresponds exactly to the **MPS transfer map**.

This observation is correct and conceptually important.

It explains why the operator‑theoretic language of quantum channels is relevant for tensor‑network transfer operators.

No issues are detected here.

---

## Definition 4.13 — Unital Kraus Map

Definition:

Σᵢ Kᵢ Kᵢ† = I

Assessment:

Correct.

However the definition would be clearer if it explicitly stated the equivalent condition

E(I) = I.

This is the standard formulation of unitality.

The blueprint implicitly assumes this equivalence but does not spell it out.

This is a minor clarity issue.

---

## Definition 4.14 — Trace‑Preserving Kraus Map

Definition:

Σᵢ Kᵢ† Kᵢ = I

Assessment:

Correct.

The blueprint notes that this corresponds to the **normalization condition used in MPS transfer operators**.

This is correct.

Transfer maps arising from MPS constructions typically satisfy this trace‑preserving condition.

No issues here.

---

# Main Result

## Theorem 4.15 — Kadison–Schwarz Inequality

Statement:

If a Kraus map is **unital**, then

E(X†X) ≥ E(X)†E(X).

Assessment:

Correct.

This is the standard Kadison–Schwarz inequality for completely positive maps.

---

# Proof Strategy

The blueprint uses the standard **block‑matrix argument**.

Construct the block matrix

[ X†X   X† ]
[  X     I ]

which can be written as

vv†

with

v = ( X† , I )ᵀ.

This matrix is positive semidefinite.

Applying the completely positive map blockwise preserves positivity.

Taking the **Schur complement of the lower‑right block** then yields

E(X†X) ≥ E(X)†E(X).

Assessment:

Correct.

This is the standard proof used in operator‑algebra and quantum‑information literature.

The blueprint presents the argument in a slightly compressed form, but the logical structure is sound.

In a Lean blueprint this level of compression is acceptable **provided the underlying matrix‑analysis lemmas (positivity of block matrices and Schur complement properties) are available elsewhere in the formalization**.

---

# Theorem 4.16 — Kadison–Schwarz for the Adjoint Map

Statement:

If the Kraus map is **trace‑preserving**, then the adjoint satisfies

E*(X†X) ≥ E*(X)†E*(X).

Proof idea:

Apply the Kadison–Schwarz inequality to the Kraus operators Kᵢ†.

Assessment:

Correct.

This is the standard way to derive the inequality for trace‑preserving maps via the adjoint channel.

---

# Literature Consistency

The blueprint cites the corresponding result from **Wolf (2012)**.

The theorem and proof structure match the standard presentation of the Kadison–Schwarz inequality for completely positive maps.

Therefore the section is fully consistent with the cited literature.

---

# Missing Clarifications

One conceptual clarification could improve readability.

The Kadison–Schwarz inequality is stated for **unital maps**, while MPS transfer maps are typically **trace‑preserving rather than unital**.

The blueprint resolves this by applying the theorem to the **adjoint channel**, which is unital when the original channel is trace‑preserving.

Although this reasoning is correct, the blueprint does not explicitly explain why the adjoint version is needed.

Adding a brief explanation here would help readers understand the connection to tensor‑network transfer operators.

---

# Structural Issues

The only structural issue in this section is the **redundant introduction of Kraus maps**, since CP maps were already defined earlier in the chapter.

This redundancy is minor and does not affect correctness.

---

# AI‑Style Language Issues

Very few AI‑style phrasing issues appear in this section.

One slightly informal expression appears in the exposition:

“Applying the CP map blockwise preserves PSD‑ness.”

Although mathematically correct, the phrasing is informal.

Otherwise the exposition is clean and natural.

---

# Cross‑Chapter Dependencies

This result is **important for later chapters**.

In particular, the blueprint later uses the Kadison–Schwarz inequality to derive:

- Hilbert–Schmidt contraction properties
- spectral radius bounds for transfer operators
- Perron–Frobenius–type results for primitive channels

Therefore Section 4.2 provides a **key technical lemma** supporting the later spectral theory of MPS transfer maps.

---

# Final Assessment of Section 4.2

| Category | Evaluation |
|---|---|
Correctness | correct |
Clarity | good |
Structure | good |
Literature alignment | excellent |

No mathematical problems were detected in this section.

Compared with earlier parts of the blueprint, Section 4.2 is well structured and mathematically clear.

---

# Cleanup Recommendations

1. Clarify the relationship between **CP maps and Kraus maps** to avoid redundant definitions.
2. Explicitly state that **unitality means E(I) = I**.
3. Briefly explain why the **adjoint channel formulation is required for MPS transfer operators**.


---


# Blueprint Review – Chapter 4 (Sections 4.3–4.5)

This document records the **finalized review and assessment** of Sections **4.3–4.5 of Chapter 4** of `blueprint20260302`.

This review follows the protocol defined in `blueprint_review_protocol.md` and preserves the finalized discussion **without compression**, in accordance with the standing order established in this project.

The analysis includes:

- mathematical correctness
- literature consistency
- statement-by-statement verification
- structural issues
- missing assumptions or definitions
- cross‑chapter consistency
- stylistic issues

Special attention is given to **subtle normalization issues** (unital vs trace‑preserving maps), since these play an important role in later chapters.

---

# Global Assessment of Sections 4.3–4.5

These sections are mathematically sound and important for later chapters, especially Chapter 6.

Chapter 6 explicitly uses the Hilbert–Schmidt contraction from Theorem 4.17 and the chain

Kadison–Schwarz equality → multiplicative-domain arguments → Skolem–Noether.

Thus these sections provide a **load‑bearing part of the proof architecture**.

The most notable feature is that the blueprint **reorganizes the standard arguments** from the literature into a custom chain of lemmas tailored to later tensor‑network proofs.

This is legitimate but deviates somewhat from the standard exposition found in references such as Wolf.

Overall status:

| Aspect | Evaluation |
|---|---|
Mathematical correctness | correct |
Literature alignment | good, but reorganized |
Structural quality | acceptable |
Terminology | one important issue in Section 4.3 |
Cross‑chapter consistency | good |

---

# Section 4.3 — Multiplicative Domain

## Theorem 4.18 — Kadison–Schwarz gap decomposition

Statement:

For a unital Kraus map

E(X†X) − E(X)†E(X) = Σᵢ Rᵢ†Rᵢ

with

Rᵢ = XKᵢ† − Kᵢ†E(X).

Assessment:

Correct.

This is a useful algebraic refinement of the Kadison–Schwarz inequality and allows the blueprint to turn equality conditions into explicit Kraus‑operator relations.

The result is mathematically sound.

The only observation is structural: this lemma is somewhat specialized compared with the standard literature presentation, where this identity is usually not isolated as a named theorem.

However isolating it is reasonable because it is later used directly in the spectral‑gap proof.

---

## Theorem 4.19 — KS equality implies Kraus commutation

Statement:

If equality holds in the Kadison–Schwarz inequality for some X, then

XKᵢ† = Kᵢ†E(X)

for all i.

Assessment:

Correct.

The proof follows immediately from the gap decomposition, since the sum of positive operators vanishes only if each term vanishes.

This lemma is well positioned for later arguments.

No conflict with earlier chapters.

---

## Theorem 4.20 — KS equality for peripheral eigenvectors

Statement:

If E is unital and trace‑preserving and

E(X) = μX with |μ| = 1,

then equality holds in the Kadison–Schwarz inequality.

Assessment:

Correct.

The proof uses positivity of the KS gap together with trace preservation to show that the trace of the gap is zero.

Thus the gap operator must vanish.

This theorem is later used in Chapter 6 for the spectral‑gap argument.

One important subtlety appears here:

The theorem requires **both unitality and trace preservation**.

However MPS transfer maps are usually only **trace‑preserving** under the standard normalization Σ Aᵢ†Aᵢ = I.

Later chapters therefore pass to a **doubly stochastic gauge** before using this result.

This normalization subtlety must be tracked carefully in later chapters.

---

## Theorem 4.21 — “Multiplicative domain”

Statement:

If equality holds in the Kadison–Schwarz inequality for X, then

E(X†Y) = E(X)†E(Y)

for all Y.

Assessment:

The statement itself is correct.

The proof uses the Kraus‑commutation relation from Theorem 4.19 to move X† past the Kraus operators and factor out E(X)†.

However the **terminology is somewhat misleading**.

The theorem proves only a **one‑sided multiplicative identity**, whereas the standard multiplicative‑domain theorem gives both left‑ and right‑multiplicative relations.

Thus the blueprint proves a **restricted version** of the usual multiplicative‑domain result.

This is sufficient for the later arguments but the name “multiplicative domain” is somewhat broader than the theorem actually establishes.

---

# Section 4.4 — Irreducibility

## Definition 4.22 — Irreducible map

Definition:

A linear map E is irreducible if the only orthogonal projections P satisfying

E(P M_D(C) P) ⊆ P M_D(C) P

are P = 0 and P = I.

Assessment:

Correct.

The definition matches Wolf’s condition for irreducibility.

The blueprint explicitly notes that complete positivity is not required for this definition.

No issues.

---

## Theorem 4.23 — Injectivity implies irreducibility

Statement:

If an MPS tensor A is injective, then its transfer map is irreducible.

Assessment:

Correct.

The proof uses the invariance condition to obtain

(I − P)AᵢP = 0

for all i.

Injectivity then upgrades this relation from the generators Aᵢ to all matrices, forcing P = 0 or P = I.

The argument is mathematically correct.

One step is slightly compressed and may require an explicit supporting lemma in a formalization context.

---

## Theorem 4.24 — Transfer map is completely positive

Statement:

The transfer map

E_A(X) = Σ Aᵢ X Aᵢ†

is completely positive.

Assessment:

Correct.

This follows immediately because the transfer map is a Kraus map.

This result is almost definitional once Kraus maps have been introduced.

---

## Theorem 4.25 — Transfer map is a channel

Statement:

Under the normalization

Σ Aᵢ†Aᵢ = I

the transfer map is a completely positive trace‑preserving map.

Assessment:

Correct.

Trace preservation follows from cyclicity of the trace.

This is where the normalization issue appears explicitly:

The transfer map is **trace‑preserving but not necessarily unital** under the usual MPS normalization.

Later chapters handle this by moving to a **doubly stochastic gauge**.

Tracking this subtlety will be important in later chapters.

---

# Section 4.5 — Cesàro Fixed‑Point Theorem

## Definition 4.26 — Cesàro mean

Definition:

σ_N = (1/N) Σ_{n=0}^{N−1} Eⁿ(ρ₀).

Assessment:

Correct.

Standard definition.

---

## Theorem 4.27 — Cesàro telescope

Statement:

E(σ_N) − σ_N = (1/N)(Eⁿ(ρ₀) − ρ₀).

Assessment:

Correct.

This is a simple telescoping identity.

The statement is mathematically trivial but harmless.

---

## Theorem 4.28 — Hermitian fixed‑point decomposition

Statement:

If X is a Hermitian fixed point of a channel, then its positive and negative parts are also fixed points.

Assessment:

Correct.

This follows from positivity and trace preservation.

The theorem matches results appearing in Wolf’s treatment of fixed points of quantum channels.

---

## Theorem 4.29 — Cesàro fixed‑point theorem

Statement:

Every quantum channel has a non‑zero positive semidefinite fixed point.

Assessment:

Correct.

The proof uses Cesàro averaging together with compactness of the density‑matrix set to obtain a convergent subsequence.

The telescoping identity then shows the limit is a fixed point.

This theorem is later used to establish the existence of fixed points for injective transfer maps.

---

# Deviations from the Literature

The blueprint reorganizes the standard argument used in the literature.

Instead of stating the full multiplicative‑domain theorem directly, it builds the following chain:

1. Kadison–Schwarz gap decomposition  
2. Equality implies Kraus commutation  
3. One‑sided multiplicative identity  

This structure is tailored to the later spectral‑gap proof in Chapter 6.

The deviation from the literature is therefore **intentional and structurally motivated** rather than an error.

---

# Missing or Redundant Definitions

Two minor issues appear:

1. Theorem 4.21 is called “Multiplicative domain” but proves only a one‑sided version.
2. Theorem 4.24 is essentially definitional once Kraus maps have been introduced.

These are stylistic issues rather than mathematical problems.

---

# Structural and Logical Issues

The logical dependency chain is clean:

Section 4.2 → Kadison–Schwarz inequality  
Section 4.3 → equality structure  
Section 4.4 → specialization to transfer maps  
Section 4.5 → fixed‑point existence  

Later chapters use these results in spectral arguments.

No circular dependencies were detected.

---

# Cross‑Chapter Consistency

No conflicts with the earlier Chapter 2 and Chapter 3 reviews were detected.

In fact, Section 4.4 realizes one of the recommendations made in the Chapter 2 review: moving transfer‑map positivity statements into the positive‑map chapter.

Thus the chapters are structurally consistent.

---

# Important Normalization Subtlety

Several results in Section 4.3 require both

unitality and trace preservation.

However the standard MPS transfer map normalization

Σ Aᵢ†Aᵢ = I

only guarantees trace preservation.

Later chapters therefore pass to a **doubly stochastic gauge** before applying these results.

This subtlety must be tracked carefully in later chapters in order to avoid incorrect assumptions.

---

# AI‑Style Language Issues

Very few AI‑style phrasing issues appear in these sections.

The only stylistic issue is the tendency to promote very small steps (such as the Cesàro telescoping identity) to the level of named theorems.

This is harmless but slightly unnatural stylistically.

---

# Final Verdict for Sections 4.3–4.5

1. No mathematical errors were detected.
2. The main deviation from the literature is the specialized structure of the multiplicative‑domain argument.
3. Terminology in Theorem 4.21 is slightly broader than the result proved.
4. The normalization subtlety (unital vs trace‑preserving maps) must be handled carefully in later chapters.

Overall the sections are mathematically sound and fit well into the blueprint’s later proof architecture.


---


# Blueprint Review – Chapter 4 (Sections 4.6–4.7) — Updated Analysis

This document records the **updated finalized review and assessment** of Sections **4.6–4.7 of Chapter 4** of `blueprint20260302`.

This version supersedes the earlier Section 4.6–4.7 review because it corrects an important conceptual issue regarding **doubly stochastic (DS) gauge** and the normalization of MPS transfer maps.

The updated analysis reflects the following correction:

> A single MPS tensor cannot in general be gauge-transformed so that its transfer map is both **unital and trace-preserving simultaneously**.

Thus, DS gauge should **not** be treated as a generic property of a single MPS tensor. The blueprint's usage of DS normalization must therefore be interpreted more carefully.

As before, this review follows the protocol defined in `blueprint_review_protocol.md` and preserves the finalized discussion **without compression**.

---

# Chapter 4 Review — Sections 4.6–4.7  
## Fixed-point projection; Peripheral spectrum and primitivity

These sections introduce the fixed-point projection and the spectral machinery required for later Perron–Frobenius arguments used in Chapters 5 and 8.

Their purpose is to establish:

- the decomposition of powers of a channel around a fixed point,
- structure of the peripheral spectrum,
- periodicity and primitivity of channels.

The section is mostly mathematically sound but contains several structural issues and one substantive conceptual mistake regarding peripheral eigenvalues.

---

# Section 4.6 — Fixed-point projection

## Definition 4.30 — Fixed-point projection

The blueprint defines

P(X) = tr(X)/tr(ρ) · ρ

for a fixed point ρ with tr(ρ) ≠ 0.

### Assessment

This definition is mathematically correct. The map P is a rank‑one idempotent whose image is span{ρ}.

However the name **“fixed-point projection”** is slightly misleading at this stage, because the blueprint has not yet proven that the fixed‑point space is one‑dimensional. That uniqueness result appears later in Chapter 5.

Thus P is not yet known to be the projection onto the entire fixed‑point space, but only a projection onto the span of a chosen fixed point.

### Recommendation

Rename it more conservatively as:

    rank‑one projection associated with a fixed point

or explicitly state that it becomes the canonical fixed‑point projection once uniqueness of the fixed point is proven later.

---

## Theorem 4.31 — Power decomposition

The blueprint states

E^n = P + (E − P)^n

for a trace‑preserving map E satisfying E(ρ)=ρ.

### Assessment

This result is correct.

The argument relies on

• P² = P  
• EP = P (because E(ρ)=ρ)  
• PE = P (because E is trace‑preserving)

which causes all mixed terms in the binomial expansion to vanish.

This decomposition isolates the contracting component (E−P) and is useful for later spectral arguments.

### Structural remark

This result behaves more like a **lemma** than a major theorem. Its promotion to a headline theorem is mostly stylistic.

---

# Section 4.7 — Peripheral spectrum and primitivity

This subsection develops spectral tools needed for primitive transfer operators and periodic channels.

Several issues appear here: a notation error, redundant statements, and an overly strong theorem.

---

## Definition 4.32 — Peripheral spectrum

The blueprint defines the peripheral spectrum using the notation

‖μ‖ = spectral radius.

### Issue

This is a **notation error**.

For complex numbers the correct notation is

|μ|.

Using ‖μ‖ is incorrect.

---

## Definition 4.33 — Peripheral eigenvalues

Peripheral eigenvalues are defined as eigenvalues satisfying

|λ| = 1.

This definition is valid for channels because the spectral radius equals 1.

### Structural comment

The blueprint now uses two overlapping notions:

• peripheral spectrum defined via spectral radius  
• peripheral eigenvalues defined via modulus 1

This duplication appears to arise from Lean formalization choices.

For exposition it would be cleaner to define peripheral eigenvalues once using the spectral radius definition.

---

## Theorem 4.34 — 1 is peripheral

If E has a nonzero fixed point then 1 belongs to the peripheral spectrum.

### Assessment

Correct **provided E is a channel**, since channels have spectral radius 1.

The statement should explicitly mention the channel hypothesis.

---

## Theorem 4.35 — Peripheral eigenvalues lie on the unit circle

This theorem merely restates the definition of peripheral eigenvalues.

### Assessment

Redundant.

This is definitional unpacking rather than a mathematical theorem.

---

## Theorem 4.36 — Finiteness of peripheral eigenvalues

The peripheral spectrum is finite in finite dimension.

### Assessment

Correct and harmless.

---

## Theorem 4.37 — Peripheral eigenvalues are roots of unity

The blueprint claims every peripheral eigenvalue of a channel is a root of unity.

### Assessment

This statement is **too strong as written**.

The argument assumes that powers μⁿ remain eigenvalues, but that closure property requires additional hypotheses (such as irreducibility combined with multiplicative‑domain arguments).

Those hypotheses only appear later in Lemma 4.42 and subsequent results.

Thus Theorem 4.37 should be rewritten or removed.

---

## Theorem 4.38 — Root‑of‑unity criterion

If the peripheral spectrum is closed under powers then every peripheral eigenvalue is a root of unity.

### Assessment

Correct.

This theorem captures the essential mathematical mechanism and should replace Theorem 4.37.

---

## Lemma 4.40 and Lemma 4.41

These lemmas implement the standard argument:

• finitely many roots of unity have a common exponent  
• powering the map removes periodic phases

Both statements are correct and well placed.

---

# Lemma 4.42 — Closure under powers

This lemma assumes:

• Kraus map  
• unital  
• trace‑preserving  
• irreducible

and proves closure of the peripheral spectrum under powers.

### Mathematical correctness

The proof is valid. It uses equality in the Kadison–Schwarz inequality to show invertibility of peripheral eigenvectors and then applies multiplicative‑domain arguments.

### Important normalization subtlety

However the assumptions **unital + trace‑preserving** are stronger than the natural normalization of MPS transfer maps.

For a standard MPS tensor A the transfer map

E_A(X) = Σ_i A_i X A_i†

satisfies

Σ_i A_i† A_i = I

which implies **trace preservation**, but not unitality.

The opposite condition

Σ_i A_i A_i† = I

gives **unitality** instead.

A similarity gauge transformation

A_i → X A_i X⁻¹

can enforce **one** of these canonical forms, but not both simultaneously in general.

Thus a generic MPS tensor cannot be gauge‑transformed so that its transfer map becomes both unital and trace‑preserving.

If such a transformation always existed, the Perron fixed points of the map and its adjoint would both become the identity, which is generally false.

Therefore Lemma 4.42 should be interpreted only as a **special doubly stochastic case**, not the generic MPS situation.

---

# Later correction inside the blueprint

The blueprint partially corrects this by introducing a more general formulation using **adjoint fixed points**, which removes the need for the doubly stochastic assumption.

This is the correct general framework for MPS transfer operators.

---

# Definitions of period and primitivity

Definitions 4.47–4.48 introduce:

• channel period  
• primitive maps

These definitions match standard usage in quantum Perron–Frobenius theory.

---

# Spectral characterization of primitivity

Theorems 4.49–4.50 give the standard characterization:

primitive ⇔ peripheral spectrum = {1}

and therefore all other eigenvalues satisfy |λ| < 1.

These statements are correct.

---

# Cross‑chapter consistency

These sections connect correctly with later parts of the blueprint.

Chapter 5 uses fixed‑point existence and irreducibility results.

Chapter 8 uses periodicity arguments to obtain primitive blocked transfer maps.

The only structural inconsistency appears in Theorem 4.37, which should be corrected before relying on the later results.

---

# Main issues in Sections 4.6–4.7

1. Typographical error in Definition 4.32.
2. Redundant theorem (4.35).
3. Incorrectly stated theorem (4.37).
4. Overly strong assumptions in Lemma 4.42.
5. Insufficient explanation of the role of DS gauge.

---

# Final verdict

Section 4.6 is mathematically correct with only minor naming issues.

Section 4.7 is largely correct but requires cleanup and clarification before being considered finalized.

In particular the blueprint should clarify the relationship between

• trace‑preserving canonical form  
• unital canonical form  
• doubly stochastic normalization.

Without this clarification the current presentation may give the false impression that DS gauge is generically attainable for MPS tensors.