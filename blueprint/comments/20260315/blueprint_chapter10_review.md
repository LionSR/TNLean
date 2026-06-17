
# Blueprint Review — Chapter 10 (Bases of Normal Tensors)

This review follows the protocol in `blueprint_review_protocol.md` and the
format established in the Chapter 8 review. It covers v2 of the blueprint,
identifies v1 → v2 changes, compares against the source papers [PGVWC07]
and [CPGSV21], and checks cross-chapter consistency with Chapters 2–9 and
forward dependencies on Chapter 11.

---

## 1. Role of Chapter 10 in the Blueprint

Chapter 10 has four functions:

1. **§10.1 (Bases of normal tensors and cross-overlap decay):** Defines
   bases of normal tensors (Definition 10.1), the canonical form with BNT
   separation and the normal-canonical variant (Definitions 10.2–10.3),
   proves cross-overlap decay for distinct blocks (Theorem 10.4), and
   shows canonical-form data with BNT separation yield a basis of normal
   tensors (Theorem 10.5).

2. **§10.2 (BNT permutation rigidity):** Two permutation theorems —
   Theorem 10.7 (proportional MPV case) and Theorem 10.8 (overlap-
   orthonormal case) — showing that two BNT-like families related by
   proportional or same MPV must be related by a block permutation and
   gauge-phase equivalence.

3. **§10.3 (Coefficient convergence):** Theorem 10.9 (coefficient ratio
   decay) and Remark 10.10 (strict-dominance regime).

4. **§10.4 (Newton–Girard identities):** Theorem 10.11 (trace recursion)
   and Theorem 10.12 (equal power sums imply equal multisets).

The chapter draws on Chapters 2, 6, 8, and 9, and feeds directly into
Chapter 11 (full assembly of the Fundamental Theorem).

---

## 2. Global Assessment

| Aspect | Evaluation |
|---|---|
| Mathematical correctness | Mostly correct; several issues flagged below |
| Conceptual clarity | Fair; some gaps in hypotheses and proof sketches |
| Structural quality | Significantly restructured from v1; cleaner separation of concerns |
| Cross-chapter consistency | Good; inherits the "two meanings of normal" issue |
| Literature alignment | Partial; see §6 |
| v1 → v2 changes | Major restructuring (see §3) |

Chapter 10 is the shortest substantive chapter (12 statements across 3 pages).
The restructuring from v1 is the most important change: v1 combined BNT
theory and full assembly in one chapter, while v2 separates them (Chapter 10
for BNT, Chapter 11 for assembly). This is cleaner. However, several issues
remain: Definition 10.1 has a problematic coefficient ambiguity, Theorem 10.7
is overloaded with hypotheses that should be factored, and the Newton–Girard
section is orphaned from its only consumer (Chapter 11's equal-MPV theorem,
which no longer appears to use it).

---

## 2a. Naming: "Basis of Normal Tensors" vs "Basis Normal Tensor"

The original literature consistently uses "basis **of** normal tensors"
([CPGSV21, Definition IV.2]; [CPGSV17, Definition 2.6]). This is a
"basis"-type collection made of normal tensors: "basis" describes the
mathematical role (spanning + linear independence of the generated MPVs),
while "normal" is a property of each constituent tensor. The preposition
"of" is load-bearing.

The blueprint drops the preposition and treats "BNT" as an abbreviation
for "Basis Normal Tensor" — as if this were a compound noun naming a
special type of tensor. This is misleading: a single tensor is either
normal or not; "basis" is a property of the *collection*. The blueprint's
Definition 10.1 title reads "Basis Normal Tensor (BNT)," but should read
"Basis of Normal Tensors (BNT)." This error propagates to the chapter
title ("Basis Normal Tensors" → should be "Bases of Normal Tensors") and
to usages like "the block tensors form a BNT decomposition" (better:
"the block tensors form a basis of normal tensors").

The abbreviation "BNT" is fine for subsequent use, but the expanded form
should always be "basis of normal tensors," and the blueprint should not
use "BNT" as a noun for a single tensor.

---

## 2b. Clarification: Injective vs Normal vs Irreducible Tensors

This section addresses a cross-chapter presentation issue that surfaces
most acutely in Chapter 10 (via Remark 10.6) but originates in the
definitions of Chapter 2 and the bridge theorems of Chapters 7–8.

### The hierarchy

Three properties of an MPS tensor A with bond dimension D, in order of
decreasing strength:

**Injective** (Def 2.16): span{A_i : i = 0, ..., d−1} = M_D(ℂ). The
Kraus operators span the full matrix algebra at length 1. Equivalently,
S_1(A) = M_D(ℂ).

**Normal** (Def 2.19 / [CPGSV21, Def IV.1]): ∃L₀ such that S_{L₀}(A) =
M_D(ℂ). The L₀-fold blocked tensor is injective.

**Irreducible**: The transfer operator ℰ_A has no nontrivial invariant
subspace — equivalently, it has a unique eigenvalue of maximum modulus,
and the corresponding left and right eigenvectors are positive definite.
However, ℰ_A may have other eigenvalues of modulus 1, of the form
e^{2πiq/p}.

The chain is: injective ⟹ normal ⟹ irreducible. After blocking p sites
(removing periodicity), an irreducible tensor becomes normal.

### At the transfer operator level

- **Injective** ⟺ ℰ_A has full Kraus rank at length 1 (the Kraus
  operators span M_D). This forces the transfer map to be primitive
  (irreducible + aperiodic) and much more: the primitivity index is 1.

- **Normal** ⟺ ℰ_A is a **primitive channel**: irreducible AND aperiodic
  (peripheral spectrum = {1}, no eigenvalue of modulus 1 other than 1
  itself). Equivalently: ∃n such that ℰ_A^n has full Kraus rank. This is
  [SPGWC10, Proposition 3]: eventual full Kraus rank ⟺ primitive channel
  ⟺ strongly irreducible. The primitivity index can be as large as
  O(D²).

- **Irreducible** ⟺ ℰ_A is an irreducible CP map: unique eigenvalue of
  maximum modulus with PD eigenvectors, but the peripheral spectrum may
  contain roots of unity e^{2πiq/p}. After blocking p sites, the
  irreducible map becomes primitive, hence normal.

### What the blueprint should say

There is **one** notion of normal tensor, with two equivalent
characterizations:
(a) algebraic: eventual full Kraus rank (Def 2.19),
(b) spectral: primitive transfer operator ([CPGSV21, Def IV.1]).

These are proved equivalent by [SPGWC10, Proposition 3], and the
blueprint establishes directions of this equivalence via Theorems 7.45,
7.52, and 8.26. The blueprint should include a single, prominent
"equivalence of normality" remark — ideally near Definition 2.19 or at
the start of Chapter 7 — stating all equivalent characterizations. Every
subsequent use should simply say "normal" without qualification, and
Remark 10.6 should reference this equivalence rather than treating the
gap between the two characterizations as an open issue.

The current presentation, which introduces Def 2.19 in Chapter 2 and
Def 8.28 ("normal canonical form") in Chapter 8 without a clear
statement that these describe the same class of tensors, creates
unnecessary confusion that propagates into Chapter 10.

---

## 3. v1 → v2 Changes

### What changed

**3-A. Chapter split.** v1's Chapter 10 ("BNT and Full Assembly") contained
both BNT theory (§10.1–10.4) and the full assembly (§10.5–10.6, Theorems
10.12–10.13). v2 splits this into Chapter 10 (BNT) and Chapter 11 (Full
Assembly). This is a structural improvement: the BNT theory is logically
independent of the assembly, and the split makes the dependency graph
cleaner.

**3-B. Definition 10.2: Lean name removed.** v1 reads: "An
*IsCanonicalFormBNT* extends the canonical form predicate..." v2 reads:
"A *canonical form with BNT separation* extends the canonical form..."
The Lean identifier `IsCanonicalFormBNT` is removed from the mathematical
text. Good — consistent with the AI-language cleanup tracked in
`ai_language_issues.md`.

**3-C. Definition 10.3 (Normal canonical form with BNT separation): NEW.**
v2 adds a normal-canonical companion to Definition 10.2, extending
Definition 8.28 (normal canonical form predicate) with the BNT separation
condition. This parallels the two-route structure established in Chapter 8
and continued in Chapter 9 (where Theorem 9.14 was similarly added).

**3-D. Theorem 10.3 → 10.4 (Cross-overlap decay): proof corrected.** v1's
Theorem 10.3 proof says: "If D_j ≠ D_k the overlap is zero by dimension
mismatch." v2's Theorem 10.4 proof says: "If D_j ≠ D_k, the rectangular
spectral gap theorem (Theorem 6.15) gives O_{A_j A_k}(N) → 0."

The v2 correction is important: the overlap O_{A_j A_k}(N) for blocks of
different bond dimension is not identically zero — it involves the mixed
transfer operator F_{A_j A_k}, which is a map between *different* matrix
algebras M_{D_j}(ℂ) and M_{D_k}(ℂ). The statement is that this overlap
*decays to zero*, which requires the rectangular spectral gap (Theorem 6.15),
not that it is zero. v1's claim was incorrect; v2 fixes it. ✔

**3-E. Theorem 10.5 (CF-BNT yields BNT): proof expanded.** v2 adds the
explicit overlap matrix argument G_{jk}(N) = O_{A_j A_k}(N) → δ_{jk}
and the "eventually invertible" conclusion. v1's proof was more compressed.

**3-F. Remark 10.6 (normality gap for normal-CF-BNT): NEW.** v2 adds an
important clarification: normal-CF-BNT data use "normal" in the
normal-canonical sense (Definition 8.28 = irreducible + primitive), not
the eventual block-injective sense (Definition 2.19). Therefore
normal-CF-BNT data do not automatically yield the BNT predicate, which
requires eventual block injectivity. This is a genuine mathematical
subtlety that v1 did not address.

**3-G. Theorem 10.7 (BNT permutation — proportional MPV case): rewritten
with explicit hypotheses.** v1's Theorem 10.5 assumed "two BNT
decompositions" and "proportional MPV families with convergent nonzero
coefficients." v2's Theorem 10.7 spells out all the hypotheses explicitly:
injective families, TP normalization, self-overlap → 1, cross-overlap → 0,
coefficient arrays with nonzero limits, and the proportional MPV identity.
This is significantly more explicit, which is appropriate for a
formalization blueprint.

**3-H. Theorem 10.8 (overlap-orthonormal case): DS → TP.** v1's Theorem
10.6 assumed "injective DS-gauge tensors." v2's Theorem 10.8 assumes
"injective tensors satisfying the TP normalization." Consistent with the
DS → TP corrections throughout the blueprint. ✔

**3-I. v1 §10.5 (Primitivity bridge) removed.** v1's Definition 10.10
(Primitive MPS tensor) and Theorem 10.11 (Primitive overlap convergence)
are gone in v2. These were absorbed into the Chapter 8 normal-canonical
route (Theorem 8.29 derives the self-overlap automatically from
primitivity). The removal is correct — the results were redundant with
the Chapter 8 machinery.

**3-J. Remark 10.10 (Strict-dominance regime): NEW.** v2 adds a remark
noting that Theorem 10.9 applies only in the strict-dominance case and
that the oscillatory case (equal moduli with different phases) is handled
separately in the full paper. This is an honest scope limitation.

**3-K. Theorem number renumbering.** Due to the additions and removal:
- v1 Def 10.1 → v2 Def 10.1 (identical)
- v1 Def 10.2 → v2 Def 10.2 (Lean name removed) + v2 Def 10.3 (NEW)
- v1 Thm 10.3 → v2 Thm 10.4 (proof corrected)
- v1 Thm 10.4 → v2 Thm 10.5 (proof expanded)
- v1 Thm 10.5 → v2 Thm 10.7 (rewritten with explicit hypotheses)
- v1 Thm 10.6 → v2 Thm 10.8 (DS → TP)
- v1 Thm 10.7 → v2 Thm 10.9
- v1 Thm 10.8 → v2 Thm 10.11
- v1 Thm 10.9 → v2 Thm 10.12
- v1 §10.5 (Def 10.10, Thm 10.11) → REMOVED
- v1 §10.6 (Thms 10.12–10.13) → moved to Chapter 11

### What did NOT change

**§10.4 (Newton–Girard identities):** Content identical between v1 and v2
modulo theorem renumbering.

**Definition 10.1:** Content identical modulo the cross-reference update
(v1 cites Definition 2.18; v2 cites Definition 2.19).

---

## 4. Statement-by-Statement Review

### Section 10.1 — Basis normal tensors

**Definition 10.1 (Basis Normal Tensor (BNT)).**

⚠️ **The coefficients c_j are not N-dependent in the statement, but they
must be.** The definition writes:
|V^{(N)}(A_tot)⟩ = ∑_j c_j |V^{(N)}(A_j)⟩.
This makes c_j look like constants independent of N. But the actual
decomposition (from Theorem 2.24 via the block-diagonal structure, cf.
Eq. (74) of [CPGSV21]) gives coefficients that depend on N:
V^{(N)}(A_tot)_σ = ∑_j (∑_q μ_{j,q}^N) V^{(N)}(A_j)_σ.
The coefficients are a_{N,j} = ∑_q μ_{j,q}^N, which depend on N through
the weights μ_{j,q}.

Compare with [CPGSV21, Definition IV.2], which says: "(i) for each N,
|V^{(N)}(A)⟩ can be written as a linear combination of V^{(N)}(A_j)."
This is more careful — it allows N-dependent coefficients without naming
them explicitly.

The blueprint's notation c_j (no N subscript) is misleading. Either:
(a) write a_{N,j} explicitly, or (b) follow the paper's phrasing and avoid
naming the coefficients in the definition.

**Recommendation:** Replace condition 2 with: "at each system size N, the
MPV of A_tot lies in the span of the block MPVs {|V^{(N)}(A_j)⟩}."

**Definition 10.2 (Canonical form with BNT separation).**
Correct. Extends Definition 9.8 with non-gauge-phase-equivalence of
distinct blocks of equal bond dimension.

**Definition 10.3 (Normal canonical form with BNT separation).**
Correct. Extends Definition 8.28 with the same non-equivalence condition.

⚠️ **Cross-chapter note:** This inherits the "two meanings of normal" issue.
"Normal canonical form" (Definition 8.28) uses "normal" in the sense of
irreducible + primitive, which is equivalent to but superficially different
from "normal" in Definition 2.19 (eventual block injectivity). Remark 10.6
correctly flags this gap, which is good.

**Theorem 10.4 (Cross-overlap decay for distinct CF-BNT blocks).**
Correct. The proof is clean:
- D_j ≠ D_k: rectangular spectral gap (Theorem 6.15) → decay.
- D_j = D_k but not gauge-phase equivalent: spectral gap (Theorem 6.17) → decay.

⚠️ **Missing hypothesis check.** The spectral gap theorems (6.15, 6.17)
require TP normalization of the individual blocks. This is supplied by the
CF-BNT predicate (which inherits it from Definition 9.8), so the theorem
is correct. But the proof sketch should note this: "The CF-BNT predicate
provides TP normalization for each block, which is the operative hypothesis
for the spectral gap."

⚠️ **Theorem 6.15 vs 6.17 for the rectangular case.** The proof cites
Theorem 6.15 for D_j ≠ D_k. Checking Chapter 6: Theorem 6.14 (v2) is
the rectangular spectral gap statement (for blocks of different dimension),
and Theorem 6.15 is the rectangular overlap decay corollary. The citation
should be verified — if v2's numbering is Theorem 6.15, fine; if the
rectangular overlap decay is actually Theorem 6.14, the citation needs
correction. (I cannot verify the exact numbering without re-reading
Chapter 6 page images, but the Chapter 6 review should contain this
information.)

**Theorem 10.5 (CF-BNT yields BNT).**
Correct. The argument is:
1. Each block is injective → 1-block injective → normal (Def 2.19). ✔
2. MPV decomposition (Theorem 2.24) gives the spanning condition. ✔
3. Gram matrix G_{jk}(N) = O_{A_j A_k}(N) → δ_{jk} (diagonal from
   self-overlap hypothesis, off-diagonal from Theorem 10.4), hence
   eventually invertible → linear independence. ✔

⚠️ **Subtlety: the Gram matrix is not the overlap matrix.** The overlap
O_{A_j A_k}(N) is the *bilinear* overlap (Definition 2.31, bar on B
side), while linear independence of vectors requires the *inner product*
(sesquilinear, bar on A side). The Gram matrix for linear independence is
G_{jk} = ⟨V^{(N)}(A_j) | V^{(N)}(A_k)⟩, not O_{A_j A_k}(N). The
relationship between the two involves complex conjugation (Lemma 2.32).

For self-overlaps this doesn't matter (O_{A A}(N) is real and equals the
norm squared), and for cross-overlaps the decay to zero is preserved
under conjugation. So the conclusion is correct. But the proof
conflates the two objects. For a formalization blueprint, this distinction
matters — the Lean code will need to pass through the conjugation lemma.

**Recommendation:** Note that G_{jk}(N) = ⟨V^{(N)}(A_j)|V^{(N)}(A_k)⟩ =
\overline{O_{A_j A_k}(N)} · (normalization factors), and that the decay /
convergence properties are preserved.

**Remark 10.6 (The normality gap for normal-CF-BNT).**
Correct and important. This is the honest statement that the normal-canonical
route (Definition 10.3 / Definition 8.28) does not automatically yield the
BNT predicate (Definition 10.1) because BNT requires eventual block
injectivity (Definition 2.19), while the normal-canonical route only
provides irreducibility + primitivity. The bridge would require
[SPGWC10, Proposition 3] / the Wielandt bound (Chapter 7), which does
connect primitivity to eventual full Kraus rank.

⚠️ **However, this gap is closable.** Primitivity of the transfer map
implies eventual full Kraus rank by [SPGWC10, Proposition 3], (b) ⟺ (c).
The blueprint already establishes this equivalence via Theorems 7.45, 7.52,
and the aperiodicity bridge (§7.11). So the remark is correct that
normal-CF-BNT data do not *by themselves* yield BNT, but the additional
step is available within the blueprint's own machinery. The remark should
note this: "The bridge from primitive transfer map to eventual block
injectivity is available via the Wielandt theory (Chapter 7), but is not
included in the normal-CF-BNT predicate itself."

### Section 10.2 — BNT permutation rigidity

**Theorem 10.7 (BNT permutation — proportional MPV case).**

⚠️ **The theorem is overloaded and unnecessarily opaque.** It packs the
following into a single statement:
- Two injective families with TP normalization
- Self-overlap → 1 and cross-overlap → 0 hypotheses
- Existence of total tensors A_tot, B_tot
- Coefficient arrays a_{N,j}, b_{N,k} with nonzero limits
- A proportionality sequence c_N with nonzero limit
- The MPV decomposition identities

Most of this is redundant with the canonical form structure. In the actual
setting of the theorem (two tensors in canonical form with BNT
separation), A_tot = ⊕_k μ_k A_k, the coefficients are a_{N,k} = μ_k^N,
and the MPV decomposition V^{(N)}(A_tot)_σ = ∑_k μ_k^N V^{(N)}(A_k)_σ
follows from Theorem 2.24. The way the theorem is stated, A_tot and the
coefficient arrays are introduced as arbitrary external objects with no
structural relationship to the block-diagonal assembly. This obscures the
natural origin of all these quantities from the direct sum decomposition.

A mathematician would state this as: "Let ⊕_j μ_j A_j and ⊕_k ν_k B_k
be two block-diagonal tensors in canonical form with BNT separation. If
they generate proportional MPV families, then the number of blocks is
equal and the blocks are related by a permutation and gauge-phase
equivalence."

All the TP normalization, self-overlap convergence, and coefficient data
are *part of the canonical form predicate* or consequences of the
block-diagonal structure — they do not need to be restated as separate
hypotheses. The current statement reads like a list of Lean type
signatures rather than a mathematical theorem.

This is a significant amount of input data. For a formalization blueprint,
it would be cleaner to factor the theorem into:
(a) A lemma extracting the limiting mixed-overlap matrix from the
    coefficient and overlap data.
(b) A lemma showing the limiting matrix has at most one nonzero entry
    per row/column (from the spectral gap).
(c) The permutation and gauge-phase equivalence conclusion.

The proof sketch is also somewhat compressed: "one extracts the limit of
each mixed overlap O_{A_j B_k}(N)" — but how? This requires expanding
V^{(N)}(A_tot)_σ = ∑_j a_{N,j} V^{(N)}(A_j)_σ and V^{(N)}(B_tot)_σ =
∑_k b_{N,k} V^{(N)}(B_k)_σ, forming the overlap
⟨V^{(N)}(A_tot)|V^{(N)}(B_tot)⟩, and using the decomposition plus
convergence of coefficients to extract the individual limits. This
intermediate step is nontrivial and should be sketched.

⚠️ **The hypotheses on A_tot and B_tot are unclear.** The theorem says
"Assume moreover that there exist MPS tensors A_tot and B_tot." But what
are A_tot and B_tot? Are they the block-diagonal assemblies ⊕_k μ_k A_k?
If so, the MPV decomposition V^{(N)}(A_tot)_σ = ∑_j a_{N,j} V^{(N)}(A_j)_σ
follows from Theorem 2.24, and the coefficient arrays are a_{N,j} = μ_j^N.
The way the theorem is stated, A_tot and the coefficient arrays are given
as arbitrary external data, which is more general than what the CF-BNT
setting provides. This generality is fine as a mathematical statement, but
the connection to the CF-BNT setting (where A_tot = ⊕_k μ_k A_k and
a_{N,j} = μ_j^N) should be made explicit, either in the theorem or in a
remark.

⚠️ **The variable name σ is overloaded.** In the theorem statement,
σ appears both as the spin configuration index (in V^{(N)}(A_j)_σ) and
as the permutation (σ ∈ S_g). This is a notational clash that should be
fixed — use π for the permutation, as Chapter 11 does.

**Theorem 10.8 (BNT permutation — overlap-orthonormal case).**
The statement is correct but the proof sketch is thin.

⚠️ **The hypothesis "span the same MPV subspace at every system size"
is ambiguous.** Does this mean span{V^{(N)}(A_j)} = span{V^{(N)}(B_k)}
for each fixed N? Or does it mean the *families* generate the same MPV
family (i.e., V^{(N)}(A_tot) = c_N V^{(N)}(B_tot) for some sequence
c_N)? These are different conditions. The former is what "span the same
MPV subspace" literally says; the latter is what Theorem 10.7 assumes.
For the overlap-orthonormal case the intended meaning should be clarified.

⚠️ **The proof says "The irreducible-TP variant uses the same matching
argument with the irreducible-TP overlap decay theorems in place of the
injective ones."** This is a forward reference to an unstated normal-
canonical companion theorem. Unlike §10.1 (where Definition 10.3 provides
the normal-canonical predicate) and Chapter 9 (where Theorem 9.14
provides the normal-canonical block separation), §10.2 does not have a
separate normal-canonical permutation theorem. The proof of Theorem 10.8
merely mentions an "irreducible-TP variant" in passing, without stating
it as a theorem. Either state the variant explicitly (as a Theorem 10.8a
or Remark), or remove the mention.

### Section 10.3 — Coefficient convergence

**Theorem 10.9 (Coefficient ratio decay).**
Correct and trivial. (μ_k/μ_0)^N → 0 follows from |μ_k/μ_0| < 1.

⚠️ **Not cited by any downstream theorem in v2.** In v1, this was used by
v1's Theorem 10.12 (proportional FT assembly): "Coefficient convergence
(Theorem 10.7) provides the convergent nonzero coefficients." In v2,
Theorems 11.1 and 11.2 take the coefficient arrays a_{N,j} and their
nonzero limits as *explicit input hypotheses* — the Chapter 11 preamble
says "The proportional-MPV theorems take explicit coefficient-convergence
input." The proofs of Theorems 11.1–11.2 never cite Theorem 10.9.

Theorem 10.9 is not useless — it would be needed to *instantiate* the
hypotheses of Theorem 11.1 in the specific case where A_tot = ⊕ μ_k A_k
and a_{N,k} = μ_k^N. But this instantiation step (deriving the coefficient
convergence from the canonical form weights) is not stated as a theorem
anywhere in v2. The gap should be closed: either Theorem 11.1 should
derive the coefficient convergence internally (citing Theorem 10.9), or
a separate "application lemma" should instantiate Theorem 11.1's
hypotheses from canonical form data.

⚠️ **The notation μ_0 for the dominant weight is introduced here without
warning.** Earlier in the blueprint, the weights are indexed μ_1, ..., μ_r
(Definition 9.8) or μ_k with k ranging over blocks. This theorem switches
to 0-indexed (μ_0 is the dominant block). The indexing convention should
be stated.

⚠️ **The hypothesis "under the canonical form predicate" is
underspecified.** Which canonical form predicate — Definition 9.8
(block-injective) or Definition 8.28 (normal-canonical)? The strict
ordering |μ_0| > |μ_1| > ... is part of Definition 9.8 (condition on
weights), but Definition 8.28 has a similar condition (strictly
decreasing moduli, per Theorem 8.34). The theorem should specify which
predicate is assumed.

**Remark 10.10 (Strict-dominance regime).**
Correct. Good honest statement about the scope limitation. The oscillatory
case ∑_q μ_{j,q}^N with |μ_{j,q}| = 1 arises from periodic eigenvalues
in blocks that have not been fully reduced to primitive form.

⚠️ **The notation μ_{j,q} appears without definition.** This is the
notation from [CPGSV21, Eq. (72a) / Eq. (74)], where each block j can
have multiple contributing weights μ_{j,q} (from the periodic
sub-structure before blocking). The blueprint uses this notation only in
this remark and does not define it. Either define it or give an explicit
cross-reference.

### Section 10.4 — Newton–Girard identities

**Theorem 10.11 (Newton–Girard trace recursion).**
Correct. Standard result.

⚠️ **The theorem is stated for matrices A, B ∈ M_n(ℂ), but the proof
invokes Newton–Girard identities by name without stating them.** For a
formalization blueprint, the Newton–Girard identities should be stated
explicitly, or a reference to Mathlib should be given. The identities
express the k-th elementary symmetric polynomial e_k(λ_1, ..., λ_n) in
terms of the power sums p_m = ∑ λ_i^m via the recursion
k · e_k = ∑_{i=1}^k (-1)^{i-1} e_{k-i} p_i. This is what enables the
passage from equal power sums to equal elementary symmetric polynomials,
hence equal characteristic polynomials.

**Theorem 10.12 (Equal power sums imply equal multisets).**
Correct. Clean reduction to Theorem 10.11 via diagonal matrices.

⚠️ **This theorem requires equal-sized multisets (both functions map from
{1, ..., n}).** If the two multisets have different cardinalities, the
statement fails. The theorem should note that |α| = |β| = n is part of
the hypothesis.

⚠️ **Usage: confirmed orphaned in v2.** In v1, Theorem 10.9 (= v2's
Theorem 10.12) was used in v1's Theorem 10.13 (equal-MPV FT) to pass
from equal power sums ∑_k (μ_k^A)^N = ∑_k (μ_k^B)^N to multiset equality
{μ_k^A} = {μ_k^B}. v1's Theorem 10.13 proof explicitly says: "By
Theorem 10.9, the multisets {μ_k^A} and {μ_k^B} agree."

In v2, the equal-MPV theorem (Theorem 11.3) takes a completely different
route: it assumes a *common block structure* (same r, same D_k, same μ_k)
from the start, then applies Theorem 9.15 (canonical-form FT,
same-structure version) directly. There is no need to deduce weight
multiset equality from power sums because the weights are assumed equal.

**Verified:** A search of the entire v2 blueprint confirms that Theorems
10.11 and 10.12 are never cited outside §10.4 itself (Theorem 10.12's
proof cites 10.11; no other theorem in the blueprint cites either).
These are genuinely orphaned statements in v2.

---

## 5. Cross-Chapter Consistency

### Chapter 2 dependencies

Definition 10.1 cites Definition 2.19 (normal tensor). ✔
v1 cited Definition 2.18; this reflects the v1 → v2 renumbering in
Chapter 2.

Theorem 10.5 cites Theorem 2.24 (MPV decomposition). ✔

### Chapter 6 dependencies

Theorem 10.4 cites Theorems 6.15 (rectangular spectral gap) and 6.17
(spectral gap for non-gauge-phase-equivalent blocks). These should be
verified against the v2 numbering in Chapter 6. The Chapter 6 review
confirms the spectral gap results are correctly stated in v2.

### Chapter 8 dependencies

Definition 10.3 extends Definition 8.28 (normal canonical form predicate). ✔
Remark 10.6 references Theorem 8.29 (self-overlap derived from
primitivity) and correctly notes the gap. ✔

### Chapter 9 dependencies

Definition 10.2 extends Definition 9.8 (canonical form predicate). ✔
Theorem 10.9 assumes "the canonical form predicate" — should specify
which one (9.8 or 8.28).

### Chapter 11 forward dependencies

Chapter 11 uses:
- Theorem 10.7 in Theorem 11.1 (proportional FT, injective route).
- Theorem 10.4 in Theorem 11.1 (off-diagonal decay).
- Remark 10.6 in Theorem 11.2 (explains why the NT route stops at
  separated form).
- Theorem 8.29 in Theorem 11.2 (self-overlap for normal-canonical route).
- Theorem 9.15 in Theorem 11.3 (equal-MPV FT).

**Not used by Chapter 11:**
- Theorem 10.9 (coefficient ratio decay): Theorems 11.1–11.2 take
  coefficient convergence as an explicit hypothesis rather than deriving
  it. See §4 discussion.
- Theorems 10.11–10.12 (Newton–Girard): confirmed orphaned. v1's
  equal-MPV theorem used these to deduce weight multiset equality from
  power sums; v2's Theorem 11.3 assumes common weights from the start
  and uses Theorem 9.15 instead. Neither theorem is cited anywhere
  outside §10.4 in the entire v2 blueprint.

### Two meanings of "normal"

See §2b above. This is a presentation issue, not a mathematical one: the
two definitions (Def 2.19 and Def 8.28) describe the same class of tensors.
The blueprint should state this equivalence once and prominently. Remark
10.6's "normality gap" is real in the narrow sense that the normal-CF-BNT
predicate does not *include* the algebraic characterization as a field, but
the equivalence means it can always be derived. The remark should say so.

### Definition 9.8 vs BNT separation

Definition 10.2 extends Definition 9.8 by adding the non-gauge-phase-
equivalence condition. This means Definition 10.2 is a *strict
extension* — every CF-BNT datum is a canonical form datum, but not
conversely. The relationship is correctly stated.

---

## 6. Literature Alignment

### [CPGSV21, Definition IV.2] vs Definition 10.1

The blueprint cites [CPGSV21, Definition IV.2] for Definition 10.1. The
paper's definition says:

> "A basis of normal tensors for A is a set of normal tensors A_j
> (j = 1, ..., g) such that (i) for each N, |V^{(N)}(A)⟩ can be written as
> a linear combination of V^{(N)}(A_j), and (ii) there is some N_0 such
> that, for all N > N_0, |V^{(N)}(A_j)⟩ are linearly independent."

The blueprint's Definition 10.1 tracks this closely, with one deviation:
the paper's coefficients are implicit ("can be written as a linear
combination"), while the blueprint writes explicit c_j that look
N-independent. As noted in §4, this is a notational issue.

### [CPGSV21, Proposition IV.3] — characterization of BNT

The paper's Proposition IV.3 gives an *if-and-only-if* characterization of
BNT: the A_j form a BNT for A if and only if every normal block in the
canonical form (70) is gauge-phase equivalent to exactly one A_j, and the
set is minimal. The blueprint does not include this characterization; it
instead defines the CF-BNT predicate (Definition 10.2) which builds BNT
separation directly into the canonical form. This is a different
packaging — the blueprint constructs the separation rather than
characterizing it post hoc. This is a reasonable choice for formalization,
but the blueprint should note the deviation.

### [CPGSV21, Theorem IV.4] vs Theorems 10.7 / 11.1

The paper's Theorem IV.4 (fundamental theorem for proportional MPVs) says:
if A and B are in canonical form with BNT A_{k_a} and B_{k_b}, and if
for all N the MPVs are proportional, then g_a = g_b and B_k is gauge-phase
equivalent to some A_{j_k}.

The blueprint splits this into Theorem 10.7 (the permutation rigidity step)
and Theorem 11.1 (the full assembly). The paper deduces the result from
the uniqueness of BNT decompositions; the blueprint deduces it from the
overlap matrix argument (spectral gap → at most one nonzero entry per
row/column → permutation). These are related but different proof
strategies.

### [PGVWC07, Theorem 4] vs the blueprint's canonical form

The paper's Theorem 4 uses the unital gauge (∑ A_i A_i† = 𝟙) and requires
the CP map E_j to have unique fixed point 𝟙. The blueprint's canonical form
uses the TP gauge (∑ (A^i)† A^i = 𝟙). This is the same normalization
convention deviation flagged in the Chapter 9 review. It propagates through
all overlap arguments.

### Newton–Girard

The Newton–Girard identities are standard number-theoretic/algebraic results.
In [PGVWC07], the passage from equal power sums to equal multisets is used
in the proof of the full uniqueness theorem. In v1 of the blueprint, these
were similarly used in v1's Theorem 10.13 (equal-MPV FT). In v2, Theorem
11.3 takes a different route (common-structure assumption + Theorem 9.15),
and a full search of the v2 blueprint confirms that Theorems 10.11–10.12
are never cited outside §10.4. They are orphaned.

---

## 7. Formalization Notes (Type-Level Transitions)

### 10-F1. BNT predicate as a dependent structure

The BNT predicate (Definition 10.1) packages: a number g of blocks, a
function k ↦ D_k of bond dimensions, a family of tensor functions
k ↦ A_k (each A_k : Fin d → Matrix (Fin (D k)) (Fin (D k)) ℂ), a
total tensor A_tot, a normality proof for each block, coefficient
functions a_{N,j}, and the spanning/independence conditions. In Lean,
this is a structure with dependent fields. The key Lean types:
- `g : ℕ`
- `D : Fin g → ℕ`
- `A : (k : Fin g) → Fin d → Matrix (Fin (D k)) (Fin (D k)) ℂ`
- `A_tot : Fin d → Matrix (Fin (∑ k, D k)) (Fin (∑ k, D k)) ℂ`

The dependent typing on D is the same issue as Definition 2.23 / 8.1
(see formalization notes 2-F3).

### 10-F2. Coefficient arrays: convergent sequences with nonzero limits

Theorem 10.7 assumes a_{N,j} → a_j^∞ ≠ 0. In Lean, this is a
`Filter.Tendsto` proof together with a `Ne` proof on the limit. The
coefficient array is not a plain sequence but a structured object. The
blueprint treats it as a plain sequence with a convergence hypothesis.

### 10-F3. Gram matrix invertibility from convergence

The proof of Theorem 10.5 uses "G(N) → I implies G(N) is eventually
invertible." In Lean, this requires a lemma: a matrix-valued sequence
converging to an invertible matrix is eventually invertible. This uses
the fact that `det` is continuous and det(I) = 1 ≠ 0, so det(G(N)) ≠ 0
for large N.

### 10-F4. Overlap vs inner product: the conjugation bridge

As noted in the Theorem 10.5 review, the Gram matrix uses the inner
product (sesquilinear), while the overlap O_{AB} is bilinear. The Lean
code must pass through Lemma 2.32 (or its equivalent) to convert.

### 10-F5. Newton–Girard as Mathlib dependency

The Newton–Girard identities may be available in Mathlib (or require
formalization). The blueprint should check and note the dependency status,
as was recommended for Burnside's theorem in Chapter 8 (cleanup item 10).
However, since these theorems are orphaned in v2 (see below), this is
low priority unless they are restored to the proof chain.

### 10-F6. Orphaned statements: a formalization-specific concern

A formalization blueprint has a problem that informal mathematics does
not: every statement that appears must be formalized, and every
formalized statement must either be used downstream or explicitly marked
as auxiliary/optional. Orphaned statements — theorems that are stated
and proved but never cited by any later result — create unnecessary
formalization work and obscure the dependency graph.

Chapter 10 has two classes of orphaned statements in v2:

**Fully orphaned (§10.4):** Theorems 10.11 (Newton–Girard trace
recursion) and 10.12 (equal power sums ⟹ equal multisets) are never
cited outside §10.4 in the entire v2 blueprint. They were used by v1's
Theorem 10.13 (equal-MPV FT), but v2's replacement (Theorem 11.3) uses
a different proof strategy that does not need them. Unless these are
restored to the proof chain (e.g., by adding a version of the equal-MPV
theorem that does not assume common weights), they should be either
removed or explicitly flagged as "available for future extensions, not
required for the current formalization target."

**Indirectly orphaned (§10.3):** Theorem 10.9 (coefficient ratio decay)
is not cited by any downstream theorem, but it *would be needed* to
instantiate the hypotheses of Theorem 11.1 in the concrete canonical
form setting. The gap is that no "application lemma" connects the
abstract Theorem 11.1 (which takes coefficient convergence as input) to
the specific case A_tot = ⊕ μ_k A_k, a_{N,k} = μ_k^N. Adding this
lemma would close the gap and make Theorem 10.9 non-orphaned.

**General recommendation for the blueprint:** Each chapter should include
a dependency summary listing which of its results are used downstream
and where. This is especially important for a formalization project,
where the dependency graph determines the build order and where
orphaned statements represent wasted effort. The `formalization_notes_
type_transitions.md` file already tracks type-level transitions; it
should be extended to track the usage graph as well.

---

## 8. AI-Style Language Issues

The chapter is cleaner than v1 (which used `IsCanonicalFormBNT`), but a
number of AI-generated patterns remain. This chapter is probably the one
where the AI voice is most noticeable in the blueprint, likely because
the content is relatively straightforward and the AI compensated by adding
formality and jargon where a human would write plainly.

### Naming and terminology

- **"Basis Normal Tensor (BNT)"** — should be "basis of normal tensors
  (BNT)." See §2a above. This is the most consequential naming error in
  the chapter.

- **"CF-BNT predicate"** — used as a noun throughout ("satisfies the
  CF-BNT predicate"). A mathematician would say "is in canonical form
  with distinct blocks" or "satisfies the hypotheses of Definition 10.2."
  The compound abbreviation reads like an API name.

- **"normal-CF-BNT data"** (Remark 10.6) — triple-abbreviated compound
  noun. Unreadable. Write "data satisfying Definition 10.3" or "normal-
  canonical-form data with BNT separation."

- **"overlap-orthonormal case"** (Theorem 10.8 title) — a mathematician
  would say "with asymptotically orthonormal overlaps" or simply
  "with overlap decay hypotheses." The compound adjective is not
  something one would find in a paper.

### Theorem statement style

- **Theorem 10.7** reads like a specification rather than a theorem. The
  hypotheses are listed in a single run-on sentence with inline formulas
  for the TP conditions. A mathematician would state the theorem as:
  "Let ⊕_j μ_j A_j and ⊕_k ν_k B_k be two block-diagonal tensors in
  canonical form with BNT separation. If they generate proportional MPV
  families, then g_A = g_B and the blocks are related by a permutation
  and gauge-phase equivalence."
  The explicit TP normalization, self-overlap convergence, and coefficient
  convergence are all *consequences* of the canonical form predicate and
  the block-diagonal structure — they do not need to be restated as
  hypotheses. See comment 3 in the user's feedback and §4 below.

- **Theorem 10.8** similarly restates hypotheses that could be absorbed
  into a reference to the canonical form predicate.

### Prose

- "The coefficient-convergence and Newton–Girard auxiliary results are
  also collected here" (chapter preamble) — "collected here" is
  organizational language. A mathematician would say "This chapter also
  contains..." or simply list the results.

- "The overlap-orthonormal hypotheses are assumed directly, rather than
  derived from proportional MPVs together with coefficient convergence"
  (Theorem 10.8 proof) — this meta-commentary about proof organization
  is unusual in mathematical writing. State the proof, not a commentary
  on how the proof differs from a related theorem.

- "The irreducible-TP variant uses the same matching argument with the
  irreducible-TP overlap decay theorems in place of the injective ones"
  (Theorem 10.8 proof) — a road-map sentence in place of an actual
  proof sketch. Either state the variant as a theorem or omit the
  sentence.

---

## 9. Cleanup Checklist

0. **Fix naming throughout: "basis of normal tensors," not "basis normal
   tensor."** The chapter title, Definition 10.1, and all uses of "BNT"
   as a standalone noun should be corrected. See §2a.

0a. **Add a prominent "equivalence of normality" remark** somewhere early
    in the blueprint (near Def 2.19 or at the start of Chapter 7/8)
    stating that the algebraic characterization (eventual full Kraus rank)
    and the spectral characterization (primitive transfer operator) are
    equivalent by [SPGWC10, Proposition 3]. All subsequent uses of
    "normal" should reference this remark. See §2b.

1. **Fix Definition 10.1 coefficient notation.** The coefficients c_j
   should either be written as a_{N,j} (N-dependent) or the condition
   should be rephrased as "lies in the span of" without naming the
   coefficients. Currently the notation suggests N-independence.

2. **Clarify Theorem 10.4 proof.** Note that the spectral gap theorems
   require TP normalization, which is supplied by the CF-BNT predicate.
   Verify the Theorem 6.15 citation against v2 numbering.

3. **Fix the overlap/inner-product conflation in Theorem 10.5.** Note that
   the Gram matrix G_{jk} = ⟨V(A_j)|V(A_k)⟩ involves the inner product,
   not the bilinear overlap O_{A_j A_k}, and that the conversion uses
   Lemma 2.32.

4. **Expand Remark 10.6.** Note that the normality gap is closable via
   the Wielandt theory (Chapter 7), even though it is not included in the
   normal-CF-BNT predicate itself.

5. **Fix the σ overload in Theorem 10.7.** Use π (or another symbol) for
   the permutation, not σ, which is already the spin configuration index.
   Chapter 11 uses π — be consistent.

6. **Rewrite Theorem 10.7 in terms of canonical form data.** State it
   as: "Let ⊕ μ_j A_j and ⊕ ν_k B_k be two block-diagonal tensors in
   canonical form with BNT separation. If they generate proportional MPV
   families, then..." All TP, overlap, and coefficient hypotheses follow
   from the canonical form predicate + block-diagonal structure and should
   not be restated. The current statement reads like a type signature
   rather than a theorem. See §4 and §8.

7. **If Theorem 10.7 is kept in its current general form,** at minimum add
   a remark connecting the abstract hypotheses to the CF-BNT setting:
   A_tot = ⊕_k μ_k A_k, a_{N,j} = μ_j^N, etc.

8. **Clarify the MPV-subspace hypothesis of Theorem 10.8.** Is it
   span-equality at each N, or proportional families?

9. **State or remove the "irreducible-TP variant" in Theorem 10.8's proof.**
   Either give it as a separate theorem (paralleling the two-route
   structure) or delete the sentence.

10. **Specify which canonical form predicate in Theorem 10.9.** Definition
    9.8 or 8.28?

11. **Define μ_{j,q} in Remark 10.10** or give an explicit cross-reference
    to [CPGSV21, Eq. (72a)].

12. **State the Newton–Girard recursion explicitly** in or before
    Theorem 10.11, for formalization purposes.

13. **Theorems 10.11–10.12 are confirmed orphaned in v2.** They were used
    by v1's Theorem 10.13 (equal-MPV FT via power-sum argument), but v2's
    Theorem 11.3 takes a different route (common-structure assumption +
    Theorem 9.15). Either: (a) note explicitly that these are auxiliary
    results retained for potential future use, (b) restore a version of the
    equal-MPV theorem that uses them (e.g., a variant of Theorem 11.3 that
    does *not* assume common weights), or (c) remove them.

13a. **Theorem 10.9 is not cited by any downstream theorem.** Theorems
     11.1–11.2 take coefficient convergence as explicit input. Add an
     "application lemma" that instantiates Theorem 11.1's hypotheses from
     canonical form data (A_tot = ⊕ μ_k A_k, a_{N,k} = μ_k^N, convergence
     via Theorem 10.9). Without this, there is a gap between the abstract
     Theorem 11.1 and its intended use case.

14. **Note Theorem 10.12's equal-cardinality hypothesis.** The multisets
    must have the same size n.

15. **Note the deviation from [CPGSV21, Proposition IV.3]** — the blueprint
    builds BNT separation into the canonical form predicate rather than
    characterizing BNT post hoc.

16. **Rewrite AI-generated phrasing.** In particular: replace "CF-BNT
    predicate" with standard mathematical language, rewrite theorem
    statements as theorems (not specification lists), remove meta-
    commentary from proof sketches ("the hypotheses are assumed directly
    rather than derived from..."). See §8 for the full list.

---

## 10. Final Assessment

Chapter 10 is mathematically sound in its theorem statements. The most
important v1 → v2 changes are the chapter split (separating BNT theory
from full assembly), the cross-overlap decay proof correction (v1 falsely
claimed the overlap is zero for different bond dimensions; v2 correctly
uses the rectangular spectral gap), and the addition of Definition 10.3
and Remark 10.6 (normal-canonical companion and the normality gap).

The main issues are:

**Naming:** "Basis Normal Tensor" should be "basis of normal tensors"
throughout; the chapter title should be corrected.

**Conceptual:** The blueprint still presents two characterizations of
normality without stating their equivalence prominently. This is a
cross-chapter issue originating in Chapter 2 that surfaces here via
Remark 10.6. There is one notion of normal tensor with two equivalent
characterizations (algebraic and spectral), and the blueprint should
say so once and clearly.

**Notational:** Definition 10.1's N-independent coefficients c_j (should be
a_{N,j}); the σ overload in Theorem 10.7; the undefined μ_{j,q} in
Remark 10.10.

**Structural:** Theorem 10.7 is overloaded with hypotheses that are
redundant with the canonical form predicate, and its use of an abstract
A_tot obscures the natural block-diagonal origin of the data. The
Newton–Girard section (§10.4) may be orphaned in v2.

**AI-generated style:** The chapter reads more like a specification than a
mathematical document in several places. Theorem statements list type
signatures rather than stating results; proof sketches contain meta-
commentary about proof organization; compound abbreviations ("CF-BNT
predicate," "normal-CF-BNT data") substitute for standard mathematical
language. This is probably the chapter where the AI voice is most
noticeable.

**Formalization:** The overlap/inner-product distinction in Theorem 10.5;
the Gram matrix invertibility lemma; the coefficient convergence as a Lean
structured type.

None of these issues are mathematically critical — they are all
presentation-level problems appropriate for a next revision of the
blueprint. The chapter correctly provides the permutation rigidity
machinery needed for Chapter 11's assembly.
