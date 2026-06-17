
# Blueprint Chapters 2–6: Consolidated Review

This document merges the v1→v2 comparison and the residual-issues list for
Chapters 2–6 into a single reference. For each chapter:

- **Corrected in v2** records what was fixed from v1.
- **Verified correct** records items that were explicitly checked and confirmed.
- **Remaining open** records items still needing attention, with severity and
  (where applicable) a recommendation.

Items marked "acceptable for formalization" are kept for the record but need no
action.

---

## Chapter 2: Matrix Product Vectors

### Corrected in v2

1. **V^{(N)}(A)_σ explicitly defined.** Definition 2.4 now writes both the ket
   form and the coefficient function V^{(N)}(A)_σ := tr(A_{i₁}⋯A_{i_N}).

2. **MPV terminology consistent.** Chapter renamed to "Matrix Product Vectors."
   Definition 2.1 is still "MPS tensor" (standard name for the tensor), but
   everything else uses MPV consistently.

3. **Lemma 2.3 proof simplified.** Now reads "Immediate from the definition of
   A_w."

4. **Canonical form properly labeled.** Renamed to "Block-injective canonical
   form" (Def 2.21) with Remark 2.22 explicitly distinguishing it from the
   NT-block form of [CPGSV21].

5. **Normal tensor bridge acknowledged.** Remark 2.20 states: "The NT notion in
   [CPGSV21] is spectral... The bridge to that viewpoint is supplied later by
   Theorem 8.26, Theorem 7.45, and Theorem 7.52."

6. **Transfer map positivity deferred.** v1's Lemma 2.7 demoted to Remark 2.6
   with forward reference to Chapter 4.

7. **Block-index notation improved.** Uses multi-index tuples (i₁,...,i_L)
   instead of flattened integers (Def 2.25).

8. **Overlap section cleaned up.** §2.6 now cleanly separates inner product
   (Def 2.30), bilinear overlap (Def 2.31), and their relation (Lemma 2.32).

9. **New content added.** Def 2.11 (proportional MPV), Lemma 2.12 (word
   evaluation under scaling), Remark 2.14, Lemma 2.15, Theorem 2.16 (gauge
   invariance), Theorem 2.24 (MPV decomposition), Theorem 2.28 (blocking
   preserves same MPV).

10. **v1 micro-lemma issue resolved.** v1's Lemma 2.24/2.25 (blocking preserves
    word evaluation) restructured into Lemma 2.26 + Lemma 2.27, folding the
    trivial step into the proof.

### Verified correct

- **Overlap conjugation conventions (2-D).** Verified against PDF images.
  Definition 2.30 (inner product) has the conjugation bar on the first argument,
  consistent with conjugate-linearity in the first argument. Definition 2.31
  (overlap) has the bar on the second argument, making it bilinear. Lemma 2.32
  correctly relates them via complex conjugation.

### Remaining open

**2-A. c_w(A) notation possibly unused.** Definition 2.4 introduces
c_w(A) := tr(A_w). Chapter 3 (Lemma 3.2 proof) references c_w, but it is
unclear whether any chapter beyond Chapter 3 uses it rather than writing tr(A_w)
directly. If used only once, consider dropping it.
— *Minor (stylistic).*

**2-B. Definitions 2.8/2.9 still split.** Same MPV for equal vs different bond
dimensions remain separate definitions. Remark 2.10 justifies the split.
Conceptually one notion, but acceptable given the justification.
— *Minor (structural). Acceptable for formalization.*

**2-C. Definition 2.23 vs Definition 2.21.** Def 2.23 (block-diagonal tensor
from blocks) constructs the same object as Def 2.21 (block-injective canonical
form data). Distinction is data package vs constructor — acceptable for Lean, but
mathematically overlapping. See also cross-chapter item X-2.
— *Minor (structural redundancy). Acceptable for formalization.*

---

## Chapter 3: Single-Block Fundamental Theorem

### Corrected in v2

1. **Redundant Lemma 3.3 removed.** The length-2 trace identity (special case
   of Lemma 3.2) is gone.

2. **Trace-pairing maps labeled as auxiliary.** Chapter preamble: "The
   trace-pairing maps introduced below are auxiliary devices attached to the
   chosen generating families."

3. **Generic linear-algebra lemma merged.** v1's Lemma 3.6 (range inclusion →
   injectivity) absorbed into the proof of Theorem 3.6 via inline rank-nullity.

4. **Nonvanishing trace proof improved.** Theorem 3.5 proof now direct: tr(A_w)
   = 0 for all w, {A_i} span M_D, so trace vanishes on M_D, contradicting
   tr(𝟙) = D ≠ 0.

5. **"Nonzero" made explicit.** Theorem 3.8 now reads "A nonzero multiplicative
   ℂ-linear endomorphism of M_D(ℂ) is bijective."

### Verified correct

- **Theorem 3.6 proof: range inclusion direction (3-C).** The proof argues
  range(Φ_A) ⊆ range(Φ_B). Verified: since ℓ_A is surjective (by injectivity
  of A), the chain range(Φ_B) ⊇ range(Φ_B ∘ ℓ_B) = range(Φ_A ∘ ℓ_A) =
  range(Φ_A) holds.

- **Section 3.4 still separate (3-B).** Remains separate from §3.3, but
  consists of a single clean theorem (Theorem 3.11) with a concise proof. Fine
  for a blueprint — having the final assembly as a named theorem is useful for
  formalization.

### Remaining open

**3-A. Theorem 3.5 still a standalone theorem.** The review recommended demoting
the nonvanishing-trace result to a remark. v2 keeps it as a numbered theorem.
For Lean this is acceptable (named lemma used in the assembly proof of
Theorem 3.11), but stylistically over-promoted.
— *Minor (stylistic). Acceptable for formalization.*

---

## Chapter 4: Quantum Channels and Positive Maps

### Corrected in v2

1. **Loewner order introduced.** Remark 4.2 explicitly states "X ≤ Y means
   Y − X ≥ 0."

2. **CP definition order justified.** Kraus-first retained with justification
   ("matches later KS arguments") and Choi equivalence cited.

3. **Kraus map duplication resolved.** Def 4.12 clarifies: "A linear map is
   completely positive (Definition 4.4) if and only if it can be written in
   this form."

4. **[CRITICAL] Theorem 4.37 replaced.** The incorrectly stated "peripheral
   eigenvalues are roots of unity" (missing closure hypothesis) replaced by:
   - Theorem 4.38: power-stable peripheral eigenvalues are roots of unity.
   - Theorem 4.39: closure under powers implies roots of unity.

5. **Redundant theorem demoted.** Theorem 4.35 ("peripheral eigenvalues lie on
   unit circle" — just restates definition) → Remark 4.36.

6. **[CRITICAL] Adjoint-fixed-point route added.** New §4.7.2:
   - Lemma 4.44: peripheral closure via adjoint fixed point.
   - Theorem 4.45: roots of unity via adjoint fixed point.
   This is the general replacement for the DS gauge route. Matches [CPGSV17,
   Appendix A].

7. **DS gauge explicitly flagged.** Remark after Lemma 4.42: "one should not
   expect a single gauge choice to make it both unital and trace-preserving."
   Remark 4.43 labels bi-canonical case as special.

8. **Notation error fixed.** ‖μ‖ for |μ| in v1's Def 4.32 corrected.

9. **Hilbert-Schmidt contraction added.** Theorem 4.18 (HS contraction for
   doubly stochastic maps) now present.

10. **Gauge language in Kraus definitions.** Definitions 4.14 and 4.15 now
    explicitly connect to "right-canonical" and "left-canonical" gauge language
    used in Chapter 5.

### Verified correct

- **CP maps defined via Kraus form (4-A).** v2 keeps the Kraus-first order with
  explicit justification and Choi equivalence cited. Justified deviation from the
  review recommendation to use tensor positivity first.

- **Adjoint Kraus map definition (4-E).** Definition 4.13 correctly identifies
  the adjoint transfer map as the transfer map of the conjugate-transposed family
  i ↦ (A_i)†. Verified: E*(X) = Σ (A_i)† X A_i matches the transfer map of the
  family i ↦ (A_i)†.

### Remaining open

**4-B. Theorem 4.5 (CP maps are positive) still a theorem.** Review recommended
downgrading to a remark. Acceptable for Lean (named lemma).
— *Minor (stylistic). Acceptable for formalization.*

**4-C. Density matrix properties still fragmented.** Theorems 4.8–4.10 (compact,
convex, nonempty) remain separate. A textbook would state these as a single
proposition. Acceptable for Lean (separate named lemmas).
— *Minor (stylistic). Acceptable for formalization.*

**4-D. Theorem 4.22 terminology.** Called "One-sided multiplicative-domain
identity," but the standard multiplicative-domain theorem gives both left- and
right-multiplicative relations. The blueprint proves only the one-sided version.
**Recommendation:** Rename to "Left multiplicative identity from KS equality."
— *Minor (terminology).*

**4-F. Lemma 4.44 proof: "weighted Kadison–Schwarz equality."** The phrase is
nonstandard. The actual argument is: G = E(X†X) − E(X)†E(X) ≥ 0 (by KS), then
tr(ρG) = 0 (using E*(ρ) = ρ and |μ| = 1), so ρ > 0 and G ≥ 0 forces G = 0.
Clearer phrasing: "the trace of the KS gap against the adjoint fixed point
vanishes."
— *Minor (clarity).*

---

## Chapter 5: Perron–Frobenius Theory

### Corrected in v2

1. **Uniqueness scalar clarified.** Remark 5.6 explicitly notes c₀ > 0 (real
   positive).

2. **Existence doesn't need injectivity.** Theorem 5.8: "injectivity is not
   needed for this step."

3. **D = 0 case removed.** v1's Theorem 5.6 (formalization artifact) gone.

4. **Theorem ordering justified.** v2 keeps the injective version first
   (Theorem 5.2) with Remark 5.1 justifying this: the injective-tensor proof
   uses a shorter direct kernel argument, so it comes first as a warm-up.

5. **[CRITICAL] DS gauge section renamed.** "Doubly stochastic gauge" →
   "Right- and left-canonical gauges" (§5.4).

6. **[CRITICAL] Remark 5.12 added.** "The right-canonical gauge... and the
   left-canonical gauge... are generally different similarity transforms... This
   section does not claim that a single gauge makes the transfer map
   simultaneously unital and trace-preserving."

7. **Substantial new content.** Theorem 5.4 (orthogonal trace condition),
   Theorem 5.7 (uniqueness of positive eigenvalue), §5.5 (similarity preserves
   irreducibility, Lemma 5.13 + Theorem 5.14), §5.6 (PF eigenvector existence,
   Theorems 5.15–5.18 including TP-gauge existence for irreducible tensors).

8. **Wolf references now explicit.** Theorem 5.2 → [Wol12, Thm 6.3, item 2];
   Theorem 5.3 → [Wol12, Thm 6.2, condition (1)]; Remark 5.1 explains the
   ordering choice.

### Verified correct

- **Theorem 5.7 (new result in v2) (5-B).** Uniqueness of positive eigenvalue
  for irreducible CP maps. Statement and proof are correct: the dual-map trace
  argument is standard ([Wol12, Thm 6.3, item 3]).

### Remaining open

**5-A. Theorem 5.5: scalar c stated as c ∈ ℂ.** The statement says
"σ = cρ for some c ∈ ℂ." Remark 5.6 clarifies that c = c₀ > 0. The theorem
statement could be tightened to c ∈ ℝ_{>0}, but the remark handles it.
— *Minor (the remark handles it).*

**5-C. Theorem 5.17 proof: irreducibility transfer to adjoint.** The proof says
"irreducibility of A transfers to the adjoint transfer map." Correct but
compressed. The argument: if ℰ†_A has an invariant projection P, taking the
adjoint gives (𝟙−P) invariant for ℰ_A; irreducibility forces P ∈ {𝟙, 0}. For
Lean, this step may need to be a separate lemma.
— *Minor (compressed proof step; may need explicit lemma for Lean).*

---

## Chapter 6: Spectral Gap and Block Separation

### Corrected in v2

1. **[CRITICAL] Theorem 6.12 proof rewritten.** The most serious issue in the
   entire blueprint (unsafe DS normalization) is fixed. The proof now gauges A
   and B separately to unital Kraus families via their individual PF fixed
   points. Key sentence: "The crucial point is that one gauges the individual
   transfer maps to unital form; one does not require the mixed transfer map
   itself to be simultaneously unital and trace-preserving."

2. **Vacuous theorem removed.** v1's Theorem 6.20 (hypothesis tr(F^N(I)) = 0
   for all N, impossible for D ≥ 1) gone.

3. **Trivial theorems demoted.** Theorems 6.18, 6.19 → Remarks 6.18, 6.19.
   Theorem 6.3 (self-transfer identity) → Remark 6.3.

4. **Rectangular spectral gap expanded.** Theorem 6.14 proof now explains the
   ker(X) argument and dimension contradiction.

5. **Trace notation disambiguated.** Theorem 6.5 includes explicit note: "This
   is the matrix trace... should not be confused with the operator trace
   Tr(F^N), which equals the MPV overlap."

6. **Theorem 6.10 proof rewritten.** Uses Cauchy–Schwarz + TP normalization
   directly, no DS gauge.

7. **Normalization scope stated.** Chapter preamble: "The algebraic
   mixed-transfer identities in the first two sections do not use normalization.
   Starting with the spectral-radius estimates, we assume the trace-preserving
   normalization."

8. **Spectral-gap theorems rewritten.** Theorems 6.20/6.21 (renumbered) use
   explicit hypothesis ρ_spec(ℰ_A − P) < 1.

### Verified correct

- **Theorem 6.20/6.21: trace notation (6-D).** Ambiguity between operator trace
  and matrix trace resolved in v2 via Theorem 6.5's explicit disambiguation. The
  remaining uses in §6.7 are consistent.

### Remaining open

**6-A. Definitions 6.1/6.2 still separate.** Square and rectangular mixed
transfer operator definitions remain separate. Acceptable for formalization
(different type signatures in Lean), though the rectangular definition subsumes
the square one.
— *Minor. Acceptable for formalization.*

**6-B. Theorem 6.12 proof: block-embedding KS argument still compressed.** For
Lean, the following intermediate steps should ideally be separate lemmas:
(1) construction of the block Kraus family from A'_i and B'_i;
(2) gauging of the eigenvector X accordingly;
(3) the KS equality for the block family applied to the off-diagonal embedding;
(4) extraction of the intertwining identity from the Kraus commutation relation;
(5) invertibility of the intertwiner from injectivity.
— *Moderate (formalization readiness).*

**6-C. Theorem 6.14 proof: rectangular case still somewhat compressed.** The
proof says "apply the same block-embedding Kadison–Schwarz argument as in the
square case." Since the rectangular case is not standard, the adaptation deserves
more detail. In particular, the step showing that a modulus-one eigenvector
X : M_{D_1 × D_2}(ℂ) must be injective (as a linear map ℂ^{D_2} → ℂ^{D_1})
should be more explicit.
— *Moderate (non-standard argument needs expansion).*

---

## Cross-Chapter Issues

### Resolved in v2

- **DS gauge misconception.** The most critical cross-chapter issue. v1 allowed
  the false impression that a single similarity transform could make the transfer
  map both unital and trace-preserving. v2 eliminates this throughout Chapters
  4–8 via the adjoint-fixed-point route (Ch4 §4.7.2), separate right/left
  canonical gauges (Ch5 §5.4, Remark 5.12), and separate gauging in the
  spectral-gap proof (Ch6 Theorem 6.12).

- **MPV coefficient notation.** Now explicit everywhere.

- **Overlap conjugation conventions.** Verified correct against PDF images.

- **X-4. Chapter 9 canonical form predicate: DS gauge residue.** Definition 9.8
  was corrected from "DS gauge" to "TP normalization" in v2. Confirmed in the
  Chapter 9 review.

### Remaining open (presentation, not mathematical)

**X-1. Two characterizations of "normal."** Def 2.19 (algebraic: S_{L₀} = M_D)
and Def 8.28 (spectral: irreducible + primitive transfer map) are **equivalent**
by [SPGWC10, Proposition 3]. The blueprint's eventual full Kraus rank definition
is provably equivalent to the paper's primitivity notion via the Wielandt paper.
This is a presentation issue, not a mathematical discrepancy (confirmed in the
Wielandt comparison). The blueprint should add a prominent remark noting the
equivalence.
**Recommendation:** Rename Def 2.19 to "eventually injective tensor" or similar,
reserving "normal" for the [CPGSV17] sense.
— *Moderate (terminology confusion across chapters).*

**X-2. Definition 8.1 duplicates Definition 2.23.** Both define the
block-diagonal tensor ⊕_k μ_k A_k. Definition 8.1 should be a cross-reference
to 2.23.
— *Minor (redundancy).*

**X-3. Definition 8.14 duplicates Definition 4.23.** Definition 8.14
(irreducible tensor) restates Definition 4.23 (irreducible map) specialized to
transfer maps. Should be phrased as a cross-reference.
— *Minor (redundancy).*

---

## Summary

| Category | Count |
|---|---|
| Verified correct (no action needed) | 7 |
| Minor stylistic / structural | 9 |
| Moderate (needs expansion or rename) | 3 |
| Major mathematical errors | 0 |

No mathematical errors remain in Chapters 2–6 of v2. The remaining issues are
structural (definition duplication, compressed proofs) and terminological (the
two meanings of "normal," the multiplicative-domain naming). The most actionable
items are:

1. The "normal" terminology disambiguation (X-1).
2. Expanding the block-embedding KS argument in Theorem 6.12 (6-B).
3. Expanding the rectangular spectral gap proof in Theorem 6.14 (6-C).
