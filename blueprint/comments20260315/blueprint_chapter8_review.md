
# Blueprint Review — Chapter 8 (Canonical Form Reduction)

## 1. Role of Chapter 8 in the Blueprint

Chapter 8 is the structural heart of the blueprint. It reduces a general MPS tensor to block-diagonal form via iterated invariant-subspace decomposition, establishes the Burnside bridge between irreducibility and matrix algebra spanning, and packages the results into two parallel routes: the **block-injective canonical form** (Definition 2.21) and the **normal canonical form** (Definition 8.28). The chapter draws on results from Chapters 2–7 and feeds into Chapters 9–11.

---

## 2. Global Assessment

| Aspect | Evaluation |
|---|---|
| Mathematical correctness | Mostly correct |
| Conceptual clarity | Good; two-route structure is explicit |
| Structural quality | Good, significantly improved from v1 |
| Cross-chapter consistency | One inherited issue (see §8.6), one definition duplication |
| Literature alignment | Good; references [PGVWC07], [CPGSV21], [Wol12] tracked |
| Open directions | Honestly stated (Remark 8.35) |

The chapter is substantially improved from v1. The most important change is that v1's Chapter 8 had a Remark 8.31 explicitly listing missing steps including a reliance on the DS gauge for Theorem 8.26. In v2, Theorem 8.26 has been rewritten to use the adjoint-fixed-point route, closing that gap. However, a few issues remain.

---

## 3. Statement-by-Statement Review

### Section 8.1 — Block-diagonal assembly

**Definition 8.1 (Block-diagonal tensor from blocks).**
Correct. Duplicates Definition 2.23 in Chapter 2. See cross-chapter note below.

**Theorem 8.2 (Per-block single-block FT).**
Correct. Direct application of Theorem 3.11. No issues.

**Theorem 8.3 (Per-block same MPV implies global same MPV).**
Correct. Uses Theorem 2.24 (MPV decomposition). Clean.

**Theorem 8.4 (Global gauge from block gauge).**
Correct. Standard block-diagonal conjugation.

### Section 8.2 — Transfer map normalization

**Theorem 8.5 (Scaling preserves injectivity).**
Correct but trivial. Could be a remark.

**Theorem 8.6 (Transfer map under scaling).**
Correct. ℰ_{ζA}(X) = |ζ|² ℰ_A(X). Standard.

**Theorem 8.7 (Phase-scaling preserves normalization).**
Correct.

**Theorem 8.8 (MPV under block normalization).**
⚠️ The statement is slightly confusing. It says "the MPVs of ⊕_k μ_k A_k and ⊕_k |μ_k| · (μ_k/|μ_k|) A_k agree." But these are the same object — writing μ_k = |μ_k| · (μ_k/|μ_k|) is just the polar decomposition of μ_k. As stated, this is a tautology.

What the theorem presumably intends to say is something about separating the modulus scaling from the phase, showing that the MPV depends on μ_k^N = |μ_k|^N · (μ_k/|μ_k|)^N in a specific way. But as written it's just restating the identity μ_k = |μ_k| · (μ_k/|μ_k|).

**Recommendation:** Clarify what this theorem actually establishes. If the point is that the modulus |μ_k| only appears through |μ_k|^N while the phase (μ_k/|μ_k|) can be absorbed into a phase-equivalent tensor, state that explicitly.

### Section 8.3 — Invariant subspace decomposition

**Theorem 8.9 (Unitary conjugation preserves MPV family).**
Correct. Special case of Theorem 2.16 (gauge invariance), since unitary matrices are invertible. Slightly redundant.

**Definition 8.10 (Support projection).**
Correct. Standard spectral construction.

**Definition 8.11 (Invariant projection predicate).**
Correct. States (𝟙 − P)A_i P = 0 for all i.

**Theorem 8.12 (PSD fixed point gives invariant projection).**
Correct. This is the finite-dimensional version of [Wol12, Prop. 6.10]. The proof sketch is adequate. The reference to [CPGSV21, §IV.A.1] is appropriate.

**Theorem 8.13 (Two-block decomposition).**
✔ Correct. The key structural step.

⚠️ However, the claim "the diagonal blocks generate the same MPV as A" needs more care. What's actually true is that the MPV of the upper-triangular form equals the sum of the block MPVs (the off-diagonal blocks drop out in the trace). The phrasing "generate the same MPV" could be read as saying each individual block generates the same MPV as A, which is false.

**Recommendation:** Restate as: "the block-diagonal tensor obtained by discarding the off-diagonal blocks generates the same MPV family as A."

### Section 8.4 — Iterated reduction

**Definition 8.14 (Irreducible tensor).**
Correct. Matches Definition 4.23 specialized to the transfer map.

⚠️ This is a **re-definition** of the irreducible-tensor concept. Chapter 4 already has Definition 4.23 (irreducible map) and Theorem 4.24 (injectivity implies irreducibility). Definition 8.14 simply restates 4.23 in tensor language. This is not wrong but should be flagged as a cross-reference rather than a new definition.

**Theorem 8.15 (Irreducible block decomposition).**
Correct. The strong induction on D is the right approach. The proof sketch correctly identifies the Cesàro argument as producing a PSD fixed point that fails to be PD when the tensor is reducible.

⚠️ One subtlety: the proof says "the transfer map has a PSD fixed point that is not PD (by the Cesàro argument)." But the Cesàro argument (Theorem 4.30) requires the transfer map to be a channel, i.e. trace-preserving. The theorem doesn't assume TP normalization. This is fine if one first obtains any PSD fixed point (which exists since every CP map on a finite-dimensional space has a positive eigenvector — Theorem 5.15), but the Cesàro route specifically requires the channel property. Either assume TP normalization or cite Theorem 5.15 instead.

**Theorem 8.16 (Unitary diagonal PD fixed point in TP gauge).**
Correct. Combines irreducibility → PD fixed point → spectral theorem diagonalization.

### Section 8.4.1 — Burnside bridge

**Definitions 8.17–8.19.** All correct. algSpan, invariant submodule, and irreducible action are standard.

**Theorem 8.20 (Irreducible tensor implies irreducible action).**
Correct. The argument via orthogonal projection is standard.

⚠️ Note that the converse is also true in finite dimensions (if the action on ℂ^D is irreducible, then there's no nontrivial invariant projection for the transfer map). The blueprint only states one direction. For completeness the converse could be noted, though it's not needed for later arguments.

**Theorem 8.21 (Burnside's theorem).**
Correct. This is the complex finite-dimensional Burnside theorem / Jacobson density theorem. The proof reference to [Jac09] is appropriate.

⚠️ For a Lean formalization, this is a significant external dependency. Burnside's theorem is a nontrivial algebraic result. The blueprint should note whether this will be formalized directly or imported from a library.

**Theorem 8.22 (Irreducible action implies eventual cumulative spanning).**
Correct. Uses ascending chain condition on finite-dimensional subspaces.

### Section 8.5 — Proportional single-block theorem

**Theorem 8.23 (Proportional MPV implies gauge-phase equivalence).**
Correct. The contradiction argument is clean: if not gauge-phase equivalent, overlap decay kills O_{AB}(N) → 0, but proportionality and self-overlap O_{AA}(N) → 1 force a contradiction.

⚠️ **Missing assumption check.** The theorem assumes O_{AA}(N) → 1 and O_{BB}(N) → 1. These are not derived here — they must come from primitivity of the individual transfer maps (supplied later by Theorem 8.24/8.29). The theorem statement is honest about this (it includes the overlap convergence as a hypothesis), but it would be helpful to add a forward reference noting where these hypotheses are discharged.

### Section 8.6 — Canonical form from peripheral primitivity

**Theorem 8.24 (Canonical form from peripheral primitivity).**
Correct. The key observation is that peripheral-spectrum primitivity implies the spectral-gap condition, which then implies self-overlap convergence.

⚠️ The proof says "peripheral-spectrum primitivity therefore implies the spectral-gap primitive condition used in Chapter 6, and hence the required self-overlap convergence." This chain has a gap: the spectral-gap condition in Chapter 6 (Theorem 4.50) requires three hypotheses: (1) primitivity, (2) all eigenvalues satisfy |μ| ≤ 1, (3) trace-zero fixed points are zero. The blueprint should verify that all three are satisfied under the stated assumptions (injective + TP + primitive). Condition (2) comes from TP normalization. Condition (3) follows from uniqueness of the PSD fixed point (Theorem 5.5). This should be made explicit.

**Theorem 8.26 (Blocking yields primitive transfer map).**
This is the most important technical theorem in the section.

✔ The v2 proof is now correct. It uses the adjoint-fixed-point route: TP normalization of A makes the conjugate-transposed family K_i = (A_i)† unital, irreducibility passes through, and Theorem 4.45 (roots of unity via adjoint fixed point) gives the peripheral eigenvalues are roots of unity. The common exponent p makes ℰ_{A[p]} primitive.

This directly addresses the v1 issue where Theorem 8.26 incorrectly assumed the doubly stochastic condition.

⚠️ However, there is one step that needs checking: the proof says "The TP fixed-point theorem for ℰ_A provides a positive definite fixed point for the adjoint map of K." Tracing this carefully:

- ℰ_A(X) = Σ A_i X A_i† is TP (by hypothesis).
- The "adjoint map of K" where K_i = A_i† is: ℰ_K*(X) = Σ K_i† X K_i = Σ A_i X A_i† = ℰ_A(X).
- So ℰ_K* = ℰ_A, and any PSD fixed point of ℰ_A is a PSD fixed point of ℰ_K*.
- By Theorem 5.2 (or 5.3), this fixed point is PD under irreducibility.

So the claim checks out. The adjoint map of the conjugate-transposed family is exactly the original transfer map.

⚠️ **One remaining subtlety**: Lemma 4.44 requires the Kraus map E to be *unital* and the adjoint E* to have a PD fixed point. In the proof, E corresponds to ℰ_K where K_i = A_i†. We need ℰ_K to be unital: ℰ_K(𝟙) = Σ K_i 𝟙 K_i† = Σ A_i† A_i = 𝟙 (by the TP normalization of A). ✔ This checks out.

### Section 8.7 — Normal canonical form

**Definition 8.28 (Normal canonical form predicate).**
Correct. Lists: irreducible, TP, primitive, strictly decreasing moduli, nonzero weights, positive bond dimensions.

⚠️ The definition explicitly notes: "Here 'normal' is used in the sense of [CPGSV17]: irreducible blocks with trivial peripheral spectrum after TP normalization. It is not the same as Definition 2.19, which means eventual block injectivity." This is an important disambiguation. However, having two different uses of "normal" in the same document is a significant source of confusion. Recommendation: either

1. Rename Definition 2.19 (block-injectivity normal) to something else (e.g., "eventually injective"), or
2. Add a more prominent warning in Chapter 2.

**Theorem 8.29 (Self-overlap is derived in normal canonical form).**
Correct. Direct consequence of the spectral-gap machinery.

**Theorem 8.30 (Modulus-one eigenvalue rigidity for irreducible TP blocks).**
⚠️ The proof sketch is very compressed: "A modulus-one eigenvector for the mixed transfer map saturates the channel Schwarz inequality. Irreducibility then upgrades this eigenvector to an intertwiner between the two Kraus families, which is exactly gauge-phase equivalence."

This is essentially the same argument as Theorem 6.12 but for *irreducible* (rather than injective) blocks. The proof should note that irreducibility is sufficient here because:

- Irreducibility → PD fixed point (Theorem 5.3)
- PD fixed point → unital gauge (Theorem 5.10)
- Then the KS equality / multiplicative-domain argument applies

The statement is correct but the proof needs expansion for a blueprint.

### Section 8.8 — Steps toward canonical form existence

**Theorems 8.31–8.34** correctly chain together the earlier results.

**Theorem 8.34 (Normal canonical form from primitive block decomposition).**
⚠️ The proof says "the theorem first performs a common blocking of the already primitive blocks; in the present statement this blocking is trivial, so one may take p = 1." This is confusing — if p = 1 is always sufficient, why mention blocking at all? The point is that this theorem takes *already primitive* blocks as input. The blocking step would be needed if one started with merely irreducible blocks (which is what Theorem 8.26 addresses). The proof should be clearer about this.

⚠️ The hypotheses include "the moduli |μ_k| are pairwise distinct" — but the normal canonical form predicate (Definition 8.28) requires *strictly decreasing* moduli. The theorem only assumes *pairwise distinct*. This is correct (you can always reorder to make them decreasing), but the proof should note this reordering step explicitly.

### Section 8.9 — Open directions

**Remark 8.35** is honest and well-structured. It clearly identifies what's done and what remains open:

- The "upstream passage" from arbitrary tensor to primitive weighted block data
- On the block-injective side: turning blocked primitive TP data into injective blocks
- On the normal-canonical side: the end-to-end construction from arbitrary tensors

This transparency is appropriate for a formalization blueprint.

---

## 4. Cross-Chapter Consistency

### Definition duplication: 8.1 vs 2.23

Definition 8.1 (block-diagonal tensor from blocks) is essentially identical to Definition 2.23 in Chapter 2. Both define ⊕_k μ_k A_k^i.

**Recommendation:** One of these should be a cross-reference to the other. Since Chapter 2 is the foundation, Definition 8.1 should simply reference 2.23.

### Definition duplication: 8.14 vs 4.23

Definition 8.14 (irreducible tensor) restates Definition 4.23 (irreducible map) specialized to transfer maps.

**Recommendation:** State as "an MPS tensor A is irreducible if ℰ_A is irreducible in the sense of Definition 4.23."

### DS gauge terminology

v1's Chapter 8 had residual DS gauge language (Theorem 8.26 assumed "doubly stochastic"). v2 has corrected this: Theorem 8.26 now assumes only TP normalization. The correction is consistent with the Ch4/Ch5 reviews.

However, the **v1 canonical form predicate** (Definition 9.8 in v1) still uses "DS gauge" language. This needs to be checked against Chapter 9 of v2 — there is a potential inconsistency if Chapter 9 still uses DS while Chapter 8 has moved to TP.

### Chapter 5 dependencies

Theorems 8.15, 8.16, 8.26, 8.30 all rely on Chapter 5 results (PF existence, PD upgrade, TP gauge). The dependencies are correctly cited.

### Chapter 6 dependencies

Theorem 8.23 relies on overlap decay (Theorem 6.17). Theorem 8.24 relies on spectral-gap primitivity from Chapter 6. Correctly cited.

### Chapter 7 dependencies

Theorem 7.52 (irreducible + aperiodicity → normality) is cited in the context of the normal-canonical route. Remark 7.54 from Chapter 7 is referenced in passing. The cross-reference is appropriate.

### Two meanings of "normal"

This is the most problematic cross-chapter consistency issue in the chapter. Definition 2.19 defines "normal" as eventual block injectivity. Definition 8.28 defines "normal canonical form" using the [CPGSV17] sense (irreducible + primitive transfer map). These are related but not identical concepts. The bridge theorems (7.45, 7.52, 8.26) connect them, but having the same word with two meanings is confusing.

---

## 5. Literature Alignment

The chapter correctly tracks the literature:

- The invariant-subspace splitting follows [PGVWC07, Theorem 4] and [CPGSV21, §IV.A.1].
- The Burnside bridge corresponds to [CPGSV21] / Jacobson density.
- The CFII construction follows [CPGSV17, Appendix A].
- The normal canonical form packaging follows [CPGSV17, §2.3].
- The alternative Wedderburn–Artin route of [Wol12, Thm. 6.14] is mentioned but not taken.

One place where the literature alignment could be improved: the Cirac et al. review describes the canonical form construction as first finding invariant subspaces, then scaling so that ℰ_k has spectral radius 1, then identifying irreducible/primitive blocks. The blueprint follows this same strategy but with the TP gauge replacing spectral-radius normalization. The equivalence (spectral-radius-1 normalization ↔ TP gauge after PF rescaling) should be noted.

---

## 6. AI-Style Language Issues

The chapter is generally well-written. A few phrasings to flag:

- "the self-overlap condition is derived rather than stored as an extra field" (Theorem 8.29) — the phrase "stored as an extra field" is Lean jargon rather than mathematical language.
- "CFII data" (throughout) — this is fine for a formalization blueprint but should be expanded at first use ("Canonical Form II data in the sense of [CPGSV17, Appendix A]").

---

## 7. Cleanup Checklist

1. **Resolve Definition 8.1 duplication** with Definition 2.23 (cross-reference instead of redefine).
2. **Resolve Definition 8.14 duplication** with Definition 4.23 (cross-reference).
3. **Clarify Theorem 8.8** — as written it's a tautology.
4. **Clarify Theorem 8.13** — "generate the same MPV" should specify that it's the block-diagonal tensor (with off-diagonal blocks discarded) that preserves the MPV.
5. **Fix the Cesàro citation in Theorem 8.15** — either assume TP or cite Theorem 5.15 instead.
6. **Expand proof of Theorem 8.24** — make the three conditions of Theorem 4.50 explicit.
7. **Expand proof of Theorem 8.30** — the sketch is too compressed for a blueprint.
8. **Clarify Theorem 8.34** — the "trivial blocking" language is confusing; note the reordering step.
9. **Address the two meanings of "normal"** — either rename Definition 2.19 or add a more prominent disambiguation. This is the most important cross-chapter terminology issue remaining in the blueprint.
10. **Note Burnside's theorem as a formalization dependency** — this is a nontrivial external result.
11. **Check Chapter 9 consistency** — the canonical form predicate (Definition 9.8) may still use DS gauge language from v1, which would be inconsistent with v2's Chapter 8.

---

## 8. Final Assessment

Chapter 8 is mathematically sound in v2. The most critical improvement over v1 is the correction of Theorem 8.26 (blocking yields primitive transfer map), which no longer relies on the DS gauge assumption. The two-route structure (block-injective vs normal-canonical) is clearly articulated, and the open directions are honestly stated.

The remaining issues are structural (definition duplication, compressed proofs, terminology ambiguity) rather than mathematical. After the cleanup, the chapter provides a solid reduction framework connecting the Perron–Frobenius theory of Chapters 4–5 with the block separation and BNT arguments of Chapters 9–10.
