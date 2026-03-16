
# Blueprint Review — Chapter 11 (Full Assembly)

This review follows the protocol in `blueprint_review_protocol.md` and the
format established in the Chapter 8 review. It covers v2 of the blueprint,
identifies v1 → v2 changes, compares against the source papers [PGVWC07],
[CPGSV21], and [CPGSV17], and checks cross-chapter consistency with
Chapters 2–10.

---

## 1. Role of Chapter 11 in the Blueprint

Chapter 11 is the terminal chapter. It assembles the Fundamental Theorem of
Matrix Product States from the preceding chapters. The chapter has two
sections and three theorems:

1. **§11.1 (Proportional Fundamental Theorem):** Two theorems — Theorem 11.1
   (block-injective CF-BNT route) and Theorem 11.2 (normal-canonical
   CF-BNT route, NT route) — stating that two block-diagonal tensors in
   canonical form with BNT separation generating proportional MPV families
   are related by a block permutation and per-block gauge-phase equivalence.

2. **§11.2 (Equal-MPV Fundamental Theorem):** Theorem 11.3 — under the
   stronger hypothesis that the two block-diagonal tensors share common
   block structure (same r, same D_k, same μ_k) and generate the *same*
   (not just proportional) MPV family, they are gauge equivalent.

The chapter draws on Chapters 6 (spectral gap), 8 (canonical form reduction
and primitivity), 9 (block separation and canonical-form fundamental
theorem), and 10 (BNT theory and permutation rigidity).

---

## 2. Global Assessment

| Aspect | Evaluation |
|---|---|
| Mathematical correctness | Correct (statements); proof sketches adequate but compressed |
| Conceptual clarity | Fair; Theorems 11.1–11.2 inherit the overloaded hypothesis style of Theorem 10.7 |
| Structural quality | Good; clean separation of proportional vs equal-MPV cases |
| Cross-chapter consistency | Several issues (see §5) |
| Notation consistency | Three moderate issues (see §2a) |
| Literature alignment | Partial; see §6 |
| v1 → v2 changes | Major restructuring: chapter split + proof strategy change in Theorem 11.3 |

Chapter 11 is the shortest chapter in the blueprint (three theorems across
two pages). It is essentially the "main theorem" of the formalization project.
The most important structural observation is how v2's Theorem 11.3 (equal-MPV
case) differs from v1's Theorem 10.13: v1 used Newton–Girard identities to
identify the weight multisets; v2 assumes common block structure from the
outset, bypassing the Newton–Girard machinery entirely. This is a change in
proof strategy with consequences for what the chapter actually proves (see
§4 and §6). The gap is closable with a short bridging lemma (see §4a).

---

## 2a. Cross-Chapter Notation Audit

### Block count: g vs r

Definition 10.1 uses g for the number of BNT blocks (following [CPGSV21,
Def IV.2]). Definition 9.8 and Theorem 9.15 use r. Theorems 10.7–10.8
use g_A, g_B. But Theorem 11.1 uses r_A, r_B, and Theorem 11.3 uses r.

This is a genuine inconsistency. The BNT literature uses g (historically for
ground-state degeneracy), while the algebraic block-permutation theory in
Chapter 9 uses r (rank of the product algebra). These collide when Chapter 11
combines both: Theorem 11.1 says "CF-BNT families (μ_j^A, A_j)_{j=1}^{r_A}"
using r_A where Chapter 10 would use g_A.

**Recommendation:** Standardize on g for the MPS chapters (10–11), keeping
r only in the purely algebraic Chapter 9. Theorem 9.15 is the bridge and
could use r in hypotheses, g in the conclusion.

### Coefficient notation: c_j vs c_N vs a_{N,j}

Definition 10.1 uses c_j for BNT coefficients (|V(A_tot)⟩ = ∑_j c_j
|V(A_j)⟩). Theorems 10.7/11.1 use c_N for the proportionality sequence
(V(A_tot) = c_N V(B_tot)). The letter c is overloaded: c_j is a per-block
coefficient (which should actually be N-dependent, as noted in the Ch10
review), while c_N is the global proportionality factor.

In the concrete CF-BNT setting, c_j(N) = μ_j^N (from Theorem 2.24) and
c_N = ∑_j (μ_j^A)^N / ∑_k (μ_k^B)^N. Using c for both is confusing. The
a_{N,j} notation in Theorems 10.7/11.1 is cleaner.

**Recommendation:** Replace c_j in Definition 10.1 with a_{N,j}, or
rephrase condition 2 as "lies in the span of" without naming the
coefficients. This was already in the Ch10 cleanup list and is now
confirmed as a notational clash with the c_N of Chapters 10–11.

### Permutation symbol: σ overload

Theorem 10.7 uses σ for both the block permutation and the spin
configuration (σ ∈ {0,...,d−1}^N) in the *same equation*:
V^{(N)}(A_tot)_σ = ∑_j a_{N,j} V^{(N)}(A_j)_σ, with conclusion
"σ ∈ S_g." Chapter 11 fixes this by using π for the permutation, but
Chapter 10 still has the clash.

**Recommendation:** Use π for the block permutation everywhere in
Chapters 9–11. Use σ exclusively for spin configurations.

### Other notation (consistent)

The following are consistent across all chapters: A^i, A^w, V^{(N)}(A)_σ,
μ_k, D_k, ⊕_k μ_k A_k, ℰ_A, F_{AB}, O_{AB}(N), ⟨V(A)|V(B)⟩.

### Minor notation issues (previously flagged)

- **c_w(A)**: Defined in Def 2.4, used only in Ch3 Lemma 3.2 proof. Possibly
  unused after Ch3. (Item 2-A from Ch2 remaining issues.)
- **G_{jk}(N)**: Theorem 10.5 proof writes G_{jk} = O_{A_j A_k} but should
  use the inner product ⟨V(A_j)|V(A_k)⟩ for the Gram matrix. Distinction
  matters for Lean (conjugation via Lemma 2.32).

### Notation summary

| Issue | Severity | Chapters affected | Recommendation |
|---|---|---|---|
| g vs r (block count) | Moderate | Ch9, 10, 11 | Standardize on g for MPS chapters |
| c_j vs c_N (coefficients) | Moderate | Ch10, 11 | Replace c_j in Def 10.1 with a_{N,j} |
| σ overload (config vs permutation) | Moderate | Ch9, 10 | Use π for permutation consistently |
| c_w(A) possibly unused after Ch3 | Minor | Ch2, 3 | Remove or note scope |
| G_{jk} conflation | Minor | Ch10 | Note the conjugation step |

---

## 3. v1 → v2 Changes

### What changed

**3-A. Chapter split.** v1's Chapter 10 ("BNT and Full Assembly") combined
BNT theory (§10.1–10.4) and full assembly (§10.5–10.6, Theorems 10.12–10.13)
in a single chapter. v2 splits this into Chapter 10 (BNT, Definitions
10.1–10.3 and Theorems 10.4–10.12) and Chapter 11 (assembly, Theorems
11.1–11.3). The split is a structural improvement.

**3-B. v1's Theorem 10.12 → v2's Theorem 11.1 (proportional MPV case).**
The content is essentially the same. The main difference is that v2's
Theorem 11.1 spells out the coefficient arrays and convergence hypotheses
explicitly (inheriting the verbose style from Theorem 10.7), while v1's
Theorem 10.12 stated the hypotheses more concisely.

**3-C. Theorem 11.2 (NT route): NEW in v2.** The normal-canonical companion
to Theorem 11.1, paralleling the two-route structure established in
Chapter 8 (Definitions 8.24 vs 8.28), Chapter 9 (Theorems 9.13 vs 9.14),
and Chapter 10 (Definitions 10.2 vs 10.3). Consistent with the two-route
pattern.

**3-D. v1's Theorem 10.13 → v2's Theorem 11.3: proof strategy changed.**

v1's Theorem 10.13 (equal-MPV FT) did NOT assume common block structure.
It deduced weight-multiset equality from equal MPVs via Newton–Girard
(Theorem 10.9 in v1). v2's Theorem 11.3 assumes common block structure
from the outset, bypassing Newton–Girard entirely. This is a scope
reduction; see §4 and §4a for detailed analysis.

**3-E. v1 §10.5 (Primitivity bridge) not carried over.** Already removed
in v2's Chapter 10 (absorbed into Chapter 8). Not present in Chapter 11.

### What did NOT change

The proportional MPV result (Theorem 11.1) is essentially v1's Theorem
10.12 with more explicit hypotheses and different numbering.

---

## 4. Statement-by-Statement Review

### Section 11.1 — Proportional Fundamental Theorem

**Theorem 11.1 (Fundamental Theorem — proportional MPV case).**

Statement: Let A_tot and B_tot be MPS tensors equipped with CF-BNT
families (μ_j^A, A_j)_{j=1}^{r_A} and (μ_k^B, B_k)_{k=1}^{r_B}. Assume
one is given coefficient arrays a_{N,j}, b_{N,k} and nonzero limits
a_j^∞, b_k^∞, c^∞ such that the MPV decomposition and proportionality
identities hold. Then r_A = r_B, and there is a permutation π with
D_j^A = D_{π(j)}^B and A_j gauge-phase equivalent to B_{π(j)}.

**Correctness**: ✔

**Proof**: Direct invocation of Theorem 10.7. ✔

⚠️ **The theorem inherits all the issues of Theorem 10.7:**

1. **Overloaded hypotheses.** The coefficient arrays and proportionality
   sequence are consequences of the CF-BNT structure. The theorem restates
   them as free-standing hypotheses. (Ch10 review, cleanup item 6.)

2. **A_tot not linked to ⊕ μ_j A_j.** The structural origin of A_tot from
   the block-diagonal assembly (Theorem 2.24) is not stated.

3. **Notation: r_A vs g_A.** See §2a above.

⚠️ **Coefficient convergence hypothesis.** Theorem 10.7 requires a_{N,j} →
a_j^∞ ≠ 0 for all j. In the CF-BNT setting, the natural coefficients from
Theorem 2.24 are a_{N,j} = μ_j^N. These do not have nonzero limits in
general: |(μ_j)^N| → ∞ for |μ_j| > 1 and → 0 for |μ_j| < 1.

Theorem 10.7 takes abstract coefficient arrays as free hypotheses, so it
does not require a_{N,j} = μ_j^N. But the proof of Theorem 11.1 does not
explain how the CF-BNT data produce arrays satisfying these hypotheses.
The resolution likely involves the fact that Theorem 10.7 operates at the
level of the BNT decomposition (where the coefficient arrays are the BNT
expansion coefficients, structured by the inductive block-separation
argument of §9.3), not at the level of the raw μ_k^N. This relationship
should be made explicit.

**Recommendation:** Add a remark (or an application lemma) showing how the
CF-BNT canonical form data instantiate the hypotheses of Theorem 10.7.

---

**Theorem 11.2 (Fundamental Theorem — proportional MPV case, NT route).**

Statement: Same as Theorem 11.1 but with normal-CF-BNT families.

**Correctness**: ✔

⚠️ **Proof should cite Theorem 8.30 explicitly.** The irreducible-TP block
identification step uses Theorem 8.30 (modulus-one eigenvalue rigidity),
not the injective-block machinery.

⚠️ **Remark 10.6 reference is appropriate but could be clearer.** The
relevance is that Theorem 11.2 gives gauge-phase equivalence but cannot
upgrade to full gauge equivalence without connecting normality (irreducible
+ primitive) to eventual block injectivity.

### Section 11.2 — Equal-MPV Fundamental Theorem

**Theorem 11.3 (Fundamental Theorem — equal MPV case).**

Statement: Fix a common block structure: same r, same D_k, same μ_k. If
two CF-BNT families on this common data generate the same MPV family, then
each pair (A_k, B_k) is gauge equivalent.

**Correctness**: ✔ Under the stated hypotheses, the proof is correct.

**Proof**: Forget BNT separation, apply Theorem 9.15 (CF FT, same-structure
version). ✔

⚠️ **The theorem is weaker than v1's Theorem 10.13.** v2 assumes common
block structure; v1 deduced it. The gap and its resolution are analysed
in §4a below.

---

## 4a. Scope Analysis: Recovering the Full FT from v2's Machinery

### What the full Fundamental Theorem says

[CPGSV21, Corollary IV.5]: If two tensors A and B in canonical form
generate the same MPV for all N, then the dimensions coincide and there
is an invertible X with A^i = XB^iX^{-1}. No assumption on common
structure.

### What v2 proves

v2's Theorem 11.3 assumes common (r, D_k, μ_k) and concludes gauge
equivalence. The structural matching is an input, not an output.

### Can the full theorem be recovered?

Yes, via the following chain using v2's existing machinery:

**Step 1.** Equal MPVs imply proportional MPVs (trivially, c_N = 1).

**Step 2.** Theorem 11.1 (proportional FT) gives r_A = r_B, a permutation π,
and per-block gauge-phase equivalence: B_{π(j)}^i = e^{iφ_j} X_j A_j^i X_j^{-1}.

**Step 3 (missing lemma).** From equal MPVs + Step 2 + BNT linear
independence (Theorem 10.5), deduce weight matching. The argument:

Equal MPVs give ∑_j (μ_j^A)^N V^{(N)}(A_j)_σ = ∑_k (μ_k^B)^N V^{(N)}(B_k)_σ.
Applying the permutation and gauge-phase equivalence from Step 2:
V^{(N)}(B_{π(j)})_σ = e^{iNφ_j} V^{(N)}(A_j)_σ.
Substituting and using BNT linear independence for large N:
(μ_j^A)^N = (μ_{π(j)}^B)^N · e^{iNφ_j} for each j.
This forces μ_j^A = μ_{π(j)}^B · e^{iφ_j}.

**Step 4.** After reindexing by π and absorbing the phase into the gauge
transformation, we have common block structure. Theorem 11.3 applies.

### Assessment

The gap between v2 and the full FT is a **short bridging lemma** (Step 3).
This lemma uses BNT linear independence (already available from Theorem
10.5) and is roughly five lines of mathematics. It does NOT require
Newton–Girard — the coefficient matching comes directly from comparing
the BNT expansion, not from power-sum identities.

The Newton–Girard theorems (10.11–10.12) are an alternative route to the
same conclusion (they match the weight multisets without using linear
independence of the block MPVs). They remain orphaned in v2 regardless of
which route is taken.

**Recommended fix:** Add a bridging lemma:

> **Lemma 11.X (Equal MPVs yield common block structure).** Under the
> hypotheses of Theorem 11.1, if additionally c_N = 1 for all N (equal
> MPVs, not just proportional), then after reindexing via the permutation π,
> the weights agree: μ_j^A = μ_{π(j)}^B · e^{iφ_j} where φ_j are the
> gauge phases from Theorem 11.1.

This lemma, combined with Theorems 11.1 and 11.3, recovers the full
[CPGSV21, Corollary IV.5].

**Severity:** Moderate. The theorem statements in v2 are correct; the gap is
a missing five-line lemma, not a deep mathematical issue. But without it, v2
does not formally prove the unconditional equal-MPV FT that the blueprint
is meant to formalize.

---

## 5. Cross-Chapter Consistency

### Dependency chain verification

Theorem 11.1 depends on:
- Theorem 10.7 (BNT permutation, proportional case) ← Chapter 10 ✔
- Theorem 10.4 (cross-overlap decay) ← Chapter 10 ← Chapter 6 ✔
- Definition 9.8 / 10.2 (canonical form with BNT separation) ← Chapters 9, 10 ✔

Theorem 11.2 depends on:
- Definition 8.28 / 10.3 (normal canonical form with BNT separation) ← Chapters 8, 10 ✔
- Theorem 8.29 (self-overlap from primitivity) ← Chapter 8 ✔
- Theorem 8.30 (modulus-one eigenvalue rigidity) ← Chapter 8 ✔

Theorem 11.3 depends on:
- Theorem 9.15 (canonical-form FT, same-structure version) ← Chapter 9 ✔
- Theorem 9.7 (per-block same-MPV → global gauge equivalence) ← Chapter 9 ✔

All dependency chains are acyclic. ✔

### Cross-chapter issues

**5-A. Orphaned theorems confirmed.** Theorems 10.11 (Newton–Girard trace
recursion) and 10.12 (equal power sums → equal multisets) are not cited
anywhere in Chapter 11. Confirmed orphaned. They would remain orphaned
even if Lemma 11.X (§4a) is added, since the BNT linear independence
route does not use Newton–Girard.

Theorem 10.9 (coefficient ratio decay) is not explicitly cited by
Theorems 11.1–11.2. The coefficient-instantiation step (how CF-BNT data
satisfy Theorem 10.7's hypotheses) is not stated as a theorem anywhere.

**5-B. Theorem 9.11 (Vandermonde separation): NOT orphaned.** Used by
Lemma 9.12 (block separation core). The earlier flag was a false alarm.

**5-C. Two meanings of "normal" — inherited.** Propagates through
Theorem 11.2 via Definition 8.28 and Remark 10.6. Same presentation issue
flagged since Chapter 2.

**5-D. DS gauge — fully eliminated.** ✔

**5-E. "Basis Normal Tensor" naming.** Inherits the naming issue from
Chapter 10. "CF-BNT" appears without expansion on first use.

---

## 6. Literature Alignment

### [CPGSV21, Theorem 4.1] (Proportional MPV FT)

v2's Theorem 11.1 corresponds to this result. The blueprint's approach
(block-injective canonical form + explicit coefficient arrays) is a valid
specialization. ✔

### [CPGSV21, Corollary IV.5] (Equal-MPV FT)

v2's Theorem 11.3 is a conditional version: it assumes common block
structure, which is part of what the corollary deduces. The full corollary
is recoverable from v2's machinery via the bridging lemma proposed in §4a.

The paper's proof proceeds by: (1) applying Theorem IV.4 (proportional FT),
(2) deducing weight matching via Lemma A.5 (Newton–Girard / Vandermonde),
(3) combining for global gauge equivalence. The blueprint's proposed route
(§4a) replaces step (2) with the BNT linear independence argument, which
is equally valid.

### [PGVWC07, Theorem 4]

The original proof uses a different route (OBC lifting + matrix equation
intertwining). The blueprint does not claim to follow [PGVWC07] directly.
Consistent.

---

## 7. AI-Style Language Issues

### Chapter preamble

- "This chapter states the assembled Fundamental Theorem results." →
  "This chapter proves the Fundamental Theorem of Matrix Product States."

- "The proportional-MPV theorems take explicit coefficient-convergence input
  in both the block-injective CF-BNT setting and the normal-canonical CF-BNT
  setting." → "We state the Fundamental Theorem in two versions: one for
  block-injective tensors in canonical form, and one for the normal-canonical
  variant."

- "The equal-MPV theorem is the common-block-structure specialization." →
  "The equal-MPV version assumes common block structure and deduces gauge
  equivalence."

### Theorem statements and proofs

- "equipped with CF-BNT families" — fine for formalization; a mathematician
  would say "in canonical form with BNT separation."

- "Assume one is given coefficient arrays..." → "Suppose there exist
  coefficient arrays..."

- "Forget the extra BNT-separation field and retain only the underlying
  canonical-form data." → "Since both families share the canonical form data,
  the BNT separation condition is not needed."

---

## 8. Cleanup Checklist

1. **Add the bridging lemma (Lemma 11.X) from §4a.** This recovers the
   full unconditional equal-MPV FT from v2's machinery. The lemma uses
   BNT linear independence (Theorem 10.5) and does not require
   Newton–Girard.

2. **Add a remark on coefficient instantiation for Theorem 11.1.** Explain
   how CF-BNT data produce coefficient arrays satisfying Theorem 10.7's
   abstract hypotheses. This closes the gap from Ch10 cleanup item 13a.

3. **Cite Theorem 8.30 explicitly in Theorem 11.2's proof.**

4. **Harmonize notation:**
   - Block count: use g (not r) in Chapters 10–11.
   - Coefficients: replace c_j in Def 10.1 with a_{N,j}.
   - Permutation: use π (not σ) in Theorems 10.7–10.8.

5. **Expand "CF-BNT" on first use.** Write "canonical form with basis of
   normal tensors separation (CF-BNT)."

6. **Fix "Basis Normal Tensor" naming.** Use "basis of normal tensors (BNT)"
   consistently.

7. **Rewrite AI-generated phrasing** (see §7 for specific replacements).

8. **Note the literature gap.** After Theorem 11.3, add a remark noting that
   the full [CPGSV21, Corollary IV.5] does not assume common block structure.
   If Lemma 11.X is added, note that the combination of Theorems 11.1 +
   Lemma 11.X + Theorem 11.3 recovers the full corollary.

9. **Decide on Newton–Girard (Theorems 10.11–10.12).** These are orphaned
   regardless of whether Lemma 11.X uses BNT linear independence or
   Newton–Girard. Either: (a) mark them as auxiliary results for potential
   future use, or (b) remove them.

---

## 9. Formalization Notes: Type-Level Transitions

### 11-F1. CF-BNT data as a Lean structure

Theorems 11.1–11.2 take as input a structured bundle: block tensors,
scaling factors, coefficient arrays, convergence proofs, and the
proportionality sequence. In Lean, this is a dependent structure with
fields carrying proof obligations (`Filter.Tendsto` proofs, `Ne` proofs
on limits, etc.). The blueprint compresses this into "such that" clauses.

**Blueprint action:** Either define a "proportional MPV data" structure
or note that the Lean code packages these fields into a structure.

### 11-F2. Gauge equivalence vs gauge-phase equivalence

Theorems 11.1–11.2 conclude gauge-*phase* equivalence. Theorem 11.3
concludes gauge equivalence. These are different Lean predicates. The
upgrade requires matching the phases (from weight matching in Lemma 11.X).

**Blueprint action:** Note the distinct predicates and the upgrade step.

### 11-F3. "Forget" as structure coercion

Theorem 11.3's proof drops the BNT-separation field. In Lean, this is a
coercion from the CF-BNT structure to the CF structure, requiring an
explicit term.

**Blueprint action:** Note the coercion.

---

## 10. Summary of Downstream Dependencies

### Results used from earlier chapters

| Theorem | Source | Used by |
|---|---|---|
| Theorem 10.7 (BNT permutation, proportional) | Ch 10 | Thm 11.1 |
| Theorem 10.4 (cross-overlap decay) | Ch 10 | Thm 11.1 |
| Theorem 10.5 (CF-BNT yields BNT) | Ch 10 | Lemma 11.X (proposed) |
| Theorem 8.29 (self-overlap from primitivity) | Ch 8 | Thm 11.2 |
| Theorem 8.30 (modulus-one eigenvalue rigidity) | Ch 8 | Thm 11.2 |
| Theorem 9.15 (CF FT, same-structure) | Ch 9 | Thm 11.3 |
| Theorem 9.7 (per-block same-MPV → global gauge equiv) | Ch 9 | Thm 11.3 |

### Orphan status (final, all chapters reviewed)

| Theorem | Status |
|---|---|
| Theorems 10.11–10.12 (Newton–Girard) | Orphaned (not needed by any route in v2) |
| Theorem 10.9 (coefficient ratio decay) | Indirectly needed but not cited |
| Theorem 9.11 (Vandermonde separation) | NOT orphaned (used by Lemma 9.12) |

---

## 11. Final Assessment

Chapter 11 is mathematically correct in all three of its theorem statements.
The proportional FT (Theorems 11.1–11.2) correctly assembles the BNT
permutation rigidity from Chapter 10 with the canonical form machinery from
Chapters 8–9. The two-route structure (block-injective vs normal-canonical)
is maintained consistently through the final chapter.

The scope of the equal-MPV theorem (Theorem 11.3) is reduced relative to v1:
v2 assumes common block structure rather than deducing it. However, the full
unconditional FT ([CPGSV21, Corollary IV.5]) is recoverable from v2's
existing machinery via a short bridging lemma (§4a) that uses BNT linear
independence to match the weights. This lemma does not require Newton–Girard.
The recommended fix is to add this lemma and a concluding remark connecting
Theorems 11.1 + 11.X + 11.3 to the full corollary.

The secondary issues are:
- Notation inconsistencies (g vs r, c_j vs c_N, σ overload) — all moderate,
  all fixable by standardizing symbols across Chapters 9–11.
- The coefficient-instantiation gap (how CF-BNT data satisfy Theorem 10.7's
  abstract hypotheses) — a presentation issue.
- AI-generated style issues (organizational language, code jargon).
- Inherited cross-chapter issues ("two meanings of normal," BNT naming).

None of these are mathematical errors. After the cleanup (especially the
bridging lemma), Chapter 11 would provide a complete proof of the
Fundamental Theorem of Matrix Product States.
