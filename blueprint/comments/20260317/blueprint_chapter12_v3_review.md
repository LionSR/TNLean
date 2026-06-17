
# Blueprint Review — Chapter 12 (Full Assembly), v2 → v3

This document reviews Chapter 12 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter11_review.md`, `full_ft_verification.md`,
`blueprint_review_comprehensive_reference.md`).

---

## Chapter numbering map

v3 Chapter 12 = v2 Chapter 11 (Full Assembly). The chapter is renumbered
+1 due to the new Chapter 5 (Schwarz Inequalities) inserted in v3.

v3 has 15 numbered statements (12.1–12.15) vs v2's 3 (11.1–11.3). Of
these, 12.1 and 12.3 are new, 12.5 is new (the bridging theorem from
`full_ft_verification.md`), 12.7 is a new remark, and 12.8–12.15
constitute the entirely new Section 12.4 (periodic FT).

| v2 | v3 | Content | Change |
|---|---|---|---|
| — | Thm 12.1 | Weak FT (conditional) | **New** |
| Thm 11.1 | Thm 12.2 | Proportional FT (CF-BNT) | Renumbered; **g notation**; **"equipped with" → "in CF with BNT separation"**; ref 10.7→11.7, 10.4→11.4 |
| — | Remark 12.3 | Coefficient instantiation | **New** |
| Thm 11.2 | Thm 12.4 | Proportional FT (NT route) | Renumbered; **proof rewritten (cites 9.30/9.31 explicitly)**; ref 8.29→9.30, Remark 10.6→11.6 |
| — | Thm 12.5 | Equal-MPV FT (unconditional) | **New** (the bridging theorem) |
| Thm 11.3 | Thm 12.6 | Equal-MPV FT (common block structure) | Renumbered; **"CF-BNT families" → "families in CF with BNT separation"**; ref 9.15→10.17; **"Forget the extra BNT-separation field" removed** |
| — | Remark 12.7 | Recovery of literature statement | **New** |
| — | Def 12.8–Remark 12.15 | Periodic FT (§12.4) | **Entirely new section** |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | **Much improved.** Theorem 12.5 now recovers [CPGSV21, Corollary IV.5] unconditionally. Remark 12.7 makes this explicit. |
| Internal consistency | Mostly good. Notation g_A/g_B adopted consistently. One issue: Theorem 12.1's non-degeneracy hypothesis (see 12-S1). |
| v2 → v3 changes | **Major.** Chapter expanded from 3 statements / 2 pages to 15 statements / 6 pages. Key additions: Theorem 12.1 (Weak FT), Theorem 12.5 (unconditional equal-MPV FT), Remark 12.3 (coefficient instantiation), Section 12.4 (periodic FT). |
| AI language | **Significantly worse than v2 in §12.1.** The section title "pipeline end-to-end" and body text ("upstream pipeline," "downstream Fundamental Theorem," "automatic pipeline") are the most concentrated AI language in the entire blueprint. Rest of chapter much improved. |
| Formalization readiness | Improved. Theorem 12.5's explicit proof is directly formalizable. Remark 12.3 closes the coefficient-instantiation gap. |
| Open items from prior review | 7 of 9 cleanup items addressed. See Prior Review Items below. |
| FT critical path | **Yes. This is the terminal chapter for the FT.** Theorems 12.2 and 12.5 together constitute the full Fundamental Theorem. |
| **New issues** | **Theorem 12.1 non-degeneracy hypothesis needs scrutiny (12-S1). §12.1 AI language is severe (12-AI1). Chapter title still "Full Assembly" (12-AI2). Theorem 12.4 proof is less explicit than 12.2's (12-S3). Theorem 12.1 forward-references Theorem 12.4 (12-S2).** |

---

# v2 → v3 Changes — Substantive

## 1. Chapter preamble rewritten

v2: "This chapter states the assembled Fundamental Theorem results. The
proportional-MPV theorems take explicit coefficient-convergence input in
both the block-injective CF-BNT setting and the normal-canonical CF-BNT
setting. The equal-MPV theorem is the common-block-structure
specialization."

v3: "This chapter proves the Fundamental Theorem of Matrix Product States.
We state the Fundamental Theorem in two versions: one for block-injective
tensors in canonical form with basis of normal tensors (BNT) separation
(CF-BNT), and one for the normal-canonical variant. We then treat the
equal-MPV case, including the common-block-structure specialization that
deduces gauge equivalence."

Assessment: v3 fixes the three AI-language items flagged in the v2 review
(§7): "states the assembled" → "proves," "take explicit
coefficient-convergence input" → "We state ... in two versions," and the
second sentence is natural. However, the phrase "common-block-structure
specialization" survives (flagged in the comprehensive reference Part II).

## 2. Notation: g replaces r throughout

v2 used r_A, r_B for block counts in Theorems 11.1–11.2 and r in Theorem
11.3. v3 uses g_A, g_B and g consistently. This addresses cleanup item 4
from the v2 review and the cross-chapter notation issue flagged in the
comprehensive reference Part III (§III.1).

## 3. Theorem 12.1 (Weak FT): entirely new

This theorem did not exist in v2. It takes families in *normal canonical
form* (not CF-BNT), adds a non-degeneracy condition ("no two distinct
blocks are gauge-phase equivalent"), and concludes gauge-phase equivalence
via Theorem 12.4. See 12-S1 and 12-S2 for analysis.

## 4. Remark 12.3 (Coefficient instantiation): new

This remark explains how CF-BNT block-diagonal data instantiate the
abstract coefficient hypotheses of Theorem 12.2, taking a_{N,j} = μ_j^N
via Theorem 2.24. Addresses cleanup item 2 from the v2 review and the
comprehensive reference Part V recommendation.

## 5. Theorem 12.5 (Equal-MPV FT, unconditional): new — the bridging theorem

This is the key structural addition. It implements the bridging argument
verified in `full_ft_verification.md`. The proof:
(a) applies Theorem 12.2 with c_N = 1 to get gauge-phase equivalence,
(b) uses Theorem 2.24 to write the BNT expansion,
(c) substitutes the gauge-phase identity V^{(N)}(B_{π(j)}) = e^{iNφ_j} V^{(N)}(A_j),
(d) invokes BNT linear independence (Theorem 11.5 + Definition 11.1),
(e) extracts μ_j^A = μ_{π(j)}^B · e^{iφ_j},
(f) absorbs the phase into the gauge to obtain global gauge equivalence.

This matches the argument in `full_ft_verification.md` §3, Steps 1–3. ✔

## 6. Theorem 12.6 (common block structure): reference updated

v2's Theorem 11.3 cited Theorem 9.15 (v2 numbering: CF FT same-structure).
v3's Theorem 12.6 cites Theorem 10.17 (v3 numbering for the same result).
Reference verified: Theorem 10.17 (v3 p.64) is indeed the canonical form
fundamental theorem, same-structure version. ✔

## 7. "Forget the extra BNT-separation field" removed

v2's Theorem 11.3 proof read: "Forget the extra BNT-separation field and
retain only the underlying canonical-form data." v3's Theorem 12.6 proof
reads: "Since both families share the canonical form data, the BNT
separation condition is not needed." This was the recommended replacement
from the v2 review §7. ✔

## 8. Remark 12.7 (Recovery of literature statement): new

Explicitly notes that Theorem 12.5 recovers [CPGSV21, Corollary IV.5]
without assuming common block structure, and that the weight matching comes
from the BNT expansion rather than Newton–Girard. Addresses cleanup items
1 and 8 from the v2 review. ✔

## 9. Section 12.4 (Periodic FT): entirely new

Definitions 12.8–12.9, Remarks 12.10/12.12/12.14/12.15, Definition 12.11,
Theorem 12.13. This section outlines the [DlCCSPG17] framework for periodic
tensors. Not on the FT critical path. Deferred from detailed review per
instruction; see §12.4 flag below.

---

# v2 → v3 Changes — Non-Substantive

- Chapter references updated for +1 shift: Ch 6→7, Ch 8→9, Ch 9→10,
  Ch 10→11.
- v2's "equipped with CF-BNT families" → v3's "in canonical form with BNT
  separation" in Theorem 12.2 statement. (Addresses AI-language item.)
- v2's "Assume one is given" → v3's "Suppose there exist" in Theorem 12.2.
  (Addresses AI-language item.)
- Theorem 12.2 proof now names Theorem 11.4 (cross-overlap decay) and
  Theorem 11.7 explicitly, where v2 named 10.4 and 10.7 — straightforward
  renumbering.
- Ket notation |V^{(N)}(A_j)⟩ adopted in the preamble (consistent with
  Ch 11 v3 review finding §12).

---

# Prior Review Items — Status Check

Source: `blueprint_chapter11_review.md` §8 (Cleanup Checklist).

| # | Item | Status in v3 |
|---|---|---|
| 1 | Add bridging lemma (Lemma 11.X) | **Fixed.** Now Theorem 12.5 with explicit proof. |
| 2 | Add coefficient-instantiation remark | **Fixed.** Remark 12.3. |
| 3 | Cite Theorem 8.30 explicitly in Thm 11.2's proof | **Partially addressed.** Thm 12.4 proof cites Thm 9.30 and 9.31 (the v3 equivalents), but does not name the Kadison–Schwarz / modulus-one eigenvalue step. See 12-S3. |
| 4 | Harmonize notation: g not r | **Fixed.** g_A, g_B throughout. |
| 5 | Expand CF-BNT on first use | **Fixed.** Preamble expands to "canonical form with basis of normal tensors (BNT) separation (CF-BNT)." |
| 6 | Fix "Basis Normal Tensor" naming | **Fixed in Ch 11.** Ch 12 uses "basis of normal tensors" correctly. |
| 7 | Rewrite AI-generated phrasing | **Partially fixed.** Preamble improved. §12.1 introduces *new* AI language ("pipeline end-to-end," "upstream pipeline," "downstream," "packages"). See 12-AI1. |
| 8 | Note literature gap after Thm 11.3 | **Fixed.** Remark 12.7. |
| 9 | Decide on Newton–Girard (Thms 10.11–10.12) | **Addressed in Ch 11.** Remark 11.14 notes orphan status. Not revisited in Ch 12 (appropriate). |

---

# Forward Reference Verification

All forward references in Chapter 12 checked against v3 PDF:

| Reference | Where cited | Target (v3) | Verified |
|---|---|---|---|
| Theorem 12.4 | Thm 12.1 proof | v3 p.70 — proportional FT, NT route | ✔ |
| Theorem 11.7 | Thm 12.2 proof | v3 p.67 — BNT permutation, proportional | ✔ |
| Theorem 11.4 | Thm 12.2 proof | v3 p.66 — cross-overlap decay | ✔ |
| Theorem 2.24 | Remark 12.3, Thm 12.5 proof | v3 p.11 — MPV decomposition | ✔ |
| Theorem 9.30 | Thm 12.4 proof | v3 p.56 — self-overlap from primitivity | ✔ |
| Theorem 9.31 | Thm 12.4 proof | v3 p.56 — modulus-one eigenvalue rigidity | ✔ |
| Remark 11.6 | Thm 12.4 proof | v3 p.67 — normality gap remark | ✔ |
| Theorem 12.2 | Thm 12.5 proof | v3 p.70 — proportional FT | ✔ |
| Theorem 11.5 | Thm 12.5 proof | v3 p.67 — CF-BNT yields BNT | ✔ |
| Definition 11.1 | Thm 12.5 proof | v3 p.66 — BNT definition | ✔ |
| Theorem 10.17 | Thm 12.6 proof | v3 p.64 — CF FT same-structure | ✔ |
| [CPGSV21, Cor IV.5] | Remark 12.7 | Literature | ✔ (correct citation) |
| Definition 9.29 | Def 12.9, Remark 12.10 | v3 p.55 — normal canonical form | ✔ |
| Definition 4.37 | Def 12.8 | v3 p.23 — primitive transfer map | ✔ |

All references resolve correctly. ✔

---

# Statement-by-Statement Analysis

## Section 12.1 — Weak Fundamental Theorem

### Theorem 12.1 (Weak FT, conditional) — NEW

**Statement:** Two families in normal canonical form, with a
non-degeneracy condition (no two distinct blocks gauge-phase equivalent),
and proportional MPV data with converging coefficients, yield a block
permutation and per-block gauge-phase equivalence.

**12-S1. Non-degeneracy hypothesis.** ⚠️ This hypothesis ("no two distinct
blocks in the same family are gauge-phase equivalent") is new and not
present in Theorems 12.2 or 12.4. The proof claims it "ensures the block
matching is well-defined."

This needs scrutiny. The block matching in Theorem 12.4 (= Theorem 11.7
via the BNT permutation argument) does not require a non-degeneracy
condition — the BNT linear independence and overlap-decay machinery handle
the matching uniquely. The non-degeneracy condition would be relevant if
one wanted to ensure the *permutation* π is unique, but uniqueness of π
is not part of the conclusion of Theorem 12.4.

Two possible interpretations:
(a) The non-degeneracy condition is genuinely needed for Theorem 12.1
because the "packaging" step that derives BNT separation from normal
canonical form data requires it. This would need to be made explicit.
(b) The condition is a redundant safety hypothesis inherited from the
[DlCCSPG17] irreducible form framework (where non-repetition of blocks
is part of the definition). In this case it should be marked as such or
removed.

**Severity:** Moderate. If the hypothesis is genuinely needed, its role
must be explained. If redundant, it should be dropped to avoid confusion
with the unconditional Theorems 12.2/12.4/12.5.

**Recommendation:** Clarify whether the non-degeneracy condition is needed
for the normal-canonical → BNT-separation derivation step, or whether it
is a presentation choice. Add a sentence to the proof explaining the role.

**12-S2. Forward reference to Theorem 12.4.** Theorem 12.1 appears in
§12.1 before Theorem 12.4 (§12.2). The proof of 12.1 invokes 12.4. This
creates a forward dependency: the "weak" theorem is stated first but
proved second. This is logically fine (and mirrors the paper's style of
stating the main theorem first, proving components after), but should be
noted for the Lean formalization — the dependency graph has 12.1 depending
on 12.4, not the reverse.

**12-S2a. Naming: "Weak Fundamental Theorem."** The name is potentially
misleading. In mathematics, a "weak" version of a theorem typically has a
weaker *conclusion*, not extra hypotheses. Here, Theorem 12.1 has *more*
hypotheses (the non-degeneracy condition) and the *same* conclusion as
Theorem 12.4. A better name would be "Conditional Fundamental Theorem" or
"Fundamental Theorem with non-degeneracy hypothesis." Alternatively, if
the intent is that "weak" refers to the current state of the formalization
(the "automatic pipeline" cannot yet produce all hypotheses), then this is
formalization-status commentary masquerading as a theorem name, which is
inappropriate for the mathematical document.

---

## Section 12.2 — Proportional Fundamental Theorem

### Theorem 12.2 (Proportional FT, CF-BNT) — was v2 Thm 11.1

**Statement:** Identical to v2's Theorem 11.1 with three changes: (i)
g_A/g_B replaces r_A/r_B, (ii) "equipped with CF-BNT families" → "in
canonical form with BNT separation," (iii) "Assume one is given" →
"Suppose there exist."

**Correctness:** ✔. Same as v2.

**Proof:** Cites Theorem 11.7 (= v2's 10.7) and Theorem 11.4 (= v2's
10.4). References updated correctly.

**Inherited issues from v2 review:** The overloaded hypotheses issue
(coefficient arrays are consequences of CF-BNT structure, not independent
data) remains. However, Remark 12.3 now explicitly addresses this by
showing how CF-BNT data instantiate the abstract hypotheses. The inherited
issue is therefore demoted to a presentation choice (keeping the abstract
formulation for Lean compatibility), not a mathematical gap. Acceptable.

### Remark 12.3 (Coefficient instantiation) — NEW

**Correctness:** ✔. The remark correctly states that a_{N,j} = (μ_j^A)^N
via Theorem 2.24, and explains why Theorem 12.2 keeps the arrays explicit
(because Theorem 11.7 is formulated abstractly).

This is exactly the content recommended in v2 cleanup item 2. ✔

### Theorem 12.4 (Proportional FT, NT route) — was v2 Thm 11.2

**Statement:** Identical to v2's Theorem 11.2 modulo renumbering and g
notation.

**Correctness:** ✔.

**12-S3. Proof less explicit than Theorem 12.2's.** The proof of
Theorem 12.4 reads: "Normal canonical form with BNT separation provides
irreducibility, TP normalization, and primitive self-overlap convergence
via Theorem 9.30. Theorem 9.31 supplies the leading-block identification
step..." This is more explicit than v2's proof (which did not name
specific theorems), but still less explicit than Theorem 12.2's proof.
In particular:
- The proof does not state *which* theorem provides the BNT permutation
  and gauge-phase equivalence (the analogue of Theorem 11.7 for the NT
  route). It says "the same peeling argument as in the injective CF-BNT
  case," which is a proof-by-analogy.
- v2 cleanup item 3 asked for Theorem 8.30 to be cited explicitly. In v3,
  Theorem 8.30 became Theorem 9.31, which *is* cited. So the specific
  citation is present. ✔

**Severity:** Low. The proof structure is clear enough, and the key
references (9.30, 9.31, Remark 11.6) are all present.

---

## Section 12.3 — Equal-MPV Fundamental Theorem

### Theorem 12.5 (Equal-MPV FT, unconditional) — NEW

**Statement:** Under the hypotheses of Theorem 12.2, if V^{(N)}(A_tot) =
V^{(N)}(B_tot) for all N and σ, then the block-diagonal tensors are gauge
equivalent.

**Correctness:** ✔. The proof is the bridging argument from
`full_ft_verification.md`, now written out in full.

**Proof verification (line by line):**

Step 1: Apply Theorem 12.2 with c_N = 1.
→ Gives g_A = g_B, permutation π, gauge-phase equivalence
B^i_{π(j)} = e^{iφ_j} X_j A^i_j X_j^{-1}. ✔

Step 2: By Theorem 2.24, write the BNT expansions.
→ V^{(N)}(A_tot) = ∑_j (μ_j^A)^N V^{(N)}(A_j),
   V^{(N)}(B_tot) = ∑_j (μ_{π(j)}^B)^N V^{(N)}(B_{π(j)}). ✔

Step 3: The gauge-phase identity gives
V^{(N)}(B_{π(j)}) = e^{iNφ_j} V^{(N)}(A_j). ✔

Step 4: Equal MPVs then yield
∑_j [(μ_j^A)^N − (μ_{π(j)}^B e^{iφ_j})^N] V^{(N)}(A_j) = 0. ✔

Step 5: BNT linear independence (Theorem 11.5 + Definition 11.1) for
large N gives (μ_j^A)^N = (μ_{π(j)}^B e^{iφ_j})^N for each j. ✔

Step 6: "Taking two consecutive large values of N and using that the
weights are nonzero gives μ_j^A = μ_{π(j)}^B e^{iφ_j}."
→ This step is correct: if z^N = w^N for two consecutive N, then
z^{N+1}/z^N = w^{N+1}/w^N, i.e., z = w (both nonzero). ✔

Step 7: Phase absorption:
μ_{π(j)}^B B^i_{π(j)} = μ_j^A X_j A^i_j X_j^{-1}. ✔

Step 8: Global gauge equivalence via X = ⊕_j X_j, composed with
the permutation matrix of π. ✔

**Assessment:** The proof matches `full_ft_verification.md` exactly and
is fully correct. The "two consecutive large values of N" step (Step 6)
is a clean way to handle the extraction — slightly more elegant than our
original write-up, which stated μ_j^A = μ_{π(j)}^B · e^{iφ_j} directly
from "(μ_j^A)^N = (μ_{π(j)}^B · e^{iφ_j})^N for all large N."

**12-S4. One subtlety worth noting for Lean.** The linear independence
from Theorem 11.5 holds "for all sufficiently large N." The proof needs
a specific N₀ such that linear independence holds for all N ≥ N₀, then
picks two consecutive values N₀ and N₀+1. In Lean, this requires
extracting a witness N₀ from the "eventually" quantifier. This is
straightforward but should be noted.

### Theorem 12.6 (Equal-MPV FT, common block structure) — was v2 Thm 11.3

**Statement:** Identical to v2's Theorem 11.3, with g replacing r and
reference updated to Theorem 10.17 (from v2's 9.15).

**Correctness:** ✔. Same as v2.

**Proof:** "Since both families share the canonical form data, the BNT
separation condition is not needed. The canonical-form fundamental theorem
(Theorem 10.17) then applies directly..."

This replaces v2's "Forget the extra BNT-separation field and retain only
the underlying canonical-form data" — the recommended fix from the v2
review. ✔

**Positioning change:** In v2, this was the terminal theorem (Thm 11.3).
In v3, Theorem 12.5 (unconditional equal-MPV FT) is now the primary
result, and Theorem 12.6 is a specialization. This is the correct
ordering: the stronger result comes first, the specialization follows.
The relationship is clarified by Remark 12.7. ✔

### Remark 12.7 (Recovery of literature statement) — NEW

**Correctness:** ✔. The remark correctly states that Theorem 12.5
recovers [CPGSV21, Corollary IV.5] without assuming common block
structure, and that the weight matching uses BNT linear independence
rather than Newton–Girard.

The remark also correctly notes that Theorem 12.6 is the
"common-block-structure specialization" — this phrasing is flagged
as AI language but is tolerable in a remark (see 12-AI3).

---

## Section 12.4 — Periodic Fundamental Theorem (deferred)

This section (Definitions 12.8–12.9, Remarks 12.10/12.12/12.14/12.15,
Definition 12.11, Theorem 12.13) is entirely new in v3 and outlines the
[DlCCSPG17] irreducible form and periodic FT framework. It is **not on
the FT critical path** — the current formalization works exclusively with
period-1 blocks via the blocking approach.

**Quick flags (not full review):**

**12-P1. Definition 12.11 (Z-gauge equivalence).** The definition states
that a Z-gauge transformation satisfies [A^i, Z] = 0 for all i. The
claim that replacing A by ZA leaves the MPV invariant for N ≡ 0 (mod m)
uses tr(Z^N) = tr(𝟙) = D when Z^m = 𝟙 and m | N. However, this is only
valid if Z is *scalar* on each block of the block-diagonal decomposition
of A's bond space induced by the cyclic-sector structure. The definition
as stated (diagonal unitary with Z^m = 𝟙, commuting with all A^i)
implicitly relies on the cyclic-sector decomposition to ensure that the
Z entries are constant within each sector. This should be verified
against [DlCCSPG17, §II] before any formalization attempt.

**12-P2. Theorem 12.13 statement.** The conclusion includes both Y_j
(invertible intertwiner) and Z_j (Z-gauge transformation). The "global"
reformulation uses Y = ⊕_j Y_j ⊗ 𝟙_{r_j} and Z = ⊕_j Z_j ⊗ 𝟙_{r_j}.
The r_j notation appears without definition — it is presumably the
multiplicity of block j in some larger structure, but this is not
explained. This would need clarification before formalization.

**12-P3. Remark 12.14 comparison.** The comparison between the blocking
approach and the periodic approach is well-written and mathematically
informative. No issues.

**12-P4. Overall assessment.** Section 12.4 reads as a roadmap for future
formalization rather than a specification for current work. This is
appropriate given that the periodic FT requires substantial new
infrastructure (cyclic-sector decomposition, Z-gauge). The section should
be clearly marked as "future work" or "outline" in any formalization
planning document.

---

# Cross-Chapter Consistency

## Dependency chain verification (Sections 12.1–12.3)

Theorem 12.1 depends on:
- Theorem 12.4 (proportional FT, NT route) ← same chapter ✔

Theorem 12.2 depends on:
- Theorem 11.7 (BNT permutation, proportional) ← Chapter 11 ✔
- Theorem 11.4 (cross-overlap decay) ← Chapter 11 ✔

Theorem 12.4 depends on:
- Theorem 9.30 (self-overlap from primitivity) ← Chapter 9 ✔
- Theorem 9.31 (modulus-one eigenvalue rigidity) ← Chapter 9 ✔
- Remark 11.6 (normality gap) ← Chapter 11 ✔

Theorem 12.5 depends on:
- Theorem 12.2 (proportional FT) ← same chapter ✔
- Theorem 2.24 (MPV decomposition) ← Chapter 2 ✔
- Theorem 11.5 (CF-BNT yields BNT) ← Chapter 11 ✔
- Definition 11.1 (BNT definition) ← Chapter 11 ✔

Theorem 12.6 depends on:
- Theorem 10.17 (CF FT same-structure) ← Chapter 10 ✔

All dependency chains verified and acyclic. ✔

## Cross-chapter issues

**12-C1. Orphaned theorems — final status.**

| Theorem (v3 numbering) | Status |
|---|---|
| Thms 11.12–11.13 (Newton–Girard) | Orphaned. Not cited in Ch 12. Remark 11.14 acknowledges this. |
| Thm 11.10 (coefficient ratio decay) | Indirectly needed: Remark 12.3 explains coefficient instantiation, but does not cite 11.10. The instantiation a_{N,j} = μ_j^N does not require 11.10 (it comes directly from Thm 2.24). **Confirmed orphaned relative to Chapter 12.** |
| Thm 12.6 (common block structure FT) | Not orphaned (cited in Remark 12.7 as a specialization), but **not needed for the full FT** — Theorem 12.5 subsumes it. |

**12-C2. "Two meanings of normal" — inherited, unresolved.** The same
issue flagged in v3 Chapter 11 review (11-S5): Remark 11.6 presents
algebraic normality (Def 2.19) and the normal-canonical-form notion as
distinct, when they are equivalent under SPGWC10 Proposition 3. This
propagates to Theorem 12.4's proof, which cites Remark 11.6. No new
manifestation in Chapter 12 specifically.

**12-C3. Notation consistency.** g_A/g_B used throughout Chapter 12. ✔
Chapter 11 uses g_A/g_B in Theorem 11.7. ✔ Chapter 10 uses g in
Theorem 10.17. ✔ No g/r clash remains in the FT critical path.

---

# Literature Alignment

## [CPGSV21, Corollary IV.5] (Full equal-MPV FT)

v3's Theorem 12.5 now recovers this result unconditionally. The proof
route differs from the paper's (BNT linear independence instead of
Newton–Girard / Lemma A.5), but the conclusion is the same. Remark 12.7
makes the correspondence explicit. ✔

## [CPGSV21, Theorem IV.4] (Proportional FT)

v3's Theorem 12.2 corresponds to this result via the CF-BNT
specialization. ✔

## [CPGSV17] (Blocking approach)

The preamble correctly attributes the blocking-then-aperiodic strategy to
[CPGSV17]. The Section 12.4 comparison (Remark 12.14) correctly contrasts
this with [DlCCSPG17]. ✔

## [DlCCSPG17] (Periodic FT)

Section 12.4 outlines this framework. The citation "Theorem 3.8" for the
equal-case periodic FT and "Theorem 3.4" for the proportional case are
stated but not verified against the paper (which is not in the project
files). Flag for future verification if Section 12.4 is formalized.

---

# AI-Language Audit

## New AI language in v3 (not present in v2)

**12-AI1. Section 12.1 title and body.** ⚠️ **Severe.**

Title: "Weak Fundamental Theorem: pipeline end-to-end"

Body: "The following theorem packages the full upstream pipeline
(zero-block separation, TP gauge, blocking, primitivity) with the
downstream Fundamental Theorem for normal canonical form data. It is
conditional on the extra hypotheses (tensor irreducibility and distinct
weight norms) that the automatic pipeline does not yet produce."

Proof: "This packages the normal-canonical-form Fundamental Theorem
(Theorem 12.4)."

This is the most concentrated AI language in the entire blueprint.
"Pipeline," "upstream," "downstream," "packages," "automatic pipeline" —
five flagged terms in three sentences.

**Recommended replacement:**

Title: "Conditional Fundamental Theorem"

Body: "The following theorem combines the preceding results — zero-block
separation, trace-preserving normalization, blocking, and the primitivity
reduction — with the proportional Fundamental Theorem for normal canonical
form data. It requires two additional hypotheses (tensor irreducibility
and distinct weight norms) that are not currently derived from the
canonical form construction."

Proof: "Apply Theorem 12.4 to the normal canonical form data. The
non-degeneracy condition ensures..."

**12-AI2. Chapter title "Full Assembly."** Still present. Flagged in the
standing instructions (§4) and the v2 review (§7). No mathematician titles
a chapter "Full Assembly."

**Recommended replacement:** "Proof of the Fundamental Theorem" or
"The Fundamental Theorem of Matrix Product States."

**12-AI3. "common-block-structure specialization."** Appears in the
preamble and Remark 12.7. Flagged in the comprehensive reference Part II.
Tolerable in the remark context but should be "under the additional
assumption of common block structure" or similar in the preamble.

## AI language fixed from v2

- "states the assembled Fundamental Theorem results" → "proves the
  Fundamental Theorem of Matrix Product States" ✔
- "take explicit coefficient-convergence input" → removed ✔
- "Assume one is given coefficient arrays" → "Suppose there exist" ✔
- "equipped with CF-BNT families" → "in canonical form with BNT
  separation" ✔
- "Forget the extra BNT-separation field" → "Since both families share
  the canonical form data, the BNT separation condition is not needed" ✔

---

# Formalization Notes

## 12-F1. Theorem 12.5 proof: extracting N₀ from eventual linear independence

The proof uses "for all sufficiently large N" from Theorem 11.5. In Lean,
this is a `Filter.Eventually` statement. The proof needs to extract a
concrete N₀, then evaluate at N₀ and N₀+1 to get the weight matching.
Standard Lean tactic: `obtain ⟨N₀, hN₀⟩ := (h.eventually).exists`.

## 12-F2. Gauge-phase equivalence → gauge equivalence upgrade

Theorems 12.2/12.4 conclude gauge-phase equivalence (a Lean predicate
involving phases e^{iφ_j}). Theorem 12.5 upgrades to gauge equivalence
(no phases). The upgrade involves absorbing the phase into the weight.
These are distinct Lean predicates, and the upgrade step (from 12-S4
Step 7) needs an explicit term.

This was noted in the v2 review as formalization note 11-F2. Still
applies. ✔

## 12-F3. Theorem 12.1 — forward dependency in Lean

Theorem 12.1's proof invokes Theorem 12.4. In Lean, this means 12.1's
declaration must come after 12.4's, regardless of the blueprint's
presentation order. The formalization agent should reorder if needed.

## 12-F4. Permutation composition in Theorem 12.5

The final step composes the block-diagonal gauge X = ⊕_j X_j with the
permutation matrix of π to get global gauge equivalence. In Lean, this
requires the `BlockPermutation` infrastructure (documented at
`sirui-lu.com/TNLean`). The permutation matrix and the block-diagonal
gauge live at different type levels; their composition must be handled
carefully.

## 12-F5. Scope of Theorem 12.5 relative to the existence pipeline

Theorem 12.5 assumes CF-BNT data as input. The canonical form *existence*
pipeline (Chapter 9, culminating in Theorem 9.47) has two remaining gaps
identified in Remark 9.50:

1. Irreducibility of blocked blocks (blocking preserves primitivity but
   not obviously irreducibility; proposed resolution via Theorem 8.50:
   primitive + PosDef fixed point ⟹ irreducible).
2. Pairwise distinct weight norms (the blueprint's predicate Def 9.29 is
   stricter than the paper's CF; needs a predicate relaxation or BNT
   grouping step).

These gaps affect the fully unconditional theorem (Level B: arbitrary
tensor → FT), not the uniqueness theorem itself (Level A: tensors already
in CF → FT). Theorem 12.5 is complete at Level A, which matches the
paper's own standard ([CPGSV21, Corollary IV.5]).

See `formalization_goal_analysis.md` for the full analysis of Levels A
and B, the proposed resolutions for both gaps, and the recommendation
that Level A suffices for claiming the FT is formalized.

---

# Cleanup Checklist

## Must fix

1. **Rewrite §12.1 AI language.** The section title "pipeline end-to-end"
   and body text ("upstream pipeline," "downstream," "packages,"
   "automatic pipeline") must be replaced. See 12-AI1 for recommended
   text.

2. **Rename chapter.** "Full Assembly" → "Proof of the Fundamental
   Theorem" or "The Fundamental Theorem of Matrix Product States." See
   12-AI2.

3. **Clarify Theorem 12.1 non-degeneracy hypothesis.** Either explain
   why the non-degeneracy condition is needed (what step in the proof
   uses it) or remove it as redundant. See 12-S1.

## Should fix

4. **Rename Theorem 12.1.** "Weak Fundamental Theorem" is misleading.
   Use "Conditional Fundamental Theorem" or "Fundamental Theorem
   (with non-degeneracy hypothesis)." See 12-S2a.

5. **Replace "common-block-structure specialization" in the preamble.**
   See 12-AI3.

## Low priority

6. **Theorem 12.4 proof: make the BNT permutation step explicit.** The
   proof says "the same peeling argument as in the injective CF-BNT case."
   Could name the specific theorem used. See 12-S3.

7. **Section 12.4: clarify r_j notation in Theorem 12.13.** See 12-P2.

8. **Section 12.4: verify Definition 12.11 against [DlCCSPG17].** See
   12-P1.

## Acceptable as-is

9. **Overloaded coefficient hypotheses in Theorem 12.2.** Now explained
   by Remark 12.3. Acceptable for Lean compatibility.

10. **Newton–Girard orphan status.** Acknowledged by Remark 11.14 in
    Chapter 11. No further action needed in Chapter 12.

11. **Theorem 12.6 retained despite being subsumed by 12.5.** Acceptable
    as a named specialization; its proof via Theorem 10.17 is an
    independent route that may be useful for alternative formalizations.

---

# Final Assessment

Chapter 12 is the terminal chapter for the Fundamental Theorem, and v3
represents a major improvement over v2. The most important structural
change — the addition of Theorem 12.5 (unconditional equal-MPV FT via
BNT linear independence) — closes the scope gap identified in the v2
review and verified in `full_ft_verification.md`. The proof is correct
and matches our verified argument exactly.

The chapter now provides a complete proof chain for [CPGSV21, Corollary
IV.5]:

  Theorem 12.2 (proportional FT) + Theorem 11.5 (BNT linear independence)
  → Theorem 12.5 (unconditional equal-MPV FT) → full gauge equivalence.

The main outstanding issues are:

1. **§12.1 AI language** — the most concentrated instance in the entire
   blueprint. Must be rewritten before the document can be considered
   a mathematical text.

2. **Theorem 12.1's non-degeneracy hypothesis** — needs clarification
   of its role. It may be a genuine requirement for packaging the normal
   canonical form route, or it may be redundant.

3. **Chapter title** — "Full Assembly" remains.

4. **Section 12.4** — a new outline of the periodic FT framework from
   [DlCCSPG17]. Not on the FT critical path. Contains two minor issues
   (r_j notation, Z-gauge definition) that should be resolved before any
   formalization attempt.

After the three "must fix" items are addressed, Chapter 12 would be a
clean, complete proof of the Fundamental Theorem of Matrix Product States,
suitable for Lean formalization.

**Scope clarification.** Theorem 12.5 proves the FT at the paper's own
level of generality (Level A: tensors already in canonical form). The
fully unconditional theorem (Level B: from arbitrary tensors) additionally
requires closing two gaps in the CF existence pipeline (Remark 9.50), as
documented in `formalization_goal_analysis.md`. These upstream gaps do not
affect the correctness or completeness of Chapter 12 itself.
