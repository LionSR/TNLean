
# Blueprint Review — Chapter 6 (Perron–Frobenius Theory), v2 → v3

This document reviews Chapter 6 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter5_review.md`, `blueprint_chapters2to6_review_consolidated.md`,
`blueprint_review_comprehensive_reference.md`).

---

## Chapter numbering map

v3 Chapter 6 = v2 Chapter 5 (Perron–Frobenius Theory for Channels and
Transfer Maps). The chapter is renumbered +1 due to the new Chapter 5
(Schwarz Inequalities) inserted in v3.

| v2 | v3 | Content | Change |
|---|---|---|---|
| Remark 5.1 | Remark 6.1 | Ordering justification | Renumbered only |
| Thm 5.2 | Thm 6.2 | PSD → PD (injective) | Renumbered only |
| Thm 5.3 | Thm 6.3 | PSD → PD (irreducible) | Renumbered; ref updated (Def 4.23 → 4.12) |
| Thm 5.4 | Thm 6.4 | Orthogonal trace condition | Renumbered only |
| Thm 5.5 | Thm 6.5 | Uniqueness of PSD fixed point | Renumbered only |
| Remark 5.6 | Remark 6.6 | c₀ > 0 | Renumbered only |
| Thm 5.7 | Thm 6.7 | Uniqueness of positive eigenvalue | Renumbered; internal refs updated |
| Thm 5.8 | Thm 6.8 | Existence of PSD fixed point | Renumbered; refs updated (4.26→4.15, 4.30→4.19) |
| Thm 5.9 | Thm 6.9 | Quantum Perron–Frobenius | Renumbered only |
| Thm 5.10 | Thm 6.10 | Right-canonical gauge | Renumbered only |
| Thm 5.11 | Thm 6.11 | Left-canonical gauge | Renumbered only |
| Remark 5.12 | Remark 6.12 | Gauges are different | Renumbered only |
| Lemma 5.13 | Lemma 6.13 | Similarity preserves irreducibility | Renumbered only |
| Thm 5.14 | Thm 6.14 | Scaling preserves irreducibility | Renumbered only |
| Thm 5.15 | Thm 6.15 | PSD eigenvector for positive maps | Renumbered only |
| Thm 5.16 | Thm 6.16 | Adjoint transfer map is nonzero | Renumbered only |
| Thm 5.17 | Thm 6.17 | PosDef adjoint eigenvector | Renumbered only |
| Thm 5.18 | Thm 6.18 | TP-gauge existence | Renumbered only |
| — | Thm 6.19 | Exponential truncation is PD | **New** |
| — | Thm 6.20 | Exponential positivity | **New** |
| — | Thm 6.21 | Unique density-matrix fixed point | **New** |
| — | Thm 6.22 | Cesàro convergence | **New** |
| — | Thm 6.23 | Spectral radius = Perron eigenvalue | **New** |
| — | Thm 6.24 | Real spectral-radius identity | **New** |
| — | Def 6.25 | Wolf spectral properties | **New** |
| — | Thm 6.26 | Irreducibility → spectral properties | **New** |
| — | Thm 6.27 | Spectral properties → irreducibility | **New** |
| — | Thm 6.28 | Irreducibility ↔ spectral properties | **New** |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Good. Follows [Wol12, Ch. 6] throughout. New sections correctly attributed. |
| Internal consistency | Good. All internal references updated for v3 numbering. |
| v2 → v3 changes | Renumbering +1; new §§6.7–6.10 (exponential positivity, ergodicity, spectral radius, spectral characterization). |
| AI language | One inherited item: §6.3 title "Existence and assembly." |
| Formalization readiness | Good. One compressed proof (Thm 6.17) carried over from v2. |
| Open items from prior review | All corrected in v2; confirmed still resolved in v3. |

---

# v2 → v3 Changes

## Retained content (renumbered, §§6.1–6.6)

Sections 6.1–6.6 (Thms 6.2–6.18, Lemma 6.13, Remarks 6.1/6.6/6.12)
are **verbatim identical** to v2 §§5.1–5.6 (Thms 5.2–5.18) modulo:

1. Theorem/definition numbers incremented by 1.
2. Internal cross-references updated: Definition 4.23 → 4.12
   (irreducibility), Theorem 4.26 → 4.15 (transfer map is channel),
   Theorem 4.30 → 4.19 (Cesàro fixed point). All verified correct.

No substantive text changes in the retained material.

## New content (§§6.7–6.10)

**§6.7: Exponential positivity for irreducible CP maps (Thms 6.19–6.20).**
Theorem 6.19 establishes that the truncated exponential
∑_{k=0}^{D−1} (t^k/k!) E^k(A) is positive definite for irreducible E,
nonzero PSD A, and t > 0. This is [Wol12, Thm. 6.2, item (3)].
Theorem 6.20 extends to the full exponential series.

**§6.8: Ergodicity of irreducible channels (Thms 6.21–6.22).**
Theorem 6.21 (unique density-matrix fixed point for irreducible
channels) is [Wol12, Cor. 6.3]. Theorem 6.22 (Cesàro convergence to
the unique fixed point) is the ergodic corollary.

**§6.9: Spectral radius at the Perron eigenvalue (Thms 6.23–6.24).**
Theorem 6.23 identifies the spectral radius of an irreducible CP map
with its Perron eigenvalue. This is [Wol12, Thm. 6.3, item (4)].
Theorem 6.24 is the real-valued reformulation.

**§6.10: Spectral characterization of irreducibility (Def 6.25,
Thms 6.26–6.28).** The bidirectional equivalence between irreducibility
and Wolf's spectral properties package. This is [Wol12, Thm. 6.4].

## FT critical path assessment

The core results (Thms 6.2–6.11, 6.15) are firmly on the FT critical
path — used in Chapters 7, 9, 10, 12. Specifically:

- Thm 6.3 (PSD→PD, irreducible): used in Ch 4 §4.5.2, Ch 9, Ch 10
- Thm 6.5 (uniqueness): used in Ch 10, Ch 12
- Thm 6.9 (quantum PF): used in Ch 7 (Thm 7.12), Ch 10
- Thm 6.10 (right-canonical gauge): used in Ch 7 (Thm 7.12), Ch 10
- Thm 6.15 (PSD eigenvector, positive maps): used in Ch 9

The new §§6.7–6.10 content: Thms 6.19–6.20 (exponential positivity)
support Chapter 13 (dynamical semigroups) and are **not on the FT
critical path**. Thms 6.21–6.22 (ergodicity) provide background but
are not directly invoked on the FT path. Thms 6.23–6.28 (spectral
radius and spectral characterization) may support the canonical form
chapters but no explicit forward references to them were found in the
FT chain — they appear to be completeness results rounding out the
Wolf Ch. 6 coverage.

---

# Review Items: Prior Status Check

## From blueprint_chapter5_review.md (v2 review, v1 numbering)

| # | Item (v1/v2 description) | Status in v2 | Status in v3 |
|---|---|---|---|
| 1 | Swap Thms 5.1/5.2 (irreducible first) | ✅ v2 kept injective first with justification (Remark 5.1/6.1) | ✅ Unchanged. |
| 2 | Uniqueness scalar c → c > 0 | ✅ Remark 5.6/6.6 clarifies c₀ > 0 | ✅ Unchanged. |
| 3 | Remove injectivity from existence theorem | ✅ v2 Thm 5.8/6.8 does not assume injectivity | ✅ Unchanged. |
| 4 | Remove/demote D = 0 theorem | ✅ Removed in v2 | ✅ Still removed. |
| 5 | Rename "Doubly stochastic gauge" | ✅ v2: "Right- and left-canonical gauges" (§5.4/6.4) | ✅ Unchanged. |
| 6 | Add remark that gauges are different transforms | ✅ Remark 5.12/6.12 | ✅ Unchanged. |

## From consolidated review

| # | Item | Status in v3 |
|---|---|---|
| 5-A | Thm 5.5/6.5: scalar c ∈ ℂ (should be c > 0) | ✅ Handled by Remark 6.6 (c₀ > 0). Acceptable. |
| 5-C | Thm 5.17/6.17: irreducibility transfer to adjoint compressed | ❌ **Still compressed.** See statement-by-statement analysis below. |

## From comprehensive reference

| # | Item | Status in v3 |
|---|---|---|
| Part II | §5.3/6.3 title "Existence and assembly" | ❌ **Unchanged.** "Assembly" is flagged AI language. |
| 5-F1 | Three results, three hypotheses | ✅ Explicit throughout (Thms 6.2/6.3 for PD, Thm 6.8 for existence, Thm 6.5 for uniqueness). |
| 5-F2 | Injective → irreducible coercion | ✅ Thm 6.2 (injective) and Thm 6.3 (irreducible) are separate; coercion via Thm 4.13 (injectivity → irreducibility). |

---

# Forward Reference Verification

All forward references from Chapter 6 checked against v3 PDF:

| Reference | Target | Status |
|---|---|---|
| Thm 6.2 proof → injectivity span | {A_i} span M_D(ℂ) | ✅ Standard injectivity. |
| Thm 6.3 → Definition 4.12 | Irreducible map | ✅ Correct (was 4.23 in v2, renumbered). |
| Thm 6.7 → Theorem 6.15 | PSD eigenvector existence | ✅ Internal forward ref, correct. |
| Thm 6.7 → Theorem 6.3 | PSD→PD upgrade | ✅ Internal, correct. |
| Thm 6.8 → Theorem 4.15 | Transfer map is channel | ✅ (Was 4.26 in v2, renumbered.) |
| Thm 6.8 → Theorem 4.19 | Cesàro fixed point | ✅ (Was 4.30 in v2, renumbered.) |
| Thm 6.17 → Thm 6.16 | Adjoint nonzero | ✅ Internal. |
| Thm 6.17 → Thm 6.15 | PSD eigenvector | ✅ Internal. |
| Thm 6.17 → Thm 6.14 | Scaling preserves irred. | ✅ Internal. |
| Thm 6.17 → Thm 6.3 | PSD→PD upgrade | ✅ Internal. |
| Thm 6.18 → Thm 6.17 | PosDef adjoint eigenvector | ✅ Internal. |
| Thm 6.18 → Thm 6.11 | TP gauge | ✅ Internal. |

References *to* Chapter 6 from later chapters (verified):

| Source | Target | Status |
|---|---|---|
| Lemma 4.33 (Ch 4) → Thm 6.3 | PSD→PD for irreducible | ✅ Cited by number. |
| Thm 7.12 (Ch 7) → Thms 6.9, 6.10 | PF + right-canonical gauge | ✅ Cited by number. |
| Ch 9 → Thm 6.15 | PSD eigenvector for positive maps | ✅ Cited by number. |
| Ch 10 → Thms 6.3, 6.5, 6.8, 6.9, 6.10 | Multiple PF results | ✅ All cited by number. |

---

# Statement-by-Statement Analysis

## §6.1: Positive definiteness (Thms 6.2–6.4)

### Remark 6.1

Unchanged from v2. Correctly explains ordering choice (injective first
as warm-up).

### Theorem 6.2 (PSD → PD, injective)

Unchanged. Correct. Direct kernel argument using injectivity
(span{A_i} = M_D).

### Theorem 6.3 (PSD → PD, irreducible)

Unchanged modulo reference update (Def 4.23 → 4.12). Correct.
Support-projection argument via [Wol12, Thm. 6.2].

### Theorem 6.4 (Orthogonal trace condition)

Unchanged. Correct. Uses the growth theorem (𝟙 + E)^{D−1}(A) > 0
and binomial expansion. This is [Wol12, Thm. 6.2, item 4].

## §6.2: Uniqueness (Thms 6.5–6.7)

### Theorem 6.5 (Uniqueness of PSD fixed point)

Unchanged. Correct. Minimal-eigenvalue subtraction argument.

**Inherited item 5-A:** The statement says σ = cρ for "some c ∈ ℂ."
Remark 6.6 clarifies c₀ > 0. The statement could be tightened to
c ∈ ℝ_{>0}, but the remark handles it. Acceptable.

### Remark 6.6

Unchanged. Correctly notes c₀ > 0.

### Theorem 6.7 (Uniqueness of positive eigenvalue)

Unchanged modulo internal reference updates. Correct. Dual-map trace
argument following [Wol12, Thm. 6.3, item 3].

## §6.3: Existence and assembly (Thms 6.8–6.9)

### Theorem 6.8 (Existence of PSD fixed point)

Unchanged modulo reference updates (4.26→4.15, 4.30→4.19). Correct.
Does not assume injectivity (resolves v1 issue).

### Theorem 6.9 (Quantum Perron–Frobenius)

Unchanged. Correct. Combines Thms 6.8 + 6.2 + 6.5.

**AI language:** The section title "Existence and assembly" uses
"assembly." Should be "Existence and the Perron–Frobenius theorem"
or similar.

## §6.4: Right- and left-canonical gauges (Thms 6.10–6.11, Remark 6.12)

All three unchanged. Correct. Remark 6.12 explicitly states gauges
are different transforms (resolves v1 DS-gauge issue).

## §6.5: Similarity preserves irreducibility (Lemma 6.13, Thm 6.14)

Both unchanged. Correct.

## §6.6: Perron–Frobenius eigenvector existence (Thms 6.15–6.18)

All four unchanged modulo reference updates. Correct.

**Inherited item 5-C (Thm 6.17 proof):** The proof says "Irreducibility
of A transfers to the adjoint transfer map." This step is still
compressed. The argument is: if ℰ†_A has a nontrivial invariant
projection P, then taking the adjoint shows (𝟙−P) is invariant for
ℰ_A, contradicting irreducibility. For Lean, this needs to be a
separate lemma (e.g., "irreducibility transfers to the adjoint CP
map"). **Still open from v2.**

## §6.7: Exponential positivity (Thms 6.19–6.20) — **NEW**

### Theorem 6.19 (Exponential truncation is positive definite)

**New in v3.** Correct. The argument: if v annihilates
∑_{k=0}^{D−1} (t^k/k!) E^k(A), then each E^k(A) annihilates v
(since all terms are PSD), contradicting (𝟙 + E)^{D−1}(A) > 0.

**Subtlety:** The proof invokes "the growth theorem for irreducible
CP maps" without citing a specific theorem number. This is the
content of [Wol12, Thm. 6.2, item (2)], which gives
(𝟙 + E)^{D−1}(A) > 0 for irreducible E and nonzero PSD A. This
fact is not stated as a standalone theorem in the blueprint. It is
implicitly used in the proof of Theorem 6.4 (orthogonal trace
condition), but should be either stated explicitly or cited to
Thm 6.4's proof.

### Theorem 6.20 (Exponential positivity, full series)

**New in v3.** Correct. Adds PSD tail to the PD truncation from
Thm 6.19.

## §6.8: Ergodicity of irreducible channels (Thms 6.21–6.22) — **NEW**

### Theorem 6.21 (Unique density-matrix fixed point)

**New in v3.** Correct. This is [Wol12, Cor. 6.3]. The proof combines
Cesàro compactness, irreducible PD upgrade, and uniqueness.

### Theorem 6.22 (Cesàro convergence)

**New in v3.** Correct. Standard subsequential-limit uniqueness
argument.

## §6.9: Spectral radius (Thms 6.23–6.24) — **NEW**

### Theorem 6.23 (Spectral radius = Perron eigenvalue)

**New in v3.** Correct. This is [Wol12, Thm. 6.3, item (4)].

**Proof is compressed.** The proof says "gauge by its square root, and
rescale by r^{−1}. The resulting map is trace-preserving and has a
positive definite fixed point, so its spectral radius is 1." The step
"TP with PD fixed point implies spectral radius 1" is not trivial —
it uses the fact that a TP map has all eigenvalues satisfying |λ| ≤ 1
(spectral radius ≤ 1, from the Russo–Dye theorem or direct trace
argument), combined with the existence of eigenvalue 1 (from the PD
fixed point). For Lean, this needs to be spelled out or cited.

### Theorem 6.24 (Real spectral-radius identity)

**New in v3.** Trivial reformulation of Thm 6.23. Correct.

## §6.10: Spectral characterization of irreducibility (Def 6.25, Thms 6.26–6.28) — **NEW**

### Definition 6.25 (Wolf spectral properties)

**New in v3.** Packages four properties: PD right eigenvector, PD left
eigenvector, uniqueness up to scaling, spectral radius = eigenvalue.
This is the predicate from [Wol12, Thm. 6.4].

### Theorem 6.26 (Irreducibility → spectral properties)

**New in v3.** Correct. Combines the chapter's results.

### Theorem 6.27 (Spectral properties → irreducibility)

**New in v3.** Correct. The proof sketch is adequate: gauge to TP,
use Cesàro in corner algebra to produce a second fixed point,
contradiction.

### Theorem 6.28 (Equivalence)

**New in v3.** Correct. Combines Thms 6.26 and 6.27. This is
[Wol12, Thm. 6.4].

---

# Cross-Chapter Consistency

## References from Chapter 6

| Reference | Target | Status |
|---|---|---|
| Thm 6.3 → Def 4.12 | Irreducible map | ✅ |
| Thm 6.8 → Thm 4.15 | Transfer map is channel | ✅ |
| Thm 6.8 → Thm 4.19 | Cesàro fixed point | ✅ |

## Chapter title

The v3 chapter title is "Perron–Frobenius Theory for Channels and
Transfer Maps." The v2 title was "Perron–Frobenius Theory for Channels
and Transfer Maps." Unchanged.

The v3 chapter preamble is expanded to mention the new content:
"ergodicity of irreducible channels, the spectral-radius identification
of Perron eigenvalues, and Wolf's spectral characterization of
irreducibility." This accurately describes the new sections.

---

# Literature Alignment

| Blueprint | Wolf | Match |
|---|---|---|
| Thm 6.2 | [Wol12, Thm. 6.3, item 2] (injective shortcut) | ✅ |
| Thm 6.3 | [Wol12, Thm. 6.2, condition (1)] | ✅ |
| Thm 6.4 | [Wol12, Thm. 6.2, item 4] | ✅ |
| Thm 6.5 | [Wol12, Thm. 6.3, item 2] | ✅ |
| Thm 6.7 | [Wol12, Thm. 6.3, item 3] | ✅ |
| Thm 6.15 | [Wol12, Thm. 6.5] / [EHK78] | ✅ |
| Thm 6.19 | [Wol12, Thm. 6.2, item (3)] | ✅ |
| Thm 6.21 | [Wol12, Cor. 6.3] | ✅ |
| Thm 6.23 | [Wol12, Thm. 6.3, item (4)] | ✅ |
| Thm 6.28 | [Wol12, Thm. 6.4] | ✅ |

No deviations from the literature.

---

# AI-Language Audit

## From comprehensive reference Part II

| Pattern | Location | Status in v3 | Recommended fix |
|---|---|---|---|
| "Assembly" | §6.3 title "Existence and assembly" | ❌ **Unchanged** | → "Existence and the Perron–Frobenius theorem" |

## New items in v3 Chapter 6

No new AI-language issues. The new sections (§§6.7–6.10) use standard
mathematical language throughout.

---

# Formalization Notes

## From comprehensive reference Part IV

| # | Note | Status in v3 |
|---|---|---|
| 5-F1 | Three results, three hypotheses (PSD existence, PD upgrade, uniqueness) | ✅ Explicit. Thms 6.8 (TP), 6.2/6.3 (injective/irreducible), 6.5 (injective). |
| 5-F2 | Injective → irreducible coercion via Thm 4.13 | ✅ Thm 4.13 (v3) is injectivity → irreducibility. |

## New formalization notes for Chapter 6

**6-F1. Thm 6.17: irreducibility transfer to adjoint needs a lemma.**
The statement "Irreducibility of A transfers to the adjoint transfer
map" is used without proof. For Lean, this is a separate lemma:
if E is irreducible and E†(X) = ∑ K_i† X K_i, then E† is also
irreducible. Proof: if P is invariant for E†, then (𝟙−P) is invariant
for E, so P ∈ {0, 𝟙}. (Inherited from v2 item 5-C.)

**6-F2. Thm 6.19: growth theorem not stated as standalone result.**
The proof invokes "(𝟙 + E)^{D−1}(A) > 0 for irreducible E" without
citing a theorem number. This growth condition is the content of
[Wol12, Thm. 6.2, item (2)]. It appears in the proof of Thm 6.4 but
is not stated as a named result. For Lean, it should be a standalone
lemma.

**6-F3. Thm 6.23: spectral radius ≤ 1 for TP maps.** The proof
assumes that a TP map has spectral radius ≤ 1. This standard fact
(every eigenvalue λ of a TP map satisfies |λ| ≤ 1) needs to be stated
or cited. It follows from tr(E^n(X)) = tr(X), which bounds the growth
of E^n.

**6-F4. Thm 6.27: Cesàro averaging in a corner algebra.** The proof
says a nontrivial invariant projection produces "by Cesàro averaging in
its corner algebra, a second positive semidefinite fixed point not
proportional to the Perron vector." For Lean, this requires:
(a) restricting the channel to the corner P·M_D·P,
(b) applying the Cesàro fixed-point theorem in the restricted space,
(c) showing the resulting fixed point is not proportional to ρ.
Each step needs explicit types.

---

# Cleanup Checklist

## Must fix

1. **§6.3 title: "Existence and assembly" → "Existence and the
   Perron–Frobenius theorem."** "Assembly" is AI language (flagged in
   comprehensive reference Part II).

## Should fix

2. **Thm 6.17: add explicit lemma for irreducibility transfer to
   adjoint.** Currently compressed. Needed for Lean. (Inherited
   item 5-C, still open.)

3. **Thm 6.19: cite or state the growth theorem as a standalone
   result.** The proof uses (𝟙 + E)^{D−1}(A) > 0 without a theorem
   number. Either add a theorem (e.g., "Theorem 6.X: Growth theorem
   for irreducible CP maps") or add an explicit citation to Thm 6.4's
   proof.

4. **Thm 6.23: state that TP maps have spectral radius ≤ 1.** This
   is used in the proof but not established in the blueprint.

## Low priority

5. **Thm 6.5: tighten c ∈ ℂ to c ∈ ℝ_{>0} in the statement.**
   Remark 6.6 handles this, so it is not strictly necessary.

6. **Thm 6.24 is a trivial reformulation of Thm 6.23.** Could be
   merged as a corollary. Acceptable as-is for Lean (named lemma).

## Acceptable as-is

7. **New §§6.7–6.10 content.** Mathematically correct and well-
   attributed to Wolf. §6.7 (exponential positivity) supports Ch 13,
   not the FT. §§6.8–6.10 round out the Perron–Frobenius theory.

8. **Remark 6.1 ordering justification.** Keeping injective before
   irreducible is justified and unchanged.

9. **Remark 6.12 on separate gauges.** Clear and correct.

---

# Final Assessment

Chapter 6 is mathematically sound. The retained content (§§6.1–6.6,
Thms 6.2–6.18) is verbatim identical to v2 modulo renumbering, and the
v2 review confirmed its correctness. All v1 issues were resolved in v2
and remain resolved.

The new content (§§6.7–6.10, Thms 6.19–6.28) correctly extends the
Perron–Frobenius coverage to match [Wol12, Ch. 6] more completely.
Exponential positivity (§6.7) supports Chapter 13 (dynamical
semigroups); ergodicity (§6.8) and the spectral characterization
(§§6.9–6.10) complete the Wolf treatment.

The main issues are:

- One AI-language item (§6.3 "assembly" in section title — must fix).
- Two compressed proofs needing explicit Lean lemmas (Thm 6.17
  irreducibility transfer, Thm 6.23 spectral radius bound — should fix).
- One unstated intermediate result (growth theorem for Thm 6.19 — should fix).

**No mathematical errors found. One "must fix" (AI language), three
"should fix" (compressed proofs and missing lemma for formalization).**
