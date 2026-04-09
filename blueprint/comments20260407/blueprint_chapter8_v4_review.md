# Blueprint Review — Chapter 8 (Perron–Frobenius Theory), v3 → v4

**Date:** April 8, 2026
**v3 counterpart:** Chapter 6
**Number mapping:** v3 6.x → v4 8.x (offset +2)

---

## v3 → v4 Changes

### Prior issues resolved

| v3 issue | v4 status |
|---|---|
| §6.3 title "Existence and assembly" (AI language) | ✅ **Fixed.** Now §8.3 "Existence and the Perron–Frobenius theorem." |
| Thm 6.17 irreducibility transfer to adjoint compressed | ⚠ **Partially improved.** See Thm 8.17 analysis below. |

### New content

**C8-1. §8.6 section header expanded.**
v3 §6.6 "Perron–Frobenius eigenvector existence" → v4 §8.6 same title but with a new section preamble (lines 1968–1972) explicitly citing Wolf Thm 6.5, [EHK78], and the [CPGSV17a] TP-gauge application. ✅ Helpful orientation.

**C8-2. No new theorems, definitions, or lemmas.**
v4 Ch 8 has exactly the same theorem set as v3 Ch 6 (renumbered 6.x → 8.x). The only changes are renumbering, the §8.3 title fix, and the §8.6 preamble.

### Unchanged content

All theorem statements, proofs, and remarks are verbatim identical to v3, modulo:
- Renumbering 6.x → 8.x.
- Internal cross-references updated (e.g., Def 4.12 → Def 5.12 for irreducibility, Thm 4.15 → Thm 5.15 for channel, Thm 4.19 → Thm 5.19 for Cesàro).

Verified by full text comparison. ✅

---

## Statement-by-statement verification of key theorems

Since the content is unchanged from v3 (which was itself verified), I focus on the items flagged in the v3 review that are still open.

### Thm 8.17 (PosDef adjoint eigenvector) — irreducibility transfer

The v3 review flagged the claim "irreducibility of ℰ_A transfers to the adjoint transfer map" as compressed. The v4 proof now includes the parenthetical: "if ℰ†_A had a nontrivial invariant projection P, then taking adjoints would show that 𝟙−P is invariant for ℰ_A, contradicting irreducibility of ℰ_A."

**Verification**: The claim is that for a CP map E with Kraus operators {K_i}, E is irreducible iff E† is irreducible. This is standard (Wolf [Wol12, after Thm 6.2]) but the proof is not trivial. The argument: P invariant for E means (𝟙−P)K_i P = 0 for all i (from the Kraus-level characterization). Taking adjoints: P K†_i (𝟙−P) = 0 for all i. This means (𝟙−P) is an invariant projection for E† (since E†(X) = Σ K†_i X K_i, and (𝟙−P) K†_i X K_i (𝟙−P) requires PK†_i(𝟙−P) = 0 to vanish...).

Actually, wait. The Kraus-level characterization of invariant projections is: P is invariant for E(X) = Σ K_i X K†_i iff (𝟙−P)K_i P = 0 for all i. For E†(X) = Σ K†_i X K_i, P is invariant iff (𝟙−P)K†_i P = 0 for all i. Conjugating (𝟙−P)K_i P = 0 gives P K†_i (𝟙−P) = 0, which is the same as (𝟙−P)K†_i P = 0 only if P = 𝟙−P... no, that's not right.

Let me be more careful. (𝟙−P)K_i P = 0 ⟹ taking adjoint: P K†_i (𝟙−P) = 0. This says (𝟙−P) is invariant for E†, NOT that P is invariant for E†. So: P invariant for E ⟺ (𝟙−P) invariant for E†. Hence E irreducible (no nontrivial invariant P) ⟺ E† irreducible (no nontrivial invariant Q, since Q = 𝟙−P). ✅

**The parenthetical in the proof is correct but terse.** For Lean, the intermediate step "(𝟙−P)K_i P = 0 ⟹ P K†_i(𝟙−P) = 0" should be a lemma. The v4 text is an improvement over v3 (which had no argument at all), but still compressed.

**⚠ Should add**: an explicit lemma stating that for Kraus maps, P invariant for E ⟺ (𝟙−P) invariant for E†. This would make the irreducibility transfer clean for Lean.

### Thm 8.3 (PSD → PD, irreducible version)

**Verified ✅**: The support-projection argument is correct. If ρ has nontrivial kernel, let Q = support projection. The fixed-point equation ℰ_A(ρ) = ρ implies Q is invariant for ℰ_A. Irreducibility forces Q = 0 or Q = 𝟙. Q = 0 contradicts ρ ≠ 0; Q = 𝟙 contradicts ρ not PD.

**⚠ The step "Q is invariant for ℰ_A"** is correct but compressed. It uses: ℰ_A(ρ) = ρ, ρ = QρQ (support), and each summand A^i ρ (A^i)† is PSD with support contained in range(A^i Q). The claim is that range(ℰ_A(QXQ)) ⊆ range(Q), i.e., (𝟙−Q)A^i QXQ(A^i)†(𝟙−Q) = 0, which uses (𝟙−Q)A^i Q... this follows from the stronger statement that ker(ρ) is invariant under all (A^i)†, which is proved in the proof of Thm 8.2. ✅

### Thm 8.7 (Uniqueness of positive eigenvalue, irreducible CP)

**Verified ✅**: The dual-map trace argument is correct: s·tr(τX) = tr(τ·E(X)) = tr(E†(τ)·X) = t·tr(τX), and τ > 0, X ≥ 0 nonzero ⟹ tr(τX) > 0 ⟹ s = t.

### Thm 8.23 (Spectral radius = Perron eigenvalue)

**Verified ✅**: Gauge by adjoint eigenvector, rescale. The resulting map is TP with PD fixed point. Spectral radius of TP map is ≤ 1 (from tr(E^n(X)) = tr(X) bounding growth). Fixed point at eigenvalue 1 gives spectral radius = 1. Undo similarity + rescaling.

### Thm 8.27 (Spectral properties ⟹ irreducibility)

**Verified ✅**: A nontrivial invariant projection would, via Cesàro averaging in the corner, produce a second PSD fixed point at eigenvalue r not proportional to ρ, contradicting uniqueness.

---

## AI-language audit

| # | Location | Text | Status |
|---|---|---|---|
| (v3) §6.3 "Existence and assembly" | §8.3 | "Existence and the Perron–Frobenius theorem" | ✅ **Fixed** |
| No new AI language items | | | ✅ |

---

## Cleanup checklist

| Priority | Item |
|---|---|
| **Should fix** | Thm 8.17: Add explicit lemma for Kraus-map invariant-projection duality (P inv for E ⟺ 𝟙−P inv for E†) |
| Verified ✅ | All theorems 8.2–8.28: statements and proofs correct |
| Verified ✅ | §8.3 title AI-language fix |
| Verified ✅ | All cross-references updated correctly |

---

## Assessment

Chapter 8 is essentially unchanged from v3 Chapter 6 — renumbering only, with one AI-language fix (§8.3 title) and an expanded §8.6 preamble. The only substantive open item from the v3 review — the compressed irreducibility transfer to the adjoint in Thm 8.17 — is partially improved (now includes a parenthetical argument) but should be extracted as a standalone lemma for Lean. No new content, no new errors, no mathematical issues.
