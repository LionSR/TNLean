
# Blueprint Review — Chapter 10 (Block Permutation and Separation), v2 → v3

This document reviews Chapter 10 of `blueprintv3.pdf` (March 16, 2026)
against `blueprint__v2.pdf` (March 14, 2026) and the prior review files
(`blueprint_chapter9_review.md`, `blueprint_review_comprehensive_reference.md`).

---

## Chapter numbering map

v3 Chapter 10 = v2 Chapter 9 (Block Permutation and Separation). The chapter
is renumbered +1 due to the new Chapter 5 (Schwarz Inequalities) inserted
in v3.

v3 has 18 numbered statements (10.1–10.18) vs v2's 15 (9.1–9.15).
The 3 new items are: Remark 10.2 (ring vs algebra levels), Remark 10.10
(normalization convention), and Remark 10.18 (relation to the literature).

| v2 | v3 | Content | Change |
|---|---|---|---|
| Thm 9.1 | Thm 10.1 | Ring isos permute block ideals | Renumbered; **arrow notation dropped** |
| — | Remark 10.2 | Ring vs algebra level | **New** |
| Thm 9.2 | Thm 10.3 | Dimension preservation | Renumbered |
| Thm 9.3 | Thm 10.4 | Automorphism decomposition | Renumbered; **proof expanded** |
| Def 9.4 | Def 10.5 | Per-block linear extension | Renumbered |
| Def 9.5 | Def 10.6 | Product algebra automorphism | Renumbered; **reclassified** |
| Thm 9.6 | Thm 10.7 | Per-block extensions assemble | Renumbered; **trivial permutation clarified** |
| Thm 9.7 | Thm 10.8 | Per-block same MPV → global gauge equiv | Renumbered; **ref updated (8.4→9.4)** |
| Def 9.8 | Def 10.9 | Canonical form predicate | Renumbered |
| Remark 9.9 | Remark 10.11 | Overlap redundancy | Renumbered; **ref updated (8.24→9.25)** |
| — | Remark 10.10 | Normalization convention | **New** |
| Remark 9.10 | Remark 10.12 | Normal-canonical companion | Renumbered; **refs updated (8.28→9.29, 8.29→9.30)** |
| Thm 9.11 | Thm 10.13 | Vandermonde separation | Renumbered |
| Lemma 9.12 | Lemma 10.14 | Block separation core | Renumbered; **proof expanded; citation corrected** |
| Thm 9.13 | Thm 10.15 | Block separation (CF) | Renumbered |
| Thm 9.14 | Thm 10.16 | Block separation (normal CF) | Renumbered; **refs updated (8.29→9.30, 8.30→9.31)** |
| Thm 9.15 | Thm 10.17 | CF FT, same-structure version | Renumbered; **refs updated (9.7→10.8)** |
| — | Remark 10.18 | Relation to the literature | **New** |

---

# Global Chapter Assessment

| Criterion | Status |
|---|---|
| Literature alignment | Improved. Chapter header now honestly distinguishes results from proof technique. |
| Internal consistency | Good. All internal references correctly updated for v3 numbering. |
| v2 → v3 changes | Moderate: 3 new remarks, 1 proof expansion, 1 citation correction, several ref updates. |
| AI language | Clean. "Pi-algebra" title renamed to "Product algebra." |
| Formalization readiness | Improved. Ring/algebra distinction documented. Some proof-text gaps remain (see 10-S2, 10-S4). |
| Open items from prior review | Mostly addressed. See Prior Review Items below. |
| FT critical path | **Yes.** Theorems 10.15, 10.16, and 10.17 are load-bearing for the full FT. |
| **New issues** | **Lemma 10.14: imprecise decay attribution (10-S2), missing D matching step (10-S4). Thm 10.16: compressed proof hides hypothesis change (10-S3). Verified against web blueprint.** |

---

# v2 → v3 Changes — Substantive

## 1. Chapter header: literature-deviation acknowledgment restored (NEW: Remark 10.18)

v2's chapter header said "The approach follows [PGVWC07] and [CPGSV21]."
The v2 review (cleanup item 7) flagged this as misleading: the proof
technique (induction on blocks via the spectral gap) is the blueprint's
own, not from either paper.

v3 replaces this with: "The results correspond to the canonical form
uniqueness of [PGVWC07] and the block separation results of [CPGSV21].
The proof technique used here—induction on blocks via the spectral
gap—is specific to this formalization."

Remark 10.18 at the end of the chapter repeats this distinction. This
directly addresses cleanup item 7 from the v2 review.

## 2. Ring vs algebra two-level structure documented (NEW: Remark 10.2)

v2 silently switched from ring isomorphisms (Theorem 9.1) to algebra
automorphisms (Theorems 9.2–9.3). The v2 review (cleanup item 1, and the
cross-cutting recommendation in section 8a) identified this as the most
important type-level transition to document.

v3 adds Remark 10.2, which explicitly states: "Theorem 10.1 is a
ring-level statement: it only uses the ideal structure... Theorems 10.3
and 10.4 require an upgrade to C-algebra automorphisms. The reason is
threefold: dimension preservation compares the blocks as C-vector spaces;
Skolem-Noether applies to the resulting central simple C-algebras; and
the per-block maps extracted from T must commute with scalar
multiplication."

This directly addresses cleanup item 1 and the cross-cutting
recommendation from section 8a of the v2 review.

## 3. Definition 10.6 reclassified

v2's Definition 9.5 was flagged (cleanup item 2) as containing a
nontrivial claim ("The per-block linear extensions T_k are C-algebra
homomorphisms") rather than being a pure definition.

v3's Definition 10.6 is now a proper definition: it defines the assembled
map T(M)_k := T_k(M_k) and defers the claim that each T_k is an algebra
homomorphism to Theorem 10.7. The wording is: "Theorem 10.7 shows that
each T_k is a C-algebra homomorphism and that this assembled map is
indeed a C-algebra automorphism."

This directly addresses cleanup item 2.

## 4. Theorem 10.7: trivial permutation clarified

v2's Theorem 9.6 invoked a permutation sigma via Theorem 9.3, but the v2
review (cleanup item 4) showed that in the per-block same-MPV setting the
permutation is necessarily trivial.

v3's Theorem 10.7 now explicitly states: "Because T is assembled
blockwise, it preserves each block ideal, so in this theorem the
permutation is actually pi = id. A nontrivial block permutation only
appears after block separation identifies which blocks match globally."

This directly addresses cleanup item 4.

## 5. Lemma 10.14: citation corrected and proof expanded

v2's Lemma 9.12 proof cited "the proportional FT (Theorem 8.23)" but the
v2 review (cleanup item 3) showed the actual argument uses the
contrapositive of Theorem 6.17 (overlap decay), not Theorem 8.23.

v3's Lemma 10.14 proof now correctly states: "Since this limit is
nonzero, the contrapositive of Theorem 7.17 forces A_0 and B_0 to be
gauge-phase equivalent; the limit O_{A_0 B_0}(N) -> 1 then makes the
phase trivial, so A_0 and B_0 generate the same MPV family."

The citation references are updated to v3 numbering: Theorems 7.15 and
7.17 (which are v2 Theorems 6.15 and 6.17 respectively).

This directly addresses cleanup item 3.

## 6. Normalization convention documented (NEW: Remark 10.10)

v2 review cleanup item 9 flagged that the TP gauge convention differs
from [PGVWC07]'s unital gauge. v3 adds Remark 10.10 explicitly stating:
"The convention here differs from [PGVWC07, Thm. 4], which uses the
unital gauge sum_i A^i_k (A^i_k)^dagger = 1. This chapter instead works
in the dual TP gauge... A positive-definite fixed point of the adjoint
transfer map provides a gauge transformation between these two
normalizations (Theorem 6.11)."

This directly addresses cleanup item 9.

## 7. Section 10.2 title renamed

v2's "Pi-algebra linear extension" is renamed to "Product algebra linear
extension" in v3. This addresses cleanup item 6 from the v2 review.

## 8. Arrow notation dropped

v2's Theorem 9.1 used the tilde-arrow without defining it. The v2 review
(cleanup item 10) flagged this. v3 drops the arrow and writes the
statement in plain text: "Every ring isomorphism T : prod_k R_k ->
prod_k R_k permutes the block ideals."

This addresses cleanup item 10.

---

# v2 → v3 Changes — Non-substantive

- All internal cross-references updated for v3 numbering:
  - Theorem 8.4 -> Theorem 9.4 (global gauge from block gauge)
  - Definition 9.8/8.28 -> Definitions 10.9/9.29
  - Theorem 8.24 -> Theorem 9.25
  - Theorem 8.29 -> Theorem 9.30
  - Theorem 8.30 -> Theorem 9.31
  - Theorem 6.15/6.17 -> Theorem 7.15/7.17
- Remark 10.11 (= v2 Remark 9.9) wording slightly improved: "because
  it can be verified independently of primitivity" replaces "because the
  overlap limit may also be assumed directly."

---

# v2 → v3 Unchanged

The mathematical content of all 15 carried-over statements is identical.
No theorem statements, hypotheses, or proof strategies changed beyond the
numbering and reference updates.

---

# Forward Reference Verification

| v3 reference | Target | Verified |
|---|---|---|
| Definition 2.31 | MPV overlap | Yes (p. 10) |
| Lemma 2.32 | Overlap = conjugate inner product | Yes (p. 10) |
| Theorem 3.6 | Linear extension existence | Yes (p. 14) |
| Theorem 3.7 | Multiplicativity of linear extension | Yes (p. 14) |
| Theorem 3.9 | Skolem-Noether | Yes (p. 14) |
| Lemma 3.10 | Promotion to algebra homomorphism | Yes (p. 14) |
| Theorem 3.11 | Single-block FT | Yes (p. 15) |
| Definition 4.12 | Irreducible map | Yes (p. 21) |
| Theorem 6.3 | PSD to PD under irreducibility | Yes (p. 29) |
| Theorem 6.8 | PSD fixed point existence | Yes (p. 30) |
| Theorem 6.10 | Adjoint gauging | Yes (p. 30) |
| Theorem 6.11 | Gauge transformation (TP to unital) | Yes (p. 30) |
| Theorem 7.7 | Overlap = transfer trace | Yes (p. 35) |
| Theorem 7.15 | Rectangular overlap decay | Yes (p. 37) |
| Theorem 7.17 | Same-dim overlap decay | Yes (p. 37) |
| Theorem 9.4 | Global gauge from block gauge | Yes (p. 50) |
| Theorem 9.25 | CF from peripheral primitivity | Yes (p. 54) |
| Def 9.29 | Normal canonical form predicate | Yes (p. 55) |
| Theorem 9.30 | Self-overlap derived in normal CF | Yes (p. 55) |
| Theorem 9.31 | Modulus-one eigenvalue rigidity | Yes (p. 55) |
| [Wol12, Thm. 6.7] | Primitive channel convergence | Literature ref |
| [Wol12, Thm. 6.8] | CP primitivity characterization | Literature ref |

All internal forward references verified.

---

# Prior Review Items — Status Check

Items from `blueprint_chapter9_review.md` (v2 review):

| # | v2 Item | Status in v3 |
|---|---|---|
| 1 | Document ring to algebra two-level structure | **Fixed.** Remark 10.2 added. |
| 2 | Reclassify Definition 9.5 as theorem | **Fixed.** Def 10.6 is now a proper definition; claim deferred to Thm 10.7. |
| 3 | Correct Lemma 9.12 citation (Thm 8.23 to Thm 6.17) | **Fixed.** Now cites Theorem 7.17 (= v2 Thm 6.17). |
| 4 | Clarify trivial permutation in Theorem 9.6 | **Fixed.** Theorem 10.7 now states pi = id explicitly. |
| 5 | Note Vandermonde (Thm 9.11) unused in Chapter 9 | **Not addressed.** See item 10-R1 below. |
| 6 | Rename "Pi-algebra" to "Product algebra" | **Fixed.** Section 10.2 title renamed. |
| 7 | Restore deviation acknowledgment in chapter header | **Fixed.** Chapter header revised; Remark 10.18 added. |
| 8 | Verify [CPGSV21, section IV.A] section numbering | **Not addressed.** Still cited without independent verification. Low priority. |
| 9 | Note normalization convention deviation | **Fixed.** Remark 10.10 added. |
| 10 | Define the tilde-arrow | **Fixed.** Arrow dropped; plain notation used. |
| 11 | Define T(M)_k notation | **Partially addressed.** Theorem 10.4 now defines it: "where T(M)_k denotes the k-th block component of T(M)." |
| 12 | Add local recall of O_{AB}(N) | **Fixed.** Section 10.3 opens with a recall citing Definition 2.31 and Theorem 7.7. |

Items from `blueprint_review_comprehensive_reference.md`:

| Item | Status |
|---|---|
| Definition duplication: 8.1 vs 2.23 (now 9.1 vs 2.23) | **Fixed in v3 Ch 9.** Definition 9.1 now says "Recall the block-diagonal tensor of Definition 2.23." |
| Cross-chapter DS gauge consistency | **Resolved.** All references use TP normalization. |

---

# Statement-by-Statement Analysis

## Theorem 10.1 (Ring isomorphisms permute block ideals)

**Statement correct.** Identical to v2 Theorem 9.1 except the tilde-arrow
is dropped and the permutation variable is renamed from sigma to pi
(consistent notation with the new Theorem 10.4).

**Proof correct.** Standard ideal-lattice argument for products of simple
rings.

## Remark 10.2 (Ring level versus algebra level)

**New. Correct and well-formulated.** Lists the three reasons for the
upgrade: (1) dimension preservation as C-vector spaces, (2) Skolem-Noether
for central simple C-algebras, (3) scalar compatibility. This matches the
analysis in the v2 review section 8a and the Lean architecture confirmed in
`BlockPermutation.lean`.

— *Acceptable as-is.*

## Theorem 10.3 (Dimension preservation)

**Statement correct.** Identical to v2 Theorem 9.2.

## Theorem 10.4 (Decomposition of automorphisms)

**Statement correct.** Identical to v2 Theorem 9.3 in content, but the
proof is slightly expanded: it now names each ingredient (Theorem 10.1,
Theorem 10.3, Skolem-Noether via Theorem 3.9) in sequence, and defines
T(M)_k notation inline.

The added sentence "where T(M)_k denotes the k-th block component of
T(M)" addresses cleanup item 11 from the v2 review.

## Definition 10.5 (Per-block linear extension)

**Correct.** Identical to v2 Definition 9.4.

Carried-over observation (from v2 review): The definition only requires
A_k to be injective, not B_k. This asymmetry is correct but matters for
the Lean formalization: the linear extension exists from the spanning of
{A^i_k}, not of {B^i_k}. The downstream Theorem 10.7 does not explicitly
require B_k to be injective either (it requires per-block same-MPV), but
the single-block FT applied in Theorem 10.8 does require both A_k and B_k
injective. This chain is correct; the point is that the injectivity of B_k
enters at the gauge-equivalence step, not at the linear-extension step.

— *Acceptable as-is.*

## Definition 10.6 (Product algebra automorphism)

**Improved from v2.** Now a proper definition (assembled map), with the
nontrivial claim deferred to Theorem 10.7. This addresses v2 cleanup
item 2.

## Theorem 10.7 (Per-block linear extensions assemble)

**Statement correct.** Content identical to v2 Theorem 9.6.

**Key improvement:** The proof now ends with "Because T is assembled
blockwise, it preserves each block ideal, so in this theorem the
permutation is actually pi = id. A nontrivial block permutation only
appears after block separation identifies which blocks match globally."
This directly addresses v2 cleanup item 4.

**Cross-references verified:** Theorems 3.6, 3.7, Lemma 3.10 all
correspond to the correct v3 statements.

## Theorem 10.8 (Per-block same MPV gives global gauge equivalence)

**Statement correct.** Identical to v2 Theorem 9.7.

**Cross-references verified:** Theorem 3.11 (single-block FT),
Theorem 9.4 (global gauge from block gauge).

**10-S5 (unstated hypotheses on B_k).** The theorem says "If all block
tensors A_k are injective and per-block same-MPV holds, then each pair
(A_k, B_k) is gauge equivalent." The B_k are not introduced in this
theorem statement. The proof invokes Theorem 3.11, which requires the two
tensors to have the same bond dimension. In the section context, the B_k
are implicitly carried from Definition 10.5, which introduces them as
"injective tensors B_k of bond dimension D_k." So this is not a
mathematical gap — the hypotheses are present in the surrounding text —
but the theorem is not self-contained as a standalone statement.

The web blueprint's Lean declaration (`fundamentalTheorem_multiBlock_full`)
presumably has explicit type signatures that include the dimension
matching, so the Lean code is likely correct. The issue is only in the
blueprint prose.

— *Low priority (context supplies the missing hypotheses; standalone
readability issue only).*

## Definition 10.9 (Canonical form predicate)

**Statement correct.** Identical to v2 Definition 9.8, with the same
five conditions.

Carried-over observation: Condition (5) (self-overlap convergence) is
included as an explicit hypothesis rather than derived from primitivity.
This design choice is documented in Remark 10.11 and is correct for the
Lean formalization (it allows the predicate to be satisfied without
proving primitivity).

## Remark 10.10 (Normalization convention)

**New. Correct.** Explicitly notes the deviation from [PGVWC07, Thm. 4]
(unital gauge vs TP gauge) and cites Theorem 6.11 for the gauge
transformation. This addresses v2 cleanup item 9.

## Remark 10.11 (Overlap redundancy)

**Correct.** Updated reference: Theorem 9.25 (= v2 Theorem 8.24). The
wording is improved from v2's "because the overlap limit may also be
assumed directly" to "because it can be verified independently of
primitivity."

## Remark 10.12 (Normal-canonical companion)

**Correct.** References updated to Definition 9.29 (= v2 Definition 8.28)
and Theorem 9.30 (= v2 Theorem 8.29).

## Theorem 10.13 (Vandermonde separation)

**Statement correct.** Identical to v2 Theorem 9.11.

**Still unused in this chapter.** The v2 review (cleanup item 5) flagged
that this theorem is a forward deposit for Chapter 11, not used in the
block separation argument. v3 does not add a forward reference. Checking
v3 Chapter 11: Remark 11.14 states that the current route to Theorem 12.5
uses "linear independence of the block MPV family supplied by a basis of
normal tensors, rather than Newton-Girard identities, to match the weight
multiset." This means Theorem 10.13 is not used in the current proof
chain at all — neither in Chapter 10 nor in Chapter 11/12 (the
Newton-Girard route is not taken).

— *Low priority; the theorem is harmless but unused. See item 10-R1.*

## Lemma 10.14 (Block separation core)

**Statement correct.** Identical to v2 Lemma 9.12.

**Proof partially corrected.** The v2 review (cleanup item 3) flagged that
the proof cited Theorem 8.23 (proportional MPV) when the actual argument
uses the contrapositive of Theorem 6.17 (overlap decay). v3 removes the
incorrect Theorem 8.23 citation and now correctly cites Theorem 7.17 for
the final step (gauge-phase equivalence from nonzero overlap limit). This
fixes the main error.

However, the proof has an **imprecise attribution** at the k ≥ 1 decay
step. It says "the contributions from k ≥ 1 decay exponentially by
Theorems 7.15 and 7.17."

**10-S2 (imprecise decay attribution).** After dividing by μ_0^N, the
k ≥ 1 terms in the overlap equation are:

  (μ_k/μ_0)^N · [O_{A_0 A_k}(N) − O_{A_0 B_k}(N)]

The primary decay mechanism is the weight ratio |μ_k/μ_0| < 1 (from the
strict ordering in the canonical form predicate), giving geometric decay
(μ_k/μ_0)^N → 0. Theorems 7.15 and 7.17 contribute by bounding or
decaying the overlap factors, but they are not the main driver. The web
blueprint's dependency graph confirms that Lemma 10.14 does use both
Theorems 7.15 and 7.17, so the citation is not wrong per se — these
theorems are genuine dependencies. However, the "by" phrasing suggests
they are the sole mechanism, which is misleading. At this stage of the
induction we do not know whether blocks within the A-family are
gauge-phase equivalent (Definition 10.9 does not require BNT separation),
so O_{A_0 A_k}(N) could tend to 1 rather than 0. In that case the
overlaps are bounded but not decaying, and the decay comes entirely from
the weight ratio.

The fix is to say: "the contributions from k ≥ 1 decay because
|μ_k/μ_0| < 1 (strict weight ordering) and the bilinear overlaps are
bounded (Theorems 7.15 and 7.17 supply the relevant bounds)."

— *Should fix (imprecise attribution, correct conclusion).*

**10-S4 (missing bond-dimension case split).** The proof says "the
contrapositive of Theorem 7.17 forces A_0 and B_0 to be gauge-phase
equivalent." But Theorem 7.17 has a hypothesis D_A = D_B (same bond
dimension). The statement of Lemma 10.14 does not require D_{B_k} =
D_{A_k}. The correct argument needs one more step: since O_{A_0 B_0}(N)
→ 1 ≠ 0, and Theorem 7.15 gives O → 0 whenever D_{A_0} ≠ D_{B_0},
we first conclude D_{A_0} = D_{B_0} by contradiction. Then Theorem 7.17's
contrapositive applies. The mathematical conclusion is correct, but the
bond-dimension matching is unstated.

**Confirmed against the web blueprint:** The Lean dependency graph for
Lemma 10.14 lists both Theorem 7.15 (rectangular overlap decay) and
Theorem 7.17 (same-dimension overlap decay) as dependencies. This
confirms that the Lean proof does use both theorems — 7.15 for the
dimension matching, 7.17 for the gauge-phase equivalence — even though
the blueprint proof text mentions only the 7.17 step explicitly.

For the Lean formalization this matters concretely: the formalizer will
need to discharge `D_A = D_B` before applying the `Theorem_7_17`
contrapositive, and will need to know to use `Theorem_7_15` for this.

— *Should fix (missing intermediate step for formalization).*

## Theorem 10.15 (Block separation from canonical form)

**Statement correct.** Identical to v2 Theorem 9.13.

## Theorem 10.16 (Block separation from normal canonical form)

**Statement correct.** Identical to v2 Theorem 9.14.

**References updated:** Theorem 9.30 (= v2 Theorem 8.29) and
Theorem 9.31 (= v2 Theorem 8.30).

**10-S3 (proof clarity: irreducible vs injective).** The proof says "The
proof follows the same peeling argument as Theorem 10.15." But there is
a non-trivial difference: Theorem 10.15 uses Lemma 10.14, which invokes
Theorem 7.17 at the key step (contrapositive: nonzero overlap limit ⟹
gauge-phase equivalence). Theorem 7.17 requires *injective* tensors. In
Theorem 10.16, the B_k are *irreducible*, not injective. Irreducibility
does not imply injectivity in general (the implication goes the other
way: injective ⟹ algSpan = M_D ⟹ irreducible action ⟹ irreducible
tensor).

The proof acknowledges this by citing Theorem 9.31 instead of 7.17.
Theorem 9.31 (modulus-one eigenvalue rigidity) works for irreducible
TP-normalized tensors, not just injective ones. So the argument is
correct. But the "same peeling argument" language obscures the fact that
the key step uses a different theorem with weaker hypotheses. The proof
should say: "the same peeling argument as Theorem 10.15, with
Theorem 9.31 replacing the contrapositive of Theorem 7.17 at the
identification step, since the blocks are irreducible rather than
injective."

— *Should fix (compressed proof obscures a genuine hypothesis difference).*

Carried-over observation (from v2): The proof uses Theorem 9.31
(modulus-one eigenvalue rigidity), whose proof in turn invokes
Theorem 6.10 to gauge both tensors to unital Kraus families and then
applies the Kadison-Schwarz equality argument. The v2 review flagged
Theorem 8.30 (= v3 Theorem 9.31) as having a compressed proof. The v3
version of this theorem (in Chapter 9, p. 55-56) expands the proof
somewhat, now naming the specific theorems used (6.8, 6.3, 6.10). This
is improved from v2 but the proof sketch remains relatively compressed
for a formalization blueprint. The key step — "the embedded modulus-one
eigenvector saturates the Kadison-Schwarz inequality" — is stated but
not fully expanded. This is a Chapter 9 issue, not a Chapter 10 issue.

— *Acceptable for Chapter 10; the proof expansion should be tracked as a
Chapter 9 item.*

## Theorem 10.17 (CF FT, same-structure version)

**Statement correct.** Identical to v2 Theorem 9.15.

**References updated:** Theorem 10.15 (block separation), Theorem 10.8
(per-block gauge equivalence).

## Remark 10.18 (Relation to the literature)

**New. Correct and well-formulated.** Explicitly states: "The results...
correspond to the canonical form uniqueness of [PGVWC07] and the block-
separation statements of [CPGSV21]. The proof technique used here — an
induction on the number of blocks driven by the spectral gap of the
mixed transfer operators — is specific to this formalization."

This mirrors the chapter header and addresses v2 cleanup item 7.

---

# Cross-Chapter Consistency

**DS gauge:** Fully eliminated. All statements use TP normalization.

**Definition duplication:** v2's Definition 9.8 was a standalone definition
of the canonical form predicate. In v3, it is renumbered as
Definition 10.9 and remains standalone. v3's Chapter 9 has its own
Definition 9.29 (normal canonical form predicate). These are parallel
definitions for the two routes (block-injective vs normal-canonical) and
are correctly cross-referenced in Remark 10.12.

**Overlap recall:** v3 adds a local recall of the overlap notation at the
start of section 10.3 (citing Definition 2.31 and Theorem 7.7). This
addresses v2 cleanup item 12.

**Permutation variable name:** v2 used sigma throughout; v3 switches to pi.
This is consistent within v3 Chapter 10.

**Chapter 9 to Chapter 10 interface:** Theorem 10.8 cites Theorem 9.4
(global gauge from block gauge, in Chapter 9). This is correct — v3's
Chapter 9 contains the block-diagonal assembly results (section 9.1) which
include Theorem 9.4.

**Downstream:** Theorem 10.15 is cited in Chapter 12 (Theorem 12.5) for
the final assembly. Theorem 10.17 is the same-structure CF FT. Both are
on the critical path.

---

# Literature Alignment

## Changes from v2

1. **Chapter header revised.** Now correctly distinguishes results
   (corresponding to [PGVWC07] and [CPGSV21]) from proof technique
   (specific to this formalization). This is the most important alignment
   improvement.

2. **Normalization convention noted.** Remark 10.10 documents the
   deviation from [PGVWC07]'s unital gauge.

3. **Remark 10.18 added.** Repeats the deviation acknowledgment at the
   end of the chapter.

## Remaining deviations (carried from v2, now documented)

1. **Proof technique:** Blueprint uses induction on blocks via spectral
   gap. [PGVWC07] uses OBC lifting + Horn-Johnson intertwining.
   [CPGSV21] deduces block separation from BNT uniqueness. Now
   explicitly acknowledged.

2. **Normalization convention:** TP gauge vs [PGVWC07]'s unital gauge.
   Now explicitly documented.

3. **Canonical form predicate:** Requires injectivity (stronger than the
   literature's irreducibility); uses self-overlap convergence (weaker
   than primitivity). This design choice is documented in Remarks 10.11
   and 10.12. Not explicitly flagged as a deviation from the literature,
   but the structure makes this clear.

---

# AI-Language Audit

**"Pi-algebra" (v2 section 9.2 title):** Fixed. Now reads "Product algebra
linear extension."

**Remark 10.11 wording:** Improved from v2. No longer reads awkwardly.

**No new AI-language issues detected.** The new remarks (10.2, 10.10,
10.18) read as standard mathematical commentary.

---

# Formalization Notes

**10-F1. Ring to algebra two-level structure (from v2 cleanup item 1).**
Now documented in Remark 10.2. The Lean architecture uses `RingEquiv`
for the block ideal permutation and `AlgEquiv` for the dimension
preservation and Skolem-Noether decomposition. The blueprint now
correctly describes this distinction.

**10-F2. Per-block linear extension type chain (from v2 section 8a).**
The type transitions in Theorem 10.7: linear to multiplicative to
bijective to unital to algebra automorphism. Each step corresponds to a
separate Lean lemma (Theorems 3.6, 3.7, 3.8, Lemma 3.10). The blueprint
compresses this into one proof paragraph but names each ingredient.
Acceptable for a blueprint.

**10-F3. Vandermonde theorem not used.**
Theorem 10.13 is not used anywhere in the current proof chain (Chapters
10-12). Remark 11.14 in Chapter 11 confirms the Newton-Girard route is
not taken. For the Lean formalization, this theorem is inert — it can be
formalized but has no downstream consumers.

---

# Cleanup Checklist

## Must fix

(None.)

## Should fix

**10-S1.** Theorem 10.13 (Vandermonde): add a remark noting that this
theorem is not used in the current proof chain and is retained for
potential alternative routes. Currently it appears as if it should be
used somewhere but is not. Remark 11.14 in Chapter 11 makes this
partially clear, but a local note in Chapter 10 would help the
formalization agent prioritize.

**10-S2.** Lemma 10.14 proof: the claim "contributions from k ≥ 1 decay
exponentially by Theorems 7.15 and 7.17" is wrong. The decay comes from
the weight ratio |μ_k/μ_0| < 1 (geometric in N), not from the overlap
theorems. Theorems 7.15/7.17 give overlap decay under conditions (different
bond dimensions, or same dimension but not gauge-phase equivalent) that
are not established at this point in the induction. Replace "by
Theorems 7.15 and 7.17" with "because |μ_k/μ_0| < 1 (strict weight
ordering) and the bilinear overlaps are bounded." The conclusion of the
lemma is unaffected.

**10-S3.** Theorem 10.16 proof: the phrase "the same peeling argument as
Theorem 10.15" obscures a genuine hypothesis difference. Theorem 10.15
(block-injective route) uses Theorem 7.17, which requires injectivity.
Theorem 10.16 (normal-canonical route) has irreducible blocks, which are
not in general injective. The proof correctly uses Theorem 9.31 instead
of 7.17, but should say this explicitly: "the same peeling argument, with
Theorem 9.31 replacing the contrapositive of Theorem 7.17 at the
identification step, since the blocks are irreducible rather than
injective."

**10-S4.** Lemma 10.14 proof: the identification step "the contrapositive
of Theorem 7.17 forces A_0 and B_0 to be gauge-phase equivalent" skips
the bond-dimension matching. Theorem 7.17 requires same bond dimension.
The correct chain is: O_{A_0 B_0}(N) → 1 ≠ 0, so D_{A_0} = D_{B_0}
(else Theorem 7.15 gives → 0, contradiction); then Theorem 7.17's
contrapositive applies. The web blueprint's Lean dependency list confirms
both theorems are used. This intermediate step must be explicit for the
formalization agent.

**10-S5.** Theorem 10.8: the B_k are not introduced in the theorem
statement — no bond dimensions, no properties. The surrounding context
(Definition 10.5) supplies them, so this is a standalone-readability
issue rather than a mathematical gap. Moved to low priority.

## Low priority

**10-L1.** The v2 review noted that the [CPGSV21, section IV.A] section
numbering has not been independently verified against the paper. This
remains unverified but is low priority since the mathematical content is
standard.

**10-L2.** Theorem 10.8 (10-S5): the B_k hypotheses (bond dimensions,
injectivity) are implicit from §10.2 context. For a self-contained
theorem statement, add: "Let A_k and B_k be injective block tensors of
the same bond dimensions D_k."

## Acceptable as-is

- Theorem 10.7 proof compresses the type chain (linear to multiplicative
  to bijective to unital to automorphism) into one paragraph. Each
  ingredient is named; the compression is acceptable for a blueprint.

- Definition 10.5 does not require B_k injective. The asymmetry is
  correct and enters naturally in the proof chain.

- Canonical form predicate uses injectivity (stronger than the
  literature's irreducibility). This is a defensible design choice.

- Lemma 10.14 proof says "decay exponentially" for what is actually
  polynomial times exponential decay. The conclusion is correct.

---

# Final Assessment

v3 Chapter 10 addresses 10 of 12 cleanup items from the v2 review.
The most important improvements are:

1. The chapter header and Remark 10.18 now honestly distinguish the
   blueprint's proof technique from the cited literature.
2. Remark 10.2 documents the ring/algebra two-level structure, which is
   the key type-level transition for the Lean formalization.
3. The block separation proof (Lemma 10.14) now correctly cites
   Theorem 7.17 instead of Theorem 8.23 (= v3 Theorem 9.24).
4. Theorem 10.7 explicitly notes that the permutation is trivial in the
   per-block same-MPV setting.
5. The normalization convention deviation from [PGVWC07] is documented.

However, closer scrutiny of the proofs — verified against the web
blueprint's Lean dependency graph — reveals three "should fix" items
and two low-priority items:

- **10-S2:** Lemma 10.14 proof attributes k ≥ 1 decay to Theorems 7.15/
  7.17 with "by," but the primary mechanism is the weight ratio
  |μ_k/μ_0| < 1. The theorems are genuine dependencies (confirmed by
  the Lean dependency graph) but the attribution is imprecise.
- **10-S4:** Lemma 10.14 proof invokes Theorem 7.17's contrapositive
  without first establishing that D_{A_0} = D_{B_0}. The bond-dimension
  matching follows from Theorem 7.15's contrapositive but is unstated.
  Confirmed by the Lean dependency graph listing both 7.15 and 7.17.
- **10-S3:** Theorem 10.16 proof says "the same peeling argument" but
  silently substitutes Theorem 9.31 for Theorem 7.17, which matters
  because the hypotheses differ (irreducible vs injective).
- **10-L2:** Theorem 10.8 does not introduce the B_k in its statement;
  the hypotheses are implicit from §10.2 context. Standalone readability.
- **10-S1:** Theorem 10.13 (Vandermonde) is unused in the current proof
  chain and should be marked as such.

**Priority for the formalization agent:**
1. Fix Lemma 10.14 proof text: clarify the decay attribution (10-S2)
   and add the bond-dimension matching step (10-S4).
2. Make Theorem 10.16 proof explicit about using Theorem 9.31 (10-S3).
3. Add a remark to Theorem 10.13 noting it is unused (10-S1).
4. Optionally: make Theorem 10.8 self-contained (10-L2).
