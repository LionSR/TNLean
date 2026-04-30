# Formalization Goal Analysis: The Fundamental Theorem of MPS

This document records the analysis of what the blueprint currently
proves, what remains, and whether the formalization achieves its goal.
It was produced during the v3 blueprint review session (March 2026).

---

## 1. Two Levels of "Done"

There are two natural standards for when the formalization is complete.

### Level A: The literature's own standard

CPGSV21 Corollary IV.5 states the FT for **tensors already in canonical
form**: if A and B are in CF and generate the same MPV for all N, then
there exists an invertible X with A^i = X B^i X^{-1}.

The paper treats "bring any tensor to CF" as a routine preprocessing
step (CPGSV17 Propositions 2.4–2.5, 2.9), separate from the FT itself.
The FT is stated and proved only for tensors already in CF.

**Blueprint status at Level A: COMPLETE.** Theorem 12.5 recovers
CPGSV21 Corollary IV.5 without assuming common block structure, as
stated explicitly in Remark 12.7. The proof combines the proportional FT
(Theorem 12.2) with BNT linear independence (Theorem 11.5 / Def 11.1)
to derive block matching, weight matching, and gauge equivalence from
MPV equality alone. The weight matching uses the BNT expansion
directly, bypassing Newton–Girard identities.

### Level B: The fully unconditional theorem

A single Lean theorem starting from arbitrary tensors:

> For any two MPS tensors A, B with 𝒱(A) = 𝒱(B), there exists p ≥ 1
> such that A[p] and B[p] admit canonical form decompositions into
> primitive blocks, and the resulting block-diagonal tensors are gauge
> equivalent.

This requires chaining the CF existence pipeline (Chapter 9) into the
uniqueness theorem (Chapters 10–12).

**Blueprint status at Level B: Two gaps remain in the existence
pipeline.** See §3.

---

## 2. What Is Proved (Uniqueness Side)

### Theorem 12.5 (Equal-MPV FT, unconditional on block structure)

Given two families in CF-BNT form with V^{(N)}(A_tot) = V^{(N)}(B_tot)
for all N, the block-diagonal tensors are gauge equivalent. This derives:
- equality of block counts g_A = g_B,
- a permutation π matching blocks by bond dimension,
- per-block gauge-phase equivalence,
- weight matching μ_j^A = μ_{π(j)}^B · e^{iφ_j},
- global gauge equivalence of the assembled block-diagonal tensors.

### Theorem 12.6 (Common-structure specialization)

Assumes the same block counts, bond dimensions, and weights from the
outset. A corollary of 12.5, not the main result.

### Remark 12.7

States that Theorem 12.5 "recovers the full [CPGSV21, Corollary IV.5]
without assuming common block structure." This is the paper's own FT,
at the paper's own level of generality (tensors in CF).

### What v2 was missing

v2's assembly theorem (the analogue of 12.6) assumed common block
structure as input. The scope gap identified in our v2 review — that the
theorem was strictly weaker than the full FT — is closed by v3's
Theorem 12.5. The bridging argument verified in `full_ft_verification.md`
is now internalized.

---

## 3. What Remains (Existence Side)

The existence pipeline takes an arbitrary tensor and produces CF data.
v3 made substantial progress here relative to v2.

### v2 status (Remark 8.35)

The entire "upstream passage from arbitrary tensor to primitive weighted
block data" was flagged as open.

### v3 status (Remark 9.50)

The pipeline is mostly in place:
- Thm 9.15: any tensor → irreducible blocks (invariant-subspace splitting)
- Thm 9.38: zero-block separation
- Thm 9.39: arbitrary tensor -> TP-gauged irreducible nonzero blocks
- Thms 9.40–9.43: blocking infrastructure (distributes over MPV, powers
  preserve primitivity, common blocking period)
- Thm 9.47: arbitrary tensor → primitive block decomposition

Two gaps remain per Remark 9.50.

### Gap 1: Irreducibility of blocked blocks

**The claim in Remark 9.50:** "blocking does not in general preserve
tensor irreducibility."

**Analysis:** The blueprint has Theorem 9.41 (primitivity under powers)
but not irreducibility under powers. These are distinct conditions:
primitivity = peripheral spectrum {1}, irreducibility = no nontrivial
invariant projections. The normal canonical form predicate (Def 9.29)
requires both.

After blocking, the transfer map is known to be primitive (Thm 9.42).
But the predicate also requires irreducibility.

**Resolution without proving "irreducibility under powers" directly:**
1. The original block A_k is irreducible (from Thm 9.15).
2. In TP gauge, its fixed point ρ is positive definite (Thm 6.3).
3. This same ρ is a PosDef fixed point of ℰ_{A_k}^p = ℰ_{A_k[p]}
   (since ℰ_A(ρ) = ρ implies ℰ_A^p(ρ) = ρ).
4. The blocked map is primitive (Thm 9.42).
5. Theorem 8.50 says: primitive + PosDef fixed point ⟹ irreducible.

The critical check is that step (5) is non-circular. Theorem 8.50's
proof uses the convergence ℰ^n(σ) → (tr σ / tr ρ) ρ, which comes from
the spectral gap (part of the primitivity hypothesis), and then the
positive definiteness of ρ to rule out nontrivial invariant projections.
This does not assume irreducibility as input.

**What the papers do:** Do not treat this as a separate issue. The papers
work with NTs (irreducible by definition) and blocking only removes
periodicity. Irreducibility of blocked blocks is never questioned.

### Gap 2: Pairwise distinct weight norms

**The issue:** Def 9.29 condition 4 requires |μ_1| > |μ_2| > ... > |μ_r|
(strictly decreasing). The existence pipeline (Thm 9.47) does not
guarantee this — two blocks could emerge with |μ_j| = |μ_k|.

**What the papers do:** CPGSV17 Definition 2.6 and Proposition 2.7
define the BNT with a minimality condition. Gauge-phase-equivalent
blocks with the same weight modulus are grouped together. The CF
decomposition (CPGSV17 eq. 20a) writes:

  A^i = X [⊕_{j=1}^g (M_j ⊗ A_j^i)] X^{-1}

where g is the number of BNT elements and M_j is diagonal with entries
μ_{j,q}. Different BNT elements can have the same |μ_{j,q}| — the
strictly decreasing condition is imposed only on the BNT-level
effective coefficients ∑_q μ_{j,q}^N, not on individual block weights.

**The blueprint's predicate is too strict.** Def 9.29 and Def 10.9
require strictly decreasing moduli at the block level. The papers' CF
does not require this. The fix is either:
(a) relax the predicate to match the paper's CF definition, or
(b) include a BNT grouping/merging step in the existence pipeline.

This is a definitional/organizational issue, not a mathematical one.

---

## 4. The Paper's Existence Proof (for Reference)

CPGSV17 Propositions 2.4–2.5, 2.9 and CPGSV21 §IV.A:

1. Iterate invariant-subspace splitting until all blocks are irreducible
   (= normal tensors in the paper's spectral sense).
2. Each block has peripheral eigenvalues that are roots of unity. Block
   by p = lcm of all periods. Now each block is primitive.
3. By quantum Wielandt (SPGWC10): after blocking at most D⁴ times,
   every NT becomes injective. After at most 3D⁵ total blockings, the
   tensor is in block-injective CF.
4. State the FT for tensors in CF.

The papers treat steps 1–3 as routine preprocessing, not part of the
FT itself. Step 3 (Wielandt → injectivity) is formalized in blueprint
Chapter 8. Steps 1–2 are formalized in blueprint Chapter 9 modulo the
two gaps above.

---

## 5. Connection to the ChatGPT Discussion

The ChatGPT discussion (exported as PDF) analyzed whether Theorems 12.5
and 12.6 constitute the full unconditional FT.

**What it got right:**
- The distinction between 12.5 (unconditional on block structure) and
  12.6 (common-structure specialization) is correct.
- The characterization of v2's gap (missing bridge from equal MPV to
  structural matching) is correct.
- The assessment that v3 Theorem 12.5 closes the uniqueness gap is
  correct.
- The observation that the periodic irreducible-form theorem
  (de las Cuevas et al.) is a separate story is correct.

**What it did not address:**
- The existence side (Chapter 9 pipeline status).
- The specific gaps in Remark 9.50.
- The fact that the paper's own FT is stated for tensors already in CF,
  making the existence pipeline a separate concern.

---

## 6. Summary

### At the paper's own standard (Level A): the FT is proved.

Theorem 12.5 = CPGSV21 Corollary IV.5. Remark 12.7 says this
explicitly. The uniqueness theorem for tensors in canonical form, without
assuming common block structure, is complete.

### For the fully unconditional theorem (Level B): two gaps remain.

Both are in the CF existence pipeline (Chapter 9):

| Gap | Nature | Proposed resolution |
|---|---|---|
| Irreducibility of blocked blocks | Lean formalization gap, not mathematical | Use Thm 8.50: primitive + PosDef FP (inherited from original irreducible block) ⟹ irreducible. Verify non-circularity of Thm 8.50's proof. |
| Pairwise distinct weight norms | Predicate mismatch with the literature | Either relax Def 9.29/10.9 to match the paper's CF, or add a BNT grouping step. Definitional, not mathematical. |

Neither gap involves deep mathematics. The papers treat both as trivial
or definitional. The formalization overhead is in Lean type-correctness,
not in any new mathematical content.

### Recommendation

For the purpose of claiming the FT is formalized, Level A suffices — it
matches the literature's own standard. The existence pipeline (Level B)
is valuable for completeness and should be finished, but its remaining
gaps are mechanical rather than conceptual. The formalization agent
should prioritize: (1) the non-circular Thm 8.50 route for Gap 1, and
(2) a predicate adjustment or BNT grouping step for Gap 2.
