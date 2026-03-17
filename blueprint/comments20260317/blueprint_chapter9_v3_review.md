
# Blueprint v3 Review — Chapter 9 (Canonical Form Reduction)

v3 Chapter 9 = v2 Chapter 8. v2 review file: `blueprint_chapter8_review.md`.

---

## 1. Global Assessment

| Aspect | Evaluation |
|---|---|
| Mathematical correctness | Correct (one misnomer in Thm 9.44, off critical path) |
| Conceptual clarity | Good; significantly expanded from v2 |
| Structural quality | Good; new sections fill previously open pipeline steps |
| v2 → v3 changes | All 11 cleanup items from v2 review addressed |
| Cross-chapter consistency | Improved (Def 9.1 cross-refs 2.23; Def 9.14 cross-refs 4.12; "normal" disambiguation improved) |
| Literature alignment | Good; [PGVWC07], [CPGSV21], [CPGSV17], [Wol12], [SPGWC10] tracked |
| AI language | "Pipeline" (5×), "Assembly" (2×) remain |
| FT critical path | §9.1–9.11, §9.13 on path; §9.12 off path (periodic extension infrastructure) |

---

## 2. Number Mapping (v2 → v3)

| v2 | v3 | Name |
|---|---|---|
| Def 8.1 | Def 9.1 | Block-diagonal tensor from blocks |
| Thm 8.2 | Thm 9.2 | Per-block single-block FT |
| Thm 8.3 | Thm 9.3 | Per-block same MPV ⟹ global same MPV |
| Thm 8.4 | Thm 9.4 | Global gauge from block gauge |
| Thm 8.5 | Thm 9.5 | Scaling preserves injectivity |
| Thm 8.6 | Thm 9.6 | Transfer map under scaling |
| Thm 8.7 | Thm 9.7 | Phase-scaling preserves normalization |
| Thm 8.8 | Thm 9.8 | MPV under block normalization |
| Thm 8.9 | Thm 9.9 | Unitary conjugation preserves MPV |
| Def 8.10 | Def 9.10 | Support projection |
| Def 8.11 | Def 9.11 | Invariant projection predicate |
| Thm 8.12 | Thm 9.12 | PSD fixed point gives invariant projection |
| Thm 8.13 | Thm 9.13 | Two-block decomposition |
| Def 8.14 | Def 9.14 | Irreducible tensor |
| Thm 8.15 | Thm 9.15 | Irreducible block decomposition |
| Thm 8.16 | Thm 9.16 | Unitary diagonal PD fixed point in TP gauge |
| Def 8.17 | Def 9.17 | Algebra span |
| Def 8.18 | Def 9.18 | Invariant submodule |
| Def 8.19 | Def 9.19 | Irreducible action |
| Thm 8.20 | Thm 9.20 | Irreducible tensor ⟹ irreducible action |
| Thm 8.21 | Thm 9.21 | Burnside's theorem for Kraus algebras |
| — | Rmk 9.22 | **New.** Burnside as formalization dependency |
| Thm 8.22 | Thm 9.23 | Irreducible action ⟹ eventual cumulative spanning |
| Thm 8.23 | Thm 9.24 | Proportional MPV ⟹ gauge-phase equivalence |
| Thm 8.24 | Thm 9.25 | Canonical form from peripheral primitivity |
| Rmk 8.25 | Rmk 9.26 | Overlap convergence is redundant |
| Thm 8.26 | Thm 9.27 | Blocking yields primitive transfer map |
| Rmk 8.27 | Rmk 9.28 | Periodicity removal step |
| Def 8.28 | Def 9.29 | Normal canonical form predicate |
| Thm 8.29 | Thm 9.30 | Self-overlap derived in normal CF |
| Thm 8.30 | Thm 9.31 | Modulus-one eigenvalue rigidity |
| Thm 8.31 | Thm 9.32 | Irreducible block decomposition (restatement) |
| Thm 8.32 | Thm 9.33 | CFII data for irreducible TP blocks |
| Thm 8.33 | Thm 9.34 | CFII continuation |
| Thm 8.34 | Thm 9.35 | Normal CF from primitive block decomposition |
| — | Def 9.36 | **New.** Zero MPS tensor |
| — | Thm 9.37 | **New.** MPV of zero tensor |
| — | Thm 9.38 | **New.** Zero-block separation |
| — | Thm 9.39 | **New.** Arbitrary-input TP-gauge reduction with zero-block separation |
| — | Thm 9.40 | **New.** Blocking distributes over MPV equivalence |
| — | Thm 9.41 | **New.** Primitive channels remain primitive under powers |
| — | Thm 9.42 | **New.** Blocking-period divisibility preserves primitivity |
| — | Thm 9.43 | **New.** Common blocking period for a block family |
| — | Thm 9.44 | **New.** Compression to a supported projection sector |
| — | Thm 9.45 | **New.** Block decomposition from commuting projections |
| — | Thm 9.46 | **New.** Block decomposition from adjoint-fixed projections |
| — | Thm 9.47 | **New.** Arbitrary tensor to primitive block decomposition |
| — | Thm 9.48 | **New.** TP-primitive irreducible tensor is normal |
| — | Thm 9.49 | **New.** Blocking preserves normality |
| Rmk 8.35 | Rmk 9.50 | Open directions (expanded) |

---

## 3. v2 → v3 Changes

### Substantive changes

1. **Def 9.1 now cross-references Def 2.23.** v2's Def 8.1 was a standalone
   duplicate. v3 says "Recall the block-diagonal tensor of Definition 2.23."
   Addresses v2 cleanup item #1.

2. **Def 9.14 now cross-references Def 4.12.** v2's Def 8.14 said
   "irreducible (in the sense of [CPGSV21])"; v3 says "irreducible if its
   transfer map ℰ_A is irreducible in the sense of Definition 4.12."
   Addresses v2 cleanup item #2.

3. **Thm 9.8 (= v2 8.8) rewritten.** v2 was flagged as a tautology (it
   just restated μ_k = |μ_k|·(μ_k/|μ_k|)). v3 introduces η_k := μ_k/|μ_k|
   and B_k := |μ_k|A_k, explicitly factoring the MPV contribution as
   η_k^N |μ_k|^N V^(N)(A_k). The statement is now nontrivial.
   Addresses v2 cleanup item #3.

4. **Thm 9.13 (= v2 8.13) clarified.** v3 now says "the block-diagonal
   tensor obtained by discarding the off-diagonal blocks generates the same
   MPV family as A." Addresses v2 cleanup item #4.

5. **Thm 9.15 (= v2 8.15) proof expanded.** Adds parenthetical: "If one
   prefers a positive-eigenvector route without assuming TP normalization,
   the correct replacement for the channel-specific Cesàro theorem is
   Theorem 6.15." Addresses v2 cleanup item #5.

6. **Thm 9.25 proof (= v2 8.24) expanded.** Now explicitly checks the
   three conditions for Theorem 4.39: (1) E is primitive, (2) eigenvalue
   bound via Theorem 7.10, (3) trace-zero uniqueness via Theorem 6.5.
   Addresses v2 cleanup item #6.

7. **Thm 9.31 proof (= v2 8.30) expanded.** The compressed sketch is
   replaced with an explicit chain: PSD fixed point via Thm 6.8 →
   PD upgrade via Thm 6.3 → unital gauge via Thm 6.10 → KS equality →
   multiplicative domain → intertwiner = gauge-phase equivalence. Also
   notes the argument parallels Thm 7.12 but uses irreducibility instead
   of injectivity. Addresses v2 cleanup item #7.

8. **Thm 9.35 proof (= v2 8.34) clarified.** Now explicitly says p = 1
   suffices and explains the reordering step that converts pairwise distinct
   moduli to strictly decreasing. Addresses v2 cleanup item #8.

9. **Def 9.29 (= v2 8.28) — "normal" disambiguation improved.** v2
   explicitly said "It is not the same as Definition 2.19." v3 now says:
   "As noted in the remark after Definition 2.19, this is equivalent to
   the eventual block-injectivity formulation of Definition 2.19; see
   [SPGWC10, Proposition 3]." This correctly acknowledges the equivalence,
   resolving the long-standing cross-chapter terminology issue.
   Substantially addresses v2 cleanup item #9.

10. **Rmk 9.22 added.** Notes Burnside/Jacobson-density as "a substantial
    external algebraic dependency for the formalization," formalized
    directly in the project. Addresses v2 cleanup item #10.

11. **Thm 9.30 proof (= v2 8.29) AI language fixed.** v2: "the self-overlap
    condition is derived rather than stored as an extra field." v3: "the
    self-overlap condition follows from the other hypotheses rather than
    appearing as a separate assumption."

### New content (§9.9–§9.14)

v3 adds six new sections with 16 new statements (Def 9.36 through Rmk 9.50),
roughly doubling the chapter. These fill the "upstream passage" that v2's
Remark 8.35 identified as open.

**§9.9 Zero-block separation** (Def 9.36, Thms 9.37–9.38). Introduces the
zero MPS tensor and separates all-zero irreducible blocks from "live" blocks.
On the FT critical path.

**§9.10 Arbitrary-input TP-gauge reduction** (Thm 9.39). Combines zero-block
separation with blockwise TP gauging. On the FT critical path.

**§9.11 Blocking infrastructure** (Thms 9.40–9.43). Four theorems on blocking
distributing over MPV equivalence, primitivity under powers, divisibility,
and common blocking periods. On the FT critical path.

**§9.12 Cyclic sector decomposition** (Thms 9.44–9.46). Compression to
projection sectors, block decomposition from commuting projections, and from
adjoint-fixed projections. **Not on the FT critical path.** This is
infrastructure for the periodic extension of [DlCCSPG17] discussed in §12.4,
which the blueprint marks as incomplete.

**§9.13 Arbitrary tensor to primitive block decomposition** (Thms 9.47–9.49).
The main theorem combining all the above into a single pipeline from
arbitrary tensor to primitive block data. Plus two supporting results
(TP-primitive irreducible tensor is normal; blocking preserves normality).
On the FT critical path.

**§9.14 Open directions** (Rmk 9.50). Expanded from v2's Rmk 8.35 with more
specific identification of remaining gaps: establishing tensor irreducibility
after blocking, and establishing pairwise distinct weight norms.

### Non-substantive changes

- All theorem numbers shifted +1 from v2 (8.x → 9.x) plus offset from
  new Remark 9.22.
- Internal cross-references updated to match v3 numbering.
- Theorem 9.27 proof: v2 cited "Theorem 4.45" → v3 cites "Theorem 4.34";
  v2 cited "Theorem 4.37" → v3 cites "Theorem 4.26"; v2 cited
  "Lemma 4.41/4.42" → v3 cites "Lemma 4.30/4.31". All reflect v3
  renumbering of Chapter 4.

---

## 4. Forward Reference Verification

All forward references checked directly against v3 PDF:

| Reference | Target | Verified |
|---|---|---|
| Definition 10.9 (Thms 9.25, 9.26) | Canonical form predicate (p. 63) | ✓ |
| Theorem 8.52 (Thm 9.48) | Primitive MPS with PD fixed point is normal (p. 47) | ✓ |
| Chapter 12 (§9.8) | Periodic extension discussion (p. 72–73) | ✓ |
| Definition 4.12 (Def 9.14) | Irreducible map (p. 15) | ✓ |
| Theorem 6.15 (Thm 9.15) | PSD eigenvector for positive maps (p. 30) | ✓ |
| Theorem 4.39 (Thm 9.25) | Primitive maps have spectral gap (p. 19) | ✓ |
| Theorem 7.10 (Thm 9.25) | Eigenvalue bound (p. 36) | ✓ |
| Theorem 6.5 (Thm 9.25) | Uniqueness of PSD fixed point (p. 28) | ✓ |
| Theorem 7.21 (Thm 9.25) | Self-overlap convergence (p. 38) | ✓ |
| Theorem 4.34 (Thm 9.27) | Roots of unity via adjoint fixed point (p. 18) | ✓ |
| Theorem 4.26 (Thm 9.27) | Finiteness of peripheral eigenvalues (p. 17) | ✓ |
| Lemma 4.30 (Thm 9.27) | Common exponent for roots of unity (p. 17) | ✓ |
| Lemma 4.31 (Thm 9.27) | Powering collapses peripheral eigenvalues (p. 17) | ✓ |
| Theorem 6.3 (Thms 9.16, 9.31, 9.48) | PD upgrade under irreducibility (p. 27) | ✓ |
| Theorem 6.8 (Thm 9.31) | Existence of PSD fixed point (p. 29) | ✓ |
| Theorem 6.10 (Thm 9.31) | Unital gauge (p. 29) | ✓ |
| Theorem 7.12 (Thm 9.31) | Spectral radius ≥ 1 ⟹ gauge-phase equivalence (p. 36) | ✓ |
| Theorem 7.17 (Thm 9.24) | Overlap decay (p. 37) | ✓ |
| Lemma 2.12 (Thm 9.8) | Word evaluation under scaling (p. 7) | ✓ |
| Definition 2.19 (Def 9.29) | Normal tensor (algebraic) (p. 8) | ✓ |
| [SPGWC10, Prop. 3] (Def 9.29) | Equivalence of normal definitions | ✓ (cross-ref) |
| Theorem 6.9 (Thm 9.25) | Quantum Perron–Frobenius (p. 29) | ✓ |

---

## 5. Prior Review Items — Status

| v2 Review Item | Status in v3 |
|---|---|
| #1: Def 8.1 duplicates Def 2.23 | **Fixed.** Def 9.1 cross-references 2.23. |
| #2: Def 8.14 duplicates Def 4.23 | **Fixed.** Def 9.14 references Def 4.12. |
| #3: Thm 8.8 is a tautology | **Fixed.** Thm 9.8 rewritten with explicit factorization. |
| #4: Thm 8.13 "generate the same MPV" ambiguous | **Fixed.** Thm 9.13 specifies "block-diagonal tensor obtained by discarding off-diagonal blocks." |
| #5: Cesàro citation in Thm 8.15 requires TP | **Fixed.** Thm 9.15 parenthetical cites Thm 6.15 as alternative. |
| #6: Thm 8.24 proof should list three conditions | **Fixed.** Thm 9.25 proof lists all three explicitly. |
| #7: Thm 8.30 proof too compressed | **Fixed.** Thm 9.31 proof expanded with full chain. |
| #8: Thm 8.34 "trivial blocking" confusing | **Fixed.** Thm 9.35 proof now explicit about p = 1 and reordering. |
| #9: Two meanings of "normal" | **Substantially improved.** Def 9.29 acknowledges equivalence with Def 2.19 via [SPGWC10, Prop. 3]. |
| #10: Note Burnside as formalization dependency | **Fixed.** Rmk 9.22 added. |
| #11: Check Ch 9 (v2) DS gauge consistency | N/A (v2 Ch 9 = v3 Ch 10, separate review). |
| AI: "stored as an extra field" | **Fixed.** Thm 9.30 uses standard language. |

All 11 cleanup items addressed.

### Comprehensive reference items

| Item | Status |
|---|---|
| 8-F1: Two routes, two predicate families | Intact. Both routes present (Def 9.29 for normal-canonical, Def 10.9 for block-injective). |
| 8-F2: Adjoint-fixed-point route in Thm 8.26 | Intact as Thm 9.27. Same proof structure. |
| 8-F3: Burnside as external dependency | Addressed by new Rmk 9.22. |
| Part II AI: "assembly" | Still present in §9.1 and §9.13 titles. |
| Part II AI: "pipeline" | Still present in §9.10 title, Thm 9.39 name, Rmk 9.50. |

---

## 6. Statement-by-Statement Review

### §9.1 Block-diagonal assembly (Def 9.1, Thms 9.2–9.4)

All correct and unchanged from v2 except that Def 9.1 now cross-references
Def 2.23. No issues.

### §9.2 Transfer map normalization (Thms 9.5–9.8)

Thms 9.5–9.7 unchanged and correct. Thm 9.8 substantially improved — the
factorization μ_k = η_k |μ_k| with η_k := μ_k/|μ_k| is now explicit, and
the proof correctly uses Lemma 2.12. No issues.

### §9.3 Invariant subspace decomposition (Thm 9.9, Defs 9.10–9.11, Thms 9.12–9.13)

All correct and unchanged in substance. Thm 9.13 clarification ("block-
diagonal tensor obtained by discarding off-diagonal blocks") resolves the
v2 ambiguity.

### §9.4 Iterated reduction (Def 9.14, Thms 9.15–9.16)

Def 9.14 now correctly cross-references Def 4.12. Thm 9.15 proof expanded
with the Theorem 6.15 parenthetical. Thm 9.16 unchanged.

**Formalization note (9-K).** The Thm 9.15 parenthetical says Theorem 6.15
provides a PSD eigenvector (not necessarily a fixed point). Theorem 9.12 is
stated for fixed points (eigenvalue 1). The invariant-projection argument
works for any PSD eigenvector with positive eigenvalue (the proof is
identical after rescaling), but this generalization is not stated. For Lean,
either a variant of Thm 9.12 for eigenvectors, or an explicit rescaling
lemma, would be needed. Low priority.

### §9.4.1 Burnside bridge (Defs 9.17–9.19, Thms 9.20–9.21, Rmk 9.22, Thm 9.23)

All correct and unchanged except for the new Remark 9.22 noting Burnside
as a formalization dependency. The proof of Thm 9.21 (Jacobson density)
is correctly sketched.

### §9.5 Proportional single-block theorem (Thm 9.24)

Correct and unchanged from v2.

### §9.6 Canonical form from peripheral primitivity (Thm 9.25, Rmk 9.26, Thm 9.27, Rmk 9.28)

Thm 9.25 proof now explicitly verifies the three conditions for Thm 4.39.
The three conditions check out:

1. Primitivity: by hypothesis.
2. Eigenvalue bound |μ| ≤ 1: via Thm 7.10, since E = ℰ_{A_k} is the
   self-transfer of a TP-normalized tensor. (The proof writes "E = F_{A_k A_k}
   is a normalized mixed transfer operator" — technically correct since the
   self-transfer is a special case of the mixed transfer, but slightly odd
   phrasing. Low priority.)
3. Trace-zero fixed points are zero: from uniqueness of the PSD fixed
   point (Thm 6.5). Argument: if ρ₀ > 0 is the unique PSD fixed point and
   σ is a trace-zero fixed point, then ρ₀ + εσ ≥ 0 for small ε, giving
   another PSD fixed point; uniqueness forces σ = 0. ✓

Thm 9.27 proof correctly uses the adjoint-fixed-point route (unchanged
from v2). Cross-references updated to v3 numbering.

### §9.7 Normal canonical form (Def 9.29, Thm 9.30)

Def 9.29 correctly disambiguates "normal": now acknowledges equivalence with
Def 2.19 via [SPGWC10, Prop. 3]. This resolves the v2 issue where the
blueprint explicitly denied the equivalence.

Thm 9.30 proof language fixed (no more "stored as an extra field").

### Thm 9.31 (Modulus-one eigenvalue rigidity)

Proof substantially expanded. The chain is explicit: PSD fixed point
(Thm 6.8) → PD by irreducibility (Thm 6.3) → unital gauge (Thm 6.10)
→ KS equality / multiplicative domain (as in Thm 7.12) → intertwiner
= gauge-phase equivalence. Correct.

### §9.8 Steps toward CF existence (Thms 9.32–9.35)

Thms 9.32–9.34 unchanged in substance. Thm 9.35 proof clarified: p = 1
suffices, reordering step explicit. New: mentions [DlCCSPG17] and
forward-references §12.4 for the periodic extension.

### §9.9 Zero-block separation (Def 9.36, Thms 9.37–9.38) — NEW

Correct. The zero tensor is well-defined and the MPV formula is immediate.
The separation theorem (9.38) partitions irreducible blocks into all-zero
and "live" (at least one nonzero Kraus operator).

One minor point: the proof of Thm 9.38 says "The all-zero blocks satisfy a
dimension bound via irreducibility." This refers to the fact that an
irreducible tensor with all-zero Kraus operators must have D = 1 (since
any nontrivial projection would be invariant). Not explicitly stated but
follows from definitions. Acceptable for a blueprint.

### §9.10 Arbitrary-input TP-gauge reduction (Thm 9.39) — NEW

Correct. Chains Thm 9.38 (zero-block separation) with blockwise TP gauging.

### §9.11 Blocking infrastructure (Thms 9.40–9.43) — NEW

All four theorems are correct and straightforward.

Thm 9.40: blocking distributes over MPV equivalence. Uses the standard
identity V^(N)(A[p])_σ = V^(Np)(A)_{σ_flat}.

Thm 9.41: primitive under powers. Immediate from spectral mapping.

Thm 9.42: divisibility preserves primitivity. Follows from Thm 9.41.

Thm 9.43: common blocking period via lcm. Follows from Thm 9.42.

### §9.12 Cyclic sector decomposition (Thms 9.44–9.46) — NEW, OFF CRITICAL PATH

This section is infrastructure for the periodic extension of [DlCCSPG17]
(§12.4). It is **not used** by any theorem on the FT critical path.
Theorem 9.47 (the main assembly theorem) depends only on §9.9–9.11.

**Issue 9-D (Thm 9.44).** The statement says "Let A be a left-canonical MPS
tensor with ∑_i (A^i)†A^i = P for an orthogonal projection P." The
blueprint defines left-canonical as ∑_i (A^i)†A^i = 𝟙 (Theorem 6.11,
p. 29). If P ≠ 𝟙, the hypothesis contradicts the "left-canonical" label.

The intended usage (visible from Thm 9.45's proof) is: start with a
genuinely left-canonical tensor and commuting projections P_k; the sector
tensor P_k A^i satisfies ∑_i (P_k A^i)†(P_k A^i) = P_k. Theorem 9.44 is
the compression lemma for such a sector. The *output* C is genuinely
left-canonical (∑(C^i)†C^i = 𝟙_n), but the *input* is not.

**Recommendation:** Drop "left-canonical" from Thm 9.44's hypothesis.
Write: "Let A be an MPS tensor satisfying ∑_i (A^i)†A^i = P for an
orthogonal projection P, and suppose PA^iP = A^i for every i."

**Issue 9-E (Thm 9.46).** The proof says "The Kadison–Schwarz equality
condition for a TP map implies that a projection fixed by ℰ†_A commutes
with every Kraus operator." This is correct (the fixed projection lies in
the multiplicative domain of ℰ†_A) but should cite Theorem 5.9 (KS equality
implies Kraus commutation) or the multiplicative domain results of §5.2.

### §9.13 Assembly (Thms 9.47–9.49) — NEW

Thm 9.47 correctly chains Thms 9.39, 9.43, 9.40. This is the main
reduction theorem: arbitrary tensor → (after blocking) zero tail + primitive
left-canonical blocks with positive bond dimensions.

Thm 9.48 (TP-primitive irreducible ⟹ normal): correct. Uses Thm 6.3 (PD
upgrade) and Thm 8.52 (primitive + PD fixed point ⟹ normal).

Thm 9.49 (blocking preserves normality): correct. If S_N(A) = M_D, then
S_N(A[p]) ⊇ S_{Np}(A) = M_D.

### §9.14 Open directions (Rmk 9.50) — EXPANDED

Honestly identifies the remaining gap: "establishing tensor irreducibility
for each blocked block (blocking does not in general preserve tensor
irreducibility)" and "establishing pairwise distinct weight norms."
The cyclic-sector decomposition (§9.12) is noted as providing partial
infrastructure for the first gap.

---

## 7. Cross-Chapter Consistency

### Definition duplication

Both duplications flagged in v2 are resolved:
- Def 9.1 cross-references Def 2.23 (block-diagonal tensor).
- Def 9.14 cross-references Def 4.12 (irreducible map).

### "Normal" terminology

Def 9.29 now correctly states the equivalence with Def 2.19 via
[SPGWC10, Prop. 3]. This is a significant improvement over v2, which
denied the equivalence. The long-standing cross-chapter item X-1 from the
comprehensive reference is substantially resolved for this chapter.

### DS gauge

No residual DS gauge language. All normalization is TP throughout.

### Backward dependencies

All backward references to Chapters 2–8 verified correct (see §4 above).

### Forward dependencies

Def 10.9 (canonical form predicate) and Chapter 12 (periodic extension)
references verified correct.

---

## 8. Literature Alignment

The chapter correctly tracks the literature:

- Invariant-subspace splitting: [PGVWC07, Thm 4] and [CPGSV21, §IV.A.1].
- Burnside bridge: Jacobson density theorem [Jac09].
- CFII construction: [CPGSV17, Appendix A].
- Normal canonical form: [CPGSV17, §2.3].
- Wedderburn–Artin alternative: [Wol12, Thm. 6.14] (mentioned, not taken).
- Support projection / invariant subspaces: [Wol12, Prop. 6.10, Thm. 6.2].
- Normal equivalence: [SPGWC10, Prop. 3].
- Periodic extension: [DlCCSPG17] (new in v3, forward reference to §12.4).

[DlCCSPG17] is De las Cuevas, Cirac, Schuch, Perez-Garcia 2017. The
reference is not among the project PDFs, so the citation cannot be verified
against the source. The mathematical content (periodic fundamental theorem
without blocking) is standard.

---

## 9. AI-Language Audit

### Still present

| Phrase | Location | Recommendation |
|---|---|---|
| "Block-diagonal assembly" | §9.1 title | "Block-diagonal structure" or "Block-diagonal construction" |
| "Assembly: arbitrary tensor to primitive block decomposition" | §9.13 title | "Reduction to primitive blocks" or "From arbitrary tensors to primitive block data" |
| "Arbitrary-input TP-gauge pipeline" | §9.10 title, Thm 9.39 name | "Arbitrary-input TP-gauge reduction" |
| "pipeline" | §9.10 title, Thm 9.39, Rmk 9.50 (×5 total) | "reduction," "construction," or "chain" |
| "core pipeline steps are in place" | Rmk 9.50 | "core reduction steps are in place" |
| "arbitrary-input pipeline" | Rmk 9.50 | "arbitrary-input reduction" |

### Fixed from v2

| v2 phrase | v3 replacement |
|---|---|
| "stored as an extra field" (Thm 8.29) | "appearing as a separate assumption" (Thm 9.30) |

---

## 10. Formalization Notes

### 8-F1 (two predicate families) — intact

Both routes present: block-injective (Def 10.9) and normal-canonical
(Def 9.29). Bridge between them is Theorem 9.25.

### 8-F2 (adjoint-fixed-point route) — intact

Thm 9.27 uses the same adjoint-fixed-point proof. Cross-references
updated to v3 Chapter 4 numbering.

### 8-F3 (Burnside as external dependency) — addressed

Rmk 9.22 explicitly notes Burnside/Jacobson-density is formalized directly
in the project. If Mathlib later acquires it, the chapter can be retargeted.

### New formalization note: 9-K (eigenvector vs fixed point)

Thm 9.15's parenthetical invokes Thm 6.15 (PSD eigenvector) but Thm 9.12
is stated for fixed points (eigenvalue 1). The invariant-projection argument
generalizes to any PSD eigenvector with positive eigenvalue (the proof is
identical up to rescaling). For Lean, either:
- State a variant of Thm 9.12 for eigenvectors, or
- Add a one-line rescaling lemma (PSD eigenvector with eigenvalue λ > 0
  gives PSD fixed point of λ⁻¹ℰ_A).

Low priority.

### New formalization note: 9-L (cyclic sector compression)

Thm 9.44's compression step (restricting to the support of P) requires
constructing a rectangular isometry V : ℂⁿ → ℂᴰ from the spectral
decomposition of P. In Lean, this is a `Matrix.submatrix` or similar
construction. Off the FT critical path.

---

## 11. Cleanup Checklist

### Must fix

(None.)

### Should fix

1. **§9.10 title, Thm 9.39, Rmk 9.50: "pipeline" → "reduction."** Five
   occurrences. AI language per Part II of comprehensive reference.
   On FT critical path.

2. **§9.1 and §9.13 titles: "assembly."** Two occurrences. AI language.
   On FT critical path.

3. **Thm 9.44: "left-canonical" misnomer.** Drop "left-canonical" from the
   hypothesis; state ∑(A^i)†A^i = P directly. Off FT critical path.

4. **Thm 9.46 proof: cite Thm 5.9** (KS equality ⟹ Kraus commutation) or
   the multiplicative domain results of §5.2. Off FT critical path.

### Low priority

5. **Thm 9.25 proof: "E = F_{A_k A_k} is a normalized mixed transfer
   operator."** Calling the self-transfer "mixed" is technically correct
   but stylistically odd. Consider "E = ℰ_{A_k} is a normalized transfer
   operator."

6. **[DlCCSPG17] reference.** Not among project PDFs; citation format
   cannot be verified.

7. **Formalization note 9-K.** Thm 9.12 should either be generalized to
   PSD eigenvectors or supplemented with a rescaling lemma, for the
   Thm 9.15 parenthetical to be directly formalizable.

### Acceptable as-is

8. **Def 9.29 "normal" disambiguation.** Now correctly states equivalence
   with Def 2.19. The two definitions coexist with a cross-reference.

9. **Rmk 9.50 open directions.** Honestly identifies remaining gaps
   (irreducibility after blocking, pairwise distinct weight norms).

10. **§9.12 off critical path.** The section provides forward-looking
    infrastructure for §12.4 (periodic extension). Not needed for the
    main FT.

---

## 12. Final Assessment

Chapter 9 in v3 is a substantial improvement over v2's Chapter 8. All 11
cleanup items from the v2 review are addressed, several compressed proofs
have been expanded, and the chapter has nearly doubled in size with new
content (§9.9–9.13) that fills the "upstream passage" previously flagged
as open. The most significant conceptual improvement is the correction of
the "normal" disambiguation in Definition 9.29, which now correctly
acknowledges the equivalence with Definition 2.19 via [SPGWC10, Prop. 3].

The remaining issues are:
- AI language ("pipeline" ×5, "assembly" ×2) — should fix.
- One misnomer in Theorem 9.44 ("left-canonical") — should fix, but off
  the FT critical path.
- One missing citation in Theorem 9.46 — should fix, off critical path.
- Minor formalization notes (eigenvector vs fixed point, self-transfer
  phrasing).

No mathematical errors found. The FT critical path through this chapter
runs via §9.1–9.11 and §9.13 (Theorem 9.47 being the main output); §9.12
is off-path infrastructure for the periodic extension.
