# Blueprint v4 Review Plan

**Date:** April 7, 2026
**v4 file:** `blueprint-v4.pdf` (text, 7427 lines, 20 chapters)
**v3 file:** `blueprintv3.pdf` (ZIP/page-image, ~4000 lines, 13 chapters)

---

## Structural overview

v4 nearly doubles v3 in length. The original 13-chapter structure is preserved (with renumbering due to two inserted chapters), and 5 entirely new chapters are appended.

## Chapter mapping: v3 → v4

| v3 Ch | v4 Ch | Topic | Change type |
|-------|-------|-------|-------------|
| 2 | 2 | Matrix Product Vectors | Expanded: new §2.2 (periodic-chain aliases), §2.7 (MPV overlap) |
| — | **3** | **MPO and Density Operators** | **New chapter** |
| 3 | 4 | Single-Block Fundamental Theorem | Expanded: new §4.5 (non-TI setup) |
| 4 | 5 | Quantum Channels and Positive Maps | Significantly expanded: new §5.6–5.12 (representation infrastructure, Choi–Jamiołkowski, Kraus, Stinespring, determinant, fixed-point algebra, QDS stub) |
| — | **6** | **Quantum Entropy** | **New chapter** (von Neumann entropy, SSA, mutual information) |
| 5 | 7 | Schwarz Inequalities and Multiplicative Domains | Expanded: new §7.1.1–7.1.2 (two-positive maps, Douglas factorization), §7.2.3 (subnormal/commuting-dominant operators) |
| 6 | 8 | Perron–Frobenius Theory | Diff TBD |
| 7 | 9 | Spectral Gap and Block Separation | Significantly expanded: new §9.3 (Frobenius norm infrastructure), §9.8–9.14 (TP hypotheses, conditional expectation, stationary support, Wedderburn, Wolf Ch 6 equivalences, peripheral eigenvalue group, cyclic decomposition, primitive overlap convergence) |
| 8 | 10 | Wielandt Bound | Diff TBD |
| 9 | 11 | Canonical Form Reduction | Expanded: new §11.9–11.13 subsections (zero-block separation, TP-gauge reduction, blocking infrastructure, cyclic sector decomposition, reduction to primitive blocks with sub-subsections) |
| 10 | 12 | Block Permutation and Separation | Diff TBD |
| 11 | 13 | Basis of Normal Tensors | Diff TBD |
| 12 | 14 | Proof of the Fundamental Theorem | Expanded: new §14.3.1 (multiplicity data with repeated blocks), §14.4.1–14.4.5 (irreducible form, common-period helpers, Z-gauge, periodic FT statement, periodic overlap dichotomy) |
| 13 | 15 | Quantum Dynamical Semigroups | Greatly expanded: new subsections on Kossakowski matrix, primitivity/irreducibility of QDS, kernel of adjoint Liouvillian, reducibility |
| — | **16** | **The Algebraic Fundamental Theorem** | **New chapter** (one-sided inverse, physical realisation, aligned gauges, injective-chain FT, multi-block FT, TI reduction, global symmetry) |
| — | **17** | **Symmetries and String Order** | **New chapter** (virtual gauges, virtual representation theorem, cohomology classes, permutation symmetry, string order, SPT classification) |
| — | **18** | **Parent Hamiltonians** | **New chapter** (local ground space, parent interaction, intersection property, unique ground state, commuting Hamiltonians, decorrelation, spectral gap, non-injective ground space) |
| — | **19** | **Exponential Decay of Correlations** | **New chapter** (connected correlators, spectral expansion, quantitative bounds, relation to parent Hamiltonians, renormalization fixed points) |
| — | **20** | **Concrete Examples** | **New chapter** (GHZ, AKLT, cluster state) |

## Review plan

### Chapters with v3 counterparts (v4 Ch 2, 4, 5, 7–15)

- **Diff-only review**: skip lines identical to v3 (up to relabeling/renumbering).
- Focus on: new definitions, changed theorem statements, new proof content, changed hypotheses.
- Cross-check against prior v3 review files and the comprehensive reference.
- Track whether prior review issues (from v2→v3 reviews) have been addressed.

### New chapters (v4 Ch 3, 6, 16–20)

- **Full standalone review** against primary literature.
- Chapters 16–20 are largely beyond the original FT critical path (Ch 16 overlaps); flag FT-relevance explicitly.

### Tensor network diagrams

v4 includes tensor network diagrams in proofs. For each diagram:
1. Verify it is a valid tensor network diagram (correct leg structure, contraction pattern).
2. Verify it corresponds to the surrounding proof text (same equation, same identity).
3. Flag any diagram that is ambiguous, incorrect, or disconnected from the proof.

### Pacing

- One chapter per message when substantial.
- Batch short or minimally-changed chapters.
- Each review produces a `blueprint_chapter{N}_v4_review.md` file.

### Governing documents

- `v3_review_standing_instructions.md` (review protocol, output structure, key instructions)
- `blueprint_review_comprehensive_reference.md` (full reference: protocol, AI-language catalogue, notation audit, formalization notes, orphaned statements)
- Per-chapter v3 review files: `blueprint_chapter{N}_v3_review.md`
- `formalization_goal_analysis.md`, `full_ft_verification.md`
