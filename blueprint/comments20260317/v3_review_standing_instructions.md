
# v3 Blueprint Review — Standing Instructions

These instructions govern the chapter-by-chapter review of `blueprintv3.pdf`
against `blueprint__v2.pdf` and the prior review corpus. They were
established during the review of Chapters 2–4 and should be carried
forward to all subsequent chapters.

---

## Source Documents

**Blueprints:**
- `blueprintv3.pdf` (v3, March 16 2026, 80 pages, LaTeX PDF, clean text extraction via `pdftotext`)
- `blueprint__v2.pdf` (v2, March 14 2026, 55 pages, also clean LaTeX PDF)
- `blueprint20260302.pdf` (v1, old format)

**Review corpus (from prior v1→v2 reviews):**
- `blueprint_chapterN_review.md` for N = 2–11: per-chapter detailed reviews
- `blueprint_chapters2to6_review_consolidated.md`: consolidated summary of Ch 2–6 reviews with "Corrected in v2" / "Remaining open" structure
- `blueprint_review_comprehensive_reference.md`: the governing document containing:
  - Part I: Review protocol (criteria, workflow, output structure)
  - Part II: AI-style language patterns and corrections (accumulated catalogue)
  - Part III: Cross-chapter notation audit
  - Part IV: Formalization notes (type-level transitions)
  - Part V: Orphaned statements and dependency graph

**Primary literature:**
- CPGSV21 = `Cirac_Quantum_Wielandt_inequality.pdf`
- PGVWC07 = `PerezGarcia__MPS_representations.pdf`
- CPGSV17 = `Cirac_MPDO__fixed_points.pdf`
- Wolf's quantum channels notes (accessible via project knowledge search, not as standard PDF)

**Web blueprint** (for spot-checking cross-references and Lean declarations):
- Base URL: `https://sirui-lu.com/TNLean/blueprint/`
- Chapter URLs: `ch-mps.html`, `ch-single.html`, `ch-channels.html`, etc.
- Use only for targeted checks; the PDF is the primary source due to token efficiency.

---

## Review Protocol

Follow the protocol in `blueprint_review_comprehensive_reference.md` Part I.

### Required criteria (all 8):
1. Consistency with known literature
2. Repetitive or conflicting statements
3. Missing clarifications or subtleties
4. Deviations from the literature
5. Unused or missing definitions
6. Structural or logical issues
7. Statement-by-statement review
8. AI-generated language

### Required output structure for each chapter review .md file:
- Global chapter assessment (table)
- v2 → v3 changes (substantive, non-substantive, unchanged)
- Forward reference verification (check directly against v3 PDF, do not defer)
- Review items: prior status check (from per-chapter review, consolidated review, and comprehensive reference)
- Statement-by-statement analysis
- Cross-chapter consistency
- Literature alignment
- AI-language audit (cross-reference against Part II of comprehensive reference)
- Formalization notes (from Part IV of comprehensive reference)
- Cleanup checklist (must fix / should fix / low priority / acceptable as-is)
- Final assessment

---

## Key Instructions (from the user)

### 1. Use PDF files only for blueprints
Do not use the web blueprint for chapter content. The web version wastes
tokens on the repeated sidebar ToC. Use the PDF via `pdftotext` extraction.
The web blueprint may be used for targeted cross-reference checks only.

### 2. Verify forward references directly
Do not defer cross-chapter reference verification to later reviews. Check
each forward reference against the v3 PDF in the same review where it
appears. This is important because each chat is restricted to one or a
few chapters.

### 3. Flag new content relevance for the Fundamental Theorem
When encountering new sections in v3, explicitly flag whether they are on
the FT critical path or not. The FT proof chain runs through Chapters
2–3, 4 (§4.1–4.5), 5 (KS/mult domain), 6 (Perron-Frobenius), 7 (spectral
gap), 8 (Wielandt), 9 (canonical form), 10 (block permutation), 11 (BNT),
12 (full assembly). New material that serves only Chapter 13 (dynamical
semigroups) or is illustrative (e.g., Wolf Example 5.3) should be noted as
low priority.

### 4. AI-language audit
The blueprint should read as a mathematical document that happens to be
targeted at formalization, not as documentation for a codebase. Flag and
recommend replacements for:
- "Assembly" as a section title → "Proof of [theorem name]"
- "Pipeline" → "construction" or specific mathematical description
- "In this blueprint" / "Within this blueprint" → "here" or "in what follows"
- "Bridge" → "connection" or name by content
- Formalization jargon in prose (e.g., "stored as an extra field," "re-exports," "sorry-free")
- The full catalogue is in Part II of `blueprint_review_comprehensive_reference.md`

The title of Chapter 12 ("Full Assembly") is a known example — no
mathematician titles a chapter "Full Assembly."

### 5. Diff the actual text
Always diff the actual text content between v2 and v3, not just the
structural overview. Even sections that appear to be "just renumbered" may
have genuine content changes (as discovered in Ch 4: Lemma 4.33 proof
rewrite, new Theorem 4.26).

### 6. Explain in addition to producing .md files
Do not just produce the .md file silently. Explain the findings in the
chat — what changed, what matters, what's new, what remains open. The .md
file is for the formalization agent; the chat explanation is for the user.

### 7. Check the consolidated review
Before writing the chapter review, re-read the relevant section of
`blueprint_chapters2to6_review_consolidated.md` (for Chapters 2–6) and
the per-chapter review file. Verify that all items from those files are
tracked in the new review.

### 8. Precision standard
This is for Lean formalization. Check mathematical correctness at the
statement level: hypotheses, quantifiers, type-level distinctions, scope
of applicability. Flag conventions (e.g., Choi matrix normalization) that
differ from common references.

### 9. Chapter renumbering in v3
v3 has 13 chapters vs v2's 11. The mapping is:
- v2 Ch 1–3 = v3 Ch 1–3 (unchanged)
- v2 Ch 4 §4.1, §4.4–4.7 = v3 Ch 4 §4.1–4.5 (renumbered, KS/mult domain removed)
- v2 Ch 4 §4.2–4.3 (KS, mult domain) = v3 Ch 5 (new chapter)
- v2 Ch 5 (Perron-Frobenius) = v3 Ch 6
- v2 Ch 6 (Spectral gap) = v3 Ch 7
- v2 Ch 7 (Wielandt) = v3 Ch 8
- v2 Ch 8 (Canonical form) = v3 Ch 9
- v2 Ch 9 (Block permutation) = v3 Ch 10
- v2 Ch 10 (BNT) = v3 Ch 11
- v2 Ch 11 (Full assembly) = v3 Ch 12
- v3 Ch 13 (Quantum dynamical semigroups) = entirely new

The comprehensive reference and per-chapter review files use v2 numbering.
The formalization notes in Part IV use v2 theorem numbers. When writing
v3 reviews, always provide the v2→v3 number mapping for the chapter
under review.

---

## Completed Reviews

| Chapter (v3) | v3 Review File | Status |
|---|---|---|
| 2 | `blueprint_chapter2_v3_review.md` | Complete |
| 3 | `blueprint_chapter3_v3_review.md` | Complete |
| 4 | `blueprint_chapter4_v3_review.md` | Complete |
| 5 | `blueprint_chapter5_v3_review.md` | Complete |
| 6 | `blueprint_chapter6_v3_review.md` | Complete |
| 7 | `blueprint_chapter7_v3_review.md` | Complete |
| 8 | `blueprint_chapter8_v3_review.md` | Complete |
| 9 | `blueprint_chapter9_v3_review.md` | Complete |
| 10 | `blueprint_chapter10_v3_review.md` | Complete |
| 11 | `blueprint_chapter11_v3_review.md` | Complete |
| 12 | `blueprint_chapter12_v3_review.md` | Complete |
| 13 | Not yet started | Pending (not on FT critical path) |

All FT-critical chapters (2–12) are now reviewed. The full review corpus
consists of the v3 per-chapter reviews above, the v2 per-chapter reviews
(`blueprint_chapterN_review.md`), the consolidated v2 review
(`blueprint_chapters2to6_review_consolidated.md`), the comprehensive
reference (`blueprint_review_comprehensive_reference.md`), the full FT
verification (`full_ft_verification.md`), and the formalization goal
analysis (`formalization_goal_analysis.md`).

---

## Notes for Chapter 13 (the only remaining chapter)

- **Chapter 13 (v3):** Entirely new. Quantum dynamical semigroups / GKSL.
  Not on the FT critical path. No v2 counterpart exists, so this would be
  a standalone review against the primary literature only.

---

## Summary of FT Proof Status

The Fundamental Theorem of Matrix Product States is proved at the paper's
own standard (Level A: tensors already in canonical form). Theorem 12.5
recovers [CPGSV21, Corollary IV.5] unconditionally, as stated in
Remark 12.7. The proof chain is:

  Theorem 12.2 (proportional FT) + Theorem 11.5 (BNT linear independence)
  → Theorem 12.5 (unconditional equal-MPV FT) → full gauge equivalence.

Two gaps remain in the CF existence pipeline (Chapter 9, Remark 9.50) for
the fully unconditional theorem (Level B: from arbitrary tensors). These
are documented in `formalization_goal_analysis.md` and are mechanical
rather than conceptual.
