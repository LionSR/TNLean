# Blueprint v4 Quality Scout Findings

**Date:** April 8, 2026
**Scope:** All newer/expanded chapters (ch02b, ch04b, ch06, ch08, ch11, ch12, ch13, ch13b, ch14, ch15, ch16)
**Method:** Parallel codex scouts, each comparing against ch04_channels.tex as reference

---

## Cross-cutting issues (appear in multiple chapters)

### 1. Theorems without proofs not marked `\notready`
- **ch14** lines 494-502 (chain ground space block-injective), 504-513 (normal), 566-580 (block-injective/normal unique GS)
- **ch06** lines 664-739 (scalar conditional expectation block), 826-905 (Wedderburn section), 1011-1123 (declaration subsections)
- **ch13** lines 1177-1231 (six PEPS theorems)
- **ch12** lines 769-839 (auxiliary theorems), 857-887 (fraction-slice)

### 2. Formalization-speak in prose
- **ch14**: "implemented as", "implemented via the star-projection"
- **ch06**: subsection titles "Cyclic decomposition declarations", "Peripheral group-structure declarations"
- **ch12**: `\mathrm{dysonTerm}_n(t)`, "Fraction-slice bridge", "is now formalized in Lean"
- **ch13**: `(\mathrm{gaugeVertex}\; X\; A\; v)`, "(scaffold)" section title, `\ell_A`/`\ell_B`

### 3. Missing/inaccurate `\uses{}` in proofs
- **ch13** lines 252-285 (missing `lem:center_scalar`), 543-555 (same), 630-642 (missing `lem:tensor_proportional`)
- **ch06** multiple proofs cite results without `\uses`

### 4. Notation inconsistency
- **ch12**: `T(t)` vs `T_t`, `\MN{D}` vs `\MN{d}` vs `M_d(\C)`
- **ch06**: `\rho(F_{AB})` vs `\rho_{\mathrm{spec}}(E-P)`
- **ch14**: `\sigma_1,\dots,\sigma_L` vs `\sigma_0,\dots,\sigma_{N-1}`

### 5. Over-compressed proofs
- **ch06** lines 595-599, 616-623, 535-546
- **ch12** lines 542-554, 983-989, 1058-1064
- **ch13** lines 685-688, 827-833, 919-951

---

## Per-chapter summaries

### ch14_parent_hamiltonian.tex (Chapter 18)
Already partially fixed in round 1. Remaining:
- Must: ambiguous definition of periodic chain ground space (line 455-468)
- Must: theorems 18.32, 18.33, 18.35, 18.36 still have no proofs
- Should: notation G_L^{left/right} undefined (line 343-349)
- Should: "implemented as" language (lines 32-44)

### ch06_spectral.tex (Chapter 9)
Heavy tail section with declaration dumps:
- Must: conditional expectation block (664-739) all proofless
- Must: Wedderburn section (826-905) mostly proofless
- Must: declaration subsections (1011-1123) are stubs
- Should: "Cyclic decomposition declarations" → rename
- Should: compressed proofs at 535-546, 595-599

### ch13_algebraic_ft.tex (Chapter 16)
Complex chapter with multiple gaps:
- Must: virtual-bond-gauge proof gap (lines 159-167, 252-285)
- Must: PEPS section has 6 theorems with no proofs (1177-1231)
- Must: normal-MPS corollary proof is placeholder (630-642)
- Should: missing `\uses{}` in several proofs
- Should: Lean-like notation in PEPS section

### ch12_semigroup.tex (Chapter 15)
Notation drift and proofless blocks:
- Must: multiple `\notready`-equivalent gaps (769-839, 857-887)
- Must: Cor 7.2(3) undefined variable C (1270-1283)
- Medium: "Fraction-slice bridge" is formalization-speak
- Medium: notation drifts T(t) vs T_t, MN{D} vs M_d

### ch13b_symmetry.tex (Chapter 17)
(Scout report pending)

### ch08_canonical.tex (Chapter 11)
(Scout report pending)

### ch11_assembly.tex (Chapter 14)
(Scout report pending)

### ch02b_mpdo.tex, ch04b_entropy.tex (Chapters 3, 6)
(Scout report pending)

### ch15_correlations.tex, ch16_examples.tex (Chapters 19, 20)
(Scout report pending)

---

## Priority triage for this PR

### Batch 1: Mechanical cross-cutting fixes (do now)
1. Rename formalization-speak subsection titles in ch06
2. Remove "(bundled)" from ch14 decorrelation theorem
3. Fix "implemented as/via" language in ch14

### Batch 2: Add `\notready` markers (do now)
1. ch14: theorems without proofs that aren't marked
2. ch13: PEPS theorems without proofs

### Batch 3: Requires mathematical work (defer to follow-up)
1. Compressed proofs needing expansion
2. Notation normalization across chapters
3. Missing proof content in ch06, ch12, ch13
