# Blueprint Style Guide & Lessons Learned

## Core Philosophy
The blueprint links the mathematics to its Lean formalization. A reader should be able to read a blueprint entry and immediately understand the corresponding Lean declaration. Conversely, someone reading the Lean code should find the blueprint proof sketch faithful to what the code actually does.

## General Principles
1. **Blueprint ↔ Lean must match.** Every `\lean{X}` tag must correspond to an actual Lean declaration. Every proof sketch must match what the Lean proof actually does — not a hand-wavy version of it.
2. **Standalone.** `blueprint/` and `slides/` are independent — no cross-references, no shared files. Each has its own macros, its own `references.bib`.
3. **Mathematical language only — zero Lean jargon.** See [`prose_style.md`](prose_style.md) Section 1 for the full rule and examples; in short, the `\lean{...}` tag is the link, the body text is standard mathematics.
4. **No filler prose.** Only precise definitions, theorem statements, and proof sketches. No "this is important because..." or "the transfer map governs the spectral theory...".
5. **Cite non-trivial things.** Basic definitions (MPS tensor, MPV) don't need citations. Important results and non-obvious definitions should cite the source paper.
6. **Don't invent terminology or notation.** Don't create ad-hoc notation like `⟨·,·⟩^ip` when standard notation exists. Don't name things that the literature doesn't name. If Lean calls it `IsInjective`, the blueprint says "injective" — not "Condition C1".
7. **Do not use external theorem numbers as titles.** Theorem, lemma, and
   definition headings should name the mathematical content. Put external
   numbering in the body with a full citation, e.g.
   `This is \cite[Theorem~4.1]{...}`. Do not write headings such as
   `Theorem 4.1` unless the source is also named and the title remains
   mathematically descriptive.
8. **Match Lean's theorem/lemma/def exactly.** If Lean says `theorem X`, use `\begin{theorem}`. If Lean says `lemma X`, use `\begin{lemma}`. Never use `\begin{proposition}` (Lean has no `proposition` keyword). Label prefix: `thm:` for theorem, `lem:` for lemma, `def:` for definition.
9. **Do not put prose quantifiers at the edge of displayed equations.** Avoid
   `\qquad \text{for all ...}` and similar tails in displays. State the
   quantifier in the surrounding sentence, or use mathematical quantifier
   notation when it is part of the formula. See [`prose_style.md`](prose_style.md)
   for the full rule and examples.
10. **Paper source first.** When a theorem, lemma, or proof sketch formalizes a
    cited result, compare against the paper source before introducing local names.
    Use the source notation and display the defining equations whenever possible.
    If Lean proves an auxiliary reformulation, state the source result first.
    Put maintainer-only proof-status notes in LaTeX comments, not displayed
    mathematical prose.

## Proof Sketches Must Match Lean
This is the most important rule. Every proof in the blueprint must faithfully describe what the Lean proof does:

- **Reference the actual lemmas used.** If the Lean proof calls `evalWord_gauge`, the blueprint proof should say "By Lemma X.Y (word evaluation under conjugation)..." and list it in `\uses`.
- **Describe the actual proof structure.** If Lean does induction on `w`, say "By induction on the word $w$." If Lean uses a specific decomposition, name it.
- **Don't hand-wave where Lean is specific.** "Standard argument" is not acceptable if Lean uses three specific lemmas. Name them.
- **Don't be more specific than Lean.** If Lean uses `simp` to close a goal, a one-line sketch is fine.
- **`\uses` in proofs must be accurate.** Only list what the proof actually uses, not what the statement mentions. If the proof uses `lem:eval_word_gauge` but the statement mentions `def:gauge_equiv`, the proof's `\uses` should list the lemma, not the definition (unless the proof also directly unfolds the definition).
- **Do not present local auxiliary routes as source mathematics.** If a proof uses
  a formal auxiliary lemma not stated in the cited source, name the mathematical
  assertion it proves. Put maintainer-only proof-status notes in LaTeX comments.
  If the auxiliary route is no longer used by the checked proof, delete the entry
  rather than keeping an unmotivated theorem-like statement in the blueprint.

## Notation Consistency
Notation must be **internally consistent** across the entire blueprint and **close to what the Lean code expresses**:

- Use `$...$` for inline mathematics in new blueprint prose. Do not mix `$...$`
  and `\(...\)` inside a newly edited paragraph; when touching an existing
  paragraph, prefer converting the local inline math to `$...$`.

- **Indices**: 0 to d−1 (matching `Fin d` in Lean), not 1 to d
- **Word evaluation**: $A^w$ for a word $w = (i_1, \ldots, i_L)$. The result is $A^{i_1} \cdots A^{i_L} \in \MN{D}$.
- **Word length**: $|w|$, never $L$ unless $L$ is a fixed blocking length in context.
- **MPV vector**: $\ket{V^{(N)}(A)}$ for the full ket vector.
- **MPV component**: $V^{(N)}(A)_\sigma = \tr(A^{i_1} \cdots A^{i_N})$ for a single coefficient.
- **Overlap**: $O_{AB}(N) = \sum_\sigma V^{(N)}(A)_\sigma \, \overline{V^{(N)}(B)_\sigma}$.
- **Inner product**: $\braket{V^{(N)}(A)}{V^{(N)}(B)}$ using the standard braket macro (conjugate-linear in first argument).
- **Transfer map**: $\E_A(X) = \sum_i A^i X (A^i)^\dagger$.
- **Blocked tensor**: $A^{[L]}$ with $(A^{[L]})^{(i_1,\ldots,i_L)} = A^{i_1} \cdots A^{i_L}$.
- **Flattened word**: $\widetilde{w}$ for a word in the original alphabet obtained by decoding blocked indices.
- **Canonical form scaling**: $\mu_k$ for the scaling factors, $A^i = \bigoplus_k \mu_k A_k^i$.
- **System size**: $N$ (reserved). **Blocking length**: $L$ or $L_0$.
- **Collections**: curly brackets `\{A^i\}_{i=0}^{d-1}`, not parentheses.
- **DeclareMathOperator subscripts**: always use braces: `\spn_{\C}` not `\spn_\C`.
- **Macros** (in `macros/common.tex`): `\C`, `\R`, `\N`, `\Z`, `\E`, `\Id`, `\MD`, `\MN{D}`, `\GL`, `\tr`, `\spn`, `\ket{·}`, `\bra{·}`, `\braket{·}{·}`, `\ketbra{·}{·}`, `\mc{·}`

## Prose conventions, banned language, and "no Lean jargon"

The rules for prose tone, the no-Lean-jargon-in-blueprint requirement, and the full
banned-language tables (software-engineering jargon and LLM writing patterns) live
in their own document:

> **See [`prose_style.md`](prose_style.md) for the authoritative prose style guide.**

That document covers:

1. **No Lean jargon in the leanblueprint** — the `\lean{...}` tag is the link to
   the formalization; blueprint prose must read as standard mathematics with no
   Lean identifiers, namespaces, or tactic syntax.
2. **Banned software-engineering terms → replacements** (e.g. "pipeline",
   "boilerplate", "wrapper", "hook", "API" / "endpoint" in prose, "utility" /
   "helper" as nouns).
3. **Banned LLM writing patterns → replacements** (e.g. "leverage", "delve into",
   "tapestry", "shed light on", "testament to", filler "moreover" / "furthermore").
4. **Additional rules** about `Assembly`/`Pipeline` grandfathering, Lean section
   naming, and definitions-vs-theorems.

These rules apply to ALL reader-facing text — blueprint `.tex` files AND Lean
docstrings, sectioning comments, and `section`/`namespace` names — and are
enforced by the dedicated `Blueprint Sync & Prose Review` CI workflow.

## `\uses` Dependency Guidelines
- **Statement `\uses`**: list only what's needed to *state* the result (typically definitions of the objects involved). Keep minimal — transitive deps are automatic.
- **Proof `\uses`**: list only what the proof *actually calls*. If the Lean proof uses `lem:eval_word_gauge`, list it. Don't list `def:gauge_equiv` unless the proof unfolds that definition.
- **Never self-reference**: a proof's `\uses` must NOT include the label of the theorem it proves.
- **Hypotheses vs definitions**: If a Lean lemma takes a pointwise hypothesis (like `∀ i, B i = X * A i * X⁻¹`) rather than a bundled structure (like `GaugeEquiv A B`), the blueprint statement's `\uses` should NOT list the bundled definition — the lemma is more general than that.

## Blueprint Structure
- `content.tex` is a router: `\input{chapter/ch01_intro}` etc.
- Each chapter is a separate file in `chapter/`
- Definitions/theorems numbered within chapters: `\newtheorem{theorem}{Theorem}[chapter]`

## Lean Blueprint Macros
- `\lean{Namespace.DeclName}` — links to Lean declaration
- `\leanok` — marks definition/theorem/proof as fully formalized
- `\uses{label1, label2}` — declares dependency edges for the graph
- `\notready` — marks as not ready for formalization (orange in graph)
- `\mathlibok` — already in Mathlib (dark green in graph)

## Dependency Graph Colors (web)
- **Light green box**: definition with `\lean` + `\leanok` (defined in Lean)
- **Green**: theorem stated + `\lean` + `\leanok` (stated in Lean)
- **Dark green**: theorem with proof also `\leanok` (fully proved)
- **Blue**: ready to state/prove (all deps are done)
- **Orange**: `\notready` (needs more blueprint work)

## Bibliography Workflow
1. Edit `blueprint/src/references.bib` (standalone, AuthorYYYYKeyword keys)
2. Run `cd blueprint/src && latexmk -lualatex -interaction=nonstopmode print.tex` (generates `print.bbl`)
3. Copy `blueprint/src/print.bbl` → `blueprint/src/web.bbl`  ← **must do this every time bib changes**
4. Run `leanblueprint web` (plasTeX reads `web.bbl`)
5. Citation key format: e.g., `Cirac2021Matrix`, `PerezGarcia2007Matrix`

## Stale/Corrupt Aux File Recovery
If LaTeX reports `! File ended while scanning use of \@newl@bel` on startup:
- The `.aux` file was truncated by a previous killed/timed-out run
- Fix: `rm -f blueprint/src/print.aux blueprint/print/print.aux blueprint/print.aux`
- Then rerun latexmk — it rebuilds the aux from scratch cleanly
- After rebuild, copy fresh `print.bbl` → `web.bbl`

## Build Commands
```bash
leanblueprint pdf     # PDF → blueprint/print/print.pdf
leanblueprint web     # HTML → blueprint/web/
leanblueprint serve   # local server at http://0.0.0.0:8000/
leanblueprint all     # pdf + web + checkdecls
```

## Fact-Check Lessons
- **Chapter 2**: `mpv` in Lean returns a scalar (the σ-component), NOT a ket vector. The ket is `mpvState`. Blueprint presents the ket form (standard physics) but `\lean{MPSTensor.mpv}` points to the component function — this is acceptable as long as it's clear.
- **Chapter 2**: Overlap and inner product differ by conjugation. Lean: `mpvOverlap A B N = star (mpvInner A B N)`. The overlap sums $V_\sigma \overline{W_\sigma}$; the inner product sums $\overline{V_\sigma} W_\sigma$.
- **Chapter 4**: KS inequality is for UNITAL maps, not TP. HS contraction requires BOTH.
- **Chapter 4**: `kraus_commute_of_ks_equality` proves $X K_i^\dagger = K_i^\dagger E(X)$, not Kraus commutation with a unitary.
- **Chapter 4**: Wolf citations: Equation (5.2) for KS; Proposition 6.1 spectral radius; Proposition 6.2 trivial Jordan; Theorem 6.6 irreducibility; Proposition 6.8 Hermitian FP; Theorem 6.11 primitive; Theorem 6.13 Cesàro.
