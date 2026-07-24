# Blueprint Style Guide & Lessons Learned

## Core Philosophy
The blueprint links the mathematics to its Lean formalization. A reader should be able to read a blueprint entry and immediately understand the corresponding Lean declaration. Conversely, someone reading the Lean code should find the blueprint proof sketch faithful to what the code actually does.

## General Principles
1. **Blueprint ↔ Lean must match.** Every `\lean{X}` tag must correspond to an actual Lean declaration. Every proof sketch must match what the Lean proof actually does — not a hand-wavy version of it.
2. **Standalone documents.** `blueprint/` and `docs/slides/` have separate
   preambles, prose macros, bibliographies, and build entry points. They share
   only the repository-wide tensor-network language in `tex/tenkz/`; neither
   document tree imports files from the other.
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
8. **Match the primary Lean declaration exactly.** If the principal declaration
   says `theorem X`, use `\begin{theorem}`; if it says `lemma X`, use
   `\begin{lemma}`. Never use `\begin{proposition}` (Lean has no `proposition`
   keyword). Label prefixes are `thm:` for theorems, `lem:` for lemmas, `cor:`
   for corollaries, and `def:` for definitions. Immediate projections and
   accessor lemmas may share the parent entry as described below; the
   environment then follows the principal declaration rather than each
   subordinate `\lean{...}` tag.
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
    mathematical prose. The explicit proof-status markers in
    [`prose_style.md`](prose_style.md) are for Lean docstrings and comments, not
    blueprint-visible paragraphs.
11. **Proofs are carried by formulas.** For mathematical proof sketches,
    especially tensor-network and overlap arguments, state the main equations
    explicitly instead of replacing them by verbal paraphrase. Short equations
    should usually be inline with `$...$`; use displayed equations only when the
    expression is long or when several implications must be compared. Avoid
    long paragraphs whose only mathematical content is described in words.
12. **Display selectively; cite displayed equations with `\ref`, not
    words.** Keep a short, single-step formula inline with `$...$` when it reads
    naturally in the sentence and is not cited elsewhere. Do not promote a
    thin conclusion to a numbered display merely to assign it a label. Retain
    a display for a long formula, a central definition or identity, several
    cases or conditions, or a genuine derivation. Use `align` for every retained
    display, including a single-line display; do not introduce new `equation`,
    `gather`, `multline`, or bare `\[...\]` environments.

    If prose points back to a displayed equation — in the same proof, a later
    proof, or another chapter — give it a concise
    `\label{eq:<chapter-prefix>_...}` and cite it with plain `\ref`, never
    `\eqref`: write `(\ref{eq:foo_bar})` or
    `Substituting~(\ref{eq:foo_bar}) into...`. This concise parenthesized form
    avoids repeating the word “equation.” Replace positional phrases such as
    "the preceding identity", "the equation above", "the first displayed
    identity", and "the two equations above" with explicit references. The
    same rule applies across chapters: cite the earlier equation label rather
    than describing its position or restating its number.
    - **Keep labels concise.** `eq:<chapter-prefix>_<two-to-four-word gist>`
      (e.g. `eq:ph_boundary_scaled`, not
      `eq:ph_boundary_crossing_scaled_boundary_equal_via_intermediate_step`).
      Reuse the surrounding entry's own label as the prefix gist rather than
      re-describing the whole statement; drop words already implied by the
      chapter prefix.
    - **Keep aligned derivations dense.** A short equality chain such as
      `$a=b=c=d$` should normally occupy one aligned line, not four lines with
      one equality per line. Break a derivation across lines only when the
      intermediate expressions are long, independently referenced, or require
      separate explanation. If a display carries several logically distinct
      equations, give each its own aligned line rather than joining them with
      `\qquad` or commas. Give a line its own `\label{}` only when that line is
      independently cited. References to a different earlier display must use
      its label.

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
  Do not introduce visible note labels such as `Formalization note.` in
  blueprint prose.
  If the auxiliary route is no longer used by the checked proof, delete the entry
  rather than keeping an unmotivated theorem-like statement in the blueprint.
- **Write tensor-network proofs with equations.** When a tensor-network proof
  applies injectivity, inserts a boundary tensor, or compares two contractions,
  introduce notation such as $P_i$, $\mathcal C_I$, or $X$ and write the
  implication being used. A sketch like "apply injectivity twice" is not enough
  when the paper proof distinguishes regions, boundaries, or inserted matrices.
  Display the sequence of equalities or kernel implications that carries the
  argument.

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
- The `chNN_` prefix is a stable subject identifier, not the chapter's displayed
  position.  The order of the `\input` commands in the relevant content router
  determines the order in the book; do not renumber existing chapter files when
  that order changes.
- Definitions and results are numbered within the smallest displayed division:
  within a subsection when one is present, and otherwise within the section.
  Thus an entry in Subsection 22.4.4 is numbered `22.4.4.n`, while an entry
  directly under Section 6.2 is numbered `6.2.n`.
- Do not introduce a redundant sole division. If all of a chapter lies in one
  section, remove that wrapper and promote its subsections to sections. If a
  section would contain only one subsection, promote that subsection to a
  section or remove the unnecessary subdivision.

### Main narrative and supporting appendices

The blueprint has two simultaneous obligations: its main chapters must read as
mathematics, and the complete document must retain the technical results that
connect that mathematics to the formalization. Satisfy both obligations by
keeping the mathematical narrative in the main chapters and collecting genuinely
supporting results in appendices at the end of the document.

#### What remains in the main chapters

1. Every theorem, lemma, proposition, or definition that is named in the primary
   paper or mathematical notes remains in the main text. Substantial new
   mathematical results introduced by the project also remain there.
2. Each retained result has a genuine mathematical proof or proof sketch. A
   proof consisting only of “see Appendix” is not acceptable.
3. A proof sketch states the central construction, the main implication or
   equations, the order of the argument, and why the hypotheses suffice. It
   identifies the precise technical points deferred to the appendices and cites
   their labels.
4. Definitions and notation needed to understand a result appear before their
   first use. They are not deferred merely because their formal definitions are
   verbose.
5. A conceptually important intermediate lemma may remain in the main text even
   when it is not named in the source. Reader comprehension, not only the
   explicit `\uses` graph, determines whether a result belongs to the narrative.

A suitable main-text proof sketch has the following form:

```latex
\begin{proof}
    Normalize the faithful fixed point and decompose its support into minimal
    invariant components. Perron--Frobenius theory gives a positive gauge on
    each component, and a common blocking length removes the residual periods.
    The resulting tensor is therefore a weighted direct sum of primitive
    left-canonical blocks. Lemma~\ref{lem:app_support_compression} proves that
    the support reduction preserves the matrix product vectors, while
    Proposition~\ref{prop:app_common_blocking} supplies the common blocking
    length.
\end{proof}
```

This sketch explains why the result is true and tells the reader exactly what
is verified later. Do not replace it by a vague reference to an entire appendix.

#### What may move to a supporting appendix

Supporting appendices may contain intermediate results introduced to manage
support restrictions, casts, reindexings, common dimensions, preservation under
standard constructions, routine matrix identities, and other detailed steps
that do not carry the main mathematical narrative. Long proof expansions may
also move when the main chapter retains the theorem, its proof mechanism, and
precise references to the deferred ingredients.

Do not move a result merely because Lean needs it. Do not move source-named
results, central constructions, or hypotheses needed to understand later
chapters. Before relocation, check both the transitive `\uses` graph and ordinary
`\ref` references, then read the surrounding mathematics to detect expository
dependencies that are not encoded in the graph.

#### Write appendices as mathematical appendices

Every appendix chapter corresponds to exactly one main chapter; a main chapter
may have no appendix. Appendix source file names use the parent chapter's stable
`chNN` subject identifier. Later reuse by another chapter does not change the
result's primary ownership. The displayed umbrella title is `Appendices`, and
appendix chapter titles use a mathematically descriptive
`...: Supporting Results` rather than `Technical Complements`.

An appendix is not a dump of Lean declarations or a transcription of a source
file. It must read like an appendix written by a mathematician:

1. Organize it by mathematical subject, not by Lean namespace, module, proof
   tactic, or implementation task. Use titles such as “Support compression in
   canonical reduction,” not “Auxiliary helpers” or “Lean details.”
2. Begin each appendix or section with a short statement of its purpose and the
   main results it supports, with backward references to those results.
3. Introduce notation before use and give enough local context that the argument
   can be read without reconstructing the main proof from the formal code.
4. State results at their natural mathematical level. Group immediate
   projections, equivalent formulations, and bookkeeping variants under the
   substantive parent entry according to the display hierarchy below.
5. Give complete mathematical proofs with the important equations visible.
   Explain the reason for a support restriction, reindexing, or preservation
   step; do not narrate tactics or type-checking operations.
6. End a technical chain by stating explicitly which step of the main theorem it
   supplies. Use exact theorem and lemma references in both directions.
7. Preserve useful existing labels when moving material. Labels are global, so
   forward references from a main chapter to an appendix are valid after the
   normal repeated LaTeX compilation.

For example, an appendix section should open along the following lines:

```latex
\section{Support compression in canonical reduction}
\label{sec:app_canonical_support}

This section proves the support and reindexing results used in
Theorem~\ref{thm:canonical_block_decomposition}. The main proof explains the
irreducible decomposition; here we verify that each support reduction preserves
the associated matrix product vectors.
```

#### Full and Fundamental-Theorem/SPT builds

The repository maintains two reader-facing builds from one source of truth:

- the complete blueprint, routed by `content.tex` and built from `print.tex`;
- the focused Fundamental-Theorem/SPT volume, routed by `content_ft_mps.tex` and
  built from `print_ft_mps.tex` (or the repository build script documented
  below).

The focused volume contains the main Fundamental-Theorem and symmetry/string-
order/SPT chapters together with all supporting appendices needed by those
chapters. The complete blueprint contains the same files and adds the later
chapters and their supporting appendices. Never duplicate theorem text or
maintain build-specific copies of an appendix.

Appendices occur after the main chapters in both builds. Shared FT/SPT appendix
files must be included by both content routers, directly or through a common
appendix manifest. An FT/SPT main chapter may refer only to material included in
the focused build; this reference closure must be checked independently of the
complete build. Later chapters may use additional appendices present only in the
complete blueprint.

Every relocation must therefore pass all of the following checks:

1. the named mathematical result and an informative proof sketch remain in the
   main chapter;
2. every deferred technical claim is cited by an exact label;
3. the appendix gives a coherent, complete mathematical treatment and refers
   back to the main result it supports;
4. labels, `\lean` tags, `\leanok`, `\uses`, citations, and theorem hypotheses
   remain faithful;
5. both the complete build and the focused Fundamental-Theorem/SPT build compile
   repeatedly with no new unresolved references;
6. the blueprint web build and declaration synchronization introduce no new
   failures.

### Display hierarchy for formal declarations

The blueprint is a mathematical document, not an inventory containing one
numbered entry for every declaration. Apply the following hierarchy.

1. Display definitions that introduce mathematical objects and theorems that
   state source-level results or substantial new implications.
2. Display a reusable intermediate consequence as a lemma. Display an
   immediate named consequence of a theorem as a corollary when that relation
   is mathematically informative.
3. Do not give separate numbered entries to structure-field projections,
   accessor statements, immediate unfoldings of a predicate, or the two
   components of a conjunction already stated in a parent entry. Keep these
   declarations in Lean, but attach their `\lean{...}` tags to the parent
   definition, theorem, or lemma whose content contains them.
4. When theorem data and an existential witness expose the same equations,
   state the equations once at the natural mathematical level. Group the
   transport declarations under that entry instead of repeating the same
   statement for each representation of the data.
5. Keep a separately numbered final formula only when later mathematics
   cites the formula itself. Such a direct consequence should normally be a
   lemma or corollary, not a theorem.

Before removing an entry, search all `\uses` and `\ref` occurrences of its
label. Redirect genuine dependencies to the retained parent result, and keep
all declaration links on that result so that formalization coverage remains
visible.

Tensor-network diagram conventions are recorded in the second-edition manual
under [`docs/tenkz/`](tenkz/). The blueprint loads `tenkz` directly. Chapter
sources write native grid, lattice, commutative-diagram, or free-placement
bodies beside the mathematics they depict; there is no central figure
catalogue. The generic web bridge captures those same bodies verbatim and
compiles them against the repository package.

Every diagram source must include adjacent comments stating the represented
formula or source passage, the ink-to-index correspondence, the contracted and
open legs, and the resulting boundary signature. Prefer exact mathematics to
a decorative picture when the source does not specify an unambiguous network.

PEPS blueprint statements should keep the relevant tensor-network diagram
attached to the theorem, lemma, or definition whose content it depicts. If the
source paper proves a step by a diagrammatic equality or a blocked-region
picture, the blueprint entry should contain the corresponding native diagram and
the proof sketch should name the regions or inserted tensors appearing in it.

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

The complete blueprint uses `blueprint/src/content.tex` as its chapter router.
The Fundamental Theorem of Matrix Product States volume uses the restricted
router `blueprint/src/content_ft_mps.tex` and is built by the repository script
shown below.

```bash
leanblueprint pdf     # PDF → blueprint/print/print.pdf
leanblueprint web     # HTML → blueprint/web/
leanblueprint serve   # local server at http://0.0.0.0:8000/
leanblueprint all     # pdf + web + checkdecls
./scripts/build_blueprint_ch01_12.sh  # FT--MPS PDF → blueprint/print/print12.pdf
```

## Fact-Check Lessons
- **Chapter 2**: `mpv` in Lean returns a scalar (the σ-component), NOT a ket vector. The ket is `mpvState`. Blueprint presents the ket form (standard physics) but `\lean{MPSTensor.mpv}` points to the component function — this is acceptable as long as it's clear.
- **Chapter 2**: Overlap and inner product differ by conjugation. Lean: `mpvOverlap A B N = star (mpvInner A B N)`. The overlap sums $V_\sigma \overline{W_\sigma}$; the inner product sums $\overline{V_\sigma} W_\sigma$.
- **Chapter 4**: KS inequality is for UNITAL maps, not TP. HS contraction requires BOTH.
- **Chapter 4**: `kraus_commute_of_ks_equality` proves $X K_i^\dagger = K_i^\dagger E(X)$, not Kraus commutation with a unitary.
- **Chapter 4**: Wolf citations (verified against the PDF, 2026-06): Equation (5.2) = Kadison–Schwarz; Proposition 6.1 = spectral radius; Theorem 6.2(1) = irreducibility definition; Theorem 6.7 = primitive maps; Proposition 6.8 = positive (Hermitian) fixed points; Theorem 6.11 = stationary states (Brouwer); Theorem 6.12 = fixed-point $*$-algebra; Theorem 6.13 = fixed points and Kraus commutant.

## Citing external sources (verified conventions)

External theorem/equation numbers were cross-checked against the **PDF-converted text** (never the LaTeX source, which can be inaccurate). Wolf per-chapter PDFs live in `Notes/WolfNotePDF/`; paper sources are the arXiv PDFs.

- **Wolf** (`Wolf2012Quantum`): sub-parts use a **parenthetical** form with no word — `Theorem~6.2(1)`, `Corollary~7.2(3)`, `Theorem~2.1(4)`, `Lemma~6.3(b)` — matching Wolf's bare `1. 2. 3.` enumeration. Spell out environment words (`Lemma~`, `Equations~`; never `Lem.`/`Eqs.`). Implications: `Proposition~7.6, (1)$\Rightarrow$(3)` / `$\Leftrightarrow$`.
- **MPDO paper** is cited on the **arXiv preprint** key `Cirac2016MPDO_arXiv` with **Arabic** numbers (Theorem 2.10 = proportional FT, Corollary 2.11 = equal FT, Theorem 4.14(ii) = MPDO structure, Section 2.3 = canonical forms). The published-Annals key `Cirac2017MPDO_AnnPhys` (Roman II.1/IV.13) is **not** used in citations — its numbering is not locally verifiable.
- **CPGSV21** (`Cirac2021Matrix`, RMP) uses **Roman** numbering exclusively (Theorem IV.4 = proportional FT, Corollary IV.5 = equal FT, Theorem IV.16 = ground-space generation, Definition IV.2 = basis of normal tensors, Section II.B.3 = correlations). It has a single appendix (A); do not cite an "Appendix B" to it.
- **PGVWC07** (`PerezGarcia2007Matrix`): Theorem 4 = TI canonical form, Theorem 5 = periodic decomposition, Lemma 3 = matrix-span lemma. Cite resolved numbers, never internal `\label`s (`Th:TIcanonical`, etc.).
